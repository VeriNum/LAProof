#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <assert.h>

#include "densemat.h"

//ldoc on
/**
 * ## Memory management
 *
 * The `densemat_malloc` function allocates space for the head structure
 * (which contains the first entry in the data array) along with space
 * for the remainder of the `m*n` double precision numbers in the data array.  
 */
densemat_t densemat_malloc(int m, int n)
{
    densemat_t h = surely_malloc(sizeof(struct densemat_t) + (m*n)*sizeof(double));
    h->m=m;
    h->n=n;
    return h;
}

void densemat_free(densemat_t vm)
{
    free(vm);
}

void densematn_clear(double* data, int m, int n)
{
  double_clear(data,m*n);
}

void densemat_clear(densemat_t vm)
{
  densematn_clear(vm->data, vm->m, vm->n);
}

double densematn_get(double *data, int rows, int i, int j) {
  return data[i+j*rows];
}

void densematn_set(double *data, int rows, int i, int j, double x) {
  data[i+j*rows]= x;
}


void densematn_addto(double *data, int rows, int i, int j, double x) {
  data[i+j*rows] += x;
}

double densemat_get(densemat_t dm, int i, int j) {
  return densematn_get(dm->data,dm->m,i,j);
}

void densemat_set(densemat_t dm, int i, int j, double x) {
  densematn_set(dm->data,dm->m,i,j,x);
}


void densemat_addto(densemat_t dm, int i, int j, double x) {
  densematn_addto(dm->data,dm->m,i,j,x);
}

/**
 * ## I/O
 * 
 * We provide a print routines as an aid to debugging.  In order
 * to make sure that modest size matrices can be printed on the
 * screen in a digestible matter, we only print the first couple
 * digits in each entry.  Note that we assume column major layout
 * throughout.
 */
void densematn_print(double* data, int m, int n)
{
    printf("%d-by-%d\n", m, n);
    for (int i = 0; i < m; ++i) {
        for (int j = 0; j < n; ++j)
	  printf(" % 6.2g", densematn_get(data,m,i,j));
        printf("\n");
    }
}

void densemat_print(densemat_t vm)
{
    densematn_print(vm->data, vm->m, vm->n);
}

/**
 * ## Cholesky factorization
 * 
 * For our finite element code, we will largely work with SPD matrices
 * for which a Cholesky solve is appropriate.  On input, we assume a column
 * major representation in which the upper triangle represents the upper
 * triangle of an SPD matrix; the lower triangle is ignored.  On output,
 * the upper triangle of the matrix argument is overwritten by the
 * Cholesky factor.  We will error out if we encounter a negative diagonal
 * (in violation of the assumed positive definiteness).
 * 
 * We will not bother to show the wrapper around the `densematn` version.
 */
void densematn_cfactor(double* A, int n)
{ 
  /* sdot method */
  int i,j,k;
  double s;
  for (j=0; j<n; j++) {
     for (i=0; i<j; i++) {
       s = densematn_get(A,n,i,j);
       for (k=0; k<i; k++)
	 s = s - densematn_get(A,n,k,i)*densematn_get(A,n,k,j);
       densematn_set(A,n,i,j, s/densematn_get(A,n,i,i));
     }
     s = densematn_get(A,n,j,j);
     for (k=0; k<j; k++) {
         double rkj = densematn_get(A,n,k,j);
     	 s = s - rkj*rkj;
     }
     densematn_set(A,n,j,j, sqrt(s));
  }
}

//ldoc off

/**
 * Outer-product Cholesky factorization
 */
void densematn_cfactor_outer(double* A, int n)
{ 
    for (int k = 0; k < n; ++k) {

        // Compute kth diagonal element
        double akk = densematn_get(A,n,k,k);
        assert(akk >= 0.0);
        double rkk = sqrt(akk);
	densematn_set(A,n,k,k,rkk);

        // Scale across the row
        for (int j = k+1; j < n; ++j)
	  densematn_set(A,n,k,j, densematn_get(A,n,k,j)/rkk);

        // Apply the Schur complement update
        for (int j = k+1; j < n; ++j)
            for (int i = k+1; i <= j; ++i)
	      densematn_addto(A,n,i,j, -densematn_get(A,n,k,i)*densematn_get(A,n,k,j));
    }
}

/**
 * Block Cholesky
 * WARNING: NOTHING ABOUT BLOCK CHOLESKY HAS BEEN TESTED OR PROVED,
 * PROBABLY CONTAINS BUGS
 */

/**
 * Block solve, for block Cholesky
 * Let A be an nxn matrix
 * let R11 be an UT submatrix, dimension cxc, whose top-left corner is at (l,l) in A
 * let A12 be a general submatrix, dimension b*(b-c), at (l,l+c) in A
 * Solve for R12 such that A12= R11^T*R12, and place it at (l,l+c) in A, overwriting A12
 */
void blocksolve(double *A, int n, int b, int c, int l) {
    // Forward substitution
  for (int k=0; k<b-c; ++k)
    for (int i = 0; i < c; ++i) {
      double bi = densematn_get(A,n,l+i,l+c+k);
      for (int j = 0; j < i; ++j)
	bi -= densematn_get(A,n,l+j,l+i)*densematn_get(A,n,l+j,l+c+k);
      densematn_set(A,n,l+i,l+c+k, bi/densematn_get(A,n,l+i,l+i));
    }
}

/**
 * Helper function for block Cholesky.
 * Let A be an nxn matrix
 * Let R12 be a submatrix, dimension b*(b-c), top-left corner at (l,l+c) in A
 * Let A22 be a submatrix, dimension (b-c)*(b-c), at (l+c,l+c) in A
 * Compute A22-R12^T*R12 and store it back over A22, i.e., at (l+c,l+c) in A
 */
void subtractoff(double *A, int n, int b, int c, int l) {
  int i,j,k;
  // Is this the best loop-nest in for this situation? 
  for (i=0; i<b-c; i++)
    for (j=0; j<b-c; j++) {
      double s = densematn_get(A,n,l+i,l+j);
      for (k=0; k<b; k++)
	s -= densematn_get(A,n,l+k,l+c+i)*densematn_get(A,n,l+j,l+c+i);
      densematn_set(A,n,l+i,l+j,s);
    }
}  

/**
 * Block Cholesky
 * factor bxb block starting at index l in an nxn matrix
 * To factor the entire matrix, call densematn_cfactor_block(A,n,n,0)
 */

void densematn_cfactor_block(double *A, int n, int b, int l) {
   if (b==1) {
     densematn_set(A,n,l,l, sqrt(densematn_get(A,n,l,l)));
   }
   else {
     int c = b/2;
     densematn_cfactor_block(A,n,c,l);
     blocksolve(A,n,b,c,l);
     subtractoff(A,n,b,c,l);
     densematn_cfactor_block(A,n,b-c,l+c);
   }
}

void densemat_cfactor(densemat_t A) {
    assert(A->m == A->n);
    densematn_cfactor(A->data, A->m);
}

//ldoc on
/**
 * The `densemat_csolve(R, x)` function assumes a Cholesky factor in the
 * upper triangle of input argument `R`; the argument `x` is the
 * right-hand side vector $b$ on input, and the solution vector $x$ on
 * output.
 */
void densematn_csolve(double* R, double* x, int n)
{
    // Forward substitution
    for (int i = 0; i < n; ++i) {
      double bi = densematn_get(x,n,i,0);
        for (int j = 0; j < i; ++j)
	  bi -= densematn_get(R,n,j,i)*densematn_get(x,n,j,0);
	densematn_set(x,n,i,0, bi/densematn_get(R,n,i,i));
    }

    // Backward substitution
    for (int i = n; i > 0; --i) {
      // start loop at n to avoid negative indexes, in case we ever
      // want to use unsigned integers to increase the indexing range
      double yi = densematn_get(x,n,i-1,0);
        for (int j = i; j < n; ++j)
	  yi -= densematn_get(R,n,i-1,j)*densematn_get(x,n,j,0);
	densematn_set(x,n,i-1,0, yi/densematn_get(R,n,i-1,i-1));
    }
}

//ldoc off
void densemat_csolve(densemat_t R, double* x)
{
    densematn_csolve(R->data, x, R->n);
}

//ldoc on
/**
 * ## LU factorization and solve
 * 
 * Even if the system matrices in a finite element code are SPD, the
 * Jacobians that are used in mapped elements generally will not be.
 * Therefore, we need a basic pivoted LU factorization along with the basic
 * Cholesky.
 * 
 * The factorization routine overwrites `A` with the $L$ and $U$ factors,
 * packed into the (strictly) lower and the upper triangular parts of $A$.
 * The pivot vector is stored in `ipiv`, where `ipiv[i] = l` implies that
 * rows $i$ and $l$ were swapped at step $i$ of the elimination.
 */
void densematn_lufactor(int* ipiv, double* A, int n)
{
    for (int j = 0; j < n; ++j) {

        // Find pivot row
        int ipivj = j;
        for (int i = j+1; i < n; ++i)
            if (fabs(A[i+n*j]) > fabs(A[ipivj+n*j]))
                ipivj = i;
        ipiv[j] = ipivj;

        // Apply row swap, if needed
        if (ipivj != j)
            for (int k = j; k < n; ++k) {
  	      double t = densematn_get(A,n,j,k);
	      densematn_set(A,n,j,k, densematn_get(A,n,ipivj,k));
	      densematn_set(A,n,ipivj,k, t);
            }

        // Compute multipliers
        double Ujj = densematn_get(A,n,j,j);
        for (int i = j+1; i < n; ++i)
	  densematn_set(A,n,i,j, densematn_get(A,n,i,j)/Ujj);

        // Apply Schur complement update
        for (int k = j+1; k < n; ++k) {
	  double Ujk = densematn_get(A,n,j,k);
            for (int i = j+1; i < n; ++i) {
	      double Lij = densematn_get(A,n,i,j);
	      densematn_addto(A,n,i,k, -Lij*Ujk);
            }
        }
    }
}

/**
 * The `densemat_lusolve` function assumes that the factorization has
 * already been computed.  On input, `x` represents $b$; on output,
 * `x` represents $x = A^{-1} b$.
 */
void densematn_lusolve(int* ipiv, double* A, double* x, int n)
{
    // Apply P
    for (int i = 0; i < n; ++i)
        if (ipiv[i] != i) {
            double t = x[i];
            x[i] = x[ipiv[i]];
            x[ipiv[i]] = t;
        }

    // Forward substitution
    for (int i = 0; i < n; ++i) {
        double bi = x[i];
        for (int j = 0; j < i; ++j)
	  bi -= densematn_get(A,n,i,j)*x[j];
        x[i] = bi;
    }

    // Backward substitution
    for (int i = n; i >= 0; --i) {
        double yi = x[i];
        for (int j = i+1; j < n; ++j)
	  yi -= densematn_get(A,n,i,j)*x[j];
        x[i] = yi/densematn_get(A,n,i,i);
    }
}

/**
 * The `densemat_lusolveT` variant solves a linear system $A^T x = b$ where
 * $A^T = U^T L^T P$
 */
void densematn_lusolveT(int* ipiv, double* A, double* x, int n)
{
    // Forward substitution (with U^T)
    for (int i = 0; i < n; ++i) {
        double bi = x[i];
        for (int j = 0; j < i; ++j)
	  bi -= densematn_get(A,n,j,i)*x[j];
        x[i] = bi/A[i+i*n];
    }
    
    // Backward substitution (with L^T)
    for (int i = n; i >= 0; --i) {
        double yi = x[i];
        for (int j = i+1; j < n; ++j)
	  yi -= densematn_get(A,n,j,i)*x[j];
        x[i] = yi;
    }

    // Apply P^T
    for (int i = n-1; i >= 0; --i)
        if (ipiv[i] != i) {
            double t = x[i];
            x[i] = x[ipiv[i]];
            x[ipiv[i]] = t;
        }
}

/**
 * The Jacobian determinant can be computed from the product of the
 * diagonals of $U$ times the sign of the permutation matrix (given by
 * the parity of the number of swaps in the factored permutation).
 */
double densematn_lujac(int* ipiv, double* A, int n)
{
    double J = 1.0;
    int nswap = 0;
    for (int i = 0; i < n; ++i) {
        if (ipiv[i] != i)
            ++nswap;
        J *= densematn_get(A,n,i,i);
    }
    return (nswap % 2 == 0) ? J : -J;
}

//ldoc off
/**
 * We don't bother including the `densemat_t` callthroughs in the
 * autodoc output.
 */

void densemat_lufactor(int* ipiv, densemat_t A)
{
    assert(A->m == A->n);
    densematn_lufactor(ipiv, A->data, A->m);
}

void densemat_lusolve(int* ipiv, densemat_t A, double* x)
{
    densematn_lusolve(ipiv, A->data, x, A->m);
}

void densemat_lusolveT(int* ipiv, densemat_t A, double* x)
{
    densematn_lusolveT(ipiv, A->data, x, A->m);
}

double densemat_lujac(int* ipiv, densemat_t A)
{
    return densematn_lujac(ipiv, A->data, A->m);
}

//ldoc on
/**
 * ## Norm computations
 * 
 * Just for checking on residuals and errors, it's convenient to have
 * some functions for computing the squared Euclidean norm and the
 * norm of a vector.  We assume that things are sufficiently well scaled
 * that we don't need to worry about over/underflow.
 */
double data_norm2(double* data, int n)
{
    double result = 0.0;
    for (int j = 0; j < n; ++j) {
        double xj = data[j];
	result = fma(xj,xj,result);
    }
    return result;
}

double data_norm(double* data, int n)
{
    return sqrt(data_norm2(data, n));
}

double densemat_norm2(densemat_t vm)
{
    return data_norm2(vm->data, vm->m*vm->n);
}

double densemat_norm(densemat_t vm)
{
    return data_norm(vm->data, vm->m*vm->n);
}

/** dot product: let x be an m*n matrix, let y be an n*p matrix,
    multiply row of x by column j of y. */
double densematn_dotprod(int m, int n, int p, int i, int j, double *x, double *y) {
  int k; double s=0.0;
  for (k=0; k<n; k++)
    s = densematn_get(x,m,i,k)*densematn_get(y,n,k,j) + s;
  return s;
}

double densemat_dotprod(int i, int j, densemat_t x, densemat_t y) {
  return densematn_dotprod(x->m, x->n, y->n, i, j, x->data, y->data);
}

/** compute z = x * y
 */
void densematn_mult(int m, int n, int p, double *x, double *y, double *z) {
  int i,j;
  for (i=0; i<m; i++)
    for (j=0; j<p; j++)
      densematn_set(z, m, i, j, densematn_dotprod(m,n,p,i,j,x,y));
}

void densemat_mult(densemat_t x, densemat_t y, densemat_t z) {
	densematn_mult(x->m, x->n, y->n, x->data, y->data, z->data);
}
