#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include <densemat.h>
#include <bandmat.h>

//ldoc on
/**
 * ## Band matrix construction
 * 
 */
// Allocate/free/clear a band matrix
bandmat_t bandmat_malloc(int n, int b)
{
  bandmat_t vm = surely_malloc(sizeof(struct bandmat_t) + (n*(b+1))*sizeof(double));
  vm->m=n; vm->b=b;
  return vm;
}

void bandmat_free(bandmat_t vm)
{
    free(vm);
}

void bandmatn_clear(double* data, int m, int b)
{
  memset(data, 0, (m*(b+1)) * sizeof(double));
}

void bandmat_clear(bandmat_t vm)
{
  bandmatn_clear(vm->data, vm->m, vm->b);
}



// Getting, setting, adding to band matrices
double bandmatn_get(double *data, int rows, int i, int d) {
  return data[i+d*rows];
}

void bandmatn_set(double *data, int rows, int i, int d, double x) {
  data[i+d*rows] = x;
}

void bandmatn_addto(double *data, int rows, int i, int d, double x) {
  data[i+d*rows] += x;
}

double bandmat_get(bandmat_t dm, int i, int d) {
  return bandmatn_get(dm->data, dm->m, i, d);
}

void bandmat_set(bandmat_t dm, int i, int d, double x) {
  bandmatn_set(dm->data, dm->m, i, d, x);
}

void bandmat_addto(bandmat_t dm, int i, int d, double x) {
  bandmatn_addto(dm->data, dm->m, i, d, x);
}


// Convert dense n-by-n A to band matrix P with bandwidth bw
bandmat_t dense_to_band(densemat_t A, int bw)
{
    int n = A->n;
    bandmat_t P = bandmat_malloc(n, bw);
    for (int d = 0; d <= bw; ++d)
        for (int j = d; j < n; ++j) {
            int i = j-d;
	    bandmat_set(P,j,d, densemat_get(A,i,j));
        }
    return P;
}

/**
 * ## Printing a band matrix
 * 
 * When printing a band matrix, we usually print just the structural
 * nonzeros.  Unless the matrix is very small, trying to introduce
 * spaces or dots for structural zeros usually just makes the output
 * too big to fit on a screen; hence, we will *almost* just print the
 * underlying `n`-by-`b+1` data array.  The only difference is that we
 * will not bother to print out the "don't care" values that are at
 * the start of the superdiagonal representations (since they will be
 * garbage unless we zeroed them out, and anyway -- we don't care
 * about them).
 * 
 */
// Print band format array
void bandmat_print(bandmat_t PA)
{
    int n = PA->m, bw = PA->b;

    for (int i = 0; i < n; ++i) {
        for (int d = 0; d <= bw && d <= i; ++d)
	  printf("  % 6.3g", bandmat_get(PA,i,d));
        printf("\n");
    }
}

/**
 * ## Band Cholesky and triangular solves
 * 
 * When computing a Cholesky factorization of a band matrix, the Schur
 * complement update step only affects elements that were already
 * structural nonzeros.  Hence, Cholesky factorization of a band
 * matrix can be done purely within the band data structure.  The
 * algorithm is essentially identical to the ordinary Cholesky
 * factorization, except with indexing appropriate to the packed data
 * structure.  As with the dense Cholesky implementation in
 * `densemat_t`, we only ever reference the upper triangle of the
 * matrix, and we overwrite the input arrays (representing the upper
 * triangle of a symmetric input) by the output (representing an upper
 * triangular Cholesky factor).  Also as with dense Cholesky, we will
 * error out if we encounter a negative diagonal in a Schur complement
 * (violating the assumption of positive definiteness).
 * 
 */
void bandmat_factor(bandmat_t PA)
{
    int n = PA->m, bw=PA->b;
    
    
    for (int k = 0; k < n; ++k) {

        // Compute kth diagonal element
        assert(bandmat_get(PA,k,0) >= 0);
	bandmat_set(PA,k,0, sqrt(bandmat_get(PA,k,0)));

        // Scale across the row
        for (int j = k+1; j < n && j <= k+bw; ++j)
	  bandmat_set(PA,j,j-k, bandmat_get(PA,j,j-k)/bandmat_get(PA,k,0));

        // Apply the Schur complement update
        for (int j = k+1; j < n && j <= k+bw; ++j)
            for (int i = k+1; i <= j; ++i)
	      bandmat_addto(PA,j,j-i, - bandmat_get(PA,i,i-k)*bandmat_get(PA,j,j-k));
    }    
}

/**
 * The `bandmat_solve(PR, x)` routine uses a band Cholesky factor $R$
 * of the matrix $A$ to solve $Ax = b$.  The `PR` input argument gives
 * the Cholesky factor (as computed by `bandmat_cholesky`);
 * on input the `x` argument should be set to the system right-hand side,
 * and on output it will be the solution vector.
 */
void bandmat_solve(bandmat_t PR, double* x)
{
    int n = PR->m, bw = PR->b;
    
    // Forward substitution
    for (int i = 0; i < n; ++i) {
        double bi = x[i];
        for (int dj = 1; dj <= bw && dj <= i; ++dj)
	  bi -= bandmat_get(PR,i,dj)*x[i-dj];
        x[i] = bi/bandmat_get(PR,i,0);
    }

    // Backward substitution
    for (int i = n-1; i >= 0; --i) {
        double yi = x[i];
        for (int j = i+1; j <= i+bw && j < n; ++j)
	  yi -= bandmat_get(PR,j,j-i)*x[j];
        x[i] = yi/bandmat_get(PR,i,0);
    }
}

/**
 * ## Norm computations
 */

double bandmat_norm2(bandmat_t vm)
{
  return data_norm2(vm->data, vm->m*(vm->b+1));
}

double bandmat_norm(bandmat_t vm)
{
  return data_norm(vm->data, vm->m*(vm->b+1));
}
