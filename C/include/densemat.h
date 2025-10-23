#ifndef DENSEMAT_H
#define DENSEMAT_H

#include "alloc.h"

//ldoc on
/**
 * # `densemat.h`: Dense matrix operations
 * 
 * To represent a dense matrix, we define a structure `densemat_t` consisting of 
 * dimensions followed by a data array.
 */

typedef struct densemat_t {
    int m,n;  // rows, columns
    double data[0];  // Start of data array
} *densemat_t;

// Create and free 
densemat_t densemat_malloc(int m, int n);
void densemat_free(densemat_t dm);

// Clear storage
void densematn_clear(double* data, int m, int n);
void densemat_clear(densemat_t dm);

// Print array (assumes column major order)
void densematn_print(double* data, int m, int n);
void densemat_print(densemat_t data);

// Cholesky factorization and solve (uses only upper triangular)
void densematn_cfactor(double* A, int n);
void densematn_csolve(double* R, double* x, int n);
void densemat_cfactor(densemat_t A);
void densemat_csolve(densemat_t R, double* x);

// LU factorization and solve
void densematn_lufactor(int* ipiv, double* A, int n);
void densematn_lusolve(int* ipiv, double* A, double* x, int n);
void densematn_lusolveT(int* ipiv, double* A, double* x, int n);
void densemat_lufactor(int* ipiv, densemat_t A);
void densemat_lusolve(int* ipiv, densemat_t A, double* x);
void densemat_lusolveT(int* ipiv, densemat_t A, double* x);

// Jacobian determinant from LU factorization
double densematn_lujac(int* ipiv, double* A, int n);
double densemat_lujac(int* ipiv, densemat_t A);

// Squared norm and norm computations
double data_norm2(double* data, int n);
double data_norm(double* data, int n);
double densemat_norm2(densemat_t dm);
double densemat_norm(densemat_t dm);

/**
 * # Accessor/setter functions for column-major indexing
 * To subscript a matrix, that is, to fetch and store individual
 * matrix entries, we don't use C array indexing directly.
 * Instead, we use these functions, which implement column-major indexing
 * within a 1-dimensional array.
 *   Even to access a column vector, where you'd think C array indexing
 * would be very natural, we use these 2-d functions.
 *   The reason is to simplify the proof.  That is, we can specify
 * and prove, once and for all, correctness of column-major indexing
 * (and the connection to the matrix abstraction of the Rocq Mathematical
 * components library), and then reason about the abstraction in C (that is,
 * function call) using the abstraction in VST/MathComp/Rocq.
 *    You might worry that using a function call instead of directly
 * subscripting the array would make the program slower, but it doesn't,
 * since the C compiler can inline the function.
 */

double densematn_get(double *data, int rows, int i, int j);
void densematn_set(double *data, int rows, int i, int j, double x);
void densematn_addto(double *data, int rows, int i, int j, double x);

double densemat_get(densemat_t dm, int i, int j);
void densemat_set(densemat_t dm, int i, int j, double x);
void densemat_addto(densemat_t dm, int i, int j, double x);

/** dot product: let x be an m*n matrix, let y be an n*p matrix,
    multiply row of x by column j of y. */
double densematn_dotprod(int m, int n, int p, int i, int j, double *x, double *y);
double densemat_dotprod(int i, int j, densemat_t x, densemat_t y);

/** compute z = x * y
 */
void densematn_mult(int m, int n, int p, double *x, double *y, double *z);
void densemat_mult(densemat_t x, densemat_t y, densemat_t z);

//ldoc off
#endif /* DENSEMAT_H */
