#ifndef BANDMAT_H
#define BANDMAT_H

//ldoc on
/**
 * # Band matrix operations
 * 
 * We store symmetric band matrices using the LAPACK symmetric band
 * format (see, e.g. `DSBTRF`).  This is a packed storage format
 * in which a symmetric matrix with `b` nonzero diagonals off th
 * main diagonal in either direction is stored one diagonal at a time.
 * That is, the dense matrix entry `A[i,j]` (column major) is stored
 * in a packed array `P` of size `n`-by-`b+1` at location `P[j,d]`,
 * where `d = j-i` is the diagonal number.  The leading `d` entries
 * of diagonal `d` are not used (but we don't try to eliminate them
 * in the interest of keeping our indexing simple).  Because we are
 * interested in symmetric matrices, we only need to explicitly store
 * the upper triangle (`d >= 0`).
 */

typedef struct bandmat_t {
    int m,b;  // rows, bands
    double data[0];  // Start of data array
} *bandmat_t;

// Allocate a new bandmat (and maybe populate from a dense matrix)
bandmat_t bandmat_malloc(int n, int b);
void bandmat_free(bandmat_t vm);
bandmat_t dense_to_band(densemat_t A, int bw);

// Clear

void bandmatn_clear(double* data, int m, int b);
void bandmat_clear(bandmat_t vm);


// Print a bandmat
void bandmat_print(bandmat_t PA);

// Frobenius norm-squared and norm 
double bandmat_norm2(bandmat_t vm);
double bandmat_norm(bandmat_t vm);


// Cholesky and linear solve with Cholesky
void bandmat_factor(bandmat_t PA);
void bandmat_solve(bandmat_t PR, double* x);

// Getting, setting, adding to band matrices
double bandmatn_get(double *data, int rows, int i, int d);
void bandmatn_set(double *data, int rows, int i, int d, double x);
void bandmatn_addto(double *data, int rows, int i, int d, double x);

double bandmat_get(bandmat_t dm, int i, int d);
void bandmat_set(bandmat_t dm, int i, int d, double x);
void bandmat_addto(bandmat_t dm, int i, int d, double x);


//ldoc off
#endif /* BANDMAT_H */
