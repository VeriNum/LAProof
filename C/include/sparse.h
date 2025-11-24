#ifndef SPARSE_DOT_H
#define SPARSE_DOT_H

#include <stddef.h>
#include <sys/time.h>

//ldoc on
/**
 * # `sparse.h`: Sparse matrix operations (Compressed Sparse Row)
 * 
 * To represent a CSR sparse matrix, we define a structure `csr_matrix` consisting of 
 * data array, index arrays, and dimensions.
 *
 * see section 4.3.1 of 
 *  "Templates for the Solution of Linear Systems: Building Blocks 
 *   for Iterative Methods" by Richard Barrett et al., 
 *   https://netlib.org/templates/templates.pdf
 */
struct csr_matrix {
  double *val;
  unsigned *col_ind;
  unsigned *row_ptr;
  unsigned rows, cols;
};

void *surely_malloc(size_t n);

unsigned csr_matrix_rows(struct csr_matrix *m);

/**
 * The principal function here is `csr_row_vector_multiply`.
 * But in some applications (such as sweep-form Jacobi iteration) one might
 * want to multiply just one row of a CSR matrix by a dense vector,
 * so `csr_matrix_vector_multiply_byrows` is also provided here.
 */

void csr_matrix_vector_multiply (struct csr_matrix *m, double *v, double *p);
double csr_row_vector_multiply(struct csr_matrix *m, double *v, unsigned i);
void csr_matrix_vector_multiply_byrows (struct csr_matrix *m, double *v, double *p);

/**
 * The following test scaffolding is not proved correct.
 */

struct csr_matrix *make_example(unsigned N, unsigned D, double diag);
void dump_csr_matrix  (struct csr_matrix *m);
void print_csr_matrix (struct csr_matrix *m);
double timediff(struct timeval *start, struct timeval *finish);


#endif
