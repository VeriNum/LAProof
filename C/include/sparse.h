#ifndef SPARSE_DOT_H
#define SPARSE_DOT_H

#include <stddef.h>
#include <sys/time.h>

/* Compressed Row Storage (CRS) representation of matrix,
   see section 4.3.1 of 
   "Templates for the Solution of Linear Systems: Building Blocks 
    for Iterative Methods" by Richard Barrett et al., 
    https://netlib.org/templates/templates.pdf
*/
struct csr_matrix {
  double *val;
  unsigned *col_ind;
  unsigned *row_ptr;
  unsigned rows, cols;
};

void *surely_malloc(size_t n);

unsigned csr_matrix_rows(struct csr_matrix *m);

void csr_matrix_vector_multiply (struct csr_matrix *m, double *v, double *p);
double csr_row_vector_multiply(struct csr_matrix *m, double *v, unsigned i);
void csr_matrix_vector_multiply_byrows (struct csr_matrix *m, double *v, double *p);

/* Let D be a diagonal matrix, whose diagonal is represented
   as the vector diag.  Let A be a matrix with number of rows equal
   to dimension of D.  let m represent A.
   Then diag_mult(diag,m) sets m to represent D*A */
void diag_mult(double *diag, struct csr_matrix *m);


struct csr_matrix *make_example(unsigned N, unsigned D, double diag);
void dump_csr_matrix  (struct csr_matrix *m);
void print_csr_matrix (struct csr_matrix *m);
double timediff(struct timeval *start, struct timeval *finish);


#endif
