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
struct crs_matrix {
  double *val;
  unsigned *col_ind;
  unsigned *row_ptr;
  unsigned rows, cols;
};

void *surely_malloc(size_t n);

void crs_matrix_vector_multiply (struct crs_matrix *m, double *v, double *p);

/* Let D be a diagonal matrix, whose diagonal is represented
   as the vector diag.  Let A be a matrix with number of rows equal
   to dimension of D.  let m represent A.
   Then diag_mult(diag,m) sets m to represent D*A */
void diag_mult(double *diag, struct crs_matrix *m);


struct crs_matrix *make_example(unsigned N, unsigned D, double diag);
void dump_crs_matrix  (struct crs_matrix *m);
void print_crs_matrix (struct crs_matrix *m);
double timediff(struct timeval *start, struct timeval *finish);


#endif
