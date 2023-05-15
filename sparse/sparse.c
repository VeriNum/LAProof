#include <stdlib.h>
#include <math.h>
#include "sparse.h"

void *surely_malloc(size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

double crs_row_vector_multiply(struct crs_matrix *m, double *v, unsigned i) {
  double *val = m->val;
  unsigned *col_ind = m->col_ind;
  unsigned *row_ptr = m->row_ptr;
  unsigned h, hi=row_ptr[i+1];
  double s=0.0;
  for (h=row_ptr[i]; h<hi; h++) {
      double x = val[h];
      unsigned j = col_ind[h];
      double y = v[j];
      s = fma(x,y,s);
  }
  return s;
}

void crs_matrix_vector_multiply_byrows (struct crs_matrix *m, double *v, double *p) {
  unsigned i, rows=crs_matrix_rows(m);
  for (i=0; i<rows; i++)
    p[i]=crs_row_vector_multiply(m,v,i);
}

/* crs_matrix_vector_multiply(m,v,p)
      multiplies a sparse matrix m by a dense vector v,
      putting the result into the (already allocated) dense vector p
*/
void crs_matrix_vector_multiply (struct crs_matrix *m, double *v, double *p) {
  unsigned i, rows=m->rows;
  double *val = m->val;
  unsigned *col_ind = m->col_ind;
  unsigned *row_ptr = m->row_ptr;
  unsigned next=row_ptr[0];
  for (i=0; i<rows; i++) {
    double s=0.0;
    unsigned h=next;
    next=row_ptr[i+1];
    for (; h<next; h++) {
      double x = val[h];
      unsigned j = col_ind[h];
      double y = v[j];
      s = fma(x,y,s);
    }
    p[i]=s;
  }
}

/* Let D be a diagonal matrix, whose diagonal is represented
   as the vector diag.  Let A be a matrix with number of rows equal
   to dimension of D.  let m represent A.
   Then diag_mult(diag,m) sets m to represent D*A */
void diag_mult(double *diag, struct crs_matrix *m) {
  unsigned i, h, rows=m->rows;
  for (i=0; i<rows; i++) {
    unsigned k=m->row_ptr[i+1];
    unsigned x = diag[i];
    for (h=m->row_ptr[i]; h<k; h++)
      m->val[h] *= x;
  }
}

unsigned crs_matrix_rows (struct crs_matrix *m) {
  return m->rows;
}
