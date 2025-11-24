#include <stdlib.h>
#include <math.h>
#include <sparse.h>

//ldoc on
/**
 * # `sparse.c`: Implementation of Compressed Sparse Row (CSR) matrix operations
 */

/**
 * csr_matrix_vector_multiply(m,v,p)
 *     multiplies a sparse matrix m by a dense vector v,
 *     putting the result into the (already allocated) dense vector p
 */
void csr_matrix_vector_multiply (struct csr_matrix *m, double *v, double *p) {
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

/**
 * Return the number of rows of a CSR matrix
 */
unsigned csr_matrix_rows (struct csr_matrix *m) {
  return m->rows;
}

/**
 * Alternate form, for multiplying just one row of a CSR matrix by a dense vector
 */
double csr_row_vector_multiply(struct csr_matrix *m, double *v, unsigned i) {
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

void csr_matrix_vector_multiply_byrows (struct csr_matrix *m, double *v, double *p) {
  unsigned i, rows=csr_matrix_rows(m);
  for (i=0; i<rows; i++)
    p[i]=csr_row_vector_multiply(m,v,i);
}

