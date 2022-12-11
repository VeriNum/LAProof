#include <stdlib.h>
#include <math.h>

struct sparsevec {
  unsigned *index;
  double *val;
  unsigned k;
  unsigned n;
};

void *surely_malloc(size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  return p;
}

double *sparse2dense (struct sparsevec *v) {
  unsigned i, j, k=v->k, n = v->n;
  unsigned *index = v->index;
  double *val = v->val;
  double *p = surely_malloc(n * sizeof(double));
  for (j=0; j<n; j++) p[j]=0.0;
  for (i=0; i<k; i++) {
    double x=val[i];
    j=index[i];
    p[j]=x;
  }
  return p;
}

struct sparsevec *dense2sparse (double *p, unsigned n) {
  double *val; unsigned *index; struct sparsevec *v;
  unsigned i=0, j, k=0;
  for (j=0; j<n; j++) k += (p[j]!=0.0);
  val = surely_malloc(k * sizeof(double));
  index=surely_malloc(k * sizeof(unsigned));
  for (j=0; j<n; j++) {
    double x = p[j];
    if (x!=0.0) {
      index[i]=j;
      val[i]=x;
      i++;
    }
  }
  v = surely_malloc (sizeof (struct sparsevec));
  v->index=index;
  v->val=val;
  v->k=k;
  v->n=n;
  return v;
}

/*  sparsedotprod(v1,v2) multiplies sparse vector v1 with dense vector v2 */
double sparsedotprod (struct sparsevec *vec1, double *vec2) {
  double result=0.0;
  unsigned i, k=vec1->k;
  unsigned *index = vec1->index;
  double *val = vec1->val;
  for (i=0; i<k; i++) {
    unsigned j = index[i];
    double x = val[i];
    double y = vec2[j];
    result = fma(x,y,result);
  }
  return result;
}

double densedotprod(double *vec1, double *vec2, unsigned n) {
  double result=0.0;
  unsigned i;
  for (i=0; i<n; i++)
    result = fma(vec1[i],vec2[i],result);
  return result;
}


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

/* crs_matrix_vector_multiply(m,v,p)
      multiplies a sparse matrix m by a dense vector v,
      putting the result into the (already allocated) dense vector p
*/
void crs_matrix_vector_multiply (struct crs_matrix *m, double *v, double *p) {
  unsigned i, rows=m->rows;
  unsigned cols=m->cols;
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

