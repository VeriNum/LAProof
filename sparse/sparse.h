struct sparsevec {
  unsigned *index;
  double *val;
  unsigned k;
  unsigned n;
};

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

double *sparse2dense (struct sparsevec *v);
struct sparsevec *dense2sparse (double *p, unsigned n);
double sparsedotprod (struct sparsevec *vec1, double *vec2);
double densedotprod(double *vec1, double *vec2, unsigned n);

void crs_matrix_vector_multiply (struct crs_matrix *m, double *v, double *p);

