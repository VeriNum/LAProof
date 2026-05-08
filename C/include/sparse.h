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

/**
 * ## To build a CSR matrix,
 * first construct a Coordinate-form (COO) matrix, then use function `coo_to_csr_matrix()` 
 * to convert it into a CSR matrix.
 *   To build the COO matrix, first use `create_coo_matrix()` and then add
 * individual elements using `add_to_coo_matrix()`.  
 *   
 */

/**
 * A Coordinate-form (COO) sparse matrix
 * is a list of triples (i,j,x), where 0<=i<rows and 0<=j<cols, and where space is allocated
 * for up to maxn triples and the first n are populated.
 */
struct coo_matrix {
  unsigned *row_ind, *col_ind;
  double *val;
  unsigned n, maxn;
  unsigned rows, cols;
};

/**
 * `create_coo_matrix(n,r,c)`
 *    Creates an empty COO matrix with enough space for up to n nonzero elements.
 * All elements will be triples (i,j,x) where 0<=i<r and 0<=j<c.
 */

struct coo_matrix *create_coo_matrix (unsigned maxn, unsigned rows, unsigned cols);
/**
 * `add_to_coo_matrix(p,i,j,x)`
 *    Add the triple (i,j,x) to the COO matrix.  Multiple elements at the same position
 * are permitted, with the semantics that they are to be added together.
 * That is, if another triple (i,j,y) is already present with the same i,j, the meaning
 * is that the element at (i,j) has value (y+x).
 */
void add_to_coo_matrix(struct coo_matrix *p, unsigned i, unsigned j, double x);

/**
 *    `coo_to_csr_matrix(p)`
 *  Given a COO matrix p, convert to a CSR matrix.  This takes NlogN time, where
 *  N is the number of triples in the COO matrix, because the first step is to
 *  sort the triples by lexicographic order of (i,j).  This function has the side effect
 *  of rearranging (sorting) the triples.
 */
struct csr_matrix *coo_to_csr_matrix(struct coo_matrix *p);

//ldoc off
#endif
