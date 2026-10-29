#include <stdlib.h>

#include "sparse.h"
#include "sparsemat.h"

//ldoc on
/**
 * # `sparsemat.c`: Implementation of sparse matrix operations
 * ## Memory management
 *
 * `sparsemat_malloc` allocates the head structure and an empty COO matrix
 * with room for `maxn` triples.  The graph is not yet fixed.
 */
sparsemat_t sparsemat_malloc(int m, int n, int maxn)
{
    sparsemat_t h = surely_malloc(sizeof(struct sparsemat_t));
    h->graph_fixed = 0;
    h->u.coo = create_coo_matrix(maxn, m, n);
    return h;
}

void sparsemat_free(sparsemat_t sm)
{
    if (sm->graph_fixed) {
        struct csr_matrix *q = sm->u.csr;
        free(q->val);
        free(q->col_ind);
        free(q->row_ptr);
        free(q);
    } else {
        struct coo_matrix *p = sm->u.coo;
        free(p->row_ind);
        free(p->col_ind);
        free(p->val);
        free(p);
    }
    free(sm);
}

/**
 * `sparsemat_clear` zeroes the stored values but keeps their positions,
 * so the graph is unchanged.  Before the graph is fixed, the same position
 * may be stored more than once; all copies become zero.
 */
void sparsemat_clear(sparsemat_t sm)
{
    if (sm->graph_fixed) {
        struct csr_matrix *q = sm->u.csr;
        double_clear(q->val, q->row_ptr[q->rows]);
    } else {
        struct coo_matrix *p = sm->u.coo;
        double_clear(p->val, p->n);
    }
}

/**
 * ## Fixing the graph
 *
 * `sparsemat_fix_graph` converts the COO matrix to a CSR matrix
 * (summing duplicates) and frees the COO matrix.
 */
void sparsemat_fix_graph(sparsemat_t sm)
{
    if (sm->graph_fixed) return;
    struct coo_matrix *p = sm->u.coo;
    sm->u.csr = coo_to_csr_matrix(p);
    sm->graph_fixed = 1;
    free(p->row_ind);
    free(p->col_ind);
    free(p->val);
    free(p);
}

/**
 * ## Getting entries
 *
 * `sparsemat_get` fixes the graph, then looks up `(i,j)` with `csr_find`.
 */
double sparsemat_get(sparsemat_t sm, int i, int j)
{
    sparsemat_fix_graph(sm);
    struct csr_matrix *q = sm->u.csr;
    unsigned k = csr_find(q, i, j);
    if (k == q->row_ptr[i+1])
        return 0.0;
    return q->val[k];
}

/**
 * ## Adding to entries
 *
 * Before the graph is fixed, `sparsemat_addto` appends the triple
 * `(i,j,x)`, even when `x` is zero, since the triple adds `(i,j)` to the graph.
 * After the graph is fixed, it adds `x` to `(i,j)` with `add_to_csr_matrix`.
 * The precondition is that `(i,j)` is in the graph; if it is not,
 * the call does nothing.
 */
void sparsemat_addto(sparsemat_t sm, int i, int j, double x)
{
    if (sm->graph_fixed)
        add_to_csr_matrix(sm->u.csr, i, j, x);
    else
        add_to_coo_matrix(sm->u.coo, i, j, x);
}

/**
 * ## Matrix-vector multiplication
 *
 * `sparsemat_mvmult` fixes the graph, then computes `y = A*x`
 * with `csr_matrix_vector_multiply`.  The vector `y` must already be allocated.
 */
void sparsemat_mvmult(sparsemat_t sm, double *x, double *y)
{
    sparsemat_fix_graph(sm);
    csr_matrix_vector_multiply(sm->u.csr, x, y);
}
