#ifndef SPARSEMAT_H
#define SPARSEMAT_H

#include "alloc.h"

//ldoc on
/**
 * # `sparsemat.h`: Sparse matrix operations
 *
 * A `sparsemat_t` is built in two phases.  While it is being assembled,
 * entries may be added at any position, and the set of positions added to
 * so far forms the matrix's sparsity pattern ("graph").  The first operation
 * that reads the matrix (multiplication, norm, printing, ...) fixes the graph.
 * After that, entries can still be added to or cleared, but only at positions
 * already in the graph.
 *
 * Clients should not access the fields directly; use the functions below.
 */

struct coo_matrix;
struct csr_matrix;

typedef struct sparsemat_t {
    int graph_fixed;                // 0: coo, 1: csr
    union {
        struct coo_matrix *coo;     // live iff !graph_fixed
        struct csr_matrix *csr;     // live iff graph_fixed
    } u;
} *sparsemat_t;

// Create an empty m-by-n matrix with room for up to maxn additions
// before the graph is fixed
sparsemat_t sparsemat_malloc(int m, int n, int maxn);
void sparsemat_free(sparsemat_t sm);

// Set all entries to zero, keeping the graph
void sparsemat_clear(sparsemat_t sm);

// Fix the graph (no-op if already fixed)
void sparsemat_fix_graph(sparsemat_t sm);

// Get entry (i,j), fixing the graph first; 0 if (i,j) is not in the graph
double sparsemat_get(sparsemat_t sm, int i, int j);

// Add x to entry (i,j).  Before the graph is fixed, (i,j) joins the graph
// (even if x is zero).  After, (i,j) must already be in the graph.
void sparsemat_addto(sparsemat_t sm, int i, int j, double x);

// Compute y = A*x, fixing the graph first
void sparsemat_mvmult(sparsemat_t sm, double *x, double *y);

//ldoc off
#endif /* SPARSEMAT_H */
