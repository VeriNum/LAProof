#ifndef BUILD_CSR2_H
#define BUILD_CSR2_H

struct rowcol *start_coog(unsigned n);
void add_to_coog(struct rowcol *rc, unsigned i, unsigned r, unsigned c);
struct csr_matrix *coog_to_csrg(struct rowcol *rc, unsigned n, unsigned rows, unsigned cols);
void reset_csr(struct csr_matrix *q);
void add_to_csr(struct csr_matrix *q, unsigned r, unsigned c, double x);

#endif
