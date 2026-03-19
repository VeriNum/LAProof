#include <sparse.h>
#include <build_csr2.h>

void main()
{
  struct rowcol *coog = start_coog(3);
  add_to_coog(coog, 0, 0, 1);
  add_to_coog(coog, 1, 1, 2);
  add_to_coog(coog, 2, 2, 3);
  struct csr_matrix *csr = coog_to_csrg(coog, 3, 4, 4);

  reset_csr(csr);
  add_to_csr(csr, 0, 1, 1.0);
  add_to_csr(csr, 1, 2, 1.0);
  add_to_csr(csr, 2, 3, 1.0);
  add_to_csr(csr, 0, 1, 1.0);

  double v[4] = {1.0, 1.0, 1.0, 1.0};
  double p[4];
  csr_matrix_vector_multiply(csr, v, p);

  for (int i = 0; i < 4; ++i) {
    printf("p[%d] = %g\n", i, p[i]);
  }

}
