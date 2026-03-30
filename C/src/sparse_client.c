#include <stdio.h>
#include <sparse.h>
#include <build_csr2.h>

void test(double *p1, double *p2)
{
  struct rowcol *coog = start_coog(3);
  add_to_coog(coog, 0, 0, 0);
  add_to_coog(coog, 1, 1, 2);
  add_to_coog(coog, 2, 2, 1);
  struct csr_matrix *csr = coog_to_csrg(coog, 3, 3, 3);
  
  reset_csr(csr);
  add_to_csr(csr, 0, 0, 1.0);
  add_to_csr(csr, 1, 2, 1.0);
  add_to_csr(csr, 2, 1, 1.0);
  add_to_csr(csr, 0, 0, 1.0);

  double v[3] = {1.0, 1.0, 1.0};
  csr_matrix_vector_multiply(csr, v, p1);

  reset_csr(csr);
  add_to_csr(csr, 0, 0, 2.0);
  add_to_csr(csr, 1, 2, 2.0);
  add_to_csr(csr, 2, 1, 1.0);
  add_to_csr(csr, 1, 2, 1.0);

  csr_matrix_vector_multiply(csr, v, p2);
}

int main()
{
  double p1[3], p2[3];
  test(p1, p2);
  for (int i = 0; i < 3; ++i) {
    printf("%g\t", p1[i]);
  }
  printf("\n");

  for (int i = 0; i < 3; ++i) {
    printf("%g\t", p2[i]);
  }
  printf("\n");
  
  return 0;
}
