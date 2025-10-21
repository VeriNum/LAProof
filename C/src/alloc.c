#include <stdlib.h>

void *surely_malloc(size_t n) {
  void *p = malloc(n);
  if (!p) exit(1);
  if (0) free(p); // temporary hack to make sure free is referenced
  return p;
}

void double_clear(double *p, int n) {
  for (int i=0; i<n; i++) 
     p[i]=0.0;
}

double *double_calloc(int n) {
  double *p = (double*)surely_malloc(n*sizeof(double));
  double_clear(p, n);
  return p;
}

int *int_calloc(int n) {
  int *p = (int*)surely_malloc(n*sizeof(int));
  for (int i=0; i<n; i++) 
     p[i]=0;
  return p;
}

