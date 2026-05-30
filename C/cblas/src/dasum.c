/* The following GSL headers are commented out for clightgen: they are
   unresolvable here (GSL's gsl/ symlink dir is not generated) and contribute
   nothing to cblas_dasum's body beyond the libc fabs, which we obtain directly
   from <math.h> (as the other LAProof C sources do, e.g. densemat.c). */
/* #include <gsl/gsl_math.h>  */
/* #include <gsl/gsl_cblas.h> */
#include <math.h>
#include "cblas.h"

double
cblas_dasum (const int N, const double *X, const int incX)
{
#define BASE double
#include "source_asum_r.h"
#undef BASE
}
