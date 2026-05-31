/* The following GSL headers are commented out for clightgen: they are
   unresolvable here (GSL's gsl/ symlink dir is not generated) and contribute
   nothing to cblas_dscal's body (only INDEX from "cblas.h" is needed; the loop
   uses no libc math). */
/* #include <gsl/gsl_math.h>  */
/* #include <gsl/gsl_cblas.h> */
#include "cblas.h"

void
cblas_dscal (const int N, const double alpha, double *X, const int incX)
{
#define BASE double
#include "source_scal_r.h"
#undef BASE
}
