//ldoc on
/**
 * # `ddot.c`: GSL CBLAS real double-precision dot product
 *
 * Thin wrapper that instantiates the generic kernel `source_dot_r.h` at type
 * `double`.  Verified in `LAProof.C.cblas.verif_ddot` against the functional
 * model `LAProof.C.cblas.ddot_model`.
 */
/* The following GSL headers are commented out for clightgen: they are
   unused by cblas_ddot's body (only OFFSET/INDEX from "cblas.h" are needed)
   and are unresolvable here because GSL's gsl/ symlink dir is not generated. */
/* #include <gsl/gsl_math.h>  */
/* #include <gsl/gsl_cblas.h> */
#include "cblas.h"

double
cblas_ddot (const int N, const double *X, const int incX, const double *Y,
            const int incY)
{
#define INIT_VAL  0.0
#define ACC_TYPE  double
#define BASE double
#include "source_dot_r.h"
#undef ACC_TYPE
#undef BASE
#undef INIT_VAL
}
