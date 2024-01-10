Require Import vcfloat.VCFloat.

Section WithNans.
Context {NAN: Nans} {t: type} {STD: is_standard t}.

Definition BFMA (x y z: ftype t) : ftype t :=
  ftype_of_float (
    (Binary.Bfma (fprec t) (femax t) (fprec_gt_0 t)
        (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE
        (float_of_ftype x) (float_of_ftype y) (float_of_ftype z))).

End WithNans.