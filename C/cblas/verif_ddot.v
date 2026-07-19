(**  * LAProof.C.cblas.verif_ddot: VST proof for GSL's [cblas_ddot]. *)
(** ** Corresponds to C program [C/cblas/src/ddot.c]. *)

(** [body_cblas_ddot] proves that the compiled C [cblas_ddot] (unit stride)
    returns a value [feq]-equal to [dotprodF X Y].  Its invariant uses
    [ddot_model] on length-[k] prefixes; the supporting lemmas are in
    [LAProof.C.cblas.ddot_model]. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import ddot ddot_model spec_ddot.
Require Import LAProof.accuracy_proofs.dotprod_model.

Set Bullet Behavior "Strict Subproofs".

Lemma body_cblas_ddot: semax_body Vprog Gprog f_cblas_ddot cblas_ddot_spec.
Proof.
start_function.
forward.
forward_if (PROP ()
  LOCAL (temp _t'1 (Vint (Int.repr 0));
         temp _r (Vfloat (Float.of_bits (Int64.repr 0)));
         temp _N (Vint (Int.repr n)); temp _X px;
         temp _incX (Vint (Int.repr 1)); temp _Y py;
         temp _incY (Vint (Int.repr 1)))
  SEP (data_at shX (tarray tdouble n) (map Vfloat X) px;
       data_at shY (tarray tdouble n) (map Vfloat Y) py)).
{ forward. entailer!!. }
{ rep_lia. }
forward.
forward_if (PROP ()
  LOCAL (temp _t'2 (Vint (Int.repr 0));
         temp _ix (Vint (Int.repr 0));
         temp _r (Vfloat (Float.of_bits (Int64.repr 0)));
         temp _N (Vint (Int.repr n)); temp _X px;
         temp _incX (Vint (Int.repr 1)); temp _Y py;
         temp _incY (Vint (Int.repr 1)))
  SEP (data_at shX (tarray tdouble n) (map Vfloat X) px;
       data_at shY (tarray tdouble n) (map Vfloat Y) py)).
{ forward. entailer!!. }
{ rep_lia. }
forward.
(* [_r] models the first [k] pairs; unit stride makes [_ix = _iy = k]. *)
forward_for_simple_bound n
  (EX k:Z,
    PROP ()
    LOCAL (temp _r (Vfloat (ddot_model (sublist 0 k X) (sublist 0 k Y)));
           temp _ix (Vint (Int.repr k));
           temp _iy (Vint (Int.repr k));
           temp _N (Vint (Int.repr n));
           temp _incX (Vint (Int.repr 1));
           temp _incY (Vint (Int.repr 1));
           temp _X px; temp _Y py)
    SEP (data_at shX (tarray tdouble n) (map Vfloat X) px;
         data_at shY (tarray tdouble n) (map Vfloat Y) py))%assert.
-
  entailer!!.
-
  forward.
  forward.
  forward.
  forward.
  forward.
  assert (Hi: 0 <= i < Zlength X) by list_solve.
  assert (Hxy: Zlength X = Zlength Y) by list_solve.
  entailer!.
  rewrite (ddot_model_step X Y i Hxy Hi).
  reflexivity.
-
  forward.
  Exists (ddot_model (sublist 0 (Zlength X) X) (sublist 0 (Zlength X) Y)).
  entailer!.
  rewrite (sublist_same 0 (Zlength X) X) by lia.
  rewrite (sublist_same 0 (Zlength X) Y) by lia.
  apply ddot_model_feq_dotprodF; lia.
Qed.

(** Conditional accuracy payoff: [cblas_ddot_spec]'s result is [feq]-equal to
    [dotprodF X Y].  After additionally establishing that [dotprodF X Y] is
    finite (the accuracy theorem's [Hfin] hypothesis), one can transfer
    [LAProof.accuracy_proofs.dot_acc.dotprod_forward_error] to the value computed
    by the compiled C [cblas_ddot].  That composition is not stated as a checked
    theorem here. *)
