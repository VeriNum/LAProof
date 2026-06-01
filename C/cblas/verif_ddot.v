(**  * LAProof.C.cblas.verif_ddot: VST proof for GSL's [cblas_ddot]. *)
(** ** Corresponds to C program [C/cblas/src/ddot.c]. *)

(** [body_cblas_ddot] proves that the compiled C [cblas_ddot] (unit stride)
    refines the [dotprodF] accuracy model: its result is [feq]-equal to
    [dotprodF X Y].  The loop invariant carries the partial accumulation
    [ddot_model (sublist 0 k X) (sublist 0 k Y)]; the step and bridge reasoning
    that discharges it lives in [LAProof.C.cblas.ddot_model].  Two dead [OFFSET]
    guards (the [incX>0]/[incY>0] conditionals) precede the loop, unreachable
    since [incX = incY = 1]. *)

Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
From LAProof.C Require Import floatlib.
From LAProof.C.cblas Require Import ddot ddot_model spec_ddot.
Require Import LAProof.accuracy_proofs.dotprod_model.

Set Bullet Behavior "Strict Subproofs".

Lemma body_cblas_ddot: semax_body Vprog Gprog f_cblas_ddot cblas_ddot_spec.
Proof.
start_function.
(* C: r = 0.0; ix = OFFSET(N,incX); iy = OFFSET(N,incY); with incX=incY=1 ⇒ ix=iy=0.
   Each OFFSET is a (incX>0 ? 0 : ...) conditional; the else-branch is
   unreachable here because incX=incY=1, so [rep_lia] closes it. *)
forward.                       (* _r = 0.0 *)
forward_if (PROP ()
  LOCAL (temp _t'1 (Vint (Int.repr 0));
         temp _r (Vfloat (Float.of_bits (Int64.repr 0)));
         temp _N (Vint (Int.repr n)); temp _X px;
         temp _incX (Vint (Int.repr 1)); temp _Y py;
         temp _incY (Vint (Int.repr 1)))
  SEP (data_at shX (tarray tdouble n) (map Vfloat X) px;
       data_at shY (tarray tdouble n) (map Vfloat Y) py)).
{ forward. entailer!!. }       (* incX = 1 > 0 : t'1 := 0 *)
{ rep_lia. }                   (* dead else-branch (incX = 1 is > 0) *)
forward.                       (* _ix = _t'1 (= 0) *)
forward_if (PROP ()
  LOCAL (temp _t'2 (Vint (Int.repr 0));
         temp _ix (Vint (Int.repr 0));
         temp _r (Vfloat (Float.of_bits (Int64.repr 0)));
         temp _N (Vint (Int.repr n)); temp _X px;
         temp _incX (Vint (Int.repr 1)); temp _Y py;
         temp _incY (Vint (Int.repr 1)))
  SEP (data_at shX (tarray tdouble n) (map Vfloat X) px;
       data_at shY (tarray tdouble n) (map Vfloat Y) py)).
{ forward. entailer!!. }       (* incY = 1 > 0 : t'2 := 0 *)
{ rep_lia. }                   (* dead else-branch (incY = 1 is > 0) *)
forward.                       (* _iy = _t'2 (= 0) *)
(* The accumulation loop.  Invariant: _r holds the value the C loop has
   accumulated over the first k element-pairs, namely [ddot_model] of the
   length-k prefixes; the strided indices ix,iy advance by 1 each step (= k). *)
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
- (* Loop entry (k = 0).  [sublist 0 0 = nil] and [ddot_model nil nil =
     Zconst Tdouble 0] (= the C [+0.0]); [entailer!!] discharges it. *)
  entailer!!.
- (* Loop body: read X[i], Y[i]; [r = r + X[i]*Y[i]]; ix++; iy++.  Re-establish
     the invariant for [i+1] via the step lemma [ddot_model_step]. *)
  forward.                       (* t'3 = X[ix] *)
  forward.                       (* t'4 = Y[iy] *)
  forward.                       (* r = r + t'3 * t'4 *)
  forward.                       (* ix = ix + incX *)
  forward.                       (* iy = iy + incY *)
  assert (Hi: 0 <= i < Zlength X) by list_solve.
  assert (Hxy: Zlength X = Zlength Y) by list_solve.
  entailer!.
  rewrite (ddot_model_step X Y i Hxy Hi).
  reflexivity.
- (* Loop exit (k = n).  Return [r = ddot_model (sublist 0 n X) (sublist 0 n Y)];
     [sublist_same] gives [= ddot_model X Y], and the bridge lemma
     [ddot_model_feq_dotprodF] discharges [feq _ (dotprodF X Y)]. *)
  forward.                       (* return r *)
  Exists (ddot_model (sublist 0 (Zlength X) X) (sublist 0 (Zlength X) Y)).
  entailer!.
  rewrite (sublist_same 0 (Zlength X) X) by lia.
  rewrite (sublist_same 0 (Zlength X) Y) by lia.
  apply ddot_model_feq_dotprodF; [ lia | auto | auto ].
Qed.

(** Payoff (stub): because [cblas_ddot_spec]'s result is [feq]-equal to
    [dotprodF X Y], the forward-error bound
    [LAProof.accuracy_proofs.dot_acc.dotprod_forward_error] applies directly to
    the value computed by the compiled C [cblas_ddot]. *)
