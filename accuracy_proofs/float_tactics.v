Require Import vcfloat.VCFloat.
From LAProof.accuracy_proofs Require Import common float_acc_lems op_defs.

Ltac field_simplify_round :=
  match goal with |- context[Generic_fmt.round _ _ _ ?a] =>
  try field_simplify a
end. 

Ltac BPLUS_correct t a b :=
match goal with | FIN : is_finite (BPLUS a b) = true |- context [FT2R (BPLUS a b)] =>  
  let X:= fresh in set 
        (X:=  FT2R (BPLUS a b)); unfold BPLUS, BINOP in X ;
  let H4 := fresh in pose proof (is_finite_sum_no_overflow a b FIN) as H4; apply Rlt_bool_true in H4 ;
  let H := fresh in 
  assert (H : is_finite a = true /\ is_finite b = true) ;
  [rewrite !is_finite_Binary; rewrite !is_finite_Binary in FIN ;
    unfold BPLUS, BINOP in FIN; rewrite float_of_ftype_of_float in FIN;
    destruct (float_of_ftype a); destruct (float_of_ftype b); 
       simpl in FIN; split; try discriminate; auto ;
          match goal with | H: Binary.is_finite _ _
                   (Binary.Bplus _ _ _ _ _ _ (Binary.B754_infinity _ _ ?s)
                      (Binary.B754_infinity _ _ ?s0)) = _ |- Binary.is_finite _ _ _ = _ =>
            destruct s; destruct s0; try discriminate; auto end 
  | ]; rewrite !is_finite_Binary in H; 
    let H1 := fresh in let H2 := fresh in  destruct H as (H1 & H2);
    let H3 := fresh in pose proof (Binary.Bplus_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE 
        (float_of_ftype a) (float_of_ftype b) H1 H2) as H3;
        rewrite !B2R_float_of_ftype in H3;
    rewrite H4 in H3 ;
    destruct H3 as (H3 & _); clear H4; unfold BPLUS, BINOP in X; subst X; 
    try field_simplify_round; rewrite <- !B2R_float_of_ftype; rewrite float_of_ftype_of_float;
    rewrite H3; try reflexivity
end.

Ltac BMINUS_correct t a b :=
match goal with | FIN : is_finite (BMINUS a b) = true |- context [FT2R (BMINUS a b)] =>
  let X:= fresh in set (X:= FT2R (BMINUS a b)); unfold BMINUS, BINOP in X ;
  let H4 := fresh in pose proof (is_finite_minus_no_overflow a b FIN) as H4; apply Rlt_bool_true in H4 ;
  let H := fresh in 
  assert (H : is_finite a = true /\ is_finite b = true) ;
  [rewrite !is_finite_Binary; rewrite !is_finite_Binary in FIN ;
    unfold BMINUS, BINOP in FIN; rewrite float_of_ftype_of_float in FIN;
    destruct (float_of_ftype a); destruct (float_of_ftype b); 
      simpl in FIN; split; try discriminate; auto;
          match goal with | H: Binary.is_finite _ _
                   (Binary.Bminus _ _ _ _ _ _ (Binary.B754_infinity _ _ ?s)
                      (Binary.B754_infinity _ _ ?s0)) = _ |- Binary.is_finite _ _ _ = _ =>
            destruct s; destruct s0; try discriminate; auto end 
  | ]; rewrite !is_finite_Binary in H ; 
    let H1 := fresh in let H2 := fresh in  destruct H as (H1 & H2);
    let H3 := fresh in pose proof (Binary.Bminus_correct (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (plus_nan t) BinarySingleNaN.mode_NE 
        (float_of_ftype a) (float_of_ftype b) H1 H2) as H3 ;
    rewrite !B2R_float_of_ftype in H3;
    rewrite H4 in H3 ;
    destruct H3 as (H3 & _); clear H4 ; unfold BMINUS, BINOP in X; subst X; 
    try field_simplify_round; rewrite <- !B2R_float_of_ftype; rewrite float_of_ftype_of_float;
    rewrite H3; try reflexivity 
end.

Ltac BMULT_correct t a b :=
match goal with | FIN : is_finite (BMULT a b) = true |- context [FT2R (BMULT a b)] =>
  let X:= fresh in set (X:= FT2R (BMULT a b)); unfold BMULT, BINOP in X ;
  let H4 := fresh in pose proof (is_finite_BMULT_no_overflow a b FIN) as H4; apply Rlt_bool_true in H4 ;
    let H3 := fresh in try pose proof (Binary.Bmult_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (mult_nan t) BinarySingleNaN.mode_NE 
        (float_of_ftype a) (float_of_ftype b)) as H3 ;
    unfold common.rounded in H4; rewrite !B2R_float_of_ftype in H3; rewrite H4 in H3;
    destruct H3 as (H3 & _); clear H4 ; unfold BMULT, BINOP in X; subst X; 
    try field_simplify_round; rewrite <- !B2R_float_of_ftype; rewrite float_of_ftype_of_float; 
    rewrite H3; try reflexivity 
end.

Ltac BFMA_correct t a b s:=
match goal with | FIN : is_finite (BFMA a b s) = true |- context [FT2R (BFMA a b s)] =>
  let X:= fresh in set (X:= FT2R (BFMA a b s)); unfold BFMA in X ;
  let H4 := fresh in pose proof (is_finite_fma_no_overflow a b s FIN) as H4; apply Rlt_bool_true in H4;
  unfold common.rounded in H4;
  let H := fresh in 
  assert (H : is_finite a = true /\ is_finite b = true /\ is_finite s = true);
 [rewrite !is_finite_Binary; rewrite !is_finite_Binary in FIN ;
    unfold BFMA, BINOP in FIN; rewrite float_of_ftype_of_float in FIN;
    destruct (float_of_ftype a); destruct (float_of_ftype b); destruct (float_of_ftype s); 
      simpl in FIN; repeat split; try discriminate; auto;
          match goal with | H: Binary.is_finite _ _
                   (Binary.Bfma _ _ _ _ _ _ ?A ?B ?C) = _ |- Binary.is_finite _ _ _ = _ =>
            match A with | (Binary.B754_infinity _ _ ?s4)  => destruct s4
                         | (Binary.B754_finite _ _ ?s4 _ _ _) => destruct s4 | _ => idtac end;
            match B with | (Binary.B754_infinity _ _ ?s4)  => destruct s4
                         | (Binary.B754_finite _ _ ?s4 _ _ _) => destruct s4 | _ => idtac end;
            match C with | (Binary.B754_infinity _ _ ?s4)  => destruct s4
                         | (Binary.B754_finite _ _ ?s4 _ _ _) => destruct s4 | _ => idtac end;
          try discriminate; auto end
  | ]; rewrite !is_finite_Binary in H; 
    let H1 := fresh in let H2 := fresh in  destruct H as (H1 & H2 & HS);
    let H3 := fresh in pose proof (Binary.Bfma_correct  (fprec t) (femax t) 
        (fprec_gt_0 t) (fprec_lt_femax t) (fma_nan t) BinarySingleNaN.mode_NE 
        (float_of_ftype a) (float_of_ftype b) (float_of_ftype s) H1 H2 HS) as H3; cbv zeta in H3;
    rewrite !B2R_float_of_ftype in H3;
    rewrite H4 in H3 ;
    destruct H3 as (H3 & _); clear H4 ; unfold BFMA in X; subst X; try field_simplify_round; 
    rewrite <- !B2R_float_of_ftype; rewrite float_of_ftype_of_float;
    rewrite H3; try reflexivity
end.

Ltac subexpr_finite_H0 fexpr HFIN :=
    match fexpr with
      | BPLUS ?b ?c =>       
          try match goal with 
            | H1: is_finite b = true |- _ =>
              try subexpr_finite_H0 b H1;
              try match goal with 
                | H2: is_finite c = true |- _ =>
                  try subexpr_finite_H0 c H2
                | _ => let H0 := fresh in pose proof (BPLUS_finite_e b c HFIN) as H0;
                       let H2 := fresh in destruct H0 as (_ & H2);
                       try subexpr_finite_H0 c H2
              end
            | _ =>  let H0 := fresh in pose proof (BPLUS_finite_e b c HFIN) as H0;
                    let H1 := fresh in let H2 := fresh in 
                    destruct H0 as (H1 & H2);
                    try subexpr_finite_H0 b H1;
                    try subexpr_finite_H0 c H2
          end
      | BMINUS ?b ?c =>       
          try match goal with 
            | H1: is_finite b = true |- _ =>
              try subexpr_finite_H0 b H1;
              try match goal with 
                | H2: is_finite c = true |- _ =>
                  try subexpr_finite_H0 c H2
                | _ => let H0 := fresh in pose proof (BMINUS_finite_sub b c HFIN) as H0;
                       let H2 := fresh in destruct H0 as (_ & H2);
                       try subexpr_finite_H0 c H2
              end
            | _ =>  let H0 := fresh in pose proof (BMINUS_finite_sub b c HFIN) as H0;
                    let H1 := fresh in let H2 := fresh in 
                    destruct H0 as (H1 & H2);
                    try subexpr_finite_H0 b H1;
                    try subexpr_finite_H0 c H2
          end
      | BMULT ?b ?c =>       
          try match goal with 
            | H1: is_finite b = true |- _ =>
              try subexpr_finite_H0 b H1;
              try match goal with 
                | H2: is_finite c = true |- _ =>
                  try subexpr_finite_H0 c H2
                | _ => let H0 := fresh in pose proof (BMULT_finite_e b c HFIN) as H0;
                       let H2 := fresh in destruct H0 as (_ & H2);
                       try subexpr_finite_H0 c H2
              end
            | _ =>  let H0 := fresh in pose proof (BMULT_finite_e b c HFIN) as H0;
                    let H1 := fresh in let H2 := fresh in 
                    destruct H0 as (H1 & H2);
                    try subexpr_finite_H0 b H1;
                    try subexpr_finite_H0 c H2
          end
      | BFMA ?a ?b ?c =>       
          try match goal with 
            | H1: is_finite a = true |- _ =>
              try subexpr_finite_H0 a H1;
              try match goal with 
                | H2: is_finite b = true |- _ =>
                  try subexpr_finite_H0 b H2;
                  try match goal with 
                    | H3: is_finite c = true |- _ =>
                      try subexpr_finite_H0 c H3
                    | _ => let H0 := fresh in pose proof (BFMA_finite_e a b c HFIN) as H0;
                           let H3 := fresh in destruct H0 as (_ & _ & H3);
                           try subexpr_finite_H0 c H3
                  end
                | _ =>  let H0 := fresh in pose proof (BFMA_finite_e a b c HFIN) as H0;
                        let H2 := fresh in let H3 := fresh in  
                        destruct H0 as (_ & H2 & H3);
                        try subexpr_finite_H0 b H2;
                        try subexpr_finite_H0 c H3
              end
            | _ =>  let H0 := fresh in pose proof (BFMA_finite_e a b c HFIN) as H0;
                    let H1 := fresh in let H2 := fresh in let H3 := fresh in   
                    destruct H0 as (H1 & H2 & H3);
                    try subexpr_finite_H0 a H1;
                    try subexpr_finite_H0 b H2;
                    try subexpr_finite_H0 c H3
          end
  end
.
  
Ltac subexpr_finite :=
    match goal with |- context [is_finite ?a = true -> _ ] => 
      let H:= fresh in intros H; subexpr_finite_H0 a H 
    end. 


Ltac  field_simplify_format :=
  match goal with |- context [Generic_fmt.generic_format _ _ ?a ] => 
    field_simplify a
  end;  
  try apply Generic_fmt.generic_format_0;
  auto with dd_base.


