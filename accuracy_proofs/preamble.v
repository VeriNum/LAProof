(** This file Exports all the things that LAProof needs to import.
   Clients of LAProof may not want to import these things, so they can avoid
   importing this preamble.   For that reason, we don't put other things in here
   that clients might need (such as the definitions in common.v). *)

From vcfloat Require Export FPStdLib IEEE754_extra RAux Float_lemmas.
Export Lra.

Export List ListNotations.
Require Export Coq.Relations.Relations Coq.Classes.Morphisms Coq.Classes.RelationPairs Coq.Classes.RelationClasses.
Export Reals.
From mathcomp Require Export ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Export fintype finfun bigop finset fingroup perm order.
From mathcomp Require Export div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Export ssrZ zify.

(** Now we undo all the settings that mathcomp has modified *)
Global Unset Implicit Arguments.
Global Unset Strict Implicit.
Global Unset Printing Implicit Defensive.
Global Set Bullet Behavior "Strict Subproofs".
