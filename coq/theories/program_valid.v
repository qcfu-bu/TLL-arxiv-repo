(* This file presents the program reflection theorem. A useful corollary of
   program reflection is the type validity theorem for program typing. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_valid program_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Theorem 6 (Program Reflection) *)
Lemma program_logical_reflect Γ Δ m A : Γ ; Δ ⊢ m : A -> Γ ⊢ m : A.
Proof with eauto using logical_type, logical_wf.
  move:Γ Δ m A.
  apply:(@program_type_mut _ (fun Γ Δ wf => logical_wf Γ))...
  Unshelve. all: eauto.
Qed.
#[global] Hint Resolve program_logical_reflect.

(* Type validity theorem for program typing. *)
Theorem program_valid Γ Δ m A : Γ ; Δ ⊢ m : A -> exists s, Γ ⊢ A : Sort s.
Proof.
  move=>ty.
  apply: logical_valid.
  apply: program_logical_reflect; eauto.
Qed.
