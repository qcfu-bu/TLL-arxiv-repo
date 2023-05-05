(* This file defines the logical context (Γ). *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition logical_ctx := seq term.

(* logical_has Γ x A represents (x : A) ∈ Γ *)
Inductive logical_has :
  logical_ctx -> var -> term -> Prop :=
| logical_has_O Γ A :
  logical_has (A :: Γ) 0 A.[ren (+1)]
| logical_has_S Γ A B x :
  logical_has Γ x A ->
  logical_has (B :: Γ) x.+1 A.[ren (+1)].

Lemma logical_has_size Γ x A : logical_has Γ x A -> x < size Γ.
Proof. elim=>//. Qed.
