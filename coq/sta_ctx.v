From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition sta_ctx := seq term.

Inductive sta_has :
  sta_ctx -> var -> term -> Prop :=
| sta_has_O Γ A :
  sta_has (A :: Γ) 0 A.[ren (+1)]
| sta_has_S Γ A B x :
  sta_has Γ x A ->
  sta_has (B :: Γ) x.+1 A.[ren (+1)].

Lemma sta_has_size Γ x A : sta_has Γ x A -> x < size Γ.
Proof. elim=>//. Qed.
