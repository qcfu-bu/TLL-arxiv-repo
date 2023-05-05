From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Import AutosubstSsr ARS mltt_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition mltt_ctx := seq term.

Inductive mltt_has :
  mltt_ctx -> var -> term -> Prop :=
| sta_has_O Γ A :
  mltt_has (A :: Γ) 0 A.[ren (+1)]
| mltt_has_S Γ A B x :
  mltt_has Γ x A ->
  mltt_has (B :: Γ) x.+1 A.[ren (+1)].

Lemma mltt_has_size Γ x A : mltt_has Γ x A -> x < size Γ.
Proof. elim=>//. Qed.
