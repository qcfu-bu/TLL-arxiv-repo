(* This file defines the operational semantics of the logical level. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast logical_ctx.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* logical values *)
Inductive logical_val : term -> Prop :=
| logical_val_var x :
  logical_val (Var x)
| logical_val_sort s :
  logical_val (Sort s)
| logical_val_pi0 A B s :
  logical_val (Pi0 A B s)
| logical_val_pi1 A B s :
  logical_val (Pi1 A B s)
| logical_val_lam0 A m s :
  logical_val (Lam0 A m s)
| logical_val_lam1 A m s :
  logical_val (Lam1 A m s)
| logical_val_sig0 A B s :
  logical_val (Sig0 A B s)
| logical_val_sig1 A B s :
  logical_val (Sig1 A B s)
| logical_val_pair0 m n s :
  logical_val m ->
  logical_val (Pair0 m n s)
| logical_val_pair1 m n s :
  logical_val m ->
  logical_val n ->
  logical_val (Pair1 m n s)
| logical_val_with A B s :
  logical_val (With A B s)
| logical_val_apair m1 m2 s :
  logical_val (APair m1 m2 s)
| logical_val_id A m n :
  logical_val (Id A m n)
| logical_val_refl m :
  logical_val (Refl m).

(* small-step relation *)
Reserved Notation "m ~> n" (at level 50).
Inductive logical_step : term -> term -> Prop :=
| logical_step_pi0L A A' B s :
  A ~> A' ->
  Pi0 A B s ~> Pi0 A' B s
| logical_step_pi1L A A' B s :
  A ~> A' ->
  Pi1 A B s ~> Pi1 A' B s
| logical_step_pi0R A B B' s :
  B ~> B' ->
  Pi0 A B s ~> Pi0 A B' s
| logical_step_pi1R A B B' s :
  B ~> B' ->
  Pi1 A B s ~> Pi1 A B' s
| logical_step_lam0L A A' m s :
  A ~> A' ->
  Lam0 A m s ~> Lam0 A' m s
| logical_step_lam1L A A' m s :
  A ~> A' ->
  Lam1 A m s ~> Lam1 A' m s
| logical_step_lam0R A m m' s :
  m ~> m' ->
  Lam0 A m s ~> Lam0 A m' s
| logical_step_lam1R A m m' s :
  m ~> m' ->
  Lam1 A m s ~> Lam1 A m' s
| logical_step_appL m m' n :
  m ~> m' ->
  App m n ~> App m' n
| logical_step_appR m n n' :
  n ~> n' ->
  App m n ~> App m n'
| logical_step_beta0 A m n s :
  App (Lam0 A m s) n ~> m.[n/]
| logical_step_beta1 A m n s :
  App (Lam1 A m s) n ~> m.[n/]
| logical_step_sig0L A A' B s :
  A ~> A' ->
  Sig0 A B s ~> Sig0 A' B s
| logical_step_sig0R A B B' s :
  B ~> B' ->
  Sig0 A B s ~> Sig0 A B' s
| logical_step_sig1L A A' B s :
  A ~> A' ->
  Sig1 A B s ~> Sig1 A' B s
| logical_step_sig1R A B B' s :
  B ~> B' ->
  Sig1 A B s ~> Sig1 A B' s
| logical_step_pair0L m m' n s :
  m ~> m' ->
  Pair0 m n s ~> Pair0 m' n s
| logical_step_pair0R m n n' s :
  n ~> n' ->
  Pair0 m n s ~> Pair0 m n' s
| logical_step_pair1L m m' n s :
  m ~> m' ->
  Pair1 m n s ~> Pair1 m' n s
| logical_step_pair1R m n n' s :
  n ~> n' ->
  Pair1 m n s ~> Pair1 m n' s
| logical_step_letinA A A' m n :
  A ~> A' ->
  LetIn A m n ~> LetIn A' m n
| logical_step_letinL A m m' n :
  m ~> m' ->
  LetIn A m n ~> LetIn A m' n
| logical_step_letinR A m n n' :
  n ~> n' ->
  LetIn A m n ~> LetIn A m n'
| logical_step_iota0 A m1 m2 n s :
  LetIn A (Pair0 m1 m2 s) n ~> n.[m2,m1/]
| logical_step_iota1 A m1 m2 n s :
  LetIn A (Pair1 m1 m2 s) n ~> n.[m2,m1/]
| logical_step_withL A A' B s :
  A ~> A' ->
  With A B s ~> With A' B s
| logical_step_withR A B B' s :
  B ~> B' ->
  With A B s ~> With A B' s
| logical_step_apairL m m' n s :
  m ~> m' ->
  APair m n s ~> APair m' n s
| logical_step_apairR m n n' s :
  n ~> n' ->
  APair m n s ~> APair m n' s
| logical_step_fst m m' :
  m ~> m' ->
  Fst m ~> Fst m'
| logical_step_snd m m' :
  m ~> m' ->
  Snd m ~> Snd m'
| logical_step_proj1 m n s :
  Fst (APair m n s) ~> m
| logical_step_proj2 m n s :
  Snd (APair m n s) ~> n
| logical_step_idA A A' m n :
  A ~> A' ->
  Id A m n ~> Id A' m n
| logical_step_idL A m m' n :
  m ~> m' ->
  Id A m n ~> Id A m' n
| logical_step_idR A m n n' :
  n ~> n' ->
  Id A m n ~> Id A m n'
| logical_step_refl m m' :
  m ~> m' ->
  Refl m ~> Refl m'
| logical_step_rwA A A' H P :
  A ~> A' ->
  Rw A H P ~> Rw A' H P
| logical_step_rwH A H H' P :
  H ~> H' ->
  Rw A H P ~> Rw A H' P
| logical_step_rwP A H P P' :
  P ~> P' ->
  Rw A H P ~> Rw A H P'
| logical_step_rwE A H m :
  Rw A H (Refl m) ~> H
where "m ~> n" := (logical_step m n).

Notation logical_red := (star logical_step).
Notation "m ~>* n" := (logical_red m n) (at level 50).
Notation "m === n" := (conv logical_step m n) (at level 50).
