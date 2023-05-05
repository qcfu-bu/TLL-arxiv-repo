From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS tll_ast.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dyn_val : term -> Prop :=
| dyn_val_var x :
  dyn_val (Var x)
| dyn_val_lam0 A B s :
  dyn_val (Lam0 A B s)
| dyn_val_lam1 A B s :
  dyn_val (Lam1 A B s)
| dyn_val_pair0 m1 m2 s :
  dyn_val m1 ->
  dyn_val (Pair0 m1 m2 s)
| dyn_val_pair1 m1 m2 s :
  dyn_val m1 ->
  dyn_val m2 ->
  dyn_val (Pair1 m1 m2 s)
| dyn_val_apair m1 m2 s :
  dyn_val (APair m1 m2 s)
| dyn_val_ptr l :
  dyn_val (Ptr l).

Reserved Notation "m ~>> n" (at level 50).
Inductive dyn_step : term -> term -> Prop :=
| dyn_step_appL m m' n :
  m ~>> m' ->
  App m n ~>> App m' n
| dyn_step_appR m n n' :
  n ~>> n' ->
  App m n ~>> App m n'
| dyn_step_beta0 A m n s :
  App (Lam0 A m s) n ~>> m.[n/]
| dyn_step_beta1 A m v s :
  dyn_val v ->
  App (Lam1 A m s) v ~>> m.[v/]
| dyn_step_pair0L m m' n s :
  m ~>> m' ->
  Pair0 m n s ~>> Pair0 m' n s
| dyn_step_pair1L m m' n s :
  m ~>> m' ->
  Pair1 m n s ~>> Pair1 m' n s
| dyn_step_pair1R m n n' s :
  n ~>> n' ->
  Pair1 m n s ~>> Pair1 m n' s
| dyn_step_letinL A m m' n :
  m ~>> m' ->
  LetIn A m n ~>> LetIn A m' n
| dyn_step_iota0 A m1 m2 n s :
  dyn_val (Pair0 m1 m2 s) ->
  LetIn A (Pair0 m1 m2 s) n ~>> n.[m2,m1/]
| dyn_step_iota1 A m1 m2 n s :
  dyn_val (Pair1 m1 m2 s) ->
  LetIn A (Pair1 m1 m2 s) n ~>> n.[m2,m1/]
| dyn_step_fst m m' :
  m ~>> m' ->
  Fst m ~>> Fst m'
| dyn_step_snd m m' :
  m ~>> m' ->
  Snd m ~>> Snd m'
| dyn_step_proj1 m n s :
  Fst (APair m n s) ~>> m
| dyn_step_proj2 m n s :
  Snd (APair m n s) ~>> n
| dyn_step_rwE A H P :
  Rw A H P ~>> H
where "m ~>> n" := (dyn_step m n).

Notation dyn_red := (star dyn_step).
Notation "m ~>>* n" := (dyn_red m n) (at level 50).
