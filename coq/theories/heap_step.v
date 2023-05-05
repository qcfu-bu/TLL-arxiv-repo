(* This file defines the heap semantics of the program level. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS heap_res.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Turner-Wadler style small-step relation *)
Reserved Notation "H1 ; m ~>> H2 ; n" (at level 50, m, H2, n at next level).
Inductive heap_step : heap -> term -> heap -> term -> Prop :=
| heap_step_lam0 H m s l :
  l = size H ->
  H ; (Lam0 Box m s) ~>> (Lam0 Box m s :{s} H) ; (Ptr l)
| heap_step_lam1 H m s l :
  l = size H ->
  H ; (Lam1 Box m s) ~>> (Lam1 Box m s :{s} H) ; (Ptr l)
| heap_step_appL H H' m m' n :
  H ; m ~>> H' ; m' ->
  H ; App m n ~>> H' ; App m' n
| heap_step_appR H H' m n n' :
  H ; n ~>> H' ; n' ->
  H ; App m n ~>> H' ; App m n'
| heap_step_beta0 H H' l m n s :
  lookup H l (Lam0 Box m s) H' ->
  H ; App (Ptr l) n ~>> H' ; m.[Box/]
| heap_step_beta1 H H' lf la m s :
  lookup H lf (Lam1 Box m s) H' ->
  H ; App (Ptr lf) (Ptr la) ~>> H' ; m.[Ptr la/]
| heap_step_pair0L H H' m m' t :
  H ; m ~>> H' ; m' ->
  H ; Pair0 m Box t ~>> H' ; Pair0 m' Box t
| heap_step_pair0 H l lm t :
  l = size H ->
  H ; Pair0 (Ptr lm) Box t ~>> (Pair0 (Ptr lm) Box t :{t} H) ; Ptr l
| heap_step_pair1L H H' m m' n t :
  H ; m ~>> H' ; m' ->
  H ; Pair1 m n t ~>> H' ; Pair1 m' n t
| heap_step_pair1R H H' m n n' t :
  H ; n ~>> H' ; n' ->
  H ; Pair1 m n t ~>> H' ; Pair1 m n' t
| heap_step_pair1 H l lm ln t :
  l = size H ->
  H ; Pair1 (Ptr lm) (Ptr ln) t ~>> (Pair1 (Ptr lm) (Ptr ln) t :{t} H) ; Ptr l
| heap_step_letinL H H' m m' n :
  H ; m ~>> H' ; m' ->
  H ; LetIn Box m n ~>> H' ; LetIn Box m' n
| heap_step_iota0 H H' lm x l n t :
  lookup H l (Pair0 (Ptr lm) x t) H' ->
  H ; LetIn Box (Ptr l) n ~>> H' ; n.[Box,Ptr lm/]
| heap_step_iota1 H H' lm ln l n t :
  lookup H l (Pair1 (Ptr lm) (Ptr ln) t) H' ->
  H ; LetIn Box (Ptr l) n ~>> H' ; n.[Ptr ln,Ptr lm/]
| heap_step_apair H m n t l :
  l = size H ->
  H ; APair m n t ~>> (APair m n t :{t} H) ; Ptr l
| heap_step_fst H H' m m' :
  H ; m ~>> H' ; m' ->
  H ; Fst m ~>> H' ; Fst m'
| heap_step_snd H H' m m' :
  H ; m ~>> H' ; m' ->
  H ; Snd m ~>> H' ; Snd m'
| heap_step_proj1 H H' m n l t :
  lookup H l (APair m n t) H' ->
  H ; Fst (Ptr l) ~>> H' ; m
| heap_step_proj2 H H' m n l t :
  lookup H l (APair m n t) H' ->
  H ; Snd (Ptr l) ~>> H' ; n
| heap_step_rwE H m :
  H ; Rw Box m Box ~>> H ; m
where "H1 ; m ~>> H2 ; n" := (heap_step H1 m H2 n).
