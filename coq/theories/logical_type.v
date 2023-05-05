(* This file defines the typing rules of the logical level. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_ctx logical_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Alternative typing rules for the logical level.

   Notice that in the logical0_lam0 and logical0_lam1 rules, there is
   logical0_type Γ A (Sort r). This serves to generate an extra
   hypothesis for A during induction. We will later show that the
   alternative and standard presentations are equivalent. *)
Inductive logical0_type : logical_ctx -> term -> term -> Prop :=
| logical0_axiom Γ s :
  logical0_wf Γ ->
  logical0_type Γ (Sort s) (Sort U)
| logical0_var Γ x A :
  logical0_wf Γ ->
  logical_has Γ x A ->
  logical0_type Γ (Var x) A
| logical0_pi0 Γ A B s r t :
  logical0_type Γ A (Sort r) ->
  logical0_type (A :: Γ) B (Sort t) ->
  logical0_type Γ (Pi0 A B s) (Sort s)
| logical0_pi1 Γ A B s r t :
  logical0_type Γ A (Sort r) ->
  logical0_type (A :: Γ) B (Sort t) ->
  logical0_type Γ (Pi1 A B s) (Sort s)
| logical0_lam0 Γ A B m s r :
  logical0_type Γ A (Sort r) ->
  logical0_type (A :: Γ) m B ->
  logical0_type Γ (Lam0 A m s) (Pi0 A B s)
| logical0_lam1 Γ A B m s r :
  logical0_type Γ A (Sort r) ->
  logical0_type (A :: Γ) m B ->
  logical0_type Γ (Lam1 A m s) (Pi1 A B s)
| logical0_app0 Γ A B m n s :
  logical0_type Γ m (Pi0 A B s) ->
  logical0_type Γ n A ->
  logical0_type Γ (App m n) B.[n/]
| logical0_app1 Γ A B m n s :
  logical0_type Γ m (Pi1 A B s) ->
  logical0_type Γ n A ->
  logical0_type Γ (App m n) B.[n/]
| logical0_sig0 Γ A B s r t :
  s ⊑ t ->
  logical0_type Γ A (Sort s) ->
  logical0_type (A :: Γ) B (Sort r) ->
  logical0_type Γ (Sig0 A B t) (Sort t)
| logical0_sig1 Γ A B s r t :
  s ⊑ t ->
  r ⊑ t ->
  logical0_type Γ A (Sort s) ->
  logical0_type (A :: Γ) B (Sort r) ->
  logical0_type Γ (Sig1 A B t) (Sort t)
| logical0_pair0 Γ A B m n t :
  logical0_type Γ (Sig0 A B t) (Sort t) ->
  logical0_type Γ m A ->
  logical0_type Γ n B.[m/] ->
  logical0_type Γ (Pair0 m n t) (Sig0 A B t)
| logical0_pair1 Γ A B m n t :
  logical0_type Γ (Sig1 A B t) (Sort t) ->
  logical0_type Γ m A ->
  logical0_type Γ n B.[m/] ->
  logical0_type Γ (Pair1 m n t) (Sig1 A B t)
| logical0_letin0 Γ A B C m n s t :
  logical0_type (Sig0 A B t :: Γ) C (Sort s) ->
  logical0_type Γ m (Sig0 A B t) ->
  logical0_type (B :: A :: Γ) n C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  logical0_type Γ (LetIn C m n) C.[m/]
| logical0_letin1 Γ A B C m n s t :
  logical0_type (Sig1 A B t :: Γ) C (Sort s) ->
  logical0_type Γ m (Sig1 A B t) ->
  logical0_type (B :: A :: Γ) n C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  logical0_type Γ (LetIn C m n) C.[m/]
| logical0_with Γ A B s r t :
  logical0_type Γ A (Sort s) ->
  logical0_type Γ B (Sort r) ->
  logical0_type Γ (With A B t) (Sort t)
| logical0_apair Γ A B m n t :
  logical0_type Γ m A ->
  logical0_type Γ n B ->
  logical0_type Γ (APair m n t) (With A B t)
| logical0_fst Γ A B m t :
  logical0_type Γ m (With A B t) ->
  logical0_type Γ (Fst m) A
| logical0_snd Γ A B m t :
  logical0_type Γ m (With A B t) ->
  logical0_type Γ (Snd m) B
| logical0_id Γ A m n s :
  logical0_type Γ A (Sort s) ->
  logical0_type Γ m A ->
  logical0_type Γ n A ->
  logical0_type Γ (Id A m n) (Sort U)
| logical0_refl Γ A m :
  logical0_type Γ m A ->
  logical0_type Γ (Refl m) (Id A m m)
| logical0_rw Γ A B H P m n s :
  logical0_type (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ) B (Sort s) ->
  logical0_type Γ H B.[Refl m,m/] ->
  logical0_type Γ P (Id A m n) ->
  logical0_type Γ (Rw B H P) B.[P,n/]
| logical0_conv Γ A B m s :
  A === B ->
  logical0_type Γ m A ->
  logical0_type Γ B (Sort s) ->
  logical0_type Γ m B

with logical0_wf : logical_ctx -> Prop :=
| logical0_wf_nil : logical0_wf nil
| logical0_wf_cons Γ A s :
  logical0_wf Γ ->
  logical0_type Γ A (Sort s) ->
  logical0_wf (A :: Γ).

Scheme logical0_type_mut := Induction for logical0_type Sort Prop
with logical0_wf_mut := Induction for logical0_wf Sort Prop.

Lemma logical0_type_wf Γ m A : logical0_type Γ m A -> logical0_wf Γ.
Proof with eauto. elim=>{Γ m A}... Qed.
#[global] Hint Resolve logical0_type_wf.

(* Standard typing rules for the logical level.

   Notice that Γ ⊢ A : (Sort r) is missing in the logical_lam0 and
   logical_lam1 rules. The hypothesis for A will be missing when
   performing induction directly over the derivation of the standard
   typing judgment. *)
Reserved Notation "Γ ⊢ m : A" (at level 50, m, A at next level).
Inductive logical_type : logical_ctx -> term -> term -> Prop :=
| logical_axiom Γ s :
  logical_wf Γ ->
  Γ ⊢ Sort s : Sort U
| logical_var Γ x A :
  logical_wf Γ ->
  logical_has Γ x A ->
  Γ ⊢ Var x : A
| logical_pi0 Γ A B s r t :
  Γ ⊢ A : Sort r ->
  (A :: Γ) ⊢ B : Sort t ->
  Γ ⊢ Pi0 A B s : Sort s
| logical_pi1 Γ A B s r t :
  Γ ⊢ A : Sort r ->
  (A :: Γ) ⊢ B : Sort t ->
  Γ ⊢ Pi1 A B s : Sort s
| logical_lam0 Γ A B m s :
  (A :: Γ) ⊢ m : B ->
  Γ ⊢ Lam0 A m s : Pi0 A B s
| logical_lam1 Γ A B m s :
  (A :: Γ) ⊢ m : B ->
  Γ ⊢ Lam1 A m s : Pi1 A B s
| logical_app0 Γ A B m n s :
  Γ ⊢ m : Pi0 A B s ->
  Γ ⊢ n : A ->
  Γ ⊢ App m n : B.[n/]
| logical_app1 Γ A B m n s :
  Γ ⊢ m : Pi1 A B s ->
  Γ ⊢ n : A ->
  Γ ⊢ App m n : B.[n/]
| logical_sig0 Γ A B s r t :
  s ⊑ t ->
  Γ ⊢ A : Sort s ->
  (A :: Γ) ⊢ B : Sort r ->
  Γ ⊢ Sig0 A B t : Sort t
| logical_sig1 Γ A B s r t :
  s ⊑ t ->
  r ⊑ t ->
  Γ ⊢ A : Sort s ->
  (A :: Γ) ⊢ B : Sort r ->
  Γ ⊢ Sig1 A B t : Sort t
| logical_pair0 Γ A B m n t :
  Γ ⊢ Sig0 A B t : Sort t ->
  Γ ⊢ m : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ⊢ Pair0 m n t : Sig0 A B t
| logical_pair1 Γ A B m n t :
  Γ ⊢ Sig1 A B t : Sort t ->
  Γ ⊢ m : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ⊢ Pair1 m n t : Sig1 A B t
| logical_letin0 Γ A B C m n s t :
  (Sig0 A B t :: Γ) ⊢ C : Sort s ->
  Γ ⊢ m : Sig0 A B t ->
  (B :: A :: Γ) ⊢ n : C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ⊢ LetIn C m n : C.[m/]
| logical_letin1 Γ A B C m n s t :
  (Sig1 A B t :: Γ) ⊢ C : Sort s ->
  Γ ⊢ m : Sig1 A B t ->
  (B :: A :: Γ) ⊢ n : C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ⊢ LetIn C m n : C.[m/]
| logical_with Γ A B s r t :
  Γ ⊢ A : Sort s ->
  Γ ⊢ B : Sort r ->
  Γ ⊢ With A B t : Sort t
| logical_apair Γ A B m n t :
  Γ ⊢ m : A ->
  Γ ⊢ n : B ->
  Γ ⊢ APair m n t : With A B t
| logical_fst Γ A B m t :
  Γ ⊢ m : With A B t ->
  Γ ⊢ Fst m : A
| logical_snd Γ A B m t :
  Γ ⊢ m : With A B t ->
  Γ ⊢ Snd m : B
| logical_id Γ A m n s :
  Γ ⊢ A : Sort s ->
  Γ ⊢ m : A ->
  Γ ⊢ n : A ->
  Γ ⊢ Id A m n : Sort U
| logical_refl Γ A m :
  Γ ⊢ m : A ->
  Γ ⊢ Refl m : Id A m m
| logical_rw Γ A B H P m n s :
  (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ) ⊢ B : Sort s ->
  Γ ⊢ H : B.[Refl m,m/] ->
  Γ ⊢ P : Id A m n ->
  Γ ⊢ Rw B H P : B.[P,n/]
| logical_conv Γ A B m s :
  A === B ->
  Γ ⊢ m : A ->
  Γ ⊢ B : Sort s ->
  Γ ⊢ m : B
where "Γ ⊢ m : A" := (logical_type Γ m A)

with logical_wf : logical_ctx -> Prop :=
| logical_wf_nil : logical_wf nil
| logical_wf_cons Γ A s :
  logical_wf Γ ->
  Γ ⊢ A : Sort s ->
  logical_wf (A :: Γ).

Scheme logical_type_mut := Induction for logical_type Sort Prop
with logical_wf_mut := Induction for logical_wf Sort Prop.

Lemma logical_type_wf Γ m A : Γ ⊢ m : A -> logical_wf Γ.
Proof with eauto.
  elim=>{Γ m A}...
  { move=>Γ A _ _ _ _ wf. inv wf... }
  { move=>Γ A _ _ _ _ wf. inv wf... }
Qed.
#[global] Hint Resolve logical_type_wf.

(* The standard and alternative presentations of TLL logical typing are
   isomorphic. So when the hypothesis for A of λ-abstractions is
   needed during induction, we first convert standard to alternative
   before performing induction. *)
Lemma logical_logical0_type Γ m A : Γ ⊢ m : A -> logical0_type Γ m A.
Proof with eauto using logical0_type, logical0_wf.
  move:Γ m A. apply:(@logical_type_mut _ (fun Γ wf => logical0_wf Γ))...
  { move=>Γ A B m s tym ihm.
    have wf0:=logical0_type_wf ihm. inv wf0.
    apply: logical0_lam0... }
  { move=>Γ A B m s tym ihm.
    have wf0:=logical0_type_wf ihm. inv wf0.
    apply: logical0_lam1... }
  Unshelve. eauto.
Qed.
#[global] Hint Resolve logical_logical0_type.

Lemma logical0_logical_type Γ m A : logical0_type Γ m A -> Γ ⊢ m : A.
Proof with eauto using logical_type, logical_wf.
  move:Γ m A. apply:(@logical0_type_mut _ (fun Γ wf => logical_wf Γ))...
  Unshelve. eauto.
Qed.
