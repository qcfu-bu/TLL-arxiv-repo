From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS mltt_ctx mltt_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive mltt0_type : mltt_ctx -> term -> term -> Prop :=
| mltt0_axiom Γ :
  mltt0_wf Γ ->
  mltt0_type Γ Ty Ty
| mltt0_var Γ x A :
  mltt0_wf Γ ->
  mltt_has Γ x A ->
  mltt0_type Γ (Var x) A
| mltt0_pi Γ A B :
  mltt0_type Γ A Ty ->
  mltt0_type (A :: Γ) B Ty ->
  mltt0_type Γ (Pi A B) Ty
| mltt0_lam Γ A B m :
  mltt0_type Γ A Ty ->
  mltt0_type (A :: Γ) m B ->
  mltt0_type Γ (Lam A m) (Pi A B)
| mltt0_app Γ A B m n :
  mltt0_type Γ m (Pi A B) ->
  mltt0_type Γ n A ->
  mltt0_type Γ (App m n) B.[n/]
| mltt0_sig Γ A B :
  mltt0_type Γ A Ty ->
  mltt0_type (A :: Γ) B Ty ->
  mltt0_type Γ (Sig A B) Ty
| mltt0_dpair Γ A B m n :
  mltt0_type Γ m A ->
  mltt0_type Γ n B.[m/] ->
  mltt0_type Γ (DPair m n) (Sig A B)
| mltt0_letin Γ A B C m n :
  mltt0_type (Sig A B :: Γ) C Ty ->
  mltt0_type Γ m (Sig A B) ->
  mltt0_type (B :: A :: Γ) n C.[DPair (Var 1) (Var 0) .: ren (+2)] ->
  mltt0_type Γ (LetIn C m n) C.[m/]
| mltt0_tuple Γ A B :
  mltt0_type Γ A Ty ->
  mltt0_type Γ B Ty ->
  mltt0_type Γ (Tuple A B) Ty
| mltt0_pair Γ A B m n :
  mltt0_type Γ m A ->
  mltt0_type Γ n B ->
  mltt0_type Γ (Pair m n) (Tuple A B)
| mltt0_fst Γ A B m :
  mltt0_type Γ m (Tuple A B) ->
  mltt0_type Γ (Fst m) A
| mltt0_snd Γ A B m :
  mltt0_type Γ m (Tuple A B) ->
  mltt0_type Γ (Snd m) B
| mltt0_id Γ A m n :
  mltt0_type Γ A Ty ->
  mltt0_type Γ m A ->
  mltt0_type Γ n A ->
  mltt0_type Γ (Id A m n) Ty
| mltt0_refl Γ A m :
  mltt0_type Γ m A ->
  mltt0_type Γ (Refl m) (Id A m m)
| mltt0_rw Γ A B H P m n :
  mltt0_type (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ) B Ty ->
  mltt0_type  Γ H B.[Refl m,m/] ->
  mltt0_type Γ P (Id A m n) ->
  mltt0_type Γ (Rw B H P) B.[P,n/]
| mltt0_conv Γ A B m :
  A === B ->
  mltt0_type Γ m A ->
  mltt0_type Γ B Ty ->
  mltt0_type Γ m B

with mltt0_wf : mltt_ctx -> Prop :=
| mltt0_wf_nil : mltt0_wf nil
| mltt0_wf_cons Γ A :
  mltt0_wf Γ ->
  mltt0_type Γ A Ty ->
  mltt0_wf (A :: Γ).

Scheme mltt0_type_mut := Induction for mltt0_type Sort Prop
with mltt0_wf_mut := Induction for mltt0_wf Sort Prop.

Lemma mltt0_type_wf Γ m A : mltt0_type Γ m A -> mltt0_wf Γ.
Proof with eauto. elim=>{Γ m A}... Qed.
#[global] Hint Resolve mltt0_type_wf.

Reserved Notation "Γ ⊢ m : A" (at level 50, m, A at next level).
Inductive mltt_type : mltt_ctx -> term -> term -> Prop :=
| mltt_axiom Γ :
  mltt_wf Γ ->
  Γ ⊢ Ty : Ty
| mltt_var Γ x A :
  mltt_wf Γ ->
  mltt_has Γ x A ->
  Γ ⊢ Var x : A
| mltt_pi Γ A B :
  Γ ⊢ A : Ty ->
  (A :: Γ) ⊢ B : Ty ->
  Γ ⊢ Pi A B : Ty
| mltt_lam Γ A B m :
  (A :: Γ) ⊢ m : B ->
  Γ ⊢ Lam A m : Pi A B
| mltt_app Γ A B m n :
  Γ ⊢ m : Pi A B ->
  Γ ⊢ n : A ->
  Γ ⊢ App m n : B.[n/]
| mltt_sig Γ A B :
  Γ ⊢ A : Ty ->
  (A :: Γ) ⊢ B : Ty  ->
  Γ ⊢ Sig A B : Ty
| mltt_dpair Γ A B m n :
  Γ ⊢ m : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ⊢ DPair m n : Sig A B
| mltt_letin Γ A B C m n :
  (Sig A B :: Γ) ⊢ C : Ty ->
  Γ ⊢ m : Sig A B ->
  (B :: A :: Γ) ⊢ n : C.[DPair (Var 1) (Var 0) .: ren (+2)] ->
  Γ ⊢ LetIn C m n : C.[m/]
| mltt_tuple Γ A B :
  Γ ⊢ A : Ty ->
  Γ ⊢ B : Ty ->
  Γ ⊢ Tuple A B : Ty
| mltt_pair Γ A B m n :
  Γ ⊢ m : A ->
  Γ ⊢ n : B ->
  Γ ⊢ Pair m n : Tuple A B
| mltt_fst Γ A B m :
  Γ ⊢ m : Tuple A B ->
  Γ ⊢ Fst m : A
| mltt_snd Γ A B m :
  Γ ⊢ m : Tuple A B ->
  Γ ⊢ Snd m : B
| mltt_id Γ A m n :
  Γ ⊢ A : Ty ->
  Γ ⊢ m : A ->
  Γ ⊢ n : A ->
  Γ ⊢ Id A m n : Ty
| mltt_refl Γ A m :
  Γ ⊢ m : A ->
  Γ ⊢ Refl m : Id A m m
| mltt_rw Γ A B H P m n :
  (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ) ⊢ B : Ty ->
  Γ ⊢ H : B.[Refl m,m/] ->
  Γ ⊢ P : Id A m n ->
  Γ ⊢ Rw B H P : B.[P,n/]
| mltt_conv Γ A B m :
  A === B ->
  Γ ⊢ m : A ->
  Γ ⊢ B : Ty ->
  Γ ⊢ m : B
where "Γ ⊢ m : A" := (mltt_type Γ m A)

with mltt_wf : mltt_ctx -> Prop :=
| mltt_wf_nil : mltt_wf nil
| mltt_wf_cons Γ A :
  mltt_wf Γ ->
  Γ ⊢ A : Ty ->
  mltt_wf (A :: Γ).

Scheme mltt_type_mut := Induction for mltt_type Sort Prop
with mltt_wf_mut := Induction for mltt_wf Sort Prop.

Axiom mltt_sn : forall Γ m A, Γ ⊢ m : A -> sn mltt_step m.

Lemma mltt_type_wf Γ m A : Γ ⊢ m : A -> mltt_wf Γ.
Proof with eauto.
  elim=>{Γ m A}...
  move=>Γ A B m tym wf. inv wf...
Qed.
#[global] Hint Resolve mltt_type_wf.

Lemma mltt_mltt0_type Γ m A : Γ ⊢ m : A -> mltt0_type Γ m A.
Proof with eauto using mltt0_type, mltt0_wf.
  move:Γ m A. apply:(@mltt_type_mut _ (fun Γ wf => mltt0_wf Γ))...
  move=>Γ A B m tym ihm.
  have wf0:=mltt0_type_wf ihm. inv wf0.
  apply: mltt0_lam...
Qed.
#[global] Hint Resolve mltt_mltt0_type.
