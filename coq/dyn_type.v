From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS
  sta_ctx sta_step sta_type
  dyn_ctx dyn_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ ; Δ ⊢ m : A" (at level 50, Δ, m, A at next level).
Inductive dyn_type : sta_ctx -> dyn_ctx -> term -> term -> Prop :=
| dyn_var Γ Δ x s A :
  dyn_wf Γ Δ ->
  sta_has Γ x A ->
  dyn_has Δ x s A ->
  Γ ; Δ ⊢ Var x : A
| dyn_lam0 Γ Δ A B m s :
  Δ ▷ s ->
  (A :: Γ) ; _: Δ ⊢ m : B ->
  Γ ; Δ ⊢ Lam0 A m s : Pi0 A B s
| dyn_lam1 Γ Δ A B m s t :
  Δ ▷ s ->
  (A :: Γ) ; A :{t} Δ ⊢ m : B ->
  Γ ; Δ ⊢ Lam1 A m s : Pi1 A B s
| dyn_app0 Γ Δ A B m n s :
  Γ ; Δ ⊢ m : Pi0 A B s ->
  Γ ⊢ n : A ->
  Γ ; Δ ⊢ App m n : B.[n/]
| dyn_app1 Γ Δ1 Δ2 Δ A B m n s :
  Δ1 ∘ Δ2 => Δ ->
  Γ ; Δ1 ⊢ m : Pi1 A B s ->
  Γ ; Δ2 ⊢ n : A ->
  Γ ; Δ ⊢ App m n : B.[n/]
| dyn_pair0 Γ Δ A B m n t :
  Γ ⊢ Sig0 A B t : Sort t ->
  Γ ; Δ ⊢ m : A ->
  Γ ⊢ n : B.[m/] ->
  Γ ; Δ ⊢ Pair0 m n t : Sig0 A B t
| dyn_pair1 Γ Δ1 Δ2 Δ A B m n t :
  Δ1 ∘ Δ2 => Δ ->
  Γ ⊢ Sig1 A B t : Sort t ->
  Γ ; Δ1 ⊢ m : A ->
  Γ ; Δ2 ⊢ n : B.[m/] ->
  Γ ; Δ ⊢ Pair1 m n t : Sig1 A B t
| dyn_letin0 Γ Δ1 Δ2 Δ A B C m n s r t :
  Δ1 ∘ Δ2 => Δ ->
  (Sig0 A B t :: Γ) ⊢ C : Sort s ->
  Γ ; Δ1 ⊢ m : Sig0 A B t ->
  (B :: A :: Γ) ; _: A :{r} Δ2 ⊢ n : C.[Pair0 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ; Δ ⊢ LetIn C m n : C.[m/]
| dyn_letin1 Γ Δ1 Δ2 Δ A B C m n s r1 r2 t :
  Δ1 ∘ Δ2 => Δ ->
  (Sig1 A B t :: Γ) ⊢ C : Sort s ->
  Γ ; Δ1 ⊢ m : Sig1 A B t ->
  (B :: A :: Γ) ; B :{r2} A :{r1} Δ2 ⊢ n : C.[Pair1 (Var 1) (Var 0) t .: ren (+2)] ->
  Γ ; Δ ⊢ LetIn C m n : C.[m/]
| dyn_apair Γ Δ A B m n t :
  Δ ▷ t ->
  Γ ; Δ ⊢ m : A ->
  Γ ; Δ ⊢ n : B ->
  Γ ; Δ ⊢ APair m n t : With A B t
| dyn_fst Γ Δ A B m t :
  Γ ; Δ ⊢ m : With A B t ->
  Γ ; Δ ⊢ Fst m : A
| dyn_snd Γ Δ A B m t :
  Γ ; Δ ⊢ m : With A B t ->
  Γ ; Δ ⊢ Snd m : B
| dyn_rw Γ Δ A B H P m n s :
  (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ) ⊢ B : Sort s ->
  Γ ; Δ ⊢ H : B.[Refl m,m/] ->
  Γ ⊢ P : Id A m n ->
  Γ ; Δ ⊢ Rw B H P : B.[P,n/]
| dyn_conv Γ Δ A B m s :
  A === B ->
  Γ ; Δ ⊢ m : A ->
  Γ ⊢ B : Sort s ->
  Γ ; Δ ⊢ m : B
where "Γ ; Δ ⊢ m : A" := (dyn_type Γ Δ m A)

with dyn_wf : sta_ctx -> dyn_ctx -> Prop :=
| dyn_wf_nil : dyn_wf nil nil
| dyn_wf_ty Γ Δ A s :
  dyn_wf Γ Δ ->
  Γ ⊢ A : Sort s ->
  dyn_wf (A :: Γ) (A :{s} Δ)
| dyn_wf_n Γ Δ A s :
  dyn_wf Γ Δ ->
  Γ ⊢ A : Sort s ->
  dyn_wf (A :: Γ) (_: Δ).

Scheme dyn_type_mut := Induction for dyn_type Sort Prop
with dyn_wf_mut := Induction for dyn_wf Sort Prop.

Lemma dyn_wf_size Γ Δ : dyn_wf Γ Δ -> size Γ = size Δ.
Proof with eauto. elim=>//={Γ Δ}... Qed.

Lemma dyn_wf_merge Γ Δ Δ1 Δ2 :
  Δ1 ∘ Δ2 => Δ -> dyn_wf Γ Δ1 -> dyn_wf Γ Δ2 -> dyn_wf Γ Δ.
Proof with eauto using dyn_wf.
  move=>mrg wf.  elim: wf Δ Δ2 mrg=>{Γ Δ1}.
  { move=>Δ Δ2 mrg wf. inv mrg... }
  { move=>Γ Δ1 A s wf1 ih tyA Δ Δ2 mrg wf2. inv mrg.
    { inv wf2. apply: dyn_wf_ty... }
    { inv wf2. apply: dyn_wf_ty... } }
  { move=>Γ Δ1 A s wf1 ih tyA Δ Δ2 mrg wf2. inv mrg.
    { inv wf2. apply: dyn_wf_ty... }
    { inv wf2. apply: dyn_wf_n... } }
Qed.

Lemma dyn_type_wf Γ Δ m A : Γ ; Δ ⊢ m : A -> dyn_wf Γ Δ.
Proof with eauto using dyn_wf.
  elim=>{Γ Δ m A}...
  { move=>Γ Δ A B m s k tym ih. inv ih... }
  { move=>Γ Δ A B m s t k tym ih. inv ih... }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn.
    apply: dyn_wf_merge... }
  { move=>Γ Δ1 Δ2 Δ A B m n t mrg tyS tym ihm tyn ihn.
    apply: dyn_wf_merge... }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn.
    inv ihn. inv H2.
    apply: dyn_wf_merge... }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn.
    inv ihn. inv H2.
    apply: dyn_wf_merge... }
Qed.
#[global] Hint Resolve dyn_type_wf.

Lemma dyn_wf_inv Γ Δ Δ1 Δ2 :
  Δ1 ∘ Δ2 => Δ -> dyn_wf Γ Δ -> dyn_wf Γ Δ1 /\ dyn_wf Γ Δ2.
Proof with eauto using dyn_wf.
  move=>mrg agr. elim: agr Δ1 Δ2 mrg=>{Γ Δ}.
  { move=>Δ1 Δ2 mrg. inv mrg... }
  { move=>Γ Δ A s wf ih tyA Δ1 Δ2 mrg. inv mrg.
    { have[wf1 wf2]:=ih _ _ H2... }
    { have[wf1 wf2]:=ih _ _ H2... }
    { have[wf1 wf2]:=ih _ _ H2... } }
  { move=>Γ Δ A s wf ih tyA Δ1 Δ2 mrg. inv mrg.
    have[wf1 wf2]:=ih _ _ H2... }
Qed.
