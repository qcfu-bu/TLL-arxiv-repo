(* This file presents the strong normalization of the logical level.  *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS mltt_subst logical_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Model.

Declare Scope model_scope.
Open Scope model_scope.

(* Modeling logical TLL in MLTT. *)
Fixpoint model (m : tll_ast.term) : mltt_ast.term :=
  match m with
  | tll_ast.Var x => mltt_ast.Var x
  | tll_ast.Sort _ => mltt_ast.Ty
  | tll_ast.Pi0 A B _ => mltt_ast.Pi (model A) (model B)
  | tll_ast.Pi1 A B _ => mltt_ast.Pi (model A) (model B)
  | tll_ast.Lam0 A m _ => mltt_ast.Lam (model A) (model m)
  | tll_ast.Lam1 A m _ => mltt_ast.Lam (model A) (model m)
  | tll_ast.App m n => mltt_ast.App (model m) (model n)
  | tll_ast.Sig0 A B _ => mltt_ast.Sig (model A) (model B)
  | tll_ast.Sig1 A B _ => mltt_ast.Sig (model A) (model B)
  | tll_ast.Pair0 m n _ => mltt_ast.DPair (model m) (model n)
  | tll_ast.Pair1 m n _ => mltt_ast.DPair (model m) (model n)
  | tll_ast.LetIn A m n => mltt_ast.LetIn (model A) (model m) (model n)
  | tll_ast.With A B _ => mltt_ast.Tuple (model A) (model B)
  | tll_ast.APair m n _ => mltt_ast.Pair (model m) (model n)
  | tll_ast.Fst m => mltt_ast.Fst (model m)
  | tll_ast.Snd m => mltt_ast.Snd (model m)
  | tll_ast.Id A m n => mltt_ast.Id (model A) (model m) (model n)
  | tll_ast.Refl m => mltt_ast.Refl (model m)
  | tll_ast.Rw A H P => mltt_ast.Rw (model A) (model H) (model P)
  | tll_ast.Box => mltt_ast.Ty
  | tll_ast.Ptr _ => mltt_ast.Ty
  end.

Fixpoint model_ctx (Γ : logical_ctx) : mltt_ctx :=
  match Γ with
  | nil => nil
  | A :: Γ => model A :: model_ctx Γ
  end.

Notation "[| m |]" := (model m).
Notation "[[ Γ ]]" := (model_ctx Γ).

Lemma model_ren_com m ξ :
  [| m |].[ren ξ] = [| m.[ren ξ] |].
Proof with eauto.
  elim: m ξ=>//=...
  { move=>A ihA B ihB _ ξ. asimpl.
    rewrite ihA. rewrite ihB... }
  { move=>A ihA B ihB _ ξ. asimpl.
    rewrite ihA. rewrite ihB... }
  { move=>A ihA m ihm _ ξ. asimpl.
    rewrite ihA. rewrite ihm... }
  { move=>A ihA m ihm _ ξ. asimpl.
    rewrite ihA. rewrite ihm... }
  { move=>m ihm n ihn ξ. asimpl.
    rewrite ihm. rewrite ihn... }
  { move=>A ihA B ihB _ ξ. asimpl.
    rewrite ihA. rewrite ihB... }
  { move=>A ihA B ihB _ ξ. asimpl.
    rewrite ihA. rewrite ihB... }
  { move=>m ihm n ihn _ ξ. asimpl.
    rewrite ihm. rewrite ihn... }
  { move=>m ihm n ihn _ ξ. asimpl.
    rewrite ihm. rewrite ihn... }
  { move=>A ihA m ihm n ihn ξ. asimpl.
    rewrite ihA. rewrite ihm. rewrite ihn... }
  { move=>A ihA B ihB _ ξ. asimpl.
    rewrite ihA. rewrite ihB... }
  { move=>m ihm n ihn _ ξ.
    rewrite ihm. rewrite ihn... }
  { move=>m ihm ξ. rewrite ihm... }
  { move=>m ihm ξ. rewrite ihm... }
  { move=>A ihA m ihm n ihn ξ.
    rewrite ihA. rewrite ihm. rewrite ihn... }
  { move=>m ihm ξ. rewrite ihm... }
  { move=>A ihA H ihH P ihP ξ. asimpl.
    rewrite ihA. rewrite ihH. rewrite ihP... }
Qed.

Definition model_subst
  (σ : var -> tll_ast.term)
  (τ : var -> mltt_ast.term) : Prop := forall x, [|σ x|] = τ x.

Lemma model_subst_up σ τ :
  model_subst σ τ -> model_subst (up σ) (up τ).
Proof with eauto.
  unfold model_subst.
  move=>h x.  elim: x σ τ h...
  move=>n ih σ τ h. asimpl.
  rewrite<-model_ren_com.
  rewrite h...
Qed.

Lemma model_subst_com m σ τ :
  model_subst σ τ -> [| m.[σ] |] = [| m |].[τ].
Proof with eauto using model_subst_up.
  elim: m σ τ=>//=.
  { move=>A ihA B ihB _ σ τ h.
    rewrite (ihA _ τ)...
    rewrite (ihB _ (up τ))... }
  { move=>A ihA B ihB _ σ τ h.
    rewrite (ihA _ τ)...
    rewrite (ihB _ (up τ))... }
  { move=>A ihA m ihm _ σ τ h.
    rewrite (ihA _ τ)...
    rewrite (ihm _ (up τ))... }
  { move=>A ihA m ihm _ σ τ h.
    rewrite (ihA _ τ)...
    rewrite (ihm _ (up τ))... }
  { move=>m ihm n ihn σ τ h.
    rewrite (ihm _ τ)...
    rewrite (ihn _ τ)... }
  { move=>A ihA B ihB _ σ τ h.
    rewrite (ihA _ τ)...
    rewrite (ihB _ (up τ))... }
  { move=>A ihA B ihB _ σ τ h.
    rewrite (ihA _ τ)...
    rewrite (ihB _ (up τ))... }
  { move=>m ihm n ihn _ σ τ h.
    rewrite (ihm _ τ)...
    rewrite (ihn _ τ)... }
  { move=>m ihm n ihn _ σ τ h.
    rewrite (ihm _ τ)...
    rewrite (ihn _ τ)... }
  { move=>A ihA m ihm n ihn σ τ h.
    replace (upn 2 σ) with (up (up σ)) by autosubst.
    rewrite (ihA _ (up τ))...
    rewrite (ihm _ τ)...
    rewrite (ihn _ (up (up τ)))... }
  { move=>A ihA B ihB _ σ τ h.
    rewrite (ihA _ τ)...
    rewrite (ihB _ τ)... }
  { move=>m ihm n ihn _ σ τ h.
    rewrite (ihm _ τ)...
    rewrite (ihn _ τ)... }
  { move=>m ihm σ τ h. rewrite (ihm _ τ)... }
  { move=>m ihm σ τ h. rewrite (ihm _ τ)... }
  { move=>A ihA m ihm n ihn σ τ h.
    rewrite (ihA _ τ)...
    rewrite (ihm _ τ)...
    rewrite (ihn _ τ)... }
  { move=>m ihm σ τ h. rewrite (ihm _ τ)... }
  { move=>A ihA H ihH P ihP σ τ h.
    replace (upn 2 σ) with (up (up σ)) by autosubst.
    rewrite (ihA _ (up (up τ)))...
    rewrite (ihH _ τ)...
    rewrite (ihP _ τ)... }
Qed.

(* Lemma 2 (Logical Reduction Model) *)
Lemma model_step m n : logical_step m n -> mltt_step [|m|] [|n|].
Proof with eauto using mltt_step.
  elim=>//={m n}...
  { move=>A m n _.
    erewrite model_subst_com.
    constructor. move=>x. destruct x=>//. }
  { move=>A m n _.
    erewrite model_subst_com.
    constructor. move=>x. destruct x=>//. }
  { move=>A m1 m2 n _.
    erewrite model_subst_com.
    constructor. move=>x.
    destruct x=>//.
    destruct x=>//. }
  { move=>A m1 m2 n _.
    erewrite model_subst_com.
    constructor. move=>x.
    destruct x=>//.
    destruct x=>//. }
Qed.

Lemma model_red m n : logical_red m n -> mltt_red [|m|] [|n|].
Proof with eauto using mltt_step, star.
  elim=>{n}...
  move=>y z rd1 rd2 st.
  apply: star_trans...
  apply: star1.
  apply: model_step...
Qed.

Lemma model_conv m n :
  conv logical_step m n -> conv mltt_step [|m|] [|n|].
Proof with eauto using mltt_step, conv.
  elim=>{n}...
  { move=>y z eq1 eq2 st.
    apply: conv_trans...
    apply: conv1.
    apply: model_step... }
  { move=>y z eq1 eq2 st.
    apply: conv_trans...
    apply: conv_sym.
    apply: conv1.
    apply: model_step... }
Qed.

Lemma model_has Γ x A :
  logical_has Γ x A -> mltt_has [[Γ]] x [|A|].
Proof with eauto using mltt_has.
  elim=>//={Γ x A}.
  { move=>Γ A. rewrite<-model_ren_com... }
  { move=>Γ A B x shs ih. rewrite<-model_ren_com... }
Qed.

(* Logical Type Model *)
Theorem logical_mltt_model Γ m A :
  logical_type Γ m A -> mltt_type [[Γ]] [|m|] [|A|].
Proof with eauto using mltt_type, mltt_wf.
  move:Γ m A. apply: (@logical_type_mut _ (fun Γ wf=> mltt_wf [[Γ]])); simpl...
  { move=>Γ x A wf1 wf2 shs.
    constructor...
    apply: model_has... }
  { move=>Γ A B m n s tym ihm tyn ihn.
    erewrite model_subst_com...
    move=>x. destruct x=>//. }
  { move=>Γ A B m n s tym ihm tyn ihn.
    erewrite model_subst_com...
    move=>x. destruct x=>//. }
  { move=>Γ A B m n t _ _ tym ihm tyn ihn.
    constructor...
    erewrite<-model_subst_com...
    move=>x. destruct x=>//. }
  { move=>Γ A B m n t _ _ tym ihm tyn ihn.
    constructor...
    erewrite<-model_subst_com...
    move=>x. destruct x=>//. }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn.
    erewrite model_subst_com...
    econstructor...
    erewrite<-model_subst_com...
    move=>x. destruct x=>//.
    move=>x. destruct x=>//. }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn.
    erewrite model_subst_com...
    econstructor...
    erewrite<-model_subst_com...
    move=>x. destruct x=>//.
    move=>x. destruct x=>//. }
  { move=>Γ A B H P m n s tyB ihB tyH ihH tyP ihP.
    erewrite model_subst_com...
    apply: mltt_rw...
    rewrite!model_ren_com...
    erewrite<-model_subst_com...
    move=>x. destruct x=>//=. destruct x=>//=.
    move=>x. destruct x=>//=. destruct x=>//=. }
  { move=>Γ A B m s eq tym ihm tyB ihB.
    apply: mltt_conv.
    apply: model_conv...
    apply: ihm.
    apply: ihB. }
Qed.

CoInductive nn T (Rel : T -> T -> Prop) : T -> Prop :=
| nnI m m' : Rel m m' -> nn Rel m' -> nn Rel m.

CoFixpoint model_nn m : (nn logical_step m) -> nn mltt_step [|m|].
Proof with eauto.
  move=>h. inv h.
  move/model_step in H.
  move/model_nn in H0.
  econstructor...
Qed.

Lemma nn_sn_false T (Rel : T -> T -> Prop) m : nn Rel m -> ~sn Rel m.
Proof with eauto.
  move=>h1 h2. elim: h2 h1.
  move=>x h1 h2 h3. inv h3...
Qed.

Lemma not_sn T (Rel : T -> T -> Prop) m :
  ~sn Rel m -> exists m', Rel m m' /\ ~sn Rel m'.
Proof with eauto using sn.
  move=>h.
  have[//|h1]:=classic (exists m', Rel m m' /\ ~sn Rel m').
  firstorder. simpl in H.
  have H':forall n, Rel m n -> sn Rel n.
  { move=>n r.
    specialize (H n).
    move/not_and_or in H.
    firstorder.
    move/NNPP in H... }
  exfalso.
  apply: h...
Qed.

CoFixpoint not_sn_nn T (Rel : T -> T -> Prop) m :
  ~sn Rel m -> nn Rel m.
Proof with eauto using nn.
  move=> h.
  apply not_sn in h.
  firstorder...
Qed.

(* Theorem 5 (Logical Strong Normalization) *)
Theorem logical_sn Γ m A : logical_type Γ m A -> sn logical_step m.
Proof with eauto.
  move=>/logical_mltt_model ty.
  have h1:=mltt_sn ty.
  have[h2|h2]:=classic (nn logical_step m).
  { move/model_nn in h2.
    exfalso. apply: nn_sn_false... }
  { have[//|h3]:=classic (sn logical_step m).
    exfalso. apply: h2. apply: not_sn_nn... }
Qed.

End Model.
