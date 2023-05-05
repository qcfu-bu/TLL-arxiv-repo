From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS mltt_ctx mltt_type mltt_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive mltt_agree_ren : (var -> var) ->
  mltt_ctx -> mltt_ctx -> Prop :=
| mltt_agree_ren_nil ξ :
  mltt_agree_ren ξ nil nil
| mltt_agree_ren_cons Γ Γ' ξ m :
  Γ ⊢ m : Ty ->
  mltt_agree_ren ξ Γ Γ' ->
  mltt_agree_ren (upren ξ) (m :: Γ) (m.[ren ξ] :: Γ')
| mltt_agree_ren_wk Γ Γ' ξ m :
  Γ' ⊢ m : Ty ->
  mltt_agree_ren ξ Γ Γ' ->
  mltt_agree_ren (ξ >>> (+1)) (Γ) (m :: Γ').

Lemma mltt_agree_ren_refl Γ : mltt_wf Γ -> mltt_agree_ren id Γ Γ.
Proof with eauto using mltt_agree_ren.
  move=>wf. elim: wf=>{Γ}...
  move=>Γ A wf agr tyA.
  have:(mltt_agree_ren (upren id) (A :: Γ) (A.[ren id] :: Γ))...
  by asimpl.
Qed.

Lemma mltt_agree_ren_has Γ Γ' ξ x A :
  mltt_agree_ren ξ Γ Γ' -> mltt_has Γ x A -> mltt_has Γ' (ξ x) A.[ren ξ].
Proof with eauto.
  move=>agr. elim: agr x A=>{Γ Γ' ξ}.
  { move=>ξ x A hs. inv hs. }
  { move=>Γ Γ' ξ m tym agr ih x A hs. inv hs; asimpl.
    { replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] by autosubst.
      constructor. }
    { replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)] by autosubst.
      constructor... } }
  { move=>Γ Γ' ξ m tym agr ih x B /ih hs. asimpl.
    replace B.[ren (ξ >>> (+1))] with B.[ren ξ].[ren (+1)] by autosubst.
    constructor... }
Qed.

Lemma mltt_agree_weak_wf_nil Γ' ξ : mltt_agree_ren ξ nil Γ' -> mltt_wf Γ'.
Proof with eauto using mltt_wf.
  move e:(nil)=>Γ agr. elim: agr e=>//{Γ Γ' ξ}...
Qed.

Lemma mltt_agree_weak_wf_cons Γ Γ' A ξ :
  mltt_agree_ren ξ (A :: Γ) Γ' -> mltt_wf Γ ->
  (∀ Γ' ξ, mltt_agree_ren ξ Γ Γ' → mltt_wf Γ') ->
  (∀ Γ' ξ, mltt_agree_ren ξ Γ Γ' → Γ' ⊢ A.[ren ξ] : Ty) ->
  mltt_wf Γ'.
Proof with eauto using mltt_wf.
  move e:(A :: Γ)=>Γ0 agr. elim: agr Γ A e=>//{Γ0 Γ' ξ}...
  move=>Γ Γ' ξ m tym agr _ Γ0 A [e1 e2] wf h1 h2; subst.
  apply: mltt_wf_cons...
Qed.

Lemma mltt_rename Γ Γ' m A ξ :
  Γ ⊢ m : A -> mltt_agree_ren ξ Γ Γ' -> Γ' ⊢ m.[ren ξ] : A.[ren ξ].
Proof with eauto using mltt_type, mltt_wf, mltt_agree_ren.
  move=>tym. move:Γ m A tym Γ' ξ.
  apply:(@mltt_type_mut _ (fun Γ wf => forall Γ' ξ, mltt_agree_ren ξ Γ Γ' -> mltt_wf Γ'))...
  { move=>Γ x A wf h hs Γ' ξ agr. asimpl.
    apply: mltt_var...
    apply: mltt_agree_ren_has... }
  { move=>Γ A B tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have wf:=mltt_type_wf tyB. inv wf.
    apply: mltt_pi... }
  { move=>Γ A B m tym ihm Γ' ξ agr. asimpl.
    have wf:=mltt_type_wf tym. inv wf.
    apply: mltt_lam... }
  { move=>Γ A B m n tym ihm tyn ihn Γ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    apply: mltt_app...
    asimpl in ihm... }
  { move=>Γ A B tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have{}ihA:=ihA _ _ agr.
    have{}ihB:=ihB _ _ (mltt_agree_ren_cons tyA agr).
    apply: mltt_sig... }
  { move=>Γ A B m n tym ihm tyn ihn Γ' ξ agr. asimpl.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    asimpl in ihn.
    apply: mltt_dpair...
    by autosubst. }
  { move=>Γ A B C m n tyC ihC tym ihm tyn ihn Γ' ξ agr. asimpl.
    have wf:=mltt_type_wf tyC. inv wf.
    have wf:=mltt_type_wf tyn. inv wf. inv H3.
    have{}ihC:=ihC _ _ (mltt_agree_ren_cons H2 agr).
    have{}ihm:=ihm _ _ agr.
    have/ihn{}ihn:mltt_agree_ren (upren (upren ξ)) (B :: A :: Γ)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[DPair (Var 1) (Var 0) .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[DPair (Var 1) (Var 0) .: ren (+2)]
        in ihn by autosubst.
    have:=mltt_letin ihC ihm ihn.
    by autosubst. }
  { move=>Γ A B H P m n tyB ihB tyH ihH tyP ihP Γ' ξ agr. asimpl.
    have wf:=mltt_type_wf tyB. inv wf. inv H2.
    have{}ihP:=ihP _ _ agr.
    have/ihB{}ihB:
      mltt_agree_ren (upren (upren ξ))
        (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ)
        ((Id A.[ren (+1)] m.[ren (+1)] (Var 0)).[ren (upren ξ)] :: A.[ren ξ] :: Γ')...
    have{}ihH:=ihH _ _ agr.
    asimpl in ihP.
    asimpl in ihB.
    asimpl in ihH.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)] in ihB by autosubst.
    replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] in ihB by autosubst.
    have pf:=mltt_rw ihB. asimpl in pf.
    have:=pf _ _ _ ihH ihP.
    by autosubst. }
  { move=>Γ A B m eq tym ihm tyB ihB Γ' ξ agr.
    apply: mltt_conv.
    apply: mltt_conv_subst.
    apply: eq.
    by apply: ihm.
    have:=ihB _ _ agr.
    asimpl... }
  { exact: mltt_agree_weak_wf_nil. }
  { move=>Γ A wf ih tyA ihA Γ' ξ agr.
    apply: mltt_agree_weak_wf_cons... }
Qed.

Lemma mltt_wf_ok Γ x A :
  mltt_wf Γ -> mltt_has Γ x A -> Γ ⊢ A : Ty.
Proof with eauto using mltt_agree_ren, mltt_agree_ren_refl.
  move=>wf. elim: wf x A=>{Γ}.
  { move=>x A hs. inv hs. }
  { move=>Γ A wf ih tyA x B hs. inv hs.
    { replace Ty with Ty.[ren (+1)] by autosubst.
      apply: mltt_rename... }
    { have tyA0:=ih _ _ H3.
      replace Ty with Ty.[ren (+1)] by autosubst.
      apply: mltt_rename... } }
Qed.

Lemma mltt_weaken Γ m A B :
  Γ ⊢ m : A ->
  Γ ⊢ B : Ty ->
  (B :: Γ) ⊢ m.[ren (+1)] : A.[ren (+1)].
Proof with eauto using mltt_agree_ren, mltt_agree_ren_refl.
  move=>tym tyB. apply: mltt_rename...
Qed.

Lemma mltt_eweaken Γ m m' A A' B :
  m' = m.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ m : A ->
  Γ ⊢ B : Ty ->
  (B :: Γ) ⊢ m' : A'.
Proof with eauto using mltt_agree_ren, mltt_agree_ren_refl.
  move=>*; subst. apply: mltt_weaken...
Qed.
