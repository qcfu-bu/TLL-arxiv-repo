From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_ctx sta_type sta_conf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive sta_agree_ren : (var -> var) ->
  sta_ctx -> sta_ctx -> Prop :=
| sta_agree_ren_nil ξ :
  sta_agree_ren ξ nil nil
| sta_agree_ren_cons Γ Γ' ξ m s :
  Γ ⊢ m : Sort s ->
  sta_agree_ren ξ Γ Γ' ->
  sta_agree_ren (upren ξ) (m :: Γ) (m.[ren ξ] :: Γ')
| sta_agree_ren_wk Γ Γ' ξ m s :
  Γ' ⊢ m : Sort s ->
  sta_agree_ren ξ Γ Γ' ->
  sta_agree_ren (ξ >>> (+1)) (Γ) (m :: Γ').

Lemma sta_agree_ren_refl Γ : sta_wf Γ -> sta_agree_ren id Γ Γ.
Proof with eauto using sta_agree_ren.
  move=>wf. elim: wf=>{Γ}...
  move=>Γ A s wf agr tyA.
  have:(sta_agree_ren (upren id) (A :: Γ) (A.[ren id] :: Γ))...
  by asimpl.
Qed.

Lemma sta_agree_ren_has Γ Γ' ξ x A :
  sta_agree_ren ξ Γ Γ' -> sta_has Γ x A -> sta_has Γ' (ξ x) A.[ren ξ].
Proof with eauto.
  move=>agr. elim: agr x A=>{Γ Γ' ξ}.
  { move=>ξ x A hs. inv hs. }
  { move=>Γ Γ' ξ m s tym agr ih x A hs. inv hs; asimpl.
    { replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] by autosubst.
      constructor. }
    { replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)] by autosubst.
      constructor... } }
  { move=>Γ Γ' ξ m A tym agr ih x B /ih hs. asimpl.
    replace B.[ren (ξ >>> (+1))] with B.[ren ξ].[ren (+1)] by autosubst.
    constructor... }
Qed.

Lemma sta_agree_weak_wf_nil Γ' ξ : sta_agree_ren ξ nil Γ' -> sta_wf Γ'.
Proof with eauto using sta_wf.
  move e:(nil)=>Γ agr. elim: agr e=>//{Γ Γ' ξ}...
Qed.

Lemma sta_agree_weak_wf_cons Γ Γ' A s ξ :
  sta_agree_ren ξ (A :: Γ) Γ' -> sta_wf Γ -> 
  (∀ Γ' ξ, sta_agree_ren ξ Γ Γ' → sta_wf Γ') ->
  (∀ Γ' ξ, sta_agree_ren ξ Γ Γ' → Γ' ⊢ A.[ren ξ] : Sort s) ->
  sta_wf Γ'.
Proof with eauto using sta_wf.
  move e:(A :: Γ)=>Γ0 agr. elim: agr Γ A s e=>//{Γ0 Γ' ξ}...
  move=>Γ Γ' ξ m s tym agr _ Γ0 A s0 [e1 e2] wf h1 h2; subst.
  apply: sta_wf_cons...
Qed.

Lemma sta_rename Γ Γ' m A ξ :
  Γ ⊢ m : A -> sta_agree_ren ξ Γ Γ' -> Γ' ⊢ m.[ren ξ] : A.[ren ξ].
Proof with eauto using sta_type, sta_wf, sta_agree_ren.
  move=>tym. move:Γ m A tym Γ' ξ.
  apply:(@sta_type_mut _ (fun Γ wf => forall Γ' ξ, sta_agree_ren ξ Γ Γ' -> sta_wf Γ'))...
  { move=>Γ x A wf h hs Γ' ξ agr. asimpl.
    apply: sta_var...
    apply: sta_agree_ren_has... }
  { move=>Γ A B s r t tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyB. inv wf.
    apply: sta_pi0... }
  { move=>Γ A B s r t tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyB. inv wf.
    apply: sta_pi1... }
  { move=>Γ A B m s tym ihm Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tym. inv wf.
    apply: sta_lam0... }
  { move=>Γ A B m s tym ihm Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tym. inv wf.
    apply: sta_lam1... }
  { move=>Γ A B m n s tym ihm tyn ihn Γ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    apply: sta_app0...
    asimpl in ihm... }
  { move=>Γ A B m n s tym ihm tyn ihn Γ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    apply: sta_app1...
    asimpl in ihm... }
  { move=>Γ A B s r t ord tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have{}ihA:=ihA _ _ agr.
    have{}ihB:=ihB _ _ (sta_agree_ren_cons tyA agr).
    apply: sta_sig0... }
  { move=>Γ A B s r t ord1 ord2 tyA ihA tyB ihB Γ' ξ agr. asimpl.
    have{}ihA:=ihA _ _ agr.
    have{}ihB:=ihB _ _ (sta_agree_ren_cons tyA agr).
    apply: sta_sig1.
    exact: ord1. exact: ord2. all: eauto. }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn Γ' ξ agr. asimpl.
    have{}ihS:=ihS _ _ agr.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    asimpl in ihS.
    asimpl in ihn.
    apply: sta_pair0...
    by autosubst. }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn Γ' ξ agr. asimpl.
    have{}ihS:=ihS _ _ agr.
    have{}ihm:=ihm _ _ agr.
    have{}ihn:=ihn _ _ agr.
    asimpl in ihS.
    asimpl in ihn.
    apply: sta_pair1...
    by autosubst. }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=sta_type_wf tyn. inv wf. inv H3.
    have{}ihC:=ihC _ _ (sta_agree_ren_cons H2 agr).
    have{}ihm:=ihm _ _ agr.
    have/ihn{}ihn:sta_agree_ren (upren (upren ξ)) (B :: A :: Γ)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair0 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=sta_letin0 ihC ihm ihn.
    by autosubst. }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=sta_type_wf tyn. inv wf. inv H3.
    have{}ihC:=ihC _ _ (sta_agree_ren_cons H2 agr).
    have{}ihm:=ihm _ _ agr.
    have/ihn{}ihn:sta_agree_ren (upren (upren ξ)) (B :: A :: Γ)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair1 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=sta_letin1 ihC ihm ihn.
    by autosubst. }
  { move=>Γ A B H P m n s tyB ihB tyH ihH tyP ihP Γ' ξ agr. asimpl.
    have wf:=sta_type_wf tyB. inv wf. inv H2.
    have{}ihP:=ihP _ _ agr.
    have/ihB{}ihB:
      sta_agree_ren (upren (upren ξ))
        (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ)
        ((Id A.[ren (+1)] m.[ren (+1)] (Var 0)).[ren (upren ξ)] :: A.[ren ξ] :: Γ')...
    have{}ihH:=ihH _ _ agr.
    asimpl in ihP.
    asimpl in ihB.
    asimpl in ihH.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)] in ihB by autosubst.
    replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] in ihB by autosubst.
    have pf:=sta_rw ihB. asimpl in pf.
    have:=pf _ _ _ ihH ihP.
    by autosubst. }
  { move=>Γ A B m s eq tym ihm tyB ihB Γ' ξ agr.
    apply: sta_conv.
    apply: sta_conv_subst.
    apply: eq.
    by apply: ihm.
    have:=ihB _ _ agr.
    asimpl... }
  { exact: sta_agree_weak_wf_nil. }
  { move=>Γ A s wf ih tyA ihA Γ' ξ agr.
    apply: sta_agree_weak_wf_cons... }
Qed.

Lemma sta_wf_ok Γ x A :
  sta_wf Γ -> sta_has Γ x A -> exists s, Γ ⊢ A : Sort s.
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>wf. elim: wf x A=>{Γ}.
  { move=>x A hs. inv hs. }
  { move=>Γ A s wf ih tyA x B hs. inv hs.
    { exists s.
      replace (Sort s) with (Sort s).[ren (+1)] by autosubst.
      apply: sta_rename... }
    { have[t tyA0]:=ih _ _ H3.
      exists t.
      replace (Sort t) with (Sort t).[ren (+1)] by autosubst.
      apply: sta_rename... } }
Qed.

Lemma sta_weaken Γ m A B s :
  Γ ⊢ m : A ->
  Γ ⊢ B : Sort s ->
  (B :: Γ) ⊢ m.[ren (+1)] : A.[ren (+1)].
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>tym tyB. apply: sta_rename...
Qed.

Lemma sta_eweaken Γ m m' A A' B s :
  m' = m.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ m : A ->
  Γ ⊢ B : Sort s ->
  (B :: Γ) ⊢ m' : A'.
Proof with eauto using sta_agree_ren, sta_agree_ren_refl.
  move=>*; subst. apply: sta_weaken...
Qed.
