From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma era_rename Γ Γ' Δ Δ' m m' A ξ :
  Γ ; Δ ⊢ m ~ m' : A -> dyn_agree_ren ξ Γ Δ Γ' Δ' ->
  Γ' ; Δ' ⊢ m.[ren ξ] ~ m'.[ren ξ] : A.[ren ξ].
Proof with eauto using
  era_type, sta_agree_ren, dyn_agree_ren, dyn_agree_ren_key.
  move=>ty. elim: ty Γ' Δ' ξ=>{Γ Δ m m' A}.
  { move=>Γ Δ x s A wf shs dhs Γ' Δ' ξ agr. asimpl.
    apply: era_var.
    apply: dyn_rename_wf...
    apply: sta_agree_ren_has...
    apply: dyn_sta_agree_ren...
    apply: dyn_agree_ren_has... }
  { move=>Γ Δ A B m m' s k tym ihm Γ' Δ' ξ agr. asimpl.
    have wf:=dyn_type_wf (era_dyn_type tym). inv wf.
    apply: era_lam0... }
  { move=>Γ Δ A B m m' s t k tym ihm Γ' Δ' ξ agr. asimpl.
    have wf:=dyn_type_wf (era_dyn_type tym). inv wf.
    apply: era_lam1... }
  { move=>Γ Δ A B m m' n s tym ihm tyn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ _ agr.
    have{}ihn:=sta_rename tyn (dyn_sta_agree_ren agr).
    apply: era_app0...
    asimpl in ihm... }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg.
    have{}ihm:=ihm _ _ _ agr1.
    have{}ihn:=ihn _ _ _ agr2.
    apply: era_app1...
    asimpl in ihm... }
  { move=>Γ Δ A B m m' n t tyS tym ihm tyn Γ' Δ' ξ agr. asimpl.
    have{}ihm:=ihm _ _ _ agr.
    have{}ihn:=sta_rename tyn (dyn_sta_agree_ren agr).
    have{}ihS:=sta_rename tyS (dyn_sta_agree_ren agr).
    apply: era_pair0...
    asimpl in ihS...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg tyS tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg.
    have{}ihm:=ihm _ _ _ agr1.
    have{}ihn:=ihn _ _ _ agr2.
    have{}ihS:=sta_rename tyS (dyn_sta_agree_ren agr).
    apply: era_pair1...
    asimpl in ihS...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg tyC tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf (era_dyn_type tyn). inv wf. inv H4.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg.
    have{}ihC:=sta_rename tyC (sta_agree_ren_cons H2 (dyn_sta_agree_ren agr)).
    have{}ihm:=ihm _ _ _ agr1.
    have/ihn{}ihn:dyn_agree_ren (upren (upren ξ)) (B :: A :: Γ) (_: A :{r} Δ2)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ') (_: A.[ren ξ] :{r} Δ2')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair0 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=era_letin0 mrg' ihC ihm ihn.
    by autosubst. }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg tyC tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf (era_dyn_type tyn). inv wf. inv H4.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=dyn_agree_ren_merge agr mrg.
    have{}ihC:=sta_rename tyC (sta_agree_ren_cons H2 (dyn_sta_agree_ren agr)).
    have{}ihm:=ihm _ _ _ agr1.
    have/ihn{}ihn:dyn_agree_ren (upren (upren ξ)) (B :: A :: Γ) (B :{r2} A :{r1} Δ2)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ') (B.[ren (upren ξ)] :{r2} A.[ren ξ] :{r1} Δ2')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair1 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=era_letin1 mrg' ihC ihm ihn.
    by autosubst. }
  { move=>Γ Δ A B m m' n n' t k tym ihm tyn ihn Γ' Δ' ξ agr. asimpl. apply:era_apair... }
  { move=>Γ Δ A B m m' t tym ihm Γ' Δ' ξ agr. asimpl. apply:era_fst... }
  { move=>Γ Δ A B m m' t tym ihm Γ' Δ' ξ agr. asimpl. apply:era_snd... }
  { move=>Γ Δ A B H H' P m n s tyB erH ihH tyP Γ' Δ' ξ agr. asimpl.
    have wf:=sta_type_wf tyB. inv wf. inv H2.
    have ihP:=sta_rename tyP (dyn_sta_agree_ren agr).
    have agr':=dyn_sta_agree_ren agr.
    have{}agr':
      sta_agree_ren (upren (upren ξ))
        (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ)
        ((Id A.[ren (+1)] m.[ren (+1)] (Var 0)).[ren (upren ξ)] :: A.[ren ξ] :: Γ')...
    have ihB:=sta_rename tyB agr'.
    have{}ihH:=ihH _ _ _ agr.
    asimpl in ihP.
    asimpl in ihB.
    asimpl in ihH.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)] in ihB by autosubst.
    replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] in ihB by autosubst.
    have pf:=era_rw ihB. asimpl in pf.
    have:=pf _ _ _ _ _ ihH ihP.
    by autosubst. }
  { move=>Γ Δ A B m m' s eq tym ihm tyB Γ' Δ' ξ agr.
    apply: era_conv.
    apply: sta_conv_subst...
    apply: ihm...
    have:=sta_rename tyB (dyn_sta_agree_ren agr).
    asimpl... }
Qed.

Lemma era_weakenU Γ Δ m m' A B :
  Γ ⊢ B : Sort U ->
  Γ ; Δ ⊢ m ~ m' : A ->
  (B :: Γ) ; B :U Δ ⊢ m.[ren (+1)] ~ m'.[ren (+1)] : A.[ren (+1)].
Proof with eauto using dyn_agree_ren, dyn_agree_ren_refl.
  move=>tyB tym. apply: era_rename...
Qed.

Lemma era_weakenN Γ Δ m m' A B s :
  Γ ⊢ B : Sort s ->
  Γ ; Δ ⊢ m ~ m' : A ->
  (B :: Γ) ; _: Δ ⊢ m.[ren (+1)] ~ m'.[ren (+1)] : A.[ren (+1)].
Proof with eauto using dyn_agree_ren, dyn_agree_ren_refl.
  move=>tyB tym. apply: era_rename...
Qed.

Lemma era_eweakenU Γ Δ m m' n n' A A' B :
  m' = m.[ren (+1)] ->
  n' = n.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ B : Sort U ->
  Γ ; Δ ⊢ m ~ n : A ->
  (B :: Γ) ; B :U Δ ⊢ m' ~ n' : A'.
Proof.
  move=>*; subst. exact: era_weakenU.
Qed.

Lemma era_eweakenN Γ Δ m m' n n' A A' B s :
  m' = m.[ren (+1)] ->
  n' = n.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ B : Sort s ->
  Γ ; Δ ⊢ m ~ n : A ->
  (B :: Γ) ; (_: Δ) ⊢ m' ~ n' : A'.
Proof.
  move=>*; subst. apply: era_weakenN; eauto.
Qed.
