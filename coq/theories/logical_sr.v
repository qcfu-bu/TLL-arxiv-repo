(* This file presents the subject reduction theorem of the logical level. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_valid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Theorem 4 (Logical Subject Reduction) *)
Theorem logical_sr Γ m n A : Γ ⊢ m : A -> m ~> n -> Γ ⊢ n : A.
Proof with eauto using logical0_type, logical0_wf, logical_step, logical_type.
  move=>/logical_logical0_type ty st. apply: logical0_logical_type.
  elim: ty n st=>{Γ m A}...
  { move=>Γ s wf n st. inv st. }
  { move=>Γ x A wf hs n st. inv st. }
  { move=>Γ A B s r t tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      apply: logical0_pi0...
      apply: logical_logical0_type.
      move/logical0_logical_type in tyB.
      move/logical0_logical_type in tyA'.
      apply: logical_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tyB. }
    { have tyB':=ihB _ H3.
      apply: logical0_pi0... } }
  { move=>Γ A B s r t tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      apply: logical0_pi1...
      apply: logical_logical0_type.
      move/logical0_logical_type in tyB.
      move/logical0_logical_type in tyA'.
      apply: logical_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tyB. }
    { have tyB':=ihB _ H3.
      apply: logical0_pi1... } }
  { move=>Γ A B m s r tyA ihA tym ihm n st. inv st.
    { have tyA':=ihA _ H3.
      move/logical0_logical_type in tym.
      move/logical0_logical_type in tyA'.
      have[t tyB]:=logical_valid tym.
      apply: logical0_conv.
      apply: conv1i...
      apply: logical0_lam0...
      apply: logical_logical0_type.
      apply: logical_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tym.
      apply: logical0_pi0... }
    { have tym':=ihm _ H3.
      apply: logical0_lam0... } }
  { move=>Γ A B m s r tyA ihA tym ihm n st. inv st.
    { have tyA':=ihA _ H3.
      move/logical0_logical_type in tym.
      move/logical0_logical_type in tyA'.
      have[t tyB]:=logical_valid tym.
      apply: logical0_conv.
      apply: conv1i...
      apply: logical0_lam1...
      apply: logical_logical0_type.
      apply: logical_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tym.
      apply: logical0_pi1... }
    { have tym':=ihm _ H3.
      apply: logical0_lam1... } }
  { move=>Γ A B m n s tym ihm tyn ihn x st. inv st.
    { have tym':=ihm _ H2... }
    { have tyn':=ihn _ H2.
      move/logical0_logical_type in tyn.
      have[_/logical_pi0_inv[r[tyB _]]]:=logical_valid (logical0_logical_type tym).
      apply: logical0_conv.
      apply: logical_conv_beta.
      apply: conv1i...
      apply: logical0_app0...
      apply: logical_logical0_type.
      apply: logical_esubst...
      by autosubst. }
    { have[x tyP]:=logical_valid (logical0_logical_type tym).
      have/logical_lam0_inv tym0:=logical0_logical_type tym.
      move/logical0_logical_type in tyn.
      apply: logical_logical0_type.
      apply: logical_esubst... }
    { exfalso. apply: logical_lam1_pi0_false.
      apply: logical0_logical_type... eauto. } }
  { move=>Γ A B m n s tym ihm tyn ihn x st. inv st.
    { have tym':=ihm _ H2... }
    { have tyn':=ihn _ H2.
      move/logical0_logical_type in tyn.
      have[_/logical_pi1_inv[r[tyB _]]]:=logical_valid (logical0_logical_type tym).
      apply: logical0_conv.
      apply: logical_conv_beta.
      apply: conv1i...
      apply: logical0_app1...
      apply: logical_logical0_type.
      apply: logical_esubst...
      by autosubst. }
    { exfalso. apply: logical_lam0_pi1_false.
      apply: logical0_logical_type... eauto. } 
    { have[x tyP]:=logical_valid (logical0_logical_type tym).
      have/logical_lam1_inv tym0:=logical0_logical_type tym.
      move/logical0_logical_type in tyn.
      apply: logical_logical0_type.
      apply: logical_esubst... } }
  { move=>Γ A B s r t ord tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      move/logical0_logical_type in tyB.
      move/logical0_logical_type in tyA'.
      apply: logical0_sig0...
      apply: logical_logical0_type.
      apply: logical_ctx_conv.
      apply: conv1i...
      apply: tyA'.
      apply: tyB. }
    { have tyB':=ihB _ H3.
      apply: logical0_sig0... } }
  { move=>Γ A B s r t ord1 ord2 tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      move/logical0_logical_type in tyB.
      move/logical0_logical_type in tyA'.
      apply: logical0_sig1.
      apply: ord1. apply: ord2.
      eauto.
      apply: logical_logical0_type.
      apply: logical_ctx_conv.
      apply: conv1i...
      apply: tyA'.
      apply: tyB. }
    { have tyB':=ihB _ H3.
      apply: logical0_sig1.
      apply: ord1. apply: ord2.
      all: eauto. } }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn x st. inv st.
    { have/logical0_logical_type tym':=ihm _ H3.
      have tyS':=logical0_logical_type tyS.
      have[s[r[ord[tyA[tyB _]]]]]:=logical_sig0_inv tyS'.
      apply: logical0_pair0...
      apply: logical0_conv.
      apply: logical_conv_beta.
      apply: conv1...
      apply: tyn.
      apply: logical_logical0_type.
      apply: logical_esubst...
      by autosubst. }
    { have tyn':=ihn _ H3.
      apply: logical0_pair0... } }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn x st. inv st.
    { have/logical0_logical_type tym':=ihm _ H3.
      have tyS':=logical0_logical_type tyS.
      have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=logical_sig1_inv tyS'.
      apply: logical0_pair1...
      apply: logical0_conv.
      apply: logical_conv_beta.
      apply: conv1...
      apply: tyn.
      apply: logical_logical0_type.
      apply: logical_esubst...
      by autosubst. }
    { have tyn':=ihn _ H3.
      apply: logical0_pair1... } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn x st. inv st.
    { have/logical0_logical_type tyA':=ihC _ H3.
      move/logical0_logical_type in tyC.
      move/logical0_logical_type in tym.
      have//=tyCm:=logical_subst tyC tym.
      have wf:=logical_type_wf tyC. inv wf.
      have[s1[r[ord[tyA[tyB/sort_inj e]]]]]:=logical_sig0_inv H2; subst.
      have wkA':((Sig0 A B t).[ren (+2)] :: B :: A :: Γ) ⊢ A'.[ren (upren (+2))] : Sort s.
      { replace (Sort s) with (Sort s).[ren (upren (+2))] by eauto.
        apply: logical_rename...
        apply: logical_agree_ren_cons...
        replace (+2) with (id >>> (+1) >>> (+1)) by autosubst.
        apply: logical_agree_ren_wk...
        apply: logical_agree_ren_wk...
        apply: logical_agree_ren_refl... }
      have tyP:(B :: A :: Γ) ⊢ Pair0 (Var 1) (Var 0) t : (Sig0 A B t).[ren (+2)].
      { apply: logical_pair0.
        { replace (Sig0 A.[ren (+2)] B.[up (ren (+2))] t)
          with (Sig0 A B t).[ren (+1)].[ren (+1)] by autosubst.
          apply: logical_eweaken...
          instantiate (1 := Sort t)=>//.
          apply: logical_eweaken... eauto. }
        { replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
          repeat constructor.
          econstructor... }
        { asimpl.
          repeat constructor.
          econstructor... } }
      have{}xA':=logical_subst wkA' tyP. asimpl in xA'.
      apply:logical0_conv.
      apply: logical_conv_subst.
      apply: conv1i...
      apply: logical0_letin0...
      apply: logical0_conv.
      apply: logical_conv_subst.
      apply: conv1...
      apply: tyn.
      apply: logical_logical0_type...
      eauto. }
    { have/logical0_logical_type tym':=ihm _ H3.
      move/logical0_logical_type in tyC.
      move/logical0_logical_type in tym.
      have//=tyCm:=logical_subst tyC tym.
      apply: logical0_conv.
      apply: logical_conv_beta.
      apply: conv1i...
      apply: logical0_letin0...
      eauto... }
    { have tyn':=ihn _ H3. apply: logical0_letin0... }
    { move/logical0_logical_type in tyn.
      move/logical0_logical_type in tym.
      have[e[tym1 tym2]]:=logical_pair0_inv tym; subst.
      apply: logical_logical0_type.
      replace C.[Pair0 m1 m2 t/]
        with C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      apply: logical_substitution...
      repeat constructor...
      by asimpl. }
    { move/logical0_logical_type in tym.
      exfalso. apply: logical_pair1_sig0_false... } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn x st. inv st.
    { have/logical0_logical_type tyA':=ihC _ H3.
      move/logical0_logical_type in tyC.
      move/logical0_logical_type in tym.
      have//=tyCm:=logical_subst tyC tym.
      have wf:=logical_type_wf tyC. inv wf.
      have[s1[r[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=logical_sig1_inv H2; subst.
      have wkA':((Sig1 A B t).[ren (+2)] :: B :: A :: Γ) ⊢ A'.[ren (upren (+2))] : Sort s.
      { replace (Sort s) with (Sort s).[ren (upren (+2))] by eauto.
        apply: logical_rename...
        apply: logical_agree_ren_cons...
        replace (+2) with (id >>> (+1) >>> (+1)) by autosubst.
        apply: logical_agree_ren_wk...
        apply: logical_agree_ren_wk...
        apply: logical_agree_ren_refl... }
      have tyP:(B :: A :: Γ) ⊢ Pair1 (Var 1) (Var 0) t : (Sig1 A B t).[ren (+2)].
      { apply: logical_pair1.
        { replace (Sig1 A.[ren (+2)] B.[up (ren (+2))] t)
          with (Sig1 A B t).[ren (+1)].[ren (+1)] by autosubst.
          apply: logical_eweaken...
          instantiate (1 := Sort t)=>//.
          apply: logical_eweaken... eauto. }
        { replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
          repeat constructor.
          econstructor... }
        { asimpl.
          repeat constructor.
          econstructor... } }
      have{}xA':=logical_subst wkA' tyP. asimpl in xA'.
      apply:logical0_conv.
      apply: logical_conv_subst.
      apply: conv1i...
      apply: logical0_letin1...
      apply: logical0_conv.
      apply: logical_conv_subst.
      apply: conv1...
      apply: tyn.
      apply: logical_logical0_type...
      eauto. }
    { have/logical0_logical_type tym':=ihm _ H3.
      move/logical0_logical_type in tyC.
      move/logical0_logical_type in tym.
      have//=tyCm:=logical_subst tyC tym.
      apply: logical0_conv.
      apply: logical_conv_beta.
      apply: conv1i...
      apply: logical0_letin1...
      eauto... }
    { have tyn':=ihn _ H3. apply: logical0_letin1... }
    { move/logical0_logical_type in tym.
      exfalso. apply: logical_pair0_sig1_false... }
    { move/logical0_logical_type in tyn.
      move/logical0_logical_type in tym.
      have[e[tym1 tym2]]:=logical_pair1_inv tym; subst.
      apply: logical_logical0_type.
      replace C.[Pair1 m1 m2 t/]
        with C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      apply: logical_substitution...
      repeat constructor...
      by asimpl. } }
  { move=>Γ A B s r t tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3. apply: logical0_with... }
    { have tyB':=ihB _ H3. apply: logical0_with... } }
  { move=>Γ A B m n t tym ihm tyn ihn n0 st. inv st.
    { have tym':=ihm _ H3. apply: logical0_apair... }
    { have tyn':=ihn _ H3. apply: logical0_apair... } }
  { move=>Γ A B m t tym ihm n st. inv st.
    { have tym':=ihm _ H0. apply: logical0_fst... }
    { move/logical0_logical_type in tym.
      have[_[tyn _]]:=logical_apair_inv tym... } }
  { move=>Γ A B m t tym ihm n st. inv st.
    { have tym':=ihm _ H0. apply: logical0_snd... }
    { move/logical0_logical_type in tym.
      have[_[_ tyn]]:=logical_apair_inv tym... } }
  { move=>Γ A m n s tyA ihA tym ihm tyn ihn n0 st. inv st.
    { have tyA':=ihA _ H3.
      apply: logical0_id...
      apply: logical0_conv.
      apply: conv1...
      all: eauto.
      apply: logical0_conv.
      apply: conv1...
      all: eauto. }
    { have tym':=ihm _ H3. apply: logical0_id... }
    { have tyn':=ihn _ H3. apply: logical0_id... } }
  { move=>Γ A m tym ihm n st. inv st.
    move/logical0_logical_type in tym.
    have[s tyA]:=logical_valid tym.
    have tym':=ihm _ H0.
    apply: logical0_conv.
    apply: logical_conv_id.
    eauto.
    apply: conv1i...
    apply: conv1i...
    apply: logical0_refl...
    apply: logical0_id... }
  { move=>Γ A B H P m n s tyB ihB tyH ihH tyP ihP n0 st. inv st.
    { have/logical0_logical_type tyA':=ihB _ H5.
      move/logical0_logical_type in tyB.
      move/logical0_logical_type in tyH.
      move/logical0_logical_type in tyP.
      have[r tyI]:=logical_valid tyP.
      have[tym[tyn/sort_inj e]]:=logical_id_inv tyI; subst.
      have wkA':Γ ⊢ A'.[Refl m,m/] : Sort s.
      { replace (Sort s) with (Sort s).[Refl m,m/] by eauto.
        apply: logical_substitution...
        repeat constructor...
        all: asimpl...  }
      have wkB:Γ ⊢ B.[P,n/] : Sort s.
      { replace (Sort s) with (Sort s).[P,n/] by eauto.
        apply: logical_substitution...
        repeat constructor...
        all: asimpl... }
      apply: logical0_conv.
      apply: logical_conv_subst.
      apply: conv1i...
      apply: logical0_rw...
      apply: logical0_conv.
      apply: logical_conv_subst.
      apply: conv1...
      all: eauto. }
    { have tyH':=ihH _ H5. apply: logical0_rw... }
    { have/logical0_logical_type tyP':=ihP _ H5.
      move/logical0_logical_type in tyB.
      move/logical0_logical_type in tyH.
      move/logical0_logical_type in tyP.
      have[r tyI]:=logical_valid tyP.
      have[tym[tyn/sort_inj e]]:=logical_id_inv tyI; subst.
      have sc:sconv (P' .: n .: ids) (P .: n .: ids).
      { move=>[|]//=. apply: conv1i... }
      have wkB:Γ ⊢ B.[P,n/] : Sort s.
      { replace (Sort s) with (Sort s).[P,n/] by eauto.
        apply: logical_substitution...
        repeat constructor...
        all: asimpl... }
      apply: logical0_conv.
      apply: logical_conv_compat sc.
      apply: logical0_rw...
      eauto. }
    { move/logical0_logical_type in tyB.
      move/logical0_logical_type in tyH.
      move/logical0_logical_type in tyP.
      have[tym0[eq1 eq2]]:=logical_refl_inv tyP.
      have[r tyI]:=logical_valid tyP.
      have[tym[tyn/sort_inj e]]:=logical_id_inv tyI; subst.
      have sc:sconv (Refl m .: m .: ids) (Refl m0 .: n .: ids).
      { move=>[|[|]]//=.
        apply: logical_conv_refl. apply: conv_sym...
        apply: conv_trans. apply: conv_sym... eauto. }
      have wkB:Γ ⊢ B.[Refl m0,n/] : Sort s.
      { replace (Sort s) with (Sort s).[Refl m0,n/] by eauto.
        apply: logical_substitution...
        repeat constructor...
        all: asimpl... }
      apply: logical0_conv.
      apply: logical_conv_compat sc.
      all: eauto. } }
Qed.

(* Iterated steps preserve logical typing. *)
Corollary logical_rd Γ m n A :
  Γ ⊢ m : A -> m ~>* n -> Γ ⊢ n : A.
Proof with eauto.
  move=>ty rd. elim: rd Γ A ty=>{n}...
  move=>n z rd ih st Γ A tym.
  have tyn:=ih _ _ tym.
  apply: logical_sr...
Qed.
