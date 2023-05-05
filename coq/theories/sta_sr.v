From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_valid.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Theorem sta_sr Γ m n A : Γ ⊢ m : A -> m ~> n -> Γ ⊢ n : A.
Proof with eauto using sta0_type, sta0_wf, sta_step, sta_type.
  move=>/sta_sta0_type ty st. apply: sta0_sta_type.
  elim: ty n st=>{Γ m A}...
  { move=>Γ s wf n st. inv st. }
  { move=>Γ x A wf hs n st. inv st. }
  { move=>Γ A B s r t tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      apply: sta0_pi0...
      apply: sta_sta0_type.
      move/sta0_sta_type in tyB.
      move/sta0_sta_type in tyA'.
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tyB. }
    { have tyB':=ihB _ H3.
      apply: sta0_pi0... } }
  { move=>Γ A B s r t tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      apply: sta0_pi1...
      apply: sta_sta0_type.
      move/sta0_sta_type in tyB.
      move/sta0_sta_type in tyA'.
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tyB. }
    { have tyB':=ihB _ H3.
      apply: sta0_pi1... } }
  { move=>Γ A B m s r tyA ihA tym ihm n st. inv st.
    { have tyA':=ihA _ H3.
      move/sta0_sta_type in tym.
      move/sta0_sta_type in tyA'.
      have[t tyB]:=sta_valid tym.
      apply: sta0_conv.
      apply: conv1i...
      apply: sta0_lam0...
      apply: sta_sta0_type.
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tym.
      apply: sta0_pi0... }
    { have tym':=ihm _ H3.
      apply: sta0_lam0... } }
  { move=>Γ A B m s r tyA ihA tym ihm n st. inv st.
    { have tyA':=ihA _ H3.
      move/sta0_sta_type in tym.
      move/sta0_sta_type in tyA'.
      have[t tyB]:=sta_valid tym.
      apply: sta0_conv.
      apply: conv1i...
      apply: sta0_lam1...
      apply: sta_sta0_type.
      apply: sta_ctx_conv.
      apply: conv1i...
      exact: tyA'.
      exact: tym.
      apply: sta0_pi1... }
    { have tym':=ihm _ H3.
      apply: sta0_lam1... } }
  { move=>Γ A B m n s tym ihm tyn ihn x st. inv st.
    { have tym':=ihm _ H2... }
    { have tyn':=ihn _ H2.
      move/sta0_sta_type in tyn.
      have[_/sta_pi0_inv[r[tyB _]]]:=sta_valid (sta0_sta_type tym).
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta0_app0...
      apply: sta_sta0_type.
      apply: sta_esubst...
      by autosubst. }
    { have[x tyP]:=sta_valid (sta0_sta_type tym).
      have/sta_lam0_inv tym0:=sta0_sta_type tym.
      move/sta0_sta_type in tyn.
      apply: sta_sta0_type.
      apply: sta_esubst... }
    { exfalso. apply: sta_lam1_pi0_false.
      apply: sta0_sta_type... eauto. } }
  { move=>Γ A B m n s tym ihm tyn ihn x st. inv st.
    { have tym':=ihm _ H2... }
    { have tyn':=ihn _ H2.
      move/sta0_sta_type in tyn.
      have[_/sta_pi1_inv[r[tyB _]]]:=sta_valid (sta0_sta_type tym).
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta0_app1...
      apply: sta_sta0_type.
      apply: sta_esubst...
      by autosubst. }
    { exfalso. apply: sta_lam0_pi1_false.
      apply: sta0_sta_type... eauto. } 
    { have[x tyP]:=sta_valid (sta0_sta_type tym).
      have/sta_lam1_inv tym0:=sta0_sta_type tym.
      move/sta0_sta_type in tyn.
      apply: sta_sta0_type.
      apply: sta_esubst... } }
  { move=>Γ A B s r t ord tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      move/sta0_sta_type in tyB.
      move/sta0_sta_type in tyA'.
      apply: sta0_sig0...
      apply: sta_sta0_type.
      apply: sta_ctx_conv.
      apply: conv1i...
      apply: tyA'.
      apply: tyB. }
    { have tyB':=ihB _ H3.
      apply: sta0_sig0... } }
  { move=>Γ A B s r t ord1 ord2 tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3.
      move/sta0_sta_type in tyB.
      move/sta0_sta_type in tyA'.
      apply: sta0_sig1.
      apply: ord1. apply: ord2.
      eauto.
      apply: sta_sta0_type.
      apply: sta_ctx_conv.
      apply: conv1i...
      apply: tyA'.
      apply: tyB. }
    { have tyB':=ihB _ H3.
      apply: sta0_sig1.
      apply: ord1. apply: ord2.
      all: eauto. } }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn x st. inv st.
    { have/sta0_sta_type tym':=ihm _ H3.
      have tyS':=sta0_sta_type tyS.
      have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS'.
      apply: sta0_pair0...
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1...
      apply: tyn.
      apply: sta_sta0_type.
      apply: sta_esubst...
      by autosubst. }
    { have tyn':=ihn _ H3.
      apply: sta0_pair0... } }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn x st. inv st.
    { have/sta0_sta_type tym':=ihm _ H3.
      have tyS':=sta0_sta_type tyS.
      have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS'.
      apply: sta0_pair1...
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1...
      apply: tyn.
      apply: sta_sta0_type.
      apply: sta_esubst...
      by autosubst. }
    { have tyn':=ihn _ H3.
      apply: sta0_pair1... } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn x st. inv st.
    { have/sta0_sta_type tyA':=ihC _ H3.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tym.
      have//=tyCm:=sta_subst tyC tym.
      have wf:=sta_type_wf tyC. inv wf.
      have[s1[r[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv H2; subst.
      have wkA':((Sig0 A B t).[ren (+2)] :: B :: A :: Γ) ⊢ A'.[ren (upren (+2))] : Sort s.
      { replace (Sort s) with (Sort s).[ren (upren (+2))] by eauto.
        apply: sta_rename...
        apply: sta_agree_ren_cons...
        replace (+2) with (id >>> (+1) >>> (+1)) by autosubst.
        apply: sta_agree_ren_wk...
        apply: sta_agree_ren_wk...
        apply: sta_agree_ren_refl... }
      have tyP:(B :: A :: Γ) ⊢ Pair0 (Var 1) (Var 0) t : (Sig0 A B t).[ren (+2)].
      { apply: sta_pair0.
        { replace (Sig0 A.[ren (+2)] B.[up (ren (+2))] t)
          with (Sig0 A B t).[ren (+1)].[ren (+1)] by autosubst.
          apply: sta_eweaken...
          instantiate (1 := Sort t)=>//.
          apply: sta_eweaken... eauto. }
        { replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
          repeat constructor.
          econstructor... }
        { asimpl.
          repeat constructor.
          econstructor... } }
      have{}xA':=sta_subst wkA' tyP. asimpl in xA'.
      apply:sta0_conv.
      apply: sta_conv_subst.
      apply: conv1i...
      apply: sta0_letin0...
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1...
      apply: tyn.
      apply: sta_sta0_type...
      eauto. }
    { have/sta0_sta_type tym':=ihm _ H3.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tym.
      have//=tyCm:=sta_subst tyC tym.
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta0_letin0...
      eauto... }
    { have tyn':=ihn _ H3. apply: sta0_letin0... }
    { move/sta0_sta_type in tyn.
      move/sta0_sta_type in tym.
      have[e[tym1 tym2]]:=sta_pair0_inv tym; subst.
      apply: sta_sta0_type.
      replace C.[Pair0 m1 m2 t/]
        with C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      apply: sta_substitution...
      repeat constructor...
      by asimpl. }
    { move/sta0_sta_type in tym.
      exfalso. apply: sta_pair1_sig0_false... } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn x st. inv st.
    { have/sta0_sta_type tyA':=ihC _ H3.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tym.
      have//=tyCm:=sta_subst tyC tym.
      have wf:=sta_type_wf tyC. inv wf.
      have[s1[r[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv H2; subst.
      have wkA':((Sig1 A B t).[ren (+2)] :: B :: A :: Γ) ⊢ A'.[ren (upren (+2))] : Sort s.
      { replace (Sort s) with (Sort s).[ren (upren (+2))] by eauto.
        apply: sta_rename...
        apply: sta_agree_ren_cons...
        replace (+2) with (id >>> (+1) >>> (+1)) by autosubst.
        apply: sta_agree_ren_wk...
        apply: sta_agree_ren_wk...
        apply: sta_agree_ren_refl... }
      have tyP:(B :: A :: Γ) ⊢ Pair1 (Var 1) (Var 0) t : (Sig1 A B t).[ren (+2)].
      { apply: sta_pair1.
        { replace (Sig1 A.[ren (+2)] B.[up (ren (+2))] t)
          with (Sig1 A B t).[ren (+1)].[ren (+1)] by autosubst.
          apply: sta_eweaken...
          instantiate (1 := Sort t)=>//.
          apply: sta_eweaken... eauto. }
        { replace A.[ren (+2)] with A.[ren (+1)].[ren (+1)] by autosubst.
          repeat constructor.
          econstructor... }
        { asimpl.
          repeat constructor.
          econstructor... } }
      have{}xA':=sta_subst wkA' tyP. asimpl in xA'.
      apply:sta0_conv.
      apply: sta_conv_subst.
      apply: conv1i...
      apply: sta0_letin1...
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1...
      apply: tyn.
      apply: sta_sta0_type...
      eauto. }
    { have/sta0_sta_type tym':=ihm _ H3.
      move/sta0_sta_type in tyC.
      move/sta0_sta_type in tym.
      have//=tyCm:=sta_subst tyC tym.
      apply: sta0_conv.
      apply: sta_conv_beta.
      apply: conv1i...
      apply: sta0_letin1...
      eauto... }
    { have tyn':=ihn _ H3. apply: sta0_letin1... }
    { move/sta0_sta_type in tym.
      exfalso. apply: sta_pair0_sig1_false... }
    { move/sta0_sta_type in tyn.
      move/sta0_sta_type in tym.
      have[e[tym1 tym2]]:=sta_pair1_inv tym; subst.
      apply: sta_sta0_type.
      replace C.[Pair1 m1 m2 t/]
        with C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      apply: sta_substitution...
      repeat constructor...
      by asimpl. } }
  { move=>Γ A B s r t tyA ihA tyB ihB n st. inv st.
    { have tyA':=ihA _ H3. apply: sta0_with... }
    { have tyB':=ihB _ H3. apply: sta0_with... } }
  { move=>Γ A B m n t tym ihm tyn ihn n0 st. inv st.
    { have tym':=ihm _ H3. apply: sta0_apair... }
    { have tyn':=ihn _ H3. apply: sta0_apair... } }
  { move=>Γ A B m t tym ihm n st. inv st.
    { have tym':=ihm _ H0. apply: sta0_fst... }
    { move/sta0_sta_type in tym.
      have[_[tyn _]]:=sta_apair_inv tym... } }
  { move=>Γ A B m t tym ihm n st. inv st.
    { have tym':=ihm _ H0. apply: sta0_snd... }
    { move/sta0_sta_type in tym.
      have[_[_ tyn]]:=sta_apair_inv tym... } }
  { move=>Γ A m n s tyA ihA tym ihm tyn ihn n0 st. inv st.
    { have tyA':=ihA _ H3.
      apply: sta0_id...
      apply: sta0_conv.
      apply: conv1...
      all: eauto.
      apply: sta0_conv.
      apply: conv1...
      all: eauto. }
    { have tym':=ihm _ H3. apply: sta0_id... }
    { have tyn':=ihn _ H3. apply: sta0_id... } }
  { move=>Γ A m tym ihm n st. inv st.
    move/sta0_sta_type in tym.
    have[s tyA]:=sta_valid tym.
    have tym':=ihm _ H0.
    apply: sta0_conv.
    apply: sta_conv_id.
    eauto.
    apply: conv1i...
    apply: conv1i...
    apply: sta0_refl...
    apply: sta0_id... }
  { move=>Γ A B H P m n s tyB ihB tyH ihH tyP ihP n0 st. inv st.
    { have/sta0_sta_type tyA':=ihB _ H5.
      move/sta0_sta_type in tyB.
      move/sta0_sta_type in tyH.
      move/sta0_sta_type in tyP.
      have[r tyI]:=sta_valid tyP.
      have[tym[tyn/sort_inj e]]:=sta_id_inv tyI; subst.
      have wkA':Γ ⊢ A'.[Refl m,m/] : Sort s.
      { replace (Sort s) with (Sort s).[Refl m,m/] by eauto.
        apply: sta_substitution...
        repeat constructor...
        all: asimpl...  }
      have wkB:Γ ⊢ B.[P,n/] : Sort s.
      { replace (Sort s) with (Sort s).[P,n/] by eauto.
        apply: sta_substitution...
        repeat constructor...
        all: asimpl... }
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1i...
      apply: sta0_rw...
      apply: sta0_conv.
      apply: sta_conv_subst.
      apply: conv1...
      all: eauto. }
    { have tyH':=ihH _ H5. apply: sta0_rw... }
    { have/sta0_sta_type tyP':=ihP _ H5.
      move/sta0_sta_type in tyB.
      move/sta0_sta_type in tyH.
      move/sta0_sta_type in tyP.
      have[r tyI]:=sta_valid tyP.
      have[tym[tyn/sort_inj e]]:=sta_id_inv tyI; subst.
      have sc:sconv (P' .: n .: ids) (P .: n .: ids).
      { move=>[|]//=. apply: conv1i... }
      have wkB:Γ ⊢ B.[P,n/] : Sort s.
      { replace (Sort s) with (Sort s).[P,n/] by eauto.
        apply: sta_substitution...
        repeat constructor...
        all: asimpl... }
      apply: sta0_conv.
      apply: sta_conv_compat sc.
      apply: sta0_rw...
      eauto. }
    { move/sta0_sta_type in tyB.
      move/sta0_sta_type in tyH.
      move/sta0_sta_type in tyP.
      have[tym0[eq1 eq2]]:=sta_refl_inv tyP.
      have[r tyI]:=sta_valid tyP.
      have[tym[tyn/sort_inj e]]:=sta_id_inv tyI; subst.
      have sc:sconv (Refl m .: m .: ids) (Refl m0 .: n .: ids).
      { move=>[|[|]]//=.
        apply: sta_conv_refl. apply: conv_sym...
        apply: conv_trans. apply: conv_sym... eauto. }
      have wkB:Γ ⊢ B.[Refl m0,n/] : Sort s.
      { replace (Sort s) with (Sort s).[Refl m0,n/] by eauto.
        apply: sta_substitution...
        repeat constructor...
        all: asimpl... }
      apply: sta0_conv.
      apply: sta_conv_compat sc.
      all: eauto. } }
Qed.

Corollary sta_rd Γ m n A :
  Γ ⊢ m : A -> m ~>* n -> Γ ⊢ n : A.
Proof with eauto.
  move=>ty rd. elim: rd Γ A ty=>{n}...
  move=>n z rd ih st Γ A tym.
  have tyn:=ih _ _ tym.
  apply: sta_sr...
Qed.
