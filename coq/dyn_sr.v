From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_prog dyn_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_sta_step m n A :
  nil ⊢ m : A -> m ~>> n -> m ~>* n.
Proof with eauto using sta_step.
  move e:(nil)=>Γ ty. elim: ty e n=>{Γ m A}.
  all: try solve[intros;
                 match goal with
                 | [ H : _ ~>> _ |- _ ] => inv H
                 end].
  { move=>Γ A B m n s tym ihm tyn ihn e n0 st. inv st.
    { apply: sta_red_app... }
    { apply: sta_red_app... }
    { apply: star1... }
    { apply: star1... } }
  { move=>Γ A B m n s tym ihm tyn ihn e n0 st. inv st.
    { apply: sta_red_app... }
    { apply: sta_red_app... }
    { apply: star1... }
    { apply: star1... } }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn e n0 st. inv st.
    apply: sta_red_pair0... }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn e n0 st. inv st.
    { apply: sta_red_pair1... }
    { apply: sta_red_pair1... } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn e n0 st. inv st.
    { apply: sta_red_letin... }
    { apply: star1... }
    { apply: star1... } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn e n0 st. inv st.
    { apply: sta_red_letin... }
    { apply: star1... }
    { apply: star1... } }
  { move=>Γ A B m t tym ihm e n0 st. inv st.
    { apply: sta_red_fst... }
    { apply: star1... } }
  { move=>Γ A B m t tym ihm e n0 st. inv st.
    { apply: sta_red_snd... }
    { apply: star1... } }
  { move=>Γ A B H P m n s tyB ihB tyH ihH tyP ihP e n0 st. inv st.
    have[P0[rdP vlP]]:=sta_vn tyP.
    have tyP0:=sta_rd tyP rdP.
    have[n1 e]:=sta_id_canonical tyP0 (convR _ _) vlP. subst.
    apply: star_trans.
    apply: sta_red_rw...
    apply: star1... }
  { move=>Γ A B m s eq tym ihm tyB ihB e n st. subst.
    apply: ihm... }
Qed.

Lemma dyn_sta_red m n A :
  nil ⊢ m : A -> m ~>>* n -> m ~>* n.
Proof with eauto.
  move=>ty rd. elim: rd A ty=>{n}...
  move=>m' n rd ih st A tym.
  have rdm:=ih _ tym.
  have tym':=sta_rd tym rdm.
  have rdm':=dyn_sta_step tym' st.
  apply: star_trans.
  apply: rdm.
  apply: rdm'.
Qed.

Lemma dyn_has_type Γ Δ x s A :
  dyn_has Δ x s A -> dyn_wf Γ Δ -> Γ ⊢ A : Sort s.
Proof with eauto.
  move=>hs. elim: hs Γ=>{Δ x s A}.
  { move=>Δ A s k Γ wf. inv wf.
    apply: sta_eweaken...
    by asimpl. }
  { move=>Δ A B x s hs ih Γ wf. inv wf.
    have tyA:=ih _ H2. 
    apply: sta_eweaken...
    by asimpl. }
  { move=>Δ A x s hs ih Γ wf. inv wf.
    have tyA:=ih _ H0. 
    apply: sta_eweaken...
    by asimpl. }
Qed.

Lemma dyn_has_key Δ x s A : dyn_has Δ x s A -> Δ ▷ s.
Proof with eauto using key, key_impure.
  elim=>{Δ x s A}.
  { move=>Δ A [|] k... }
  { move=>Δ A B x [|] hs k... }
  { move=>Δ A x [|] hs k... }
Qed.

Lemma dyn_val_key Γ Δ m A s :
  Γ ; Δ ⊢ m : A -> Γ ⊢ A : Sort s -> dyn_val m -> Δ ▷ s.
Proof with eauto using key_impure.
  destruct s...
  move=>ty. elim: ty=>{Γ Δ m A}.
  { move=>Γ Δ x s A shs dhs wf tyA vl.
    have tyAs:=dyn_has_type wf shs.
    have e:=sta_unicity tyA tyAs. subst.
    apply: dyn_has_key... }
  { move=>Γ Δ A B m s k tym ih tyP vl.
    have[_[_/sort_inj->//]]:=sta_pi0_inv tyP. }
  { move=>Γ Δ A B m s t k tym ih tyP vl.
    have[_[_/sort_inj->//]]:=sta_pi1_inv tyP. }
  { move=>Γ Δ A B m n s tym ih tyn tyB vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn tyB vl. inv vl. }
  { move=>Γ Δ A B m n t tyS tym ihm tyn ty vl.
    have[s[r[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv ty. subst.
    inv ord. inv vl... }
  { move=>Γ Δ1 Δ2 Δ A B m n t mrg tyS tym ihm tyn ihn ty vl.
    have[s[r[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv ty. subst.
    inv ord1. inv ord2. inv vl.
    apply: key_merge...
    apply: ihn...
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn ty vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn ty vl. inv vl. }
  { move=>Γ Δ A B m n t k tym ihm tyn ihn ty vl.
    have[_[_[_[_/sort_inj e]]]]:=sta_with_inv ty. subst... }
  { move=>Γ Δ A B m t tym ihm tyA vl. inv vl. }
  { move=>Γ Δ A B m t tym ihm tyA vl. inv vl. }
  { move=>Γ Δ A B H P m n s tyB tyH ihH tyP tyB0 vl. inv vl. }
  { move=>Γ Δ A B m s eq tym ihm tyB1 tyB2 vl.
    have[r tyA]:=dyn_valid tym.
    have[C rd1 rd2]:=church_rosser eq.
    apply: ihm...
    have tyCr:=sta_rd tyA rd1.
    have tyCU:=sta_rd tyB2 rd2.
    have<-:=sta_unicity tyCr tyCU... }
Qed.

Theorem dyn_sr m n A :
  nil ; nil ⊢ m : A -> m ~>> n -> nil ; nil ⊢ n : A.
Proof with eauto using dyn_type, dyn_step, dyn_wf, merge.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2 n=>{Γ Δ m A}...
  { move=>Γ Δ x s A wf shs dhs e1 e2 n st. inv st. }
  { move=>Γ Δ A B m s k tym ihm e1 e2 n st. inv st. }
  { move=>Γ Δ A B m s t k tym ihm e1 e2 n st. inv st. }
  { move=>Γ Δ A B m n s tym ihm tyn e1 e2 n0 st. inv st.
    { have tym':=ihm erefl erefl _ H2.
      apply: dyn_app0... }
    { have tyn':=sta_rd tyn (dyn_sta_step tyn H2).
      have[t tyP]:=dyn_valid tym.
      have[r[tyB _]]:=sta_pi0_inv tyP.
      apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: dyn_sta_step...
      apply: dyn_app0...
      have:=sta_subst tyB tyn.
      asimpl... }
    { have[x tyP]:=dyn_valid tym.
      have tym0:=dyn_lam0_inv tym.
      apply: dyn_subst0... }
    { exfalso.
      apply: sta_lam1_pi0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg. inv st.
    { have tym':=ihm erefl erefl _ H2.
      apply: dyn_app1... }
    { have tyn':=ihn erefl erefl _ H2.
      have[x tyP]:=dyn_valid tym.
      have[r[tyB _]]:=sta_pi1_inv tyP.
      apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: dyn_sta_step...
      apply: dyn_app1...
      have:=sta_subst tyB (dyn_sta_type tyn).
      asimpl... }
    { exfalso.
      apply: sta_lam0_pi1_false... }
    { have[x tyP]:=dyn_valid tym.
      have[r[tyB _]]:=sta_pi1_inv tyP.
      have[t tym0]:=dyn_lam1_inv tym.
      have wf:=dyn_type_wf tym0. inv wf.
      apply: dyn_subst1...
      apply: (dyn_val_key tyn)... } }
  { move=>Γ Δ A B m n t tyS tym ihm tyn e1 e2 n0 st. inv st.
    have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
    apply: dyn_pair0...
    apply: sta_conv.
    apply: sta_conv_beta.
    apply: star_conv.
    apply: (dyn_sta_step (dyn_sta_type tym))...
    apply: tyn.
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ Δ1 Δ2 Δ A B m n t mrg tyS tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg. inv st.
    { have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS.
      apply: dyn_pair1...
      apply: dyn_conv.
      apply: sta_conv_beta.
      apply: star_conv.
      apply: (dyn_sta_step (dyn_sta_type tym))...
      apply: tyn.
      apply: sta_esubst...
      by autosubst. }
    { apply: dyn_pair1... } }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg. inv st.
    { apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: (dyn_sta_step (dyn_sta_type tym))...
      apply: dyn_letin0...
      apply: sta_esubst...
      by autosubst. }
    { inv H3.
      have[e[tym1 tym2]]:=dyn_pair0_inv tym. subst.
      have wf:=dyn_type_wf tyn. inv wf. inv H3.
      replace C.[Pair0 m1 m2 t/]
        with C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      apply: dyn_substitution...
      apply: dyn_agree_subst_wk0...
      apply: dyn_agree_subst_wk1.
      apply: dyn_val_key tym1 H7 H0.
      apply: merge_sym...
      apply: dyn_agree_subst_refl...
      by autosubst. }
    { exfalso. apply: sta_pair1_sig0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn e1 e2 n0 st.
    subst. inv mrg. inv st.
    { apply: dyn_conv.
      apply: sta_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: (dyn_sta_step (dyn_sta_type tym))...
      apply: dyn_letin1...
      apply: sta_esubst...
      by autosubst. }
    { exfalso. apply: sta_pair0_sig1_false... }
    { inv H3.
      have[Δ1'[Δ2'[mrg'[e[tym1 tym2]]]]]:=dyn_pair1_inv tym.
      have wf:=dyn_type_wf tyn. inv wf. inv H3. inv mrg'.
      have k1:=dyn_val_key tym1 H8 H1.
      have k2:=dyn_val_key tym2 (sta_subst H6 (dyn_sta_type tym1)) H4.
      replace C.[Pair1 m1 m2 t/]
        with C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
      apply: dyn_substitution...
      apply: dyn_agree_subst_wk1...
      apply: dyn_agree_subst_wk1...
      by autosubst. } }
  { move=>Γ Δ A B m n t k tym ihm tyn ihn e1 e2 n0 st. inv st. }
  { move=>Γ Δ A B m t tym ihm e1 e2 n st. inv st.
    { apply: dyn_fst... }
    { have[_[//]]:=dyn_apair_inv tym. } }
  { move=>Γ Δ A B m t tym ihm e1 e2 n st. inv st.
    { apply: dyn_snd... }
    { have[_[//]]:=dyn_apair_inv tym. } }
  { move=>Γ Δ A B H P m n s tyB tyH ihH tyP e1 e2 n0 st. inv st.
    have[P0[rdP vlP]]:=sta_vn tyP.
    have tyP0:=sta_rd tyP rdP.
    have[m0 e]:=sta_id_canonical tyP0 (convR _ _) vlP. subst.
    have[r tyI]:=sta_valid tyP.
    have[tym[tyn/sort_inj e]]:=sta_id_inv tyI. subst.
    have[tym0[eq1 eq2]]:=sta_refl_inv tyP0.
    have sc:sconv (Refl m .: m .: ids) (P .: n .: ids).
    { move=>[|[|]]//=.
      apply: conv_trans. apply: sta_conv_refl. apply: conv_sym...
      apply: conv_sym. apply: star_conv...
      apply: conv_trans. apply: conv_sym... eauto. }
    have wkB:nil ⊢ B.[P,n/] : Sort s.
    { replace (Sort s) with (Sort s).[P,n/] by eauto.
      apply: sta_substitution...
      repeat constructor...
      all: asimpl... }
    apply: dyn_conv.
    apply: sta_conv_compat sc.
    all: eauto. }
Qed.

Corollary dyn_rd m n A :
  nil ; nil ⊢ m : A -> m ~>>* n -> nil ; nil ⊢ n : A.
Proof with eauto.
  move=>ty rd. elim: rd A ty=>{n}...
  move=>n z rd ih st A tym.
  have tyn:=ih _ tym.
  apply: dyn_sr...
Qed.
