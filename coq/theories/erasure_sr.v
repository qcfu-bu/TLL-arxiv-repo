(* This file presents the erasure subject reduction theorem. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS program_prog erasure_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The preimage of values under erasure are values. *)
Lemma erasure_program_val Γ Δ m m' A :
  Γ ; Δ ⊢ m ~ m' : A -> program_val m' -> program_val m.
Proof with eauto using program_val.
  move=>ty. elim: ty=>{Γ Δ m m' A}...
  { move=>Γ Δ A B m m' n s tym ihm tyn vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg tym ihm tyn ihn vl. inv vl. }
  { move=>Γ Δ A B m m' n t tyS tym ihm tyn vl. inv vl... }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg tyS tym ihm tyn ihn vl. inv vl... }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg tyC tym ihm tyn ihn vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg tyC tym ihm tyn ihn vl. inv vl. }
  { move=>Γ Δ A B m m' t tym ihm vl. inv vl. }
  { move=>Γ Δ A B m m' t tym ihm vl. inv vl. }
  { move=>Γ Δ A B H H' P m n s tyB tyH ihH tyP vl. inv vl. }
Qed.

(* Theorem 11 (Erasure Subject Reduction)  *)
Theorem erasure_sr m m' n' A :
  nil ; nil ⊢ m ~ m' : A -> m' ~>> n' ->
  exists2 n, m ~>> n & nil ; nil ⊢ n ~ n' : A.
Proof with eauto using program_step, erasure_type, program_val, merge.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ er. elim: er e1 e2 n'=>{Γ Δ m m' A}.
  { move=>Γ Δ x s A wf shs dhs e1 e2 n' st. inv st. }
  { move=>Γ Δ A B m m' s k erm ihm e1 e2 n' st. inv st. }
  { move=>Γ Δ A B m m' s t k erm ihm e1 e2 n' st. inv st. }
  { move=>Γ Δ A B m m' n s erm ihm tyn e1 e2 n' st. inv st.
    { have[x st tyx]:=ihm erefl erefl _ H2. exists (App x n)... }
    { inv H2. }
    { have[A'[m' e]]:=erasure_lam0_form erm.
      subst. exists (m'.[n/])...
      apply: erasure_subst0...
      have[//]:=erasure_lam0_inv erm. }
    { have[A'[m' e]]:=erasure_lam1_form erm. subst.
      have/program_logical_reflect ty:=erasure_program_reflect erm.
      exfalso. apply: logical_lam1_pi0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn e1 e2 x st.
    subst. inv mrg. inv st.
    { have[x st tyx]:=ihm erefl erefl _ H2. exists (App x n)... }
    { have[x st tyx]:=ihn erefl erefl _ H2. exists (App m x)...
      have tym:=erasure_program_reflect erm.
      have/program_logical_reflect tyn:=erasure_program_reflect ern.
      have[_/logical_pi1_inv[r[tyB _]]]:=program_valid tym.
      apply: erasure_conv.
      apply: logical_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: program_logical_step...
      apply: erasure_app1...
      have:=logical_subst tyB tyn.
      asimpl... }
    { have[A'[m' e]]:=erasure_lam0_form erm. subst.
      have/program_logical_reflect ty:=erasure_program_reflect erm.
      exfalso. apply: logical_lam0_pi1_false... }
    { have[A'[m' e]]:=erasure_lam1_form erm.
      subst. exists (m'.[n/])...
      apply: program_step_beta1.
      apply: erasure_program_val...
      have{erm}[t[erm _]]:=erasure_lam1_inv erm.
      have wf:=program_type_wf (erasure_program_reflect erm). inv wf.
      apply: erasure_subst1...
      apply: program_val_stability.
      apply: (erasure_program_reflect ern)...
      exact: H5.
      apply: erasure_program_val... } }
  { move=>Γ Δ A B m m' n t tyS erm ihm tyn e1 e2 x st. inv st.
    have[s[r[ord[tyA[tyB _]]]]]:=logical_sig0_inv tyS.
    have[x st erx]:=ihm erefl erefl _ H3. exists (Pair0 x n t)...
    apply: erasure_pair0...
    apply: logical_conv.
    apply: logical_conv_beta.
    apply: star_conv.
    apply: (program_logical_step (program_logical_reflect (erasure_program_reflect erm)))...
    apply: tyn.
    apply: logical_esubst...
    by autosubst. }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg tyS erm ihm ern ihn e1 e2 x st.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=logical_sig1_inv tyS.
    subst. inv mrg. inv st.
    { have[x st erx]:=ihm erefl erefl _ H3. exists (Pair1 x n t)...
      apply: erasure_pair1...
      apply: erasure_conv.
      apply: logical_conv_beta.
      apply: star_conv.
      apply: (program_logical_step (program_logical_reflect (erasure_program_reflect erm)))...
      apply: ern.
      apply: logical_esubst...
      by autosubst. }
    { have[x st erx]:=ihn erefl erefl _ H3. exists (Pair1 m x t)... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg tyC erm ihm ern ihn e1 e2 x st.
    subst. inv mrg. inv st.
    { have[x st erx]:=ihm erefl erefl _ H3. exists (LetIn C x n)...
      apply: erasure_conv.
      apply: logical_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: (program_logical_step (program_logical_reflect (erasure_program_reflect erm)))...
      apply: erasure_letin0...
      apply: logical_esubst...
      by autosubst. }
    { have[m3[m4 e]]:=erasure_pair0_form erm. subst.
      have wf:=program_type_wf (erasure_program_reflect ern). inv wf. inv H2.
      have[e1[e2[erm3 tym4]]]:=erasure_pair0_inv erm. subst.
      have vl:program_val (Pair0 m3 m4 t) by (apply: erasure_program_val; eauto).
      exists (n.[m4,m3/])...
      replace C.[Pair0 m3 m4 t/]
        with C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m4,m3/] by autosubst.
      apply: erasure_substitution...
      apply: erasure_agree_subst_wk0...
      apply: erasure_agree_subst_wk1.
      apply: (program_val_stability (erasure_program_reflect erm3) H7).
      inv vl...
      apply: merge_sym...
      apply: erasure_agree_subst_refl...
      by autosubst. }
    { have[m3[m4 e]]:=erasure_pair1_form erm. subst.
      have/program_logical_reflect ty:=erasure_program_reflect erm.
      exfalso. apply: logical_pair1_sig0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg tyC erm ihm ern ihn e1 e2 x st.
    subst. inv mrg. inv st.
    { have[x st erx]:=ihm erefl erefl _ H3. exists (LetIn C x n)...
      apply: erasure_conv.
      apply: logical_conv_beta.
      apply: conv_sym.
      apply: star_conv.
      apply: (program_logical_step (program_logical_reflect (erasure_program_reflect erm)))...
      apply: erasure_letin1...
      apply: logical_esubst...
      by autosubst. }
    { have[m3[m4 e]]:=erasure_pair0_form erm. subst.
      have/program_logical_reflect ty:=erasure_program_reflect erm.
      exfalso. apply: logical_pair0_sig1_false... }
    { have[m3[m4 e]]:=erasure_pair1_form erm. subst.
      have wf:=program_type_wf (erasure_program_reflect ern). inv wf. inv H2.
      have[Δ1'[Δ2'[mrg'[e[erm3 erm4]]]]]:=erasure_pair1_inv erm.
      subst. inv mrg'.
      have tym3:=erasure_program_reflect erm3.
      have tym4:=erasure_program_reflect erm4.
      have vl:program_val (Pair1 m3 m4 t) by (apply: erasure_program_val; eauto). inv vl.
      have k1:=program_val_stability tym3 H7 H1.
      have k2:=program_val_stability tym4 (logical_subst H5 (program_logical_reflect tym3)) H6.
      exists (n.[m4,m3/])...
      replace C.[Pair1 m3 m4 t/]
        with C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m4,m3/] by autosubst.
      apply: erasure_substitution...
      apply: erasure_agree_subst_wk1...
      apply: erasure_agree_subst_wk1...
      by autosubst. } }
  { move=>Γ Δ A B m m' n n' t k erm ihm tyn ihn e1 e2 x st. inv st. }
  { move=>Γ Δ A B m m' t tym ihm e1 e2 x st. inv st.
    { have[x st erx]:=ihm erefl erefl _ H0. exists (Fst x)... }
    { have[m1[m2 e]]:=erasure_apair_form tym. subst.
      have[e[erm1 erm2]]:=erasure_apair_inv tym.
      subst. exists m1... } }
  { move=>Γ Δ A B m m' t tym ihm e1 e2 x st. inv st.
    { have[x st erx]:=ihm erefl erefl _ H0. exists (Snd x)... }
    { have[m1[m2 e]]:=erasure_apair_form tym. subst.
      have[e[erm1 erm2]]:=erasure_apair_inv tym.
      subst. exists m2... } }
  { move=>Γ Δ A B H H' P m n s tyB erH ihH tyP e1 e2 x st. inv st.
    have[P0[rdP vlP]]:=logical_vn tyP.
    have tyP0:=logical_rd tyP rdP.
    have[n0 e]:=logical_id_canonical tyP0 (convR _ _) vlP. subst.
    have tyr:=logical_rd tyP rdP.
    have[r tyI]:=logical_valid tyP.
    have[tym[tyn/sort_inj e]]:=logical_id_inv tyI. subst.
    have[tym0[eq1 eq2]]:=logical_refl_inv tyr.
    have sc:sconv (Refl m .: m .: ids) (P .: n .: ids).
    { move=>[|[|]]//=.
      apply: conv_trans. apply: logical_conv_refl. apply: conv_sym...
      apply: conv_sym. apply: star_conv...
      apply: conv_trans. apply: conv_sym... eauto. }
    have wkB:nil ⊢ B.[P,n/] : Sort s.
    { replace (Sort s) with (Sort s).[P,n/] by eauto.
      apply: logical_substitution...
      repeat constructor...
      all: asimpl... }
    exists H...
    apply: erasure_conv.
    apply: logical_conv_compat sc.
    all: eauto. }
  { move=>Γ Δ A B m m' s eq tym ihm tyB e1 e2 n' st. subst.
    have[n st' tyn]:=ihm erefl erefl _ st.
    exists n... }
Qed.

(* Iterated steps preserve the erasure relation. *)
Corollary erasure_rd m m' n' A :
  nil ; nil ⊢ m ~ m' : A -> m' ~>>* n' ->
  exists2 n, m ~>>* n & nil ; nil ⊢ n ~ n' : A.
Proof with eauto.
  move=>ty rd. elim: rd m A ty=>{n'}...
  move=>n n' rd ih st m A tym.
  have[x rdx tyx]:=ih _ _ tym.
  have[y sty tyy]:=erasure_sr tyx st.
  exists y...
  apply: star_trans...
  apply: star1...
Qed.
