From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS ptr_step ptr_subst era_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ptr_srX H1 H2 H H' x y z z' A :
  H1 ; x ~ y ~ z : A -> wr_heap H ->
  H1 ∘ H2 => H -> H ; z ~>> H' ; z' ->
  exists H1' H2' x' y',
    H1' ; x' ~ y' ~ z' : A /\ wr_heap H' /\
    pad H2 H2' /\ H1' ∘ H2' => H' /\ x ~>>* x' /\ y ~>>* y'.
Proof with eauto 7 using pad, era_type, resolve, merge, free, key, dyn_step.
  move=>{H1 x y z A}[H1 x y z A].
  move e1:(nil)=>Γ. move e2:(nil)=>Δ er.
  elim: er H1 H2 H H' z z' e1 e2=>{Γ Δ x y A}.
  { move=>Γ Δ x s A wf shs dhs H1 H2 H H' z z' e1 e2 rs wr mrg st; subst. inv shs. }
  { move=>Γ Δ A B m m' s k erm _ H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    have[<-_]:=merge_size mrg.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    destruct s.
    { exists (Lam0 Box m0 U :U H1).
      exists (Lam0 Box m0 U :U H2).
      exists (Lam0 A m U).
      exists (Lam0 Box m' U).
      repeat split...
      { econstructor...
        constructor...
        apply: resolve_wkU... }
      { constructor...
        have//=nfm':=nf_typing erm.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } }
    { exists (Lam0 Box m0 L :L H1).
      exists (_: H2).
      exists (Lam0 A m L).
      exists (Lam0 Box m' L).
      repeat split...
      { econstructor...
        constructor...
        apply: resolve_wkN... }
      { constructor...
        have//=nfm':=nf_typing erm.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } } }
  { move=>Γ Δ A B m m' s t k erm _ H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    have[<-_]:=merge_size mrg.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    destruct s.
    { exists (Lam1 Box m0 U :U H1).
      exists (Lam1 Box m0 U :U H2).
      exists (Lam1 A m U).
      exists (Lam1 Box m' U).
      repeat split...
      { econstructor...
        constructor...
        apply: resolve_wkU... }
      { constructor...
        have//=nfm':=nf_typing erm.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } }
    { exists (Lam1 Box m0 L :L H1).
      exists (_: H2).
      exists (Lam1 A m L).
      exists (Lam1 Box m' L).
      repeat split...
      { econstructor...
        constructor...
        apply: resolve_wkN... }
      { constructor...
        have//=nfm':=nf_typing erm.
        have//:=resolve_wr_nfi H8 wr1 nfm'. } } }
  { move=>Γ Δ A B m m' n s erm ihm tyn H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    { have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=ihm _ _ _ _ _ _ erefl erefl H6 wr mrg H9.
      inv wrx.
      exists H1'. exists H2'. exists (App x' n). exists (App y' Box).
      repeat split...
      { apply: (star_hom (App^~ n)) rd1=>x y.
        apply: dyn_step_appL. }
      { apply: (star_hom (App^~ Box)) rd2=>x y.
        apply: dyn_step_appL. } }
    { inv H9. }
    { have[H1'[mrg' rs]]:=resolve_free H9 H6 mrg. inv rs.
      have[A0[n0 e]]:=era_lam0_form erm. subst.
      exists H1'. exists H2. exists (n0.[n/]). exists (m'0.[Box/]).
      repeat split...
      { have[ern0 _]:=era_lam0_inv erm.
        apply: era_esubst0... }
      { have[ern _]:=era_lam0_inv erm.
        have wr':=free_wr H9 wr.
        have[wr1 wr2]:=wr_merge_inv mrg' wr'.
        have[Hx[k mrgx]]:=split_self H1'.
        have[_ wrx]:=wr_merge_inv mrgx wr1.
        apply: resolve_subst...
        constructor.
        constructor... }
      { apply: free_wr... }
      { apply: star1... }
      { apply: star1... } }
    { have[wr1 wr2]:=wr_merge_inv mrg wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have//:=resolve_wr_box wr4 H11. }
    { have[wr1 wr2]:=wr_merge_inv mrg wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have//:=resolve_wr_box wr4 H11. }
    { have[wr1 wr2]:=wr_merge_inv mrg wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have//:=resolve_wr_box wr4 H11. }
    { have[wr1 wr2]:=wr_merge_inv mrg wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have//:=resolve_wr_box wr4 H11. } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 erm ihm ern ihn H1 H2 H H' z z' e1 e2 rs wr mrg2 st; subst.
    inv mrg1. inv rs; inv st.
    { have//:=era_box_form ern. }
    { have//:=era_box_form ern. }
    { have//:=era_box_form ern. }
    { have[wr1 wr2]:=wr_merge_inv mrg2 wr.
      have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg5[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H10 wr (merge_sym mrg4) H13.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg5) mrp.
      inv wrx.
      exists Hx. exists H2p. exists (App x' n). exists (App y' n').
      repeat split...
      { econstructor.
        apply: merge_sym...
        apply: H8.
        apply: resolve_pad... }
      { apply: (star_hom (App^~ n)) rd1=>x y.
        apply: dyn_step_appL. }
      { apply: (star_hom (App^~ n')) rd2=>x y.
        apply: dyn_step_appL. } }
    { have[H4[mrg3 mrg4]]:=merge_splitL mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg5[rd1 rd2]]]]]]]]]:=
        ihn _ _ _ _ _ _ erefl erefl H11 wr (merge_sym mrg4) H13.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg5) mrp.
      inv wrx.
      exists Hx. exists H2p. exists (App m x'). exists (App m' y').
      repeat split...
      { have[t tyP]:=dyn_valid (era_dyn_type erm).
        have[r[tyB/sort_inj e]]:=sta_pi1_inv tyP. subst.
        have tyn:=dyn_sta_type (era_dyn_type ern).
        have//=tyBn:=sta_subst tyB tyn.
        apply: era_conv.
        apply: sta_conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: dyn_sta_red...
        econstructor...
        apply: tyBn. }
      { econstructor...
        apply: resolve_pad... }
      { apply: (star_hom (App m)) rd1=>x y.
        apply: dyn_step_appR. }
      { apply: (star_hom (App m')) rd2=>x y.
        apply: dyn_step_appR. } }
    { have[Hx[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[Hy[mrg5 rs]]:=resolve_free H13 H10 (merge_sym mrg4). inv rs.
      have[A0[n1 e]]:=era_lam0_form erm. subst.
      exfalso. apply: sta_lam0_pi1_false... }
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H5[mrg rs]]:=resolve_free H13 H10 (merge_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg) mrg3.
      have[A0[n0 e]]:=era_lam1_form erm. subst.
      have[r[ern0 _]]:=era_lam1_inv erm.
      have wr':=free_wr H13 wr.
      have[wr1 wr2]:=wr_merge_inv mrg wr'.
      have[wr3 wr4]:=wr_merge_inv mrg3 wr2.
      have[H3'[k mrg']]:=split_self H3.
      have[_ wr3']:=wr_merge_inv mrg' wr3.
      have vl':=wr_resolve_ptr wr3 H11.
      have vl:=era_dyn_val ern vl'.
      exists Hx. exists H2. exists n0.[n/]. exists m'0.[n'/].
      repeat split...
      { apply: era_subst1.
        apply: key_nil.
        apply: merge_nil.
        apply: ern0.
        apply: ern. }
      { have wf:=dyn_type_wf (era_dyn_type ern0). inv wf.
        have k1:=resolution (Ptr_well_resolved ern H11) H17 vl' wr3.
        destruct r.
        { apply: resolve_subst.
          apply: ern0.
          apply: merge_sym...
          apply: H16.
          apply: wr1.
          apply: agree_resolve_wkU.
          apply: merge_sym...
          all: eauto.
          constructor... }
        { apply: resolve_subst.
          apply: ern0.
          apply: merge_sym...
          all: eauto.
          apply: agree_resolve_wkL.
          apply: merge_sym...
          all: eauto.
          constructor... } }
      { apply: star1. apply: dyn_step_beta1... }
      { apply: star1. apply: dyn_step_beta1... } } }
  { move=>Γ Δ A B m m' n t tyS erm ihm tyn H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    { have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=ihm _ _ _ _ _ _ erefl erefl H6 wr mrg H9.
      inv wrx.
      exists H1'. exists H2'. exists (Pair0 x' n t). exists (Pair0 y' Box t).
      repeat split...
      { have[s[r[ord[tyA[tyB _]]]]]:=sta_sig0_inv tyS.
        have tyx:=dyn_sta_type (dyn_rd (era_dyn_type erm) rd1).
        have//=tyBx:=sta_subst tyB tyx.
        constructor...
        apply: sta_conv.
        apply: sta_conv_beta.
        apply: star_conv.
        apply: (dyn_sta_red (dyn_sta_type (era_dyn_type erm)))...
        apply: tyn.
        apply: tyBx. }
      { apply: (star_hom ((Pair0^~ n)^~ t)) rd1=>x y.
        apply: dyn_step_pair0L. }
      { apply: (star_hom ((Pair0^~ Box)^~ t)) rd2=>x y.
        apply: dyn_step_pair0L. } }
    { have[e1 e2]:=merge_size mrg. destruct t.
      { exists (Pair0 (Ptr lm) Box U :U H1).
        exists (Pair0 (Ptr lm) Box U :U H2).
        exists (Pair0 m n U).
        exists (Pair0 m' Box U).
        repeat split...
        { econstructor.
          constructor...
          constructor.
          apply: resolve_wkU... }
        { constructor... } }
      { exists (Pair0 (Ptr lm) Box L :L H1).
        exists (_: H2).
        exists (Pair0 m n L).
        exists (Pair0 m' Box L).
        repeat split...
        { econstructor.
          constructor...
          constructor.
          apply: resolve_wkN... }
        { constructor... } } } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 tyS erm ihm ern ihn H1 H2 H H' z z' e1 e2 rs wr mrg2 st; subst.
    have[s[r[ord1[ord2[tyA[tyB _]]]]]]:=sta_sig1_inv tyS. inv mrg1. inv rs; inv st.
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H10.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H11 wr (merge_sym mrg4) H14. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg') mrp.
      exists Hx. exists H2p. exists (Pair1 x' n t). exists (Pair1 y' n' t).
      repeat split...
      { have tyx:=dyn_sta_type (dyn_rd (era_dyn_type erm) rd1).
        have//=tyBx:=sta_subst tyB tyx.
        econstructor...
        apply: era_conv.
        apply: sta_conv_beta.
        apply: star_conv.
        apply: (dyn_sta_red (dyn_sta_type (era_dyn_type erm)))...
        apply: ern.
        apply: tyBx. }
      { econstructor.
        apply: merge_sym...
        apply: H7.
        apply: resolve_pad... }
      { apply: (star_hom ((Pair1^~ n)^~ t)) rd1=>x y.
        apply: dyn_step_pair1L. }
      { apply: (star_hom ((Pair1^~ n')^~ t)) rd2=>x y.
        apply: dyn_step_pair1L. } }
    { have[H4[mrg3 mrg4]]:=merge_splitL mrg2 H10.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihn _ _ _ _ _ _ erefl erefl H12 wr (merge_sym mrg4) H14. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg') mrp.
      exists Hx. exists H2p. exists (Pair1 m x' t). exists (Pair1 m' y' t).
      repeat split...
      { econstructor...
        apply: resolve_pad... }
      { apply: (star_hom (Pair1 m^~ t)) rd1=>x y.
        apply: dyn_step_pair1R. }
      { apply: (star_hom (Pair1 m'^~ t)) rd2=>x y.
        apply: dyn_step_pair1R. } }
    { have[e1 e2]:=merge_size mrg2. destruct t.
      { exists (Pair1 (Ptr lm) (Ptr ln) U :U H1).
        exists (Pair1 (Ptr lm) (Ptr ln) U :U H2).
        exists (Pair1 m n U).
        exists (Pair1 m' n' U).
        repeat split...
        { econstructor.
          constructor...
          econstructor...
          apply: resolve_wkU...
          apply: resolve_wkU... }
        { constructor... } }
      { exists (Pair1 (Ptr lm) (Ptr ln) L :L H1).
        exists (_: H2).
        exists (Pair1 m n L).
        exists (Pair1 m' n' L).
        repeat split...
        { econstructor.
          constructor...
          econstructor...
          apply: resolve_wkN...
          apply: resolve_wkN... }
        { constructor... } } } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 tyC
      erm ihm ern _ H1 H2 H H' z z' e1 e2 rs wr mrg2 st; subst.
    inv mrg1. inv rs; inv st.
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H10 wr (merge_sym mrg4) H13. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg') mrp.
      exists Hx. exists H2p. exists (LetIn C x' n). exists (LetIn Box y' n').
      repeat split...
      { apply: era_conv.
        apply: sta_conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: dyn_sta_red...
        apply: era_letin0...
        apply: sta_esubst...
        autosubst. }
      { econstructor.
        apply: merge_sym...
        apply: H8.
        apply: resolve_pad... }
      { apply: (star_hom (LetIn C^~ n)) rd1=>x y.
        apply: dyn_step_letinL. }
      { apply: (star_hom (LetIn Box^~ n')) rd2=>x y.
        apply: dyn_step_letinL. } }
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_free H13 H10 (merge_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg') mrg3.
      have[m1[m2 e]]:=era_pair0_form erm. subst.
      have[e[_[erm1 tym2]]]:=era_pair0_inv erm. subst.
      have wr':=free_wr H13 wr.
      have[wr1 wr2]:=wr_merge_inv mrg2 wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have[wr5 wr6]:=wr_merge_inv mrg' wr'.
      have vl:=wr_resolve_ptr wr5 H15.
      have wf:=dyn_type_wf (era_dyn_type ern). inv wf.  inv H9.
      have k1:=resolution (Ptr_well_resolved erm1 H15) H17 vl wr5.
      have[H2'[k mrg2']]:=split_self H1'.
      have[_ wr7]:=wr_merge_inv mrg2' wr5.
      exists Hx. exists H2. exists n.[m2,m1/]. exists (n'.[Box,m'0/]).
      repeat split...
      { replace C.[Pair0 m1 m2 t/] with
          C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
        apply: era_substitution.
        apply: ern.
        constructor.
        econstructor.
        apply: key_nil.
        all: eauto...
        asimpl... }
      { destruct r.
        { apply: resolve_subst...
          constructor.
          econstructor.
          apply: merge_sym mrg2'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          constructor.
          econstructor.
          apply: merge_sym mrg2'.
          all: eauto.
          constructor... } }
      { apply: star1.
        constructor.
        constructor.
        apply: era_dyn_val... }
      { apply: star1.
        constructor.
        constructor... } }
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_free H13 H10 (merge_sym mrg4). inv rs.
      have[m1[m2 e]]:=era_pair1_form erm. subst.
      exfalso. apply: sta_pair1_sig0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 tyC
      erm ihm ern _ H1 H2 H H' z z' e1 e2 rs wr mrg2 st; subst.
    inv mrg1. inv rs; inv st.
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H10 wr (merge_sym mrg4) H13. inv wrx.
      have[H1p[H2p[pd1[pd2 mrp]]]]:=pad_merge pd mrg3.
      have[Hx[mrp1 mrp2]]:=merge_splitL (merge_sym mrg') mrp.
      exists Hx. exists H2p. exists (LetIn C x' n). exists (LetIn Box y' n').
      repeat split...
      { apply: era_conv.
        apply: sta_conv_beta.
        apply: conv_sym.
        apply: star_conv.
        apply: dyn_sta_red...
        apply: era_letin1...
        apply: sta_esubst...
        autosubst. }
      { econstructor.
        apply: merge_sym...
        apply: H8.
        apply: resolve_pad... }
      { apply: (star_hom (LetIn C^~ n)) rd1=>x y.
        apply: dyn_step_letinL. }
      { apply: (star_hom (LetIn Box^~ n')) rd2=>x y.
        apply: dyn_step_letinL. } }
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_free H13 H10 (merge_sym mrg4). inv rs.
      have[m1[m2 e]]:=era_pair0_form erm. subst.
      exfalso. apply: sta_pair0_sig1_false... }
    { have[H4[mrg3 mrg4]]:=merge_splitR mrg2 H7.
      have[H1'[mrg' rs]]:=resolve_free H13 H10 (merge_sym mrg4). inv rs.
      have[Hx[mrg5 mrg6]]:=merge_splitL (merge_sym mrg') mrg3.
      have[m1[m2 e]]:=era_pair1_form erm. subst.
      have[Δ1[Δ2[mrg[e[erm1 erm2]]]]]:=era_pair1_inv erm. inv mrg; subst.
      have wr':=free_wr H13 wr.
      have[wr1 wr2]:=wr_merge_inv mrg2 wr.
      have[wr3 wr4]:=wr_merge_inv H7 wr1.
      have[wr5 wr6]:=wr_merge_inv mrg' wr'.
      have[wr7 wr8]:=wr_merge_inv H16 wr5.
      have vm:=wr_resolve_ptr wr7 H18.
      have vn:=wr_resolve_ptr wr8 H19.
      have wf:=dyn_type_wf (era_dyn_type ern). inv wf.  inv H14.
      have k1:=resolution (Ptr_well_resolved erm1 H18) H21 vm wr7.
      have//=tyBm1:=sta_subst H17 (dyn_sta_type (era_dyn_type erm1)).
      have k2:=resolution (Ptr_well_resolved erm2 H19) tyBm1 vn wr8.
      have[H5'[k5 mrg5']]:=split_self H5.
      have[H6'[k6 mrg6']]:=split_self H6.
      have[_ wr5']:=wr_merge_inv mrg5' wr7.
      have[_ wr6']:=wr_merge_inv mrg6' wr8.
      exists Hx. exists H2. exists n.[m2,m1/]. exists (n'.[n'0,m'0/]).
      repeat split...
      { replace C.[Pair1 m1 m2 t/] with
          C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[m2,m1/] by autosubst.
        apply: era_substitution.
        apply: ern.
        econstructor. apply: key_nil.
        constructor.
        econstructor. apply: key_nil.
        all: eauto...
        asimpl... }
      { destruct r1; destruct r2.
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: merge_sym mrg5'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: merge_sym mrg5'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: merge_sym mrg5'.
          all: eauto.
          constructor... }
        { apply: resolve_subst...
          econstructor...
          econstructor.
          apply: merge_sym mrg5'.
          all: eauto.
          constructor... } }
      { apply: star1.
        constructor.
        constructor.
        apply: era_dyn_val...
        apply: era_dyn_val... }
      { apply: star1.
        constructor.
        constructor... } } }
  { move=>Γ Δ A B m m' n n' t _ erm ihm ern ihn H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    have[<-_]:=merge_size mrg.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    destruct t.
    { exists (APair m0 n0 U :U H1).
      exists (APair m0 n0 U :U H2).
      exists (APair m n U).
      exists (APair m' n' U).
      repeat split...
      { econstructor...
        constructor...
        apply: resolve_wkU...
        apply: resolve_wkU... }
      { have//=nfm':=nf_typing erm.
        have//=nfn':=nf_typing ern.
        constructor...
        have//:=resolve_wr_nfi H9 wr1 nfm'.
        have//:=resolve_wr_nfi H10 wr1 nfn'. } }
    { exists (APair m0 n0 L :L H1).
      exists (_: H2).
      exists (APair m n L).
      exists (APair m' n' L).
      repeat split...
      { econstructor...
        constructor...
        apply: resolve_wkN...
        apply: resolve_wkN... }
      { have//=nfm':=nf_typing erm.
        have//=nfn':=nf_typing ern.
        constructor...
        have//:=resolve_wr_nfi H9 wr1 nfm'.
        have//:=resolve_wr_nfi H10 wr1 nfn'. } } }
  { move=>Γ Δ A B m m' t erm ihm H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    { have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H6 wr mrg H5. inv wrx.
      exists H1'. exists H2'. exists (Fst x'). exists (Fst y').
      repeat split...
      { apply: (star_hom Fst) rd1=>x y.
        apply: dyn_step_fst. }
      { apply: (star_hom Fst) rd2=>x y.
        apply: dyn_step_fst. } }
    { have[H2'[mrg' rs]]:=resolve_free H5 H6 mrg. inv rs.
      have[m1[m2 e]]:=era_apair_form erm. subst.
      have[e[erm1 erm2]]:=era_apair_inv erm. subst.
      have wr':=free_wr H5 wr.
      exists H2'. exists H2. exists m1. exists m'0.
      repeat split...
      { apply: star1.
        apply: dyn_step_proj1. }
      { apply: star1.
        apply: dyn_step_proj1. } } }
  { move=>Γ Δ A B m m' t erm ihm H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    { have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
        ihm _ _ _ _ _ _ erefl erefl H6 wr mrg H5. inv wrx.
      exists H1'. exists H2'. exists (Snd x'). exists (Snd y').
      repeat split...
      { apply: (star_hom Snd) rd1=>x y.
        apply: dyn_step_snd. }
      { apply: (star_hom Snd) rd2=>x y.
        apply: dyn_step_snd. } }
    { have[H2'[mrg' rs]]:=resolve_free H5 H6 mrg. inv rs.
      have[n1[n2 e]]:=era_apair_form erm. subst.
      have[e[ern1 ern2]]:=era_apair_inv erm. subst.
      have wr':=free_wr H5 wr.
      exists H2'. exists H2. exists n2. exists n'.
      repeat split...
      { apply: star1.
        apply: dyn_step_proj2. }
      { apply: star1.
        apply: dyn_step_proj2. } } }
  { move=>Γ Δ A B x x' P m n s tyB erx ihx tyP H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    inv rs; inv st.
    exists H1. exists H2. exists x. exists x'.
    repeat split...
    { have[P0[rdP vlP]]:=sta_vn tyP.
      have tyP0:=sta_rd tyP rdP.
      have[n0 e]:=sta_id_canonical tyP0 (convR _ _) vlP. subst.
      have tyr:=sta_rd tyP rdP.
      have[r tyI]:=sta_valid tyP.
      have[tym[tyn/sort_inj e]]:=sta_id_inv tyI. subst.
      have[tym0[eq1 eq2]]:=sta_refl_inv tyr.
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
      apply: era_conv.
      apply: sta_conv_compat sc.
      all: eauto. }
    { apply: star1.
      apply: dyn_step_rwE. }
    { apply: star1.
      apply: dyn_step_rwE. } }
  { move=>Γ Δ A B m m' s eq erm ihm tyB H1 H2 H H' z z' e1 e2 rs wr mrg st; subst.
    have[H1'[H2'[x'[y'[wrx[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=
      ihm _ _ _ _ _ _ erefl erefl rs wr mrg st. inv wrx.
    exists H1'. exists H2'. exists x'. exists y'.
    repeat split... }
Qed.

Theorem ptr_sr H H' x y z z' A :
  H ; x ~ y ~ z : A -> wr_heap H ->
  H ; z ~>> H' ; z' ->
  exists x' y', H' ; x' ~ y' ~ z' : A /\ wr_heap H' /\ x ~>>* x' /\ y ~>>* y'.
Proof with eauto.
  move=>wrx wr st.
  have[H0[k mrg]]:=split_self H.
  have[H1'[H2'[x'[y'[wrx'[wr'[pd[mrg'[rd1 rd2]]]]]]]]]:=ptr_srX wrx wr mrg st.
  have k':=pad_key pd k.
  have e:=merge_pureR mrg' k'. subst.
  exists x'. exists y'...
Qed.
