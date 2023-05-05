From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS ptr_step ptr_sr era_prog.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma ptr_step_merge H1 H1' H2 H m n :
  H1 ; m ~>> H1' ; n -> H1 ∘ H2 => H -> exists H' n', H ; m ~>> H' ; n'.
Proof with eauto using ptr_step, pad, merge.
  move=>st. elim: st H2 H=>{H1 H1' m n}.
  { move=>H m [|] l e H2 H0 mrg; subst.
    { exists (Lam0 Box m U :U H0).
      exists (Ptr (size H0)).
      repeat split... }
    { exists (Lam0 Box m L :L H0).
      exists (Ptr (size H0)).
      repeat split... } }
  { move=>H m [|] l e H2 H0 mrg; subst.
    { exists (Lam1 Box m U :U H0).
      exists (Ptr (size H0)).
      repeat split... }
    { exists (Lam1 Box m L :L H0).
      exists (Ptr (size H0)).
      repeat split... } }
  { move=>H H' m m' n st ihm H2 H0 mrg.
    have[H0'[mx st']]:=ihm _ _ mrg.
    exists H0'. exists (App mx n)... }
  { move=>H H' m n n' st ihn H2 H0 mrg.
    have[H0'[nx st']]:=ihn _ _ mrg.
    exists H0'. exists (App m nx)... }
  { move=>H H' l m n s fr H2 H0 mrg.
    have[H4[fr' mrg']]:=free_merge fr mrg.
    exists H4. exists (m.[Box/])... }
  { move=>H H' lf la m s fr H2 H0 mrg.
    have[H4[fr' mrg']]:=free_merge fr mrg.
    exists H4. exists (m.[Ptr la/])... }
  { move=>H H' m m' t st ihm H2 H0 mrg.
    have[H1'[mx st']]:=ihm _ _ mrg.
    exists H1'. exists (Pair0 mx Box t)... }
  { move=>H l lm t e H2 H0 mrg; subst.
    destruct t.
    { exists (Pair0 (Ptr lm) Box U :{U} H0).
      exists (Ptr (size H0)).
      repeat split... }
    { exists (Pair0 (Ptr lm) Box L :{L} H0).
      exists (Ptr (size H0)).
      repeat split... } }
  { move=>H H' m m' n t st ihm H2 H0 mrg.
    have[H1'[mx st']]:=ihm _ _ mrg.
    exists H1'. exists (Pair1 mx n t)... }
  { move=>H H' m n n' t st ihn H2 H0 mrg.
    have[H1'[nx st']]:=ihn _ _ mrg.
    exists H1'. exists (Pair1 m nx t)... }
  { move=>H l lm ln t e H2 H0 mrg; subst.
    destruct t.
    { exists (Pair1 (Ptr lm) (Ptr ln) U :{U} H0).
      exists (Ptr (size H0)).
      repeat split... }
    { exists (Pair1 (Ptr lm) (Ptr ln) L :{L} H0).
      exists (Ptr (size H0)).
      repeat split... } }
  { move=>H H' m m' n st ihm H2 H0 mrg.
    have[H1'[mx st']]:=ihm _ _ mrg.
    exists H1'. exists (LetIn Box mx n)... }
  { move=>H H' lm x l n t fr H2 H0 mrg.
    have[H4[fr' mrg']]:=free_merge fr mrg.
    exists H4. exists n.[Box,Ptr lm/]... }
  { move=>H H' lm ln l n t fr H2 H0 mrg.
    have[H4[fr' mrg']]:=free_merge fr mrg.
    exists H4. exists n.[Ptr ln,Ptr lm/]... }
  { move=>H m n t l e H2 H0 mrg; subst.
    destruct t.
    { exists (APair m n U :{U} H0).
      exists (Ptr (size H0)).
      repeat split... }
    { exists (APair m n L :{L} H0).
      exists (Ptr (size H0)).
      repeat split... } }
  { move=>H H' m m' st ihm H2 H0 mrg.
    have[H1'[mx st']]:=ihm _ _ mrg.
    exists H1'. exists (Fst mx)... }
  { move=>H H' m m' st ihm H2 H0 mrg.
    have[H1'[mx st']]:=ihm _ _ mrg.
    exists H1'. exists (Snd mx)... }
  { move=>H H' m n l t fr H2 H0 mrg.
    have[H4[fr' mrg']]:=free_merge fr mrg.
    exists H4. exists m... }
  { move=>H H' m n l t fr H2 H0 mrg.
    have[H4[fr' mrg']]:=free_merge fr mrg.
    exists H4. exists n... }
  { move=>H m H2 H0 mrg.
    exists H0. exists m... }
Qed.

Lemma free_pair0_canonical H H' m n l t :
  wr_heap H -> free H l (Pair0 m n t) H' ->
  exists lm, m = Ptr lm /\ n = Box.
Proof with eauto.
  move=>wr. elim: wr H' m n l t=>{H}.
  { move=>H' m n l t fr. inv fr. }
  { move=>H m s nfm wr ih H' m0 n l t fr. inv fr... }
  { move=>H m s nfm wr ih H' m0 n l t fr. inv fr... }
  { move=>H lm t wr ih H' m n l s fr. inv fr... }
  { move=>H lm ln t wr ih H' m n l s fr. inv fr... }
  { move=>H m n t nfm nfn wr ih H' m0 n0 l s fr. inv fr... }
  { move=>H wr ih H' m n l t fr. inv fr... }
Qed.

Lemma free_pair1_canonical H H' m n l t :
  wr_heap H -> free H l (Pair1 m n t) H' ->
  exists lm ln, m = Ptr lm /\ n = Ptr ln.
Proof with eauto.
  move=>wr. elim: wr H' m n l t=>{H}.
  { move=>H' m n l t fr. inv fr. }
  { move=>H m s nfm wr ih H' m0 n l t fr. inv fr... }
  { move=>H m s nfm wr ih H' m0 n l t fr. inv fr... }
  { move=>H lm t wr ih H' m n l s fr. inv fr... }
  { move=>H lm ln t wr ih H' m n l s fr. inv fr... }
  { move=>H m n t nfm nfn wr ih H' m0 n0 l s fr. inv fr... }
  { move=>H wr ih H' m n l t fr. inv fr... }
Qed.

Theorem ptr_prog H x y z A :
  H ; x ~ y ~ z : A -> wr_heap H ->
  (exists H' z', H ; z ~>> H' ; z') \/ (exists l, z = Ptr l).
Proof with eauto using ptr_step.
  move=>{H x y z A}[H x y z A].
  move e1:(nil)=>Γ. move e2:(nil)=>Δ er.
  elim: er H z e1 e2=>{Γ Δ x y A}.
  { move=>Γ Δ x s A wf shs dhs H z e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m m' s _ erm ihm H z e1 e2 rs wr; subst.
    inv rs.
    { left. exists (Lam0 Box m0 s :{s} H). exists (Ptr (size H))... }
    { right. exists l... } }
  { move=>Γ Δ A B m m' s t _ erm ihm H z e1 e2 rs wr; subst.
    inv rs.
    { left. exists (Lam1 Box m0 s :{s} H). exists (Ptr (size H))... }
    { right. exists l... } }
  { move=>Γ Δ A B m m' n s erm ihm tyn H z e1 e2 rs wr; subst. inv rs.
    { have[[H'[z' st]]|[l e]]:=ihm _ _ erefl erefl H4 wr.
      { left. exists H'. exists (App z' Box)... }
      { subst. have vl':=wr_resolve_ptr wr H4.
        have vl:=era_dyn_val erm vl'.
        have[A0[m0 e]]:=dyn_pi0_canonical (era_dyn_type erm) (convR _ _) vl. subst.
        have[m'0 e]:=era_lam0_canonical erm. subst.
        inv H4. inv H5.
        { left. exists H'. exists m1.[Box/]... }
        { exfalso. apply: free_wr_ptr... } } }
    { have[wr1 wr2]:=wr_merge_inv H5 wr.
      have//:=resolve_wr_box wr2 H9. }
    { inv H2.
      { have vl:=wr_free_dyn_val H1 wr. inv vl. }
      { have wr':=free_wr H1 wr.
        have[wr1 wr2]:=wr_merge_inv H7 wr'.
        have//:=resolve_wr_box wr2 H11. }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn H z e1 e2 rs wr.
    subst; inv mrg. inv rs.
    { have//:=era_box_form ern. }
    { left. have[wr1 wr2]:=wr_merge_inv H5 wr.
      have[[H1'[m1 st1]]|[l1 e1]]:=ihm _ _ erefl erefl H8 wr1.
      { have[H'[m0' st']]:=ptr_step_merge st1 H5.
        exists H'. exists (App m0' n0)... }
      { subst. have[[H2'[m2 st2]]|[l2 e2]]:=ihn _ _ erefl erefl H9 wr2.
        { have[H'[m2' st']]:=ptr_step_merge st2 (merge_sym H5).
          exists H'. exists (App (Ptr l1) m2')... }
        { subst.
          have vm':=wr_resolve_ptr wr1 H8.
          have vm:=era_dyn_val erm vm'.
          have[A0[m0 e]]:=dyn_pi1_canonical (era_dyn_type erm) (convR _ _) vm. subst.
          have[m1 e]:=era_lam1_canonical erm. subst. inv H8. inv H7.
          { have[H6[fr' mrg']]:=free_merge H4 H5.
            exists H6. exists m2.[Ptr l2/]... }
          { exfalso. apply: free_wr_ptr... } } } }
    { right. exists l... } }
  { move=>Γ Δ A B m m' n t tyS erm ihm tyn H z e1 e2 rs wr; subst. inv rs.
    { have[[H'[m1 st]]|[l e]]:=ihm _ _ erefl erefl H4 wr.
      { left. exists H'. exists (Pair0 m1 Box t)... }
      { subst. left.
        exists (Pair0 (Ptr l) Box t :{t} H).
        exists (Ptr (size H))... } }
    { right. exists l... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg tyS erm ihm ern ihn H z e1 e2 rs wr.
    subst; inv mrg. inv rs.
    { left. have[wr1 wr2]:=wr_merge_inv H8 wr.
      have[[H1'[m1 st1]]|[l1 e1]]:=ihm _ _ erefl erefl H9 wr1.
      { have[H'[m0' st']]:=ptr_step_merge st1 H8.
        exists H'. exists (Pair1 m0' n0 t)... }
      { subst. have[[H2'[m2 st2]]|[l2 e2]]:=ihn _ _ erefl erefl H10 wr2.
        { have[H'[n0' st']]:=ptr_step_merge st2 (merge_sym H8).
          exists H'. exists (Pair1 (Ptr l1) n0' t)... }
        { subst.
          exists (Pair1 (Ptr l1) (Ptr l2) t :{t} H).
          exists (Ptr (size H))... } } }
    { right. exists l... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg tyC erm ihm ern _ H z e1 e2 rs wr.
    subst; inv mrg. inv rs.
    { left. have[wr1 wr2]:=wr_merge_inv H5 wr.
      have[[H1'[m1 st]]|[l e]]:=ihm _ _ erefl erefl H8 wr1.
      { have[H'[m0' st']]:=ptr_step_merge st H5.
        exists H'. exists (LetIn Box m0' n0)... }
      { subst.
        have vm':=wr_resolve_ptr wr1 H8.
        have vm:=era_dyn_val erm vm'.
        have[m1[m2 e]]:=dyn_sig0_canonical (era_dyn_type erm) (convR _ _) vm. subst.
        have[m0 e]:=era_pair0_canonical erm. subst. inv H8. inv H7.
        { have[H6[fr' mrg']]:=free_merge H4 H5.
          have[lm[e _]]:=free_pair0_canonical wr fr'. subst.
          exists H6. exists (n0.[Box,Ptr lm/])... }
        { exfalso. apply: free_wr_ptr... } } }
    { right. exists l... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg tyC erm ihm ern _ H z e1 e2 rs wr.
    subst; inv mrg. inv rs.
    { left. have[wr1 wr2]:=wr_merge_inv H5 wr.
      have[[H1'[m1 st]]|[l e]]:=ihm _ _ erefl erefl H8 wr1.
      { have[H'[m0' st']]:=ptr_step_merge st H5.
        exists H'. exists (LetIn Box m0' n0)... }
      { subst.
        have vm':=wr_resolve_ptr wr1 H8.
        have vm:=era_dyn_val erm vm'.
        have[m1[m2 e]]:=dyn_sig1_canonical (era_dyn_type erm) (convR _ _) vm. subst.
        have[m1'[m2' e]]:=era_pair1_canonical erm. subst. inv H8. inv H7.
        { have[H6[fr' mrg']]:=free_merge H4 H5.
          have[lm[ln[e1 e2]]]:=free_pair1_canonical wr fr'. subst.
          exists H6. exists (n0.[Ptr ln,Ptr lm/])... }
        { exfalso. apply: free_wr_ptr... } } }
    { right. exists l... } }
  { move=>Γ Δ A B m m' n n' t _ erm ihm ern ihn H z e1 e2 rs wr; subst. inv rs.
    { left. exists (APair m0 n0 t :{t} H). exists (Ptr (size H))... }
    { right. exists l... } }
  { move=>Γ Δ A B m m' t erm ihm H z e1 e2 rs wr; subst. inv rs.
    { left. have[[H'[m1 st]]|[l e]]:=ihm _ _ erefl erefl H4 wr.
      { exists H'. exists (Fst m1)... }
      { subst.
        have vm':=wr_resolve_ptr wr H4.
        have vm:=era_dyn_val erm vm'.
        have[m1[m2 e]]:=dyn_with_canonical (era_dyn_type erm) (convR _ _) vm. subst.
        have[m1'[m2' e]]:=era_apair_canonical erm. subst. inv H4. inv H5.
        { exists H'. exists m0... }
        { exfalso. apply: free_wr_ptr... } } }
    { right. exists l... } }
  { move=>Γ Δ A B m m' t erm ihm H z e1 e2 rs wr; subst. inv rs.
    { left. have[[H'[m1 st]]|[l e]]:=ihm _ _ erefl erefl H4 wr.
      { exists H'. exists (Snd m1)... }
      { subst.
        have vm':=wr_resolve_ptr wr H4.
        have vm:=era_dyn_val erm vm'.
        have[m1[m2 e]]:=dyn_with_canonical (era_dyn_type erm) (convR _ _) vm. subst.
        have[m1'[m2' e]]:=era_apair_canonical erm. subst. inv H4. inv H5.
        { exists H'. exists n... }
        { exfalso. apply: free_wr_ptr... } } }
    { right. exists l... } }
  { move=>Γ Δ A B x x' P m n s tyB erx ihx tyP H z e1 e2 rs wr; subst. inv rs.
    { left. exists H. exists m0... }
    { right. exists l... } }
  { move=>Γ Δ A B m m' s eq erm ihm tyB H z e1 e2 rs wr; subst... }
Qed.
