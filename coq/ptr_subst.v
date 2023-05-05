From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS ptr_step era_inv ptr_res.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive agree_resolve :
  dyn_ctx -> dyn_ctx -> (var -> term) -> (var -> term) -> nat -> Prop :=
| agree_resolve_nil H :
  H ▷ U ->
  wr_heap H ->
  agree_resolve nil H ids ids 0
| agree_resolve_upTy Δ H σ σ' A x s :
  agree_resolve Δ H σ σ' x ->
  agree_resolve (A :{s} Δ) H (up σ) (up σ') x.+1
| agree_resolve_upN Δ H σ σ' x :
  agree_resolve Δ H σ σ' x ->
  agree_resolve (_: Δ) H (up σ) (up σ') x.+1
| agree_resolve_wkU Δ H1 H2 H σ σ' m m' A :
  H1 ∘ H2 => H ->
  H2 ▷ U ->
  wr_heap H2 ->
  H2 ; m ~ m' ->
  agree_resolve Δ H1 σ σ' 0 ->
  agree_resolve (A :U Δ) H (m .: σ) (m' .: σ') 0
| agree_resolve_wkL Δ H1 H2 H σ σ' m m' A :
  H1 ∘ H2 => H ->
  wr_heap H2 ->
  H2 ; m ~ m' ->
  agree_resolve Δ H1 σ σ' 0 ->
  agree_resolve (A :L Δ) H (m .: σ) (m' .: σ') 0
| agree_resolve_wkN Δ H σ σ' m m' :
  agree_resolve Δ H σ σ' 0 ->
  agree_resolve (_: Δ) H (m .: σ) (m' .: σ') 0.

Lemma agree_resolve_key Δ H σ σ' x s :
  agree_resolve Δ H σ σ' x -> Δ ▷ s -> H ▷ s.
Proof with eauto using key, key_impure, merge_pure.
  move=>agr. elim: agr s=>//{Δ H σ σ' x}.
  { move=>H k wr [|]... }
  { move=>Δ H σ σ' A x s agr ih [|] k... inv k... }
  { move=>Δ H σ σ' x agr ih [|] k... inv k... }
  { move=>Δ H1 H2 H σ σ' m m' A mrg k1 wr rs agr ih [|] k2... inv k2... }
  { move=>Δ H1 H2 H σ σ' m m' A mrg wr rs agr ih [|] k... inv k. }
  { move=>Δ H σ σ' _ _ agr ih s k. inv k... }
Qed.

Lemma nf_agree_resolve_var Δ H σ σ' i x :
  agree_resolve Δ H σ σ' i -> x < i -> Var x = σ x.
Proof.
  move=>agr. elim: agr x=>//{Δ H σ σ' i}.
  { move=>Δ H σ σ' _ x _ agr ih [|i] lt//.
    asimpl. have/ih<-//:i < x by eauto. }
  { move=>Δ H σ σ' x agr ih [|i] lt//.
    asimpl. have/ih<-//:i < x by eauto. }
Qed.

Lemma nf_agree_resolve Δ H σ σ' i j m :
  nf i m -> i <= j -> agree_resolve Δ H σ σ' j -> m = m.[σ].
Proof with eauto using agree_resolve.
  move=>nfm. elim: nfm Δ H σ σ' j=>//{i m}.
  { move=>i x lt Δ H σ σ' j le agr.
    apply: nf_agree_resolve_var...
    apply: leq_trans... }
  { move=>i m s nfm ihm Δ H σ σ' j le agr.
    have le1:i < j.+1 by eauto. asimpl. f_equal... }
  { move=>i m s nfm ihm Δ H σ σ' j le agr.
    have le1:i < j.+1 by eauto. asimpl. f_equal... }
  { move=>i m nfm ihm Δ H σ σ' j le agr.
    asimpl. f_equal... }
  { move=>i m n nfm ihm nfn ihn Δ H σ σ' j le agr.
    asimpl. f_equal... }
  { move=>i m t nfm ihm Δ H σ σ' j le agr.
    asimpl. f_equal... }
  { move=>i m n t nfm ihm nfn ihn Δ H σ σ' j le agr.
    asimpl. f_equal... }
  { move=>i m n nfm ihm nfn ihn Δ H σ σ' j le agr.
    have le2:i.+1 < j.+2 by eauto. asimpl. f_equal... }
  { move=>i m n t nfm ihm nfn ihn Δ H σ σ' j le agr.
    asimpl. f_equal... }
  { move=>i m nfm ihm Δ H σ σ' j le agr.
    asimpl. f_equal... }
  { move=>i m nfm ihm Δ H σ σ' j le agr.
    asimpl. f_equal... }
  { move=>i m nfm ihm Δ H σ σ' j le agr.
    asimpl. f_equal... }
Qed.

Lemma agree_resolve_wr Δ H σ σ' x :
  agree_resolve Δ H σ σ' x -> wr_heap H.
Proof with eauto using wr_heap.
  elim=>{Δ H σ σ' x}...
  { move=>Δ H1 H2 H σ σ' m m' _ mrg k wr2 rs agr wr1.
    apply: wr_merge... }
  { move=>Δ H1 H2 H σ σ' m m' _ mrg wr2 rs agr wr1.
    apply: wr_merge... }
Qed.

Definition id_ren i ξ := forall x, x < i -> ξ x = x.

Lemma id_ren1 : id_ren 0 (+1).
Proof. move=>x h. inv h. Qed.

Lemma id_ren_up i ξ : id_ren i ξ -> id_ren i.+1 (upren ξ).
Proof with eauto. move=>idr [|x]//=... Qed.

Lemma nf_id_ren i m ξ : nf i m -> id_ren i ξ -> m = m.[ren ξ].
Proof with eauto using id_ren_up.
  move=>nf. elim: nf ξ=>//={i m}.
  { move=>i x lt ξ idr. asimpl. rewrite idr... }
  { move=>i m s nfm ihm ξ idr. asimpl. rewrite<-ihm... }
  { move=>i m s nfm ihm ξ idr. asimpl. rewrite<-ihm... }
  { move=>i m nfm ihm ξ idr. rewrite<-ihm... }
  { move=>i m n nfm ihm nfn ihn ξ idr. rewrite<-ihm... rewrite<-ihn... }
  { move=>i m t nfm ihm ξ idr. rewrite<-ihm... }
  { move=>i m n t nfm ihm nfn ihn ξ idr. rewrite<-ihm... rewrite<-ihn... }
  { move=>i m n nfm ihm nfn ihn ξ idr. rewrite<-ihm...
    replace n.[upn 2 (ren ξ)] with
      n.[ren (upren (upren ξ))] by autosubst.
    have<-:=ihn _ (id_ren_up (id_ren_up idr))... }
  { move=>i m n t nfm ihm nfn ihn ξ idr. rewrite<-ihm... rewrite<-ihn... }
  { move=>i m nfm ihm ξ idr. rewrite<-ihm... }
  { move=>i m nfm ihm ξ idr. rewrite<-ihm... }
  { move=>i m nfm ihm ξ idr. rewrite<-ihm... }
Qed.

Lemma resolve_ren H m m' i ξ :
  H ; m ~ m' -> wr_heap H -> id_ren i ξ -> H ; m.[ren ξ] ~ m'.[ren ξ].
Proof with eauto using resolve, id_ren_up.
  move=>rs. elim: rs i ξ=>{H m m'}...
  { move=>H m m' s k rsm ihm i ξ wr idr. asimpl. econstructor... }
  { move=>H m m' s k rsm ihm i ξ wr idr. asimpl. econstructor... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn i ξ wr idr. asimpl.
    have[wr1 wr2]:=wr_merge_inv mrg wr. econstructor... }
  { move=>H1 H2 H m m' n n' t mrg rsm ihm rsn ihn i ξ wr idr. asimpl.
    have[wr1 wr2]:=wr_merge_inv mrg wr. econstructor... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn i ξ wr idr.
    replace (LetIn Box m n).[ren ξ]
      with (LetIn Box m.[ren ξ] n.[ren (upren (upren ξ))])
        by autosubst.
    replace (LetIn Box m' n').[ren ξ]
      with (LetIn Box m'.[ren ξ] n'.[ren (upren (upren ξ))])
        by autosubst.
    have[wr1 wr2]:=wr_merge_inv mrg wr. econstructor... }
  { move=>H H' l m m' fr rsm ihm i ξ wr idr. asimpl.
    have nfm:=free_wr_nf fr wr.
    have wr':=free_wr fr wr.
    have nfm':=resolve_wr_nfi' rsm wr' nfm.
    have le: 0 <= i by eauto.
    have nfi:=nf_weaken nfm' le.
    have<-:=nf_id_ren nfi idr.
    econstructor... }
Qed.

Lemma agree_resolve_id Δ H σ σ' x i s A :
  agree_resolve Δ H σ σ' i -> dyn_has Δ x s A -> H ; σ x ~ σ' x.
Proof with eauto using resolve, id_ren1.
  move=>agr. elim: agr x s A=>{Δ H σ σ' i}...
  { move=>Δ H σ σ' A x s agr ih x0 s0 A0 hs. inv hs; asimpl.
    { constructor. apply: agree_resolve_key... }
    { apply: resolve_ren...
      apply: agree_resolve_wr... } }
  { move=>Δ H σ σ' x agr ih x0 s A hs. inv hs; asimpl.
    apply: resolve_ren...
    apply: agree_resolve_wr... }
  { move=>Δ H1 H2 H σ σ' m m' A mrg k wr rsm agr ih x s A0 hs.
    inv hs; asimpl.
    { have k1:=agree_resolve_key agr H8.
      have->//:=merge_pureL mrg k1. }
    { have->:=merge_pureR mrg k... } }
  { move=>Δ H1 H2 H σ σ' m m' A mrg wr rsm agr ih x s A0 hs.
    inv hs; asimpl.
    have k1:=agree_resolve_key agr H8.
    have->//:=merge_pureL mrg k1. }
  { move=>Δ H σ σ' m m' agr ih x s A hs. inv hs; asimpl... }
Qed.

Lemma agree_resolve_merge_inv Δ1 Δ2 Δ H σ σ' x :
  agree_resolve Δ H σ σ' x ->
  Δ1 ∘ Δ2 => Δ ->
  exists H1 H2,
    H1 ∘ H2 => H /\
    agree_resolve Δ1 H1 σ σ' x /\
    agree_resolve Δ2 H2 σ σ' x.
Proof with eauto using merge, agree_resolve.
  move=>agr. elim: agr Δ1 Δ2=>{Δ H σ σ' x}.
  { move=>H k wr Δ1 Δ2 mrg. inv mrg.
    have[H1[H2[k1[k2 mrg]]]]:=pure_split k.
    have[wr1 wr2]:=wr_merge_inv mrg wr.
    exists H1. exists H2... }
  { move=>Δ H σ σ' A x s agr ih Δ1 Δ2 mrg. inv mrg.
    { have[H1[H2[mrg[agr1 agr2]]]]:=ih _ _ H3. exists H1. exists H2... }
    { have[H1[H2[mrg[agr1 agr2]]]]:=ih _ _ H3. exists H1. exists H2... }
    { have[H1[H2[mrg[agr1 agr2]]]]:=ih _ _ H3. exists H1. exists H2... } }
  { move=>Δ H σ σ' x agr ih Δ1 Δ2 mrg. inv mrg.
    have[H1[H2[mrg[agr1 agr2]]]]:=ih _ _ H3. exists H1. exists H2... }
  { move=>Δ H1 H2 H σ σ' m m' A mrg1 k wr rsm agr ih Δ1 Δ2 mrg2. inv mrg2.
    have[H3[H4[mrg2[agr1 agr2]]]]:=ih _ _ H5.
    have e:=merge_pureR mrg1 k. subst.
    have[H6[H7[mrg3[mrg4 mrg5]]]]:=merge_distr mrg1 mrg2 (merge_pure_refl k).
    exists H6. exists H7. repeat split... }
  { move=>Δ H1 H2 H σ σ' m m' A mrg1 wr rsm agr ih Δ1 Δ2 mrg2. inv mrg2.
    { have[H3[H4[mrg2[agr1 agr2]]]]:=ih _ _ H5.
      have[H6[mrg3 mrg4]]:=merge_splitL mrg1 mrg2.
      exists H6. exists H4. repeat split... }
    { have[H3[H4[mrg2[agr1 agr2]]]]:=ih _ _ H5.
      have[H6[mrg3 mrg4]]:=merge_splitR mrg1 mrg2.
      exists H3. exists H6. repeat split...
      apply: merge_sym... } }
  { move=>Δ H σ σ' m m' agr ih Δ1 Δ2 mrg. inv mrg.
    have[H4[H5[mrg2[agr1 agr2]]]]:=ih _ _ H3.
    exists H4. exists H5. repeat split... }
Qed.

Lemma resolve_subst Γ Δ H1 H2 H m n n' A σ σ' x :
  Γ ; Δ ⊢ m ~ n : A -> H1 ∘ H2 => H ->
  H1 ; n' ~ n -> wr_heap H1 ->
  agree_resolve Δ H2 σ σ' x ->
  H ; n'.[σ] ~ n.[σ'].
Proof with eauto using
  resolve, agree_resolve, merge_pure, key_impure, merge_key.
  move=>erm. elim: erm H1 H2 H n' σ σ' x=>{Γ Δ m n A}...
  { move=>Γ Δ x s A wf shs dhs H1 H2 H n' σ σ' x0 mrg rsn wr agr.
    inv rsn; asimpl.
    { have->:=merge_pureL mrg H6.
      apply: agree_resolve_id... }
    { inv H4.
      have//:=free_wr_var H3 wr.
      have//:=free_wr_ptr H3 wr. } }
  { move=>Γ Δ A B m m' s k erm ihm H1 H2 H n' σ σ' x mrg rsn wr agr.
    have wf:=dyn_type_wf (era_dyn_type erm). inv wf.
    inv rsn; asimpl.
    { econstructor.
      { destruct s... have k2:=agree_resolve_key agr k... }
      { apply: ihm... } }
    { inv H4.
      { have nfL:=free_wr_nf H3 wr. inv nfL.
        have k2:=agree_resolve_key agr k.
        have[H4[fr mrg']]:=free_merge H3 mrg.
        have wr':=free_wr H3 wr.
        econstructor...
        econstructor...
        have le:0 < x.+1 by eauto.
        destruct s0.
        { have agr': agree_resolve (A :U Δ) H2 (up σ) (up σ') x.+1...
          have->:=nf_agree_resolve H7 le agr'... }
        { have agr': agree_resolve (A :L Δ) H2 (up σ) (up σ') x.+1...
          have->:=nf_agree_resolve H7 le agr'... } }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ A B m m' s t k erm ihm H1 H2 H n' σ σ' x mrg rsn wr agr.
    have wf:=dyn_type_wf (era_dyn_type erm). inv wf.
    inv rsn; asimpl.
    { econstructor.
      { destruct s... have k2:=agree_resolve_key agr k... }
      { apply: ihm... } }
    { inv H4.
      { have nfL:=free_wr_nf H3 wr. inv nfL.
        have k2:=agree_resolve_key agr k.
        have[H4[fr mrg']]:=free_merge H3 mrg.
        have wr':=free_wr H3 wr.
        econstructor...
        econstructor...
        have le:0 < x.+1 by eauto.
        destruct t.
        { have agr': agree_resolve (A :U Δ) H2 (up σ) (up σ') x.+1...
          have->:=nf_agree_resolve H6 le agr'... }
        { have agr': agree_resolve (A :L Δ) H2 (up σ) (up σ') x.+1...
          have->:=nf_agree_resolve H6 le agr'... } }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ A B m m' n s erm ihm tyn H1 H2 H n' σ σ' x mrg rsn wr agr.
    inv rsn; asimpl.
    { econstructor... }
    { have[wr1 wr2]:=wr_merge_inv H7 wr.
      have//:=resolve_wr_box wr2 H11. }
    { inv H4.
      { have vl:=wr_free_dyn_val H3 wr. inv vl. }
      { have vl:=wr_free_dyn_val H3 wr. inv vl. }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg1 erm ihm ern ihn H1 H2 H n0 σ σ' x mrg2 rsn wr agr.
    inv rsn; asimpl.
    { exfalso. apply: era_box_form... }
    { have[wr1 wr2]:=wr_merge_inv H7 wr.
      have[H4[H5[mrg3[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
      have[H6[H8[mrg4[mrg5 mrg6]]]]:=merge_distr mrg2 H7 mrg3.
      econstructor... }
    { inv H4.
      { have vl:=wr_free_dyn_val H3 wr. inv vl. }
      { have vl:=wr_free_dyn_val H3 wr. inv vl. }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ A B m m' n t tyS erm ihm tyn H1 H2 H n' σ σ' x mrg rsn wr agr.
    inv rsn; asimpl.
    { econstructor... }
    { inv H4.
      { have nfP:=free_wr_nf H3 wr. inv nfP.
        have[H4[fr mrg']]:=free_merge H3 mrg.
        have lx: 0 <= x by eauto.
        econstructor...
        econstructor.
        have->:=nf_agree_resolve H5 lx agr.
        apply: ihm...
        apply:free_wr... }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg1 tyS erm ihm ern ihn H1 H2 H n0 σ σ' x mrg2 rsn wr agr.
    inv rsn; asimpl.
    { have[wr1 wr2]:=wr_merge_inv H10 wr.
      have[H4[H5[mrg3[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
      have[H6[H7[mrg4[mrg5 mrg6]]]]:=merge_distr mrg2 H10 mrg3.
      econstructor... }
    { inv H4.
      { have nfP:=free_wr_nf H3 wr. inv nfP.
        have[H4[fr mrg']]:=free_merge H3 mrg2.
        have[H6[H7[mrg3[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
        have[H9[H11[mrg4[mrg5 mrg6]]]]:=merge_distr mrg' H12 mrg3.
        have wr':=free_wr H3 wr.
        have[wr1 wr2]:=wr_merge_inv H12 wr'.
        have lx: 0 <= x by eauto.
        econstructor...
        econstructor...
        have->:=nf_agree_resolve H8 lx agr1...
        have->:=nf_agree_resolve H10 lx agr2... }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg1 tyC erm ihm ern ihn H1 H2 H n0 σ σ' x mrg2 rsn wr agr.
    inv rsn; asimpl.
    { have[wr1 wr2]:=wr_merge_inv H7 wr.
      have[H4[H5[mrg3[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
      have[H6[H8[mrg4[mrg5 mrg6]]]]:=merge_distr mrg2 H7 mrg3.
      econstructor... }
    { inv H4.
      { have vl:=wr_free_dyn_val H3 wr. inv vl. }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg1 tyC erm ihm ern ihn H1 H2 H n0 σ σ' x mrg2 rsn wr agr.
    inv rsn; asimpl.
    { have[wr1 wr2]:=wr_merge_inv H7 wr.
      have[H4[H5[mrg3[agr1 agr2]]]]:=agree_resolve_merge_inv agr mrg1.
      have[H6[H8[mrg4[mrg5 mrg6]]]]:=merge_distr mrg2 H7 mrg3.
      econstructor... }
    { inv H4.
      { have vl:=wr_free_dyn_val H3 wr. inv vl. }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ A B m m' n n' t k erm ihm ern ihn H1 H2 H n0 σ σ' x mrg rsn wr agr.
    inv rsn; asimpl.
    { have k':=agree_resolve_key agr k.
      econstructor... }
    { inv H4.
      { have nfP:=free_wr_nf H3 wr. inv nfP.
        have[H4[fr mrg']]:=free_merge H3 mrg.
        have k2:=agree_resolve_key agr k.
        have wr':=free_wr H3 wr.
        have lx: 0 <= x by eauto.
        econstructor...
        have->:=nf_agree_resolve H6 lx agr.
        have->:=nf_agree_resolve H8 lx agr.
        econstructor... }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ A B m m' t erm ihm H1 H2 H n' σ σ' x mrg rsn wr agr.
    inv rsn; asimpl.
    { econstructor... }
    { inv H4.
      { have vl:=wr_free_dyn_val H3 wr. inv vl. }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ A B m m' t erm ihm H1 H2 H n' σ σ' x mrg rsn wr agr.
    inv rsn; asimpl.
    { econstructor... }
    { inv H4.
      { have vl:=wr_free_dyn_val H3 wr. inv vl. }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ A B x x' P m n s tyB erx ihx tyP H1 H2 H n' σ σ' x0 mrg rsn wr agr.
    inv rsn; asimpl.
    { constructor... }
    { inv H4.
      { have vl:=wr_free_dyn_val H3 wr. inv vl. }
      { exfalso. apply: free_wr_ptr... } } }
Qed.
