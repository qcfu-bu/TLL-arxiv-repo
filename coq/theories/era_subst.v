From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_weak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2"
  (at level 50, Δ1, σ1, σ2, Γ2 at next level).
Inductive era_agree_subst :
  sta_ctx -> dyn_ctx -> (var -> term) -> (var -> term) -> sta_ctx -> dyn_ctx -> Prop :=
| era_agree_subst_nil σ :
  nil ; nil ⊢ σ ~ σ ⊣ nil ; nil
| era_agree_subst_ty Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s :
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 ->
  Γ2 ⊢ A : Sort s ->
  (A.[σ1] :: Γ1) ; (A.[σ1] :{s} Δ1) ⊢ up σ1 ~ up σ2 ⊣ (A :: Γ2) ; (A :{s} Δ2)
| era_agree_subst_n Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s :
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 ->
  Γ2 ⊢ A : Sort s ->
  (A.[σ1] :: Γ1) ; (_: Δ1) ⊢ up σ1 ~ up σ2 ⊣ (A :: Γ2) ; (_: Δ2)
| era_agree_subst_wk0 Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A :
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 ->
  Γ1 ⊢ n : A.[σ1] ->
  Γ1 ; Δ1 ⊢ n .: σ1 ~ n' .: σ2 ⊣ (A :: Γ2) ; (_: Δ2)
| era_agree_subst_wk1 Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s :
  Δb ▷ s ->
  Δa ∘ Δb => Δ1 ->
  Γ1 ; Δa ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 ->
  Γ1 ; Δb ⊢ n ~ n' : A.[σ1] ->
  Γ1 ; Δ1 ⊢ n .: σ1 ~ n' .: σ2 ⊣ (A :: Γ2) ; (A :{s} Δ2)
| era_agree_subst_conv0 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s :
  A === B ->
  Γ1 ⊢ B.[ren (+1)].[σ1] : Sort s ->
  Γ2 ⊢ B : Sort s ->
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ (A :: Γ2) ; (_: Δ2) ->
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ (B :: Γ2) ; (_: Δ2)
| era_agree_subst_conv1 Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s :
  A === B ->
  Γ1 ⊢ B.[ren (+1)].[σ1] : Sort s ->
  Γ2 ⊢ B : Sort s ->
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ (A :: Γ2) ; (A :{s} Δ2) ->
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ (B :: Γ2) ; (B :{s} Δ2)
where "Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2" := (era_agree_subst Γ1 Δ1 σ1 σ2 Γ2 Δ2).

Lemma era_agree_subst_key Γ1 Γ2 Δ1 Δ2 σ1 σ2 s :
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> Δ2 ▷ s -> Δ1 ▷ s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Γ1 Γ2 Δ1 Δ2 σ1 σ2}...
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA r k. inv k... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA r k. inv k... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr ih tyn s k. inv k... }
  { move=>Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s k1 mrg agr ih tyn r k2.
    inv k2... apply: key_merge... apply: key_impure. }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih r k. inv k... }
Qed.

Lemma era_dyn_agree_subst Γ1 Γ2 Δ1 Δ2 σ1 σ2 :
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> Γ1 ; Δ1 ⊢ σ1 ⊣ Γ2 ; Δ2.
Proof with eauto using dyn_agree_subst.
  elim=>{Γ1 Γ2 Δ1 Δ2 σ1 σ2}...
Qed.

Lemma era_sta_agree_subst Γ1 Γ2 Δ1 Δ2 σ1 σ2 :
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> Γ1 ⊢ σ1 ⊣ Γ2.
Proof with eauto using sta_agree_subst.
  move/era_dyn_agree_subst/dyn_sta_agree_subst=>//.
Qed.

Lemma era_agree_subst_refl Γ Δ : dyn_wf Γ Δ -> Γ ; Δ ⊢ ids ~ ids ⊣ Γ ; Δ.
Proof with eauto using era_agree_subst.
  elim: Γ Δ.
  { move=>Δ wf. inv wf... }
  { move=>A Γ ih Δ wf. inv wf.
    { have agr:=ih _ H1.
      have:(A.[ids] :: Γ); A.[ids] :{s} Δ0 ⊢
       up ids ~ up ids ⊣ (A :: Γ); A :{s} Δ0...
      by asimpl. }
    { have agr:=ih _ H1.
      have:(A.[ids] :: Γ); _: Δ0 ⊢ up ids ~ up ids ⊣ (A :: Γ); _: Δ0...
      by asimpl. } }
Qed.
#[global] Hint Resolve era_agree_subst_refl.

Lemma era_agree_subst_has Γ1 Γ2 σ1 σ2 Δ1 Δ2 x s A :
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> dyn_wf Γ1 Δ1 -> dyn_has Δ2 x s A ->
  Γ1 ; Δ1 ⊢ (σ1 x) ~ (σ2 x) : A.[σ1].
Proof with eauto using era_agree_subst, era_agree_subst_key.
  move=>agr. elim: agr x s A=>{Γ1 Γ2 σ1 σ2 Δ1 Δ2}...
  { move=>σ x s A wf hs. inv hs. }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA x t B wf hs.
    inv wf. inv hs; asimpl.
    replace A.[σ1 >> ren (+1)] with A.[σ1].[ren (+1)] by autosubst.
    apply: era_var; constructor...
    replace A0.[σ1 >> ren (+1)] with A0.[σ1].[ren (+1)] by autosubst.
    apply: era_eweakenU... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA x t B wf hs.
    inv wf. inv hs; asimpl...
    replace A0.[σ1 >> ren (+1)] with A0.[σ1].[ren (+1)]
      by autosubst.
    apply: era_eweakenN... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr ih tyn x t B wf hs. inv hs; asimpl... }
  { move=>Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s k mrg agr ih tyn x t B wf hs.
    inv hs; asimpl.
    { have ka:=era_agree_subst_key agr H5.
      have->//:=merge_pureL mrg ka. }
    { have->:=merge_pureR mrg k.
      apply: ih...
      have[]//:=dyn_wf_inv mrg wf. } }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih x t C wf hs. inv hs.
    { apply: era_conv.
      apply: sta_conv_subst.
      apply: sta_conv_subst...
      apply: ih...
      constructor...
      exact: tyB1. }
    { apply: ih...
      constructor... } }
Qed.

Lemma era_agree_subst_merge Γ1 Γ2 Δ1 Δ2 Δa Δb σ1 σ2 :
  Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 -> Δa ∘ Δb => Δ2 ->
  exists Δa' Δb',
    Δa' ∘ Δb' => Δ1 /\
    Γ1 ; Δa' ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δa /\ Γ1 ; Δb' ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δb.
Proof with eauto 6 using merge, era_agree_subst, era_agree_subst_key.
  move=>agr. elim: agr Δa Δb=>{Γ1 Γ2 Δ1 Δ2 σ1 σ2}.
  { move=>σ Δa Δb mrg. inv mrg.
    exists nil. exists nil... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA Δa Δb mrg. inv mrg.
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (A.[σ1] :U Δa). exists (A.[σ1] :U Δb)... }
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (A.[σ1] :L Δa). exists (_: Δb)... }
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (_: Δa). exists (A.[σ1] :L Δb)... } }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A s agr ih tyA Δa Δb mrg. inv mrg.
    have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
    exists (_: Δa). exists (_: Δb)... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 n n' A agr ih tyn Δa Δb mrg. inv mrg.
    have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
    exists Δa. exists Δb... }
  { move=>Γ1 Γ2 σ1 σ2 Δ1 Δ2 Δa Δb n n' A s k mrg agr ih tyn Δa' Δb' mrg'.
    inv mrg'.
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ H2.
      have[Δc[mrg1 mrg2]]:=merge_splitL mrg mrg'.
      exists Δc. exists Δb'.
      repeat split...
      apply: era_agree_subst_wk1...
      have[Δd[mrg3 mrg4]]:=merge_splitR mrg mrg'.
      have e:=merge_pureR mrg3 k.
      by subst. }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ H2.
      have[Δc[mrg1 mrg2]]:=merge_splitL mrg mrg'.
      exists Δc. exists Δb'.
      repeat split... }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ H2.
      have[Δc[mrg1 mrg2]]:=merge_splitR mrg mrg'.
      exists Δa'. exists Δc.
      repeat split...
      exact: merge_sym. } }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_null H2).
    exists Δa'. exists Δb'... }
  { move=>Γ1 Δ1 σ1 σ2 Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_left A H2).
      exists Δa'. exists Δb'... }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_right1 A H2).
      exists Δa'. exists Δb'... }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_right2 A H2).
      exists Δa'. exists Δb'... } }
Qed.

Lemma era_substitution Γ1 Γ2 m m' A Δ1 Δ2 σ1 σ2 :
  Γ2 ; Δ2 ⊢ m ~ m' : A -> Γ1 ; Δ1 ⊢ σ1 ~ σ2 ⊣ Γ2 ; Δ2 ->
  Γ1 ; Δ1 ⊢ m.[σ1] ~ m'.[σ2] : A.[σ1].
Proof with eauto using era_agree_subst, era_agree_subst_key, era_type.
  move=>ty. elim: ty Γ1 Δ1 σ1 σ2=>{Γ2 Δ2 m m' A}.
  { move=>Γ Δ x s A wf shs dhs Γ1 Δ1 σ1 σ2 agr. asimpl.
    apply: era_agree_subst_has...
    apply: dyn_substitution_wf...
    apply: era_dyn_agree_subst... }
  { move=>Γ Δ A B m m' s k tym ihm Γ1 Δ1 σ1 σ2 agr. asimpl.
    have wf:=dyn_type_wf (era_dyn_type tym). inv wf.
    apply: era_lam0... }
  { move=>Γ Δ A B m m' s t k tym ihm Γ1 Δ1 σ1 σ2 agr. asimpl.
    have wf:=dyn_type_wf (era_dyn_type tym). inv wf.
    apply: era_lam1... }
  { move=>Γ Δ A B m m' n s tym ihm tyn Γ1 Δ1 σ1 σ2 agr. asimpl.
    replace B.[n.[σ1] .: σ1] with B.[up σ1].[n.[σ1]/] by autosubst.
    have{}ihm:=ihm _ _ _ _ agr.
    apply: era_app0...
    have//:=sta_substitution tyn (era_sta_agree_subst agr). }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg tym ihm tyn ihn
      Γ1 Δ0 σ1 σ2 agr. asimpl.
    replace B.[n.[σ1] .: σ1] with B.[up σ1].[n.[σ1]/] by autosubst.
    have[Δa[Δb[mrg0[agra agrb]]]]:=era_agree_subst_merge agr mrg.
    have{}ihm:=ihm _ _ _ _ agra.
    have{}ihn:=ihn _ _ _ _ agrb.
    apply: era_app1... }
  { move=>Γ Δ A B m m' n t tyS tym ihm tyn Γ1 Δ1 σ1 σ2 agr. asimpl.
    have{}ihS:=sta_substitution tyS (dyn_sta_agree_subst (era_dyn_agree_subst agr)).
    have{}ihm:=ihm _ _ _ _ agr.
    have{}ihn:=sta_substitution tyn (dyn_sta_agree_subst (era_dyn_agree_subst agr)).
    apply: era_pair0...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg tyS tym ihm tyn ihn Γ1 Δ0 σ1 σ2 agr. asimpl.
    have[Δa[Δb[mrg0[agra agrb]]]]:=era_agree_subst_merge agr mrg.
    have{}ihS:=sta_substitution tyS (dyn_sta_agree_subst (era_dyn_agree_subst agr)).
    have{}ihm:=ihm _ _ _ _ agra.
    have{}ihn:=ihn _ _ _ _ agrb.
    apply: era_pair1...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg tyC tym ihm tyn ihn Γ1 Δ0 σ1 σ2 agr. asimpl.
    have[Δa[Δb[mrg0[agra agrb]]]]:=era_agree_subst_merge agr mrg.
    replace C.[m.[σ1] .: σ1] with C.[up σ1].[m.[σ1]/] by autosubst.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf (era_dyn_type tyn). inv wf. inv H4.
    have{}ihC:=sta_substitution tyC
      (sta_agree_subst_ty (dyn_sta_agree_subst (era_dyn_agree_subst agr)) H2).
    have{}ihm:=ihm _ _ _ _ agra.
    have{}ihn:=ihn _ _ _ _ (era_agree_subst_n (era_agree_subst_ty agrb H8) H5).
    apply: era_letin0...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg tyC tym ihm tyn ihn Γ1 Δ0 σ1 σ2 agr. asimpl.
    have[Δa[Δb[mrg0[agra agrb]]]]:=era_agree_subst_merge agr mrg.
    replace C.[m.[σ1] .: σ1] with C.[up σ1].[m.[σ1]/] by autosubst.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf (era_dyn_type tyn). inv wf. inv H4.
    have{}ihC:=sta_substitution tyC
      (sta_agree_subst_ty (dyn_sta_agree_subst (era_dyn_agree_subst agr)) H2).
    have{}ihm:=ihm _ _ _ _ agra.
    have{}ihn:=ihn _ _ _ _ (era_agree_subst_ty (era_agree_subst_ty agrb H8) H6).
    apply: era_letin1...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ A B m m' n n' t k tym ihm tyn ihn Γ1 Δ1 σ1 σ2 agr. asimpl. apply: era_apair... }
  { move=>Γ Δ A B m m' t tym ihm Γ1 Δ1 σ1 σ2 agr. asimpl. apply: era_fst... }
  { move=>Γ Δ A B m m' t tym ihm Γ1 Δ1 σ1 σ2 agr. asimpl. apply: era_snd... }
  { move=>Γ Δ A B H H' P m n s tyB erH ihH tyP Γ1 Δ1 σ1 σ2 agr. asimpl.
    replace B.[P.[σ1] .: n.[σ1] .: σ1] with B.[upn 2 σ1].[P.[σ1],n.[σ1]/] by autosubst.
    have wf:=sta_type_wf tyB. inv wf. inv H2.
    have agr':=era_sta_agree_subst agr.
    have ihB:=sta_substitution tyB (sta_agree_subst_ty (sta_agree_subst_ty agr' H5) H3).
    have ihP:=sta_substitution tyP agr'.
    have{}ihH:=ihH _ _ _ _ agr.
    apply: era_rw.
    asimpl in ihB.
    replace A.[σ1 >> ren (+1)] with A.[σ1].[ren (+1)] in ihB by autosubst.
    replace m.[σ1 >> ren (+1)] with m.[σ1].[ren (+1)] in ihB by autosubst.
    exact: ihB.
    asimpl. asimpl in ihH...
    asimpl in ihP... }
  { move=>Γ Δ A B m m' s eq tym ihm tyB Γ1 Δ1 σ1 σ2 agr.
    apply: era_conv.
    apply: sta_conv_subst...
    apply: ihm...
    have:=sta_substitution tyB (era_sta_agree_subst agr).
    asimpl... }
Qed.

Lemma era_subst0 Γ Δ m m' n A B :
  (A :: Γ) ; _: Δ ⊢ m ~ m' : B -> Γ ⊢ n : A -> Γ ; Δ ⊢ m.[n/] ~ m'.[Box/] : B.[n/].
Proof with eauto using era_agree_subst_refl.
  move=>tym tyn.
  have wf:=dyn_type_wf (era_dyn_type tym). inv wf.
  apply: era_substitution...
  apply: era_agree_subst_wk0...
  by asimpl.
Qed.

Lemma era_subst1 Γ Δ1 Δ2 Δ m m' n n' A B s :
  Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  (A :: Γ) ; A :{s} Δ1 ⊢ m ~ m' : B -> Γ ; Δ2 ⊢ n ~ n' : A -> Γ ; Δ ⊢ m.[n/] ~ m'.[n'/] : B.[n/].
Proof with eauto using era_agree_subst_refl.
  move=>k mrg tym tyn.
  have wf:=dyn_type_wf (era_dyn_type tym). inv wf.
  apply: era_substitution...
  apply: era_agree_subst_wk1...
  by asimpl.
Qed.

Lemma era_esubst0 Γ Δ m m' n n' v A B B' :
  m' = m.[v/] ->
  n' = n.[Box/] ->
  B' = B.[v/] ->
  (A :: Γ) ; _: Δ ⊢ m ~ n : B -> Γ ⊢ v : A ->
  Γ ; Δ ⊢ m' ~ n' : B'.
Proof.
  move=>*; subst. apply: era_subst0; eauto.
Qed.

Lemma era_esubst1 Γ Δ1 Δ2 Δ m m' n n' v v' A B B' s :
  m' = m.[v/] ->
  n' = n.[v'/] ->
  B' = B.[v/] ->
  Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  (A :: Γ) ; A :{s} Δ1 ⊢ m ~ n : B ->
  Γ ; Δ2 ⊢ v ~ v' : A ->
  Γ ; Δ ⊢ m' ~ n' : B'.
Proof.
  move=>*; subst. apply: era_subst1; eauto.
Qed.

Lemma era_ctx_conv0 Γ Δ m m' A B C s :
  B === A ->
  Γ ⊢ B : Sort s -> (A :: Γ) ; _: Δ ⊢ m ~ m' : C -> (B :: Γ) ; _: Δ ⊢ m ~ m' : C.
Proof with eauto using dyn_wf, era_agree_subst_refl.
  move=>eq tyB tym.
  have wf:=dyn_type_wf (era_dyn_type tym). inv wf.
  have:(B :: Γ) ; _: Δ ⊢ m.[ids] ~ m'.[ids] : C.[ids].
  apply: era_substitution...
  apply: era_agree_subst_conv0...
  apply: sta_eweaken...
  asimpl...
  asimpl...
  asimpl...
Qed.

Lemma era_ctx_conv1 Γ Δ m m' A B C s :
  B === A ->
  Γ ⊢ B : Sort s -> (A :: Γ) ; A :{s} Δ ⊢ m ~ m' : C -> (B :: Γ) ; B :{s} Δ ⊢ m ~ m' : C.
Proof with eauto using dyn_wf, era_agree_subst_refl.
  move=>eq tyA tym.
  have wf:=dyn_type_wf (era_dyn_type tym). inv wf.
  have:(B :: Γ) ; B :{s} Δ ⊢ m.[ids] ~ m'.[ids] : C.[ids].
  apply: era_substitution...
  apply: era_agree_subst_conv1...
  apply: sta_eweaken...
  asimpl...
  asimpl...
  asimpl...
Qed.
