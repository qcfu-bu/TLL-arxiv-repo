From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_subst sta_inv dyn_valid dyn_weak.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Reserved Notation "Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2" (at level 50, Δ1, σ, Γ2 at next level).
Inductive dyn_agree_subst :
  sta_ctx -> dyn_ctx -> (var -> term) -> sta_ctx -> dyn_ctx -> Prop :=
| dyn_agree_subst_nil σ :
  nil ; nil ⊢ σ ⊣ nil ; nil
| dyn_agree_subst_ty Γ1 Δ1 σ Γ2 Δ2 A s :
  Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 ->
  Γ2 ⊢ A : Sort s ->
  (A.[σ] :: Γ1) ; (A.[σ] :{s} Δ1) ⊢ up σ ⊣ (A :: Γ2) ; (A :{s} Δ2)
| dyn_agree_subst_n Γ1 Δ1 σ Γ2 Δ2 A s :
  Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 ->
  Γ2 ⊢ A : Sort s ->
  (A.[σ] :: Γ1) ; (_: Δ1) ⊢ up σ ⊣ (A :: Γ2) ; (_: Δ2)
| dyn_agree_subst_wk0 Γ1 Δ1 σ Γ2 Δ2 n A :
  Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 ->
  Γ1 ⊢ n : A.[σ] ->
  Γ1 ; Δ1 ⊢ n .: σ ⊣ (A :: Γ2) ; (_: Δ2)
| dyn_agree_subst_wk1 Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s :
  Δb ▷ s ->
  Δa ∘ Δb => Δ1 ->
  Γ1 ; Δa ⊢ σ ⊣ Γ2 ; Δ2 ->
  Γ1 ; Δb ⊢ n : A.[σ] ->
  Γ1 ; Δ1 ⊢ n .: σ ⊣ (A :: Γ2) ; (A :{s} Δ2)
| dyn_agree_subst_conv0 Γ1 Δ1 σ Γ2 Δ2 A B s :
  A === B ->
  Γ1 ⊢ B.[ren (+1)].[σ] : Sort s ->
  Γ2 ⊢ B : Sort s ->
  Γ1 ; Δ1 ⊢ σ ⊣ (A :: Γ2) ; (_: Δ2) ->
  Γ1 ; Δ1 ⊢ σ ⊣ (B :: Γ2) ; (_: Δ2)
| dyn_agree_subst_conv1 Γ1 Δ1 σ Γ2 Δ2 A B s :
  A === B ->
  Γ1 ⊢ B.[ren (+1)].[σ] : Sort s ->
  Γ2 ⊢ B : Sort s ->
  Γ1 ; Δ1 ⊢ σ ⊣ (A :: Γ2) ; (A :{s} Δ2) ->
  Γ1 ; Δ1 ⊢ σ ⊣ (B :: Γ2) ; (B :{s} Δ2)
where "Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2" := (dyn_agree_subst Γ1 Δ1 σ Γ2 Δ2).

Lemma dyn_agree_subst_key Γ1 Γ2 Δ1 Δ2 σ s :
  Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> Δ2 ▷ s -> Δ1 ▷ s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Γ1 Γ2 Δ1 Δ2 σ}...
  { move=>Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA r k. inv k... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA r k. inv k... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 n A agr ih tyn s k. inv k... }
  { move=>Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s k1 mrg agr ih tyn r k2. inv k2...
    apply: key_merge...
    apply: key_impure. }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih r k. inv k... }
Qed.

Lemma dyn_sta_agree_subst Γ1 Γ2 Δ1 Δ2 σ :
  Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> Γ1 ⊢ σ ⊣ Γ2.
Proof with eauto using sta_agree_subst.
  elim=>{Γ1 Γ2 Δ1 Δ2 σ}...
Qed.

Lemma dyn_agree_subst_refl Γ Δ : dyn_wf Γ Δ -> Γ ; Δ ⊢ ids ⊣ Γ ; Δ.
Proof with eauto using dyn_agree_subst.
  elim: Γ Δ.
  { move=>Δ wf. inv wf... }
  { move=>A Γ ih Δ wf. inv wf.
    { have agr:=ih _ H1.
      have:(A.[ids] :: Γ); A.[ids] :{s} Δ0 ⊢ up ids ⊣ (A :: Γ); A :{s} Δ0...
      by asimpl. }
    { have agr:=ih _ H1.
      have:(A.[ids] :: Γ); _: Δ0 ⊢ up ids ⊣ (A :: Γ); _: Δ0...
      by asimpl. } }
Qed.
#[global] Hint Resolve dyn_agree_subst_refl.

Lemma dyn_agree_subst_has Γ1 Γ2 σ Δ1 Δ2 x s A :
  Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> dyn_wf Γ1 Δ1 -> dyn_has Δ2 x s A -> Γ1 ; Δ1 ⊢ (σ x) : A.[σ].
Proof with eauto using dyn_agree_subst, dyn_agree_subst_key.
  move=>agr. elim: agr x s A=>{Γ1 Γ2 σ Δ1 Δ2}...
  { move=>σ x s A wf hs. inv hs. }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA x t B wf hs.
    inv wf. inv hs; asimpl.
    replace A.[σ >> ren (+1)] with A.[σ].[ren (+1)] by autosubst.
    apply: dyn_var; constructor...
    replace A0.[σ >> ren (+1)] with A0.[σ].[ren (+1)] by autosubst.
    apply: dyn_eweakenU... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA x t B wf hs.
    inv wf. inv hs; asimpl...
    replace A0.[σ >> ren (+1)] with A0.[σ].[ren (+1)]
      by autosubst.
    apply: dyn_eweakenN... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 n A agr ih tyn x s B wf hs. inv hs; asimpl... }
  { move=>Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s k mrg agr ih tyn x t B wf hs.
    inv hs; asimpl.
    { have ka:=dyn_agree_subst_key agr H5.
      have->//:=merge_pureL mrg ka. }
    { have->:=merge_pureR mrg k.
      apply: ih...
      have[]//:=dyn_wf_inv mrg wf. } }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih x t C wf hs. inv hs.
    { apply: dyn_conv.
      apply: sta_conv_subst.
      apply: sta_conv_subst...
      apply: ih...
      constructor...
      exact: tyB1. }
    { apply: ih...
      constructor... } }
Qed.

Lemma dyn_agree_subst_merge Γ1 Γ2 Δ1 Δ2 Δa Δb σ :
  Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> Δa ∘ Δb => Δ2 ->
  exists Δa' Δb',
    Δa' ∘ Δb' => Δ1 /\ Γ1 ; Δa' ⊢ σ ⊣ Γ2 ; Δa /\ Γ1 ; Δb' ⊢ σ ⊣ Γ2 ; Δb.
Proof with eauto 6 using merge, dyn_agree_subst, dyn_agree_subst_key.
  move=>agr. elim: agr Δa Δb=>{Γ1 Γ2 Δ1 Δ2 σ}.
  { move=>σ Δa Δb mrg. inv mrg.
    exists nil. exists nil... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA Δa Δb mrg. inv mrg.
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (A.[σ] :U Δa). exists (A.[σ] :U Δb)... }
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (A.[σ] :L Δa). exists (_: Δb)... }
    { have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
      exists (_: Δa). exists (A.[σ] :L Δb)... } }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A s agr ih tyA Δa Δb mrg. inv mrg.
    have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
    exists (_: Δa). exists (_: Δb)... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 n A agr ih tyn Δa Δb mrg. inv mrg.
    have[Δa[Δb[mrg[agra agrb]]]]:=ih _ _ H2.
    exists Δa. exists Δb... }
  { move=>Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s k mrg agr ih tyn Δa' Δb' mrg'. inv mrg'.
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ H2.
      have[Δc[mrg1 mrg2]]:=merge_splitL mrg mrg'.
      exists Δc. exists Δb'.
      repeat split...
      apply: dyn_agree_subst_wk1...
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
  { move=>Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_null H2).
    exists Δa'. exists Δb'... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih Δa Δb mrg. inv mrg.
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_left A H2).
      exists Δa'. exists Δb'... }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_right1 A H2).
      exists Δa'. exists Δb'... }
    { have[Δa'[Δb'[mrg'[agra agrb]]]]:=ih _ _ (merge_right2 A H2).
      exists Δa'. exists Δb'... } }
Qed.

Lemma dyn_agree_subst_wf_nil Γ1 Δ1 σ : Γ1; Δ1 ⊢ σ ⊣ [::]; [::] → dyn_wf Γ1 Δ1.
Proof with eauto using dyn_wf.
  move e1:(nil)=>Γ2.
  move e2:(nil)=>Δ2 agr.
  elim: agr e1 e2=>//{Γ1 Γ2 Δ1 Δ2 σ}...
Qed.

Lemma dyn_agree_subst_wf_ty Γ1 Γ2 Δ1 Δ2 A s σ :
  Γ1; Δ1 ⊢ σ ⊣ (A :: Γ2); A :{s} Δ2 -> dyn_wf Γ2 Δ2 ->
  (∀ Γ1 Δ1 σ, Γ1; Δ1 ⊢ σ ⊣ Γ2; Δ2 → dyn_wf Γ1 Δ1) ->
  dyn_wf Γ1 Δ1.
Proof with eauto using dyn_wf.
  move e1:(A :: Γ2)=>Γ0.
  move e2:(A :{s} Δ2)=>Δ0 agr.
  elim: agr A Γ2 Δ2 s e1 e2=>//{Γ0 Δ0 Γ1 Δ1 σ}...
  { move=>Γ1 Δ1 σ Γ2 Δ2 A s agr _ tyA A0 Γ0 Δ0 s0[e1 e2][_ e3 e4]wf h; subst.
    apply: dyn_wf_ty...
    replace (Sort s) with (Sort s).[σ] by eauto.
    apply: sta_substitution...
    apply: dyn_sta_agree_subst... }
  { move=>Γ1 Γ2 σ Δ1 Δ2 Δa Δb n A s k mrg agr _ tyn A0 Γ0 Δ0 s0
      [e1 e2][_ e3 e4]wf h; subst.
    apply: dyn_wf_merge... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih A0 Γ0 Δ0 s0
      [e1 e2][_ e3 e4]wf h; subst... }
Qed.

Lemma dyn_agree_subst_wf_n Γ1 Γ2 Δ1 Δ2 A σ :
  Γ1; Δ1 ⊢ σ ⊣ (A :: Γ2); _: Δ2 -> dyn_wf Γ2 Δ2 ->
  (∀ Γ1 Δ1 σ, Γ1; Δ1 ⊢ σ ⊣ Γ2; Δ2 → dyn_wf Γ1 Δ1) ->
  dyn_wf Γ1 Δ1.
Proof with eauto using dyn_wf.
  move e1:(A :: Γ2)=>Γ0.
  move e2:(_: Δ2)=>Δ0 agr.
  elim: agr A Γ2 Δ2 e1 e2=>//{Γ0 Δ0 Γ1 Δ1 σ}...
  { move=>Γ1 Δ1 σ Γ2 Δ2 A s agr _ tyA A0 Γ0 Δ0[e1 e2][e3]wf h; subst.
    apply: dyn_wf_n...
    have:=sta_substitution tyA (dyn_sta_agree_subst agr).
    asimpl... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 n A agr ih tyn A0 Γ0 Δ0[e1 e2][e3]wf h; subst... }
  { move=>Γ1 Δ1 σ Γ2 Δ2 A B s eq tyB1 tyB2 agr ih A0 Γ0 Δ0
      [e1 e2][e3]wf h; subst... }
Qed.

Lemma dyn_substitution Γ1 Γ2 m A Δ1 Δ2 σ :
  Γ2 ; Δ2 ⊢ m : A -> Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> Γ1 ; Δ1 ⊢ m.[σ] : A.[σ].
Proof with eauto using dyn_agree_subst, dyn_agree_subst_key, dyn_type.
  move=>ty. move:Γ2 Δ2 m A ty Γ1 Δ1 σ.
  apply:(@dyn_type_mut _ (fun Γ2 Δ2 wf => forall Γ1 Δ1 σ, Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> dyn_wf Γ1 Δ1)).
  { move=>Γ Δ x s A wf h shs dhs Γ1 Δ1 σ agr. asimpl.
    apply: dyn_agree_subst_has... }
  { move=>Γ Δ A B m s k tym ihm Γ1 Δ1 σ agr. asimpl.
    have wf:=dyn_type_wf tym. inv wf.
    apply: dyn_lam0... }
  { move=>Γ Δ A B m s t k tym ihm Γ1 Δ1 σ agr. asimpl.
    have wf:=dyn_type_wf tym. inv wf.
    apply: dyn_lam1... }
  { move=>Γ Δ A B m n s tym ihm tyn Γ1 Δ1 σ agr. asimpl.
    replace B.[n.[σ] .: σ] with B.[up σ].[n.[σ]/] by autosubst.
    have{}ihm:=ihm _ _ _ agr.
    apply: dyn_app0...
    have//:=sta_substitution tyn (dyn_sta_agree_subst agr). }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn Γ1 Δ0 σ agr. asimpl.
    replace B.[n.[σ] .: σ] with B.[up σ].[n.[σ]/] by autosubst.
    have[Δa[Δb[mrg0[agra agrb]]]]:=dyn_agree_subst_merge agr mrg.
    have{}ihm:=ihm _ _ _ agra.
    have{}ihn:=ihn _ _ _ agrb.
    apply: dyn_app1... }
  { move=>Γ Δ A B m n t tyS tym ihm tyn Γ1 Δ1 σ agr. asimpl.
    have{}ihS:=sta_substitution tyS (dyn_sta_agree_subst agr).
    have{}ihm:=ihm _ _ _ agr.
    have{}ihn:=sta_substitution tyn (dyn_sta_agree_subst agr).
    apply: dyn_pair0...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B m n t mrg tyS tym ihm tyn ihn Γ1 Δ0 σ agr. asimpl.
    have[Δa[Δb[mrg0[agra agrb]]]]:=dyn_agree_subst_merge agr mrg.
    have{}ihS:=sta_substitution tyS (dyn_sta_agree_subst agr).
    have{}ihm:=ihm _ _ _ agra.
    have{}ihn:=ihn _ _ _ agrb.
    apply: dyn_pair1...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn Γ1 Δ0 σ agr. asimpl.
    have[Δa[Δb[mrg0[agra agrb]]]]:=dyn_agree_subst_merge agr mrg.
    replace C.[m.[σ] .: σ] with C.[up σ].[m.[σ]/] by autosubst.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf tyn. inv wf. inv H4.
    have{}ihC:=sta_substitution tyC (sta_agree_subst_ty (dyn_sta_agree_subst agr) H2).
    have{}ihm:=ihm _ _ _ agra.
    have{}ihn:=ihn _ _ _ (dyn_agree_subst_n (dyn_agree_subst_ty agrb H8) H5).
    apply: dyn_letin0...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn Γ1 Δ0 σ agr. asimpl.
    have[Δa[Δb[mrg0[agra agrb]]]]:=dyn_agree_subst_merge agr mrg.
    replace C.[m.[σ] .: σ] with C.[up σ].[m.[σ]/] by autosubst.
    have wf:=sta_type_wf tyC. inv wf.
    have wf:=dyn_type_wf tyn. inv wf. inv H4.
    have{}ihC:=sta_substitution tyC (sta_agree_subst_ty (dyn_sta_agree_subst agr) H2).
    have{}ihm:=ihm _ _ _ agra.
    have{}ihn:=ihn _ _ _ (dyn_agree_subst_ty (dyn_agree_subst_ty agrb H8) H6).
    apply: dyn_letin1...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ A B m n t k tym ihm tyn ihn Γ1 Δ1 σ agr. asimpl. apply: dyn_apair... }
  { move=>Γ Δ A B m t tym ihm Γ1 Δ1 σ agr. asimpl. apply: dyn_fst... }
  { move=>Γ Δ A B m t tym ihm Γ1 Δ1 σ agr. asimpl. apply: dyn_snd... }
  { move=>Γ Δ A B H P m n s tyB tyH ihH tyP Γ1 Δ1 σ agr. asimpl.
    replace B.[P.[σ] .: n.[σ] .: σ] with B.[upn 2 σ].[P.[σ],n.[σ]/] by autosubst.
    have wf:=sta_type_wf tyB. inv wf. inv H2.
    have agr':=dyn_sta_agree_subst agr.
    have ihB:=sta_substitution tyB (sta_agree_subst_ty (sta_agree_subst_ty agr' H5) H3).
    have ihP:=sta_substitution tyP agr'.
    have{}ihH:=ihH _ _ _ agr.
    apply: dyn_rw.
    asimpl in ihB.
    replace A.[σ >> ren (+1)] with A.[σ].[ren (+1)] in ihB by autosubst.
    replace m.[σ >> ren (+1)] with m.[σ].[ren (+1)] in ihB by autosubst.
    exact: ihB.
    asimpl. asimpl in ihH...
    asimpl in ihP... }
  { move=>Γ Δ A B m s eq tym ihm tyB Γ1 Δ1 σ agr.
    apply: dyn_conv.
    apply: sta_conv_subst...
    apply: ihm...
    have:=sta_substitution tyB (dyn_sta_agree_subst agr).
    asimpl... }
  { exact: dyn_agree_subst_wf_nil. }
  { move=>Γ Δ A s wf h tyA Γ1 Δ1 σ agr.
    apply: dyn_agree_subst_wf_ty... }
  { move=>Γ Δ A s wf ih tyA Γ1 Δ1 σ agr.
    apply: dyn_agree_subst_wf_n... }
Qed.

Lemma dyn_substitution_wf Γ1 Γ2 Δ1 Δ2 σ :
  dyn_wf Γ2 Δ2 -> Γ1 ; Δ1 ⊢ σ ⊣ Γ2 ; Δ2 -> dyn_wf Γ1 Δ1.
Proof with eauto using dyn_wf.
  move=>wf. elim: wf Γ1 Δ1 σ=>{Γ2 Δ2}.
  { move=>*. apply: dyn_agree_subst_wf_nil... }
  { move=>*. apply: dyn_agree_subst_wf_ty... }
  { move=>*. apply: dyn_agree_subst_wf_n... }
Qed.

Lemma dyn_subst0 Γ Δ m n A B :
  (A :: Γ) ; _: Δ ⊢ m : B -> Γ ⊢ n : A -> Γ ; Δ ⊢ m.[n/] : B.[n/].
Proof with eauto using dyn_agree_subst_refl.
  move=>tym tyn.
  have wf:=dyn_type_wf tym. inv wf.
  apply: dyn_substitution...
  apply: dyn_agree_subst_wk0...
  by asimpl.
Qed.

Lemma dyn_subst1 Γ Δ1 Δ2 Δ m n A B s :
  Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  (A :: Γ) ; A :{s} Δ1 ⊢ m : B -> Γ ; Δ2 ⊢ n : A -> Γ ; Δ ⊢ m.[n/] : B.[n/].
Proof with eauto using dyn_agree_subst_refl.
  move=>k mrg tym tyn.
  have wf:=dyn_type_wf tym. inv wf.
  apply: dyn_substitution...
  apply: dyn_agree_subst_wk1...
  by asimpl.
Qed.

Lemma dyn_esubst0 Γ Δ m m' n A B B' :
  m' = m.[n/] ->
  B' = B.[n/] ->
  (A :: Γ) ; _: Δ ⊢ m : B -> Γ ⊢ n : A -> Γ ; Δ ⊢ m': B'.
Proof.
  move=>*; subst. apply: dyn_subst0; eauto.
Qed.

Lemma dyn_esubst1 Γ Δ1 Δ2 Δ m m' n A B B' s :
  m' = m.[n/] ->
  B' = B.[n/] ->
  Δ2 ▷ s -> Δ1 ∘ Δ2 => Δ ->
  (A :: Γ) ; A :{s} Δ1 ⊢ m : B -> Γ ; Δ2 ⊢ n : A -> Γ ; Δ ⊢ m' : B'.
Proof.
  move=>*; subst. apply: dyn_subst1; eauto.
Qed.

Lemma dyn_ctx_conv0 Γ Δ m A B C s :
  B === A ->
  Γ ⊢ B : Sort s -> (A :: Γ) ; _: Δ ⊢ m : C -> (B :: Γ) ; _: Δ ⊢ m : C.
Proof with eauto using dyn_wf, dyn_agree_subst_refl.
  move=>eq tyB tym.
  have wf:=dyn_type_wf tym. inv wf.
  have:(B :: Γ) ; _: Δ ⊢ m.[ids] : C.[ids].
  apply: dyn_substitution...
  apply: dyn_agree_subst_conv0...
  apply: sta_eweaken...
  asimpl...
  asimpl...
  asimpl...
Qed.

Lemma dyn_ctx_conv1 Γ Δ m A B C s :
  B === A ->
  Γ ⊢ B : Sort s -> (A :: Γ) ; A :{s} Δ ⊢ m : C -> (B :: Γ) ; B :{s} Δ ⊢ m : C.
Proof with eauto using dyn_wf, dyn_agree_subst_refl.
  move=>eq tyB tym.
  have wf:=dyn_type_wf tym. inv wf.
  have:(B :: Γ) ; B :{s} Δ ⊢ m.[ids] : C.[ids].
  apply: dyn_substitution...
  apply: dyn_agree_subst_conv1...
  apply: sta_eweaken...
  asimpl...
  asimpl...
  asimpl...
Qed.
