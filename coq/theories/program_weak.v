(* This file presents the weakening lemmas for the program level. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_weak program_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Relation to strengthen induction for generalized renaming lemma. *)
Inductive program_agree_ren : (var -> var) ->
  logical_ctx -> program_ctx -> logical_ctx -> program_ctx -> Prop :=
| program_agree_ren_nil ξ :
  program_agree_ren ξ nil nil nil nil
| program_agree_ren_ty Γ Γ' Δ Δ' ξ m s :
  Γ ⊢ m : Sort s ->
  program_agree_ren ξ Γ Δ Γ' Δ' ->
  program_agree_ren (upren ξ)
    (m :: Γ) (m :{s} Δ) (m.[ren ξ] :: Γ') (m.[ren ξ] :{s} Δ')
| program_agree_ren_n Γ Γ' Δ Δ' ξ m s :
  Γ ⊢ m : Sort s ->
  program_agree_ren ξ Γ Δ Γ' Δ' ->
  program_agree_ren (upren ξ)
    (m :: Γ) (_: Δ) (m.[ren ξ] :: Γ') (_: Δ')
| program_agree_ren_wkU Γ Γ' Δ Δ' ξ m :
  Γ' ⊢ m : Sort U ->
  program_agree_ren ξ Γ Δ Γ' Δ' ->
  program_agree_ren (ξ >>> (+1)) Γ Δ (m :: Γ') (m :U Δ')
| program_agree_ren_wkN Γ Γ' Δ Δ' ξ m s :
  Γ' ⊢ m : Sort s ->
  program_agree_ren ξ Γ Δ Γ' Δ' ->
  program_agree_ren (ξ >>> (+1)) Γ Δ (m :: Γ') (_: Δ').

Lemma program_logical_agree_ren Γ Γ' Δ Δ' ξ :
  program_agree_ren ξ Γ Δ Γ' Δ' -> logical_agree_ren ξ Γ Γ'.
Proof with eauto using logical_agree_ren.
  elim=>{Γ Γ' Δ Δ' ξ}...
Qed.

Lemma program_agree_ren_refl Γ Δ :
  program_wf Γ Δ -> program_agree_ren id Γ Δ Γ Δ.
Proof with eauto using program_agree_ren.
  elim: Γ Δ.
  { move=>Δ wf. inv wf... }
  { move=>A Γ ih Δ wf. inv wf.
    { have agr:=ih _ H1.
      have:program_agree_ren (upren id)
        (A :: Γ) (A :{s} Δ0) (A.[ren id] :: Γ) (A.[ren id] :{s} Δ0)...
      by asimpl. }
    { have agr:=ih _ H1.
      have:program_agree_ren (upren id)
        (A :: Γ) (_: Δ0) (A.[ren id] :: Γ) (_: Δ0)...
      by asimpl. } }
Qed.

Lemma program_agree_ren_key Γ Γ' Δ Δ' ξ s :
  program_agree_ren ξ Γ Δ Γ' Δ' -> Δ ▷ s -> Δ' ▷ s.
Proof with eauto using key.
  move=>agr. elim: agr s=>{Γ Γ' Δ Δ' ξ}...
  { move=>Γ Γ' Δ Δ' ξ m s tym agr ih t k. inv k... }
  { move=>Γ Γ' Δ Δ' ξ _ _ _ agr ih s k. inv k... }
  { move=>Γ Γ' Δ Δ' ξ m _ agr ih [] /ih... }
Qed.

Lemma program_agree_ren_has Γ Γ' Δ Δ' ξ x s A :
  program_agree_ren ξ Γ Δ Γ' Δ' -> program_has Δ x s A -> program_has Δ' (ξ x) s A.[ren ξ].
Proof with eauto using program_agree_ren_key.
  move=>agr. elim: agr x s A=>{Γ Γ' Δ Δ' ξ}.
  { move=>ξ x s A hs. inv hs. }
  { move=>Γ Γ' Δ Δ' ξ m s tym agr ih x t A hs. inv hs; asimpl.
    { replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] by autosubst.
      constructor... }
    { replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)] by autosubst.
      constructor... } }
  { move=>Γ Γ' Δ Δ' ξ m s tym agr ih x t A hs. inv hs; asimpl.
    replace A0.[ren (ξ >>> (+1))] with A0.[ren ξ].[ren (+1)] by autosubst.
     constructor... }
  { move=>Γ Γ' Δ Δ' ξ m tym agr ih x s A hs.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)] by autosubst.
    constructor... }
  { move=>Γ Γ' Δ Δ' ξ m s tym agr ih x t A hs.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)] by autosubst.
    constructor... }
Qed.

Lemma program_agree_ren_merge Γ Γ' Δ Δ' Δ1 Δ2 ξ :
  program_agree_ren ξ Γ Δ Γ' Δ' -> Δ1 ∘ Δ2 => Δ ->
  ∃ Δ1' Δ2',
    Δ1' ∘ Δ2' => Δ' /\
    program_agree_ren ξ Γ Δ1 Γ' Δ1' /\
    program_agree_ren ξ Γ Δ2 Γ' Δ2'.
Proof with eauto 6 using merge, program_agree_ren.
  move=>agr. elim: agr Δ1 Δ2=>{Γ Γ' Δ Δ' ξ}.
  { move=>ξ Δ1 Δ2 mrg. inv mrg.
    exists nil. exists nil... }
  { move=>Γ Γ' Δ Δ' ξ m s tym agr ih Δ1 Δ2 mrg. inv mrg.
    { have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (m.[ren ξ] :U Δ1').
      exists (m.[ren ξ] :U Δ2')... }
    { have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (m.[ren ξ] :L Δ1').
      exists (_: Δ2')... }
    { have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (_: Δ1').
      exists (m.[ren ξ] :L Δ2')... } }
  { move=>Γ Γ' Δ Δ' ξ m s tym agr ih Δ1 Δ2 mrg. inv mrg.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ H2.
      exists (_: Δ1'). exists (_: Δ2')... }
  { move=>Γ Γ' Δ Δ' ξ m tym agr ih Δ1 Δ2 mrg.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ mrg.
    exists (m :U Δ1'). exists (m :U Δ2')... }
  { move=>Γ Γ' Δ Δ' ξ m s tym agr ih Δ1 Δ2 mrg.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=ih _ _ mrg.
    exists (_: Δ1'). exists (_: Δ2')... }
Qed.

Lemma program_agree_weak_wf_nil Γ' Δ' ξ :
  program_agree_ren ξ nil nil Γ' Δ' -> program_wf Γ' Δ'.
Proof with eauto using program_wf.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ agr.
  elim: agr e1 e2=>//{Γ Γ' Δ Δ' ξ}...
Qed.

Lemma program_agree_weak_wf_ty Γ Γ' Δ Δ' A s ξ :
  program_agree_ren ξ (A :: Γ) (A :{s} Δ) Γ' Δ' -> program_wf Γ Δ ->
  (∀ Γ' Δ' ξ, program_agree_ren ξ Γ Δ Γ' Δ' → program_wf Γ' Δ') ->
  program_wf Γ' Δ'.
Proof with eauto using program_wf.
  move e1:(A :: Γ)=>Γ0.
  move e2:(A :{s} Δ)=>Δ0 agr.
  elim: agr A Γ Δ s e1 e2=>//{Γ0 Δ0 Γ' Δ' ξ}...
  move=>Γ Γ' Δ Δ' ξ m s tym agr _ A Γ0 Δ0 s0[e1 e2][_ e4 e5]wf h; subst.
  apply: program_wf_ty...
  replace (Sort s) with (Sort s).[ren ξ] by eauto.
  apply: logical_rename...
  apply: program_logical_agree_ren...
Qed.

Lemma program_agree_weak_wf_n Γ Γ' Δ Δ' A ξ :
  program_agree_ren ξ (A :: Γ) (_: Δ) Γ' Δ' -> program_wf Γ Δ ->
  (∀ Γ' Δ' ξ, program_agree_ren ξ Γ Δ Γ' Δ' → program_wf Γ' Δ') ->
  program_wf Γ' Δ'.
Proof with eauto using program_wf.
  move e1:(A :: Γ)=>Γ0.
  move e2:(_: Δ)=>Δ0 agr.
  elim: agr A Γ Δ e1 e2=>//{Γ0 Δ0 Γ' Δ' ξ}...
  move=>Γ Γ' Δ Δ' ξ m s tym agr _ A Γ0 Δ0 [e1 e2][e4]wf h; subst.
  apply: program_wf_n...
  have:=logical_rename tym (program_logical_agree_ren agr).
  asimpl...
Qed.

(* Generalized renaming lemma. *)
Lemma program_rename Γ Γ' Δ Δ' m A ξ :
  Γ ; Δ ⊢ m : A -> program_agree_ren ξ Γ Δ Γ' Δ' -> Γ' ; Δ' ⊢ m.[ren ξ] : A.[ren ξ].
Proof with eauto using
  program_type, logical_agree_ren, program_agree_ren, program_agree_ren_key.
  move=>ty. move: Γ Δ m A ty Γ' Δ' ξ.
  apply:(@program_type_mut _
    (fun Γ Δ wf => forall Γ' Δ' ξ, program_agree_ren ξ Γ Δ Γ' Δ' -> program_wf Γ' Δ')).
  { move=>Γ Δ x s A wf h shs dhs Γ' Δ' ξ agr. asimpl.
    apply: program_var...
    apply: logical_agree_ren_has...
    apply: program_logical_agree_ren...
    apply: program_agree_ren_has... }
  { move=>Γ Δ A B m s k tym ihm Γ' Δ' ξ agr. asimpl.
    have wf:=program_type_wf tym. inv wf.
    apply: program_lam0... }
  { move=>Γ Δ A B m s t k tym ihm Γ' Δ' ξ agr. asimpl.
    have wf:=program_type_wf tym. inv wf.
    apply: program_lam1... }
  { move=>Γ Δ A B m n s tym ihm tyn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have{}ihm:=ihm _ _ _ agr.
    have{}ihn:=logical_rename tyn (program_logical_agree_ren agr).
    apply: program_app0...
    asimpl in ihm... }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    replace B.[n.[ren ξ] .: ren ξ] with B.[ren (upren ξ)].[n.[ren ξ]/]
      by autosubst.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=program_agree_ren_merge agr mrg.
    have{}ihm:=ihm _ _ _ agr1.
    have{}ihn:=ihn _ _ _ agr2.
    apply: program_app1...
    asimpl in ihm... }
  { move=>Γ Δ A B m n t tyS tym ihm tyn Γ' Δ' ξ agr. asimpl.
    have{}ihm:=ihm _ _ _ agr.
    have{}ihn:=logical_rename tyn (program_logical_agree_ren agr).
    have{}ihS:=logical_rename tyS (program_logical_agree_ren agr).
    apply: program_pair0...
    asimpl in ihS...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B m n t mrg tyS tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=program_agree_ren_merge agr mrg.
    have{}ihm:=ihm _ _ _ agr1.
    have{}ihn:=ihn _ _ _ agr2.
    have{}ihS:=logical_rename tyS (program_logical_agree_ren agr).
    apply: program_pair1...
    asimpl in ihS...
    asimpl. asimpl in ihn... }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    have wf:=logical_type_wf tyC. inv wf.
    have wf:=program_type_wf tyn. inv wf. inv H4.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=program_agree_ren_merge agr mrg.
    have{}ihC:=logical_rename tyC (logical_agree_ren_cons H2 (program_logical_agree_ren agr)).
    have{}ihm:=ihm _ _ _ agr1.
    have/ihn{}ihn:program_agree_ren (upren (upren ξ)) (B :: A :: Γ) (_: A :{r} Δ2)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ') (_: A.[ren ξ] :{r} Δ2')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair0 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair0 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=program_letin0 mrg' ihC ihm ihn.
    by autosubst. }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn Γ' Δ' ξ agr. asimpl.
    have wf:=logical_type_wf tyC. inv wf.
    have wf:=program_type_wf tyn. inv wf. inv H4.
    have[Δ1'[Δ2'[mrg'[agr1 agr2]]]]:=program_agree_ren_merge agr mrg.
    have{}ihC:=logical_rename tyC (logical_agree_ren_cons H2 (program_logical_agree_ren agr)).
    have{}ihm:=ihm _ _ _ agr1.
    have/ihn{}ihn:program_agree_ren (upren (upren ξ)) (B :: A :: Γ) (B :{r2} A :{r1} Δ2)
      (B.[ren (upren ξ)] :: A.[ren ξ] :: Γ') (B.[ren (upren ξ)] :{r2} A.[ren ξ] :{r1} Δ2')...
    asimpl in ihC.
    asimpl in ihm.
    replace C.[Pair1 (Var 1) (Var 0) t .: ren (+2)].[ren (upren (upren ξ))]
      with C.[ren (upren ξ)].[Pair1 (Var 1) (Var 0) t .: ren (+2)]
        in ihn by autosubst.
    have:=program_letin1 mrg' ihC ihm ihn.
    by autosubst. }
  { move=>Γ Δ A B m n t k tym ihm tyn ihn Γ' Δ' ξ agr. asimpl. apply:program_apair... }
  { move=>Γ Δ A B m t tym ihm Γ' Δ' ξ agr. asimpl. apply:program_fst... }
  { move=>Γ Δ A B m t tym ihm Γ' Δ' ξ agr. asimpl. apply:program_snd... }
  { move=>Γ Δ A B H P m n s tyB tyH ihH tyP Γ' Δ' ξ agr. asimpl.
    have wf:=logical_type_wf tyB. inv wf. inv H2.
    have ihP:=logical_rename tyP (program_logical_agree_ren agr).
    have agr':=program_logical_agree_ren agr.
    have{}agr':
      logical_agree_ren (upren (upren ξ))
        (Id A.[ren (+1)] m.[ren (+1)] (Var 0) :: A :: Γ)
        ((Id A.[ren (+1)] m.[ren (+1)] (Var 0)).[ren (upren ξ)] :: A.[ren ξ] :: Γ')...
    have ihB:=logical_rename tyB agr'.
    have{}ihH:=ihH _ _ _ agr.
    asimpl in ihP.
    asimpl in ihB.
    asimpl in ihH.
    replace A.[ren (ξ >>> (+1))] with A.[ren ξ].[ren (+1)] in ihB by autosubst.
    replace m.[ren (ξ >>> (+1))] with m.[ren ξ].[ren (+1)] in ihB by autosubst.
    have pf:=program_rw ihB. asimpl in pf.
    have:=pf _ _ _ _ ihH ihP.
    by autosubst. }
  { move=>Γ Δ A B m s eq tym ihm tyB Γ' Δ' ξ agr.
    apply: program_conv.
    apply: logical_conv_subst...
    apply: ihm...
    have:=logical_rename tyB (program_logical_agree_ren agr).
    asimpl... }
  { exact: program_agree_weak_wf_nil... }
  { move=>Γ Δ A s wf ih tyA Γ' Δ' ξ agr.
    apply: program_agree_weak_wf_ty... }
  { move=>Γ Δ A s wf ih tyA Γ' Δ' ξ agr.
    apply: program_agree_weak_wf_n... }
Qed.

Lemma program_rename_wf Γ Γ' Δ Δ' ξ :
  program_wf Γ Δ -> program_agree_ren ξ Γ Δ Γ' Δ' -> program_wf Γ' Δ'.
Proof with eauto using program_wf.
  move=>wf. elim: wf Γ' Δ' ξ=>{Γ Δ}.
  { move=>*. apply: program_agree_weak_wf_nil... }
  { move=>*. apply: program_agree_weak_wf_ty... }
  { move=>*. apply: program_agree_weak_wf_n... }
Qed.

(* Lemma 3 (Program 0-Weakening) *)
Lemma program_weaken0 Γ Δ m A B s :
  Γ ⊢ B : Sort s ->
  Γ ; Δ ⊢ m : A ->
  (B :: Γ) ; _: Δ ⊢ m.[ren (+1)] : A.[ren (+1)].
Proof with eauto using program_agree_ren, program_agree_ren_refl.
  move=>tyB tym. apply: program_rename...
Qed.

(* Lemma 4 (Program 1-Weakening) *)
Lemma program_weaken1 Γ Δ m A B :
  Γ ⊢ B : Sort U ->
  Γ ; Δ ⊢ m : A ->
  (B :: Γ) ; B :U Δ ⊢ m.[ren (+1)] : A.[ren (+1)].
Proof with eauto using program_agree_ren, program_agree_ren_refl.
  move=>tyB tym. apply: program_rename...
Qed.

(* Alternative statement more suitable for certain Coq tactics *)
Lemma program_eweaken0 Γ Δ m m' A A' B s :
  m' = m.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ B : Sort s ->
  Γ ; Δ ⊢ m : A ->
  (B :: Γ) ; _: Δ ⊢ m' : A'.
Proof.
  move=>*; subst. apply: program_weaken0; eauto.
Qed.

(* Alternative statement more suitable for certain Coq tactics *)
Lemma program_eweaken1 Γ Δ m m' A A' B :
  m' = m.[ren (+1)] ->
  A' = A.[ren (+1)] ->
  Γ ⊢ B : Sort U ->
  Γ ; Δ ⊢ m : A ->
  (B :: Γ) ; B :U Δ ⊢ m' : A'.
Proof.
  move=>*; subst. exact: program_weaken1.
Qed.
