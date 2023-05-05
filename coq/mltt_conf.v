From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS mltt_step.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive pstep : term -> term -> Prop :=
| pstep_var x :
  pstep (Var x) (Var x)
| pstep_ty :
  pstep Ty Ty
| pstep_pi A A' B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Pi A B) (Pi A' B')
| pstep_lam A A' m m' :
  pstep A A' ->
  pstep m m' ->
  pstep (Lam A m) (Lam A' m')
| pstep_app m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App m n) (App m' n')
| pstep_beta A m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (App (Lam A m) n) (m'.[n'/])
| pstep_sig A A' B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Sig A B) (Sig A' B')
| pstep_dpair m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (DPair m n) (DPair m' n')
| pstep_letin A A' m m' n n' :
  pstep A A' ->
  pstep m m' ->
  pstep n n' ->
  pstep (LetIn A m n) (LetIn A' m' n')
| pstep_iota A m1 m1' m2 m2' n n' :
  pstep m1 m1' ->
  pstep m2 m2' ->
  pstep n n' ->
  pstep (LetIn A (DPair m1 m2) n) (n'.[m2',m1'/])
| pstep_tuple A A' B B' :
  pstep A A' ->
  pstep B B' ->
  pstep (Tuple A B) (Tuple A' B')
| pstep_pair m m' n n' :
  pstep m m' ->
  pstep n n' ->
  pstep (Pair m n) (Pair m' n')
| pstep_fst m m' :
  pstep m m' ->
  pstep (Fst m) (Fst m')
| pstep_snd m m' :
  pstep m m' ->
  pstep (Snd m) (Snd m')
| pstep_proj1 m m' n :
  pstep m m' ->
  pstep (Fst (Pair m n)) m'
| pstep_proj2 m n n' :
  pstep n n' ->
  pstep (Snd (Pair m n)) n'
| pstep_id A A' m m' n n' :
  pstep A A' ->
  pstep m m' ->
  pstep n n' ->
  pstep (Id A m n) (Id A' m' n')
| pstep_refl m m' :
  pstep m m' ->
  pstep (Refl m) (Refl m')
| pstep_rw A A' H H' P P' :
  pstep A A' ->
  pstep H H' ->
  pstep P P' ->
  pstep (Rw A H P) (Rw A' H' P')
| pstep_rwE A H H' m :
  pstep H H' ->
  pstep (Rw A H (Refl m)) H'.

Definition sred σ τ := forall x : var, (σ x) ~>* (τ x).

Lemma mltt_step_subst σ m n : m ~> n -> m.[σ] ~> n.[σ].
Proof.
  move=> st. elim: st σ=>/={m n}; eauto using mltt_step.
  { move=> A m n σ.
    replace (m.[n/].[σ]) with (m.[up σ].[n.[σ]/]).
    apply mltt_step_beta. autosubst. }
  { move=>A m1 m2 n σ.
    replace (n.[m2,m1/].[σ]) with (n.[upn 2 σ].[m2.[σ],m1.[σ]/]).
    apply: mltt_step_iota. autosubst. }
Qed.

Lemma mltt_red_app m m' n n' :
  m ~>* m' -> n ~>* n' -> App m n ~>* App m' n'.
Proof.
  move=> r1 r2.
  apply: (star_trans (App m' n)).
  apply: (star_hom (App^~ n)) r1=>x y. exact: mltt_step_appL.
  apply: star_hom r2. exact: mltt_step_appR.
Qed.

Lemma mltt_red_lam A A' m m' :
  A ~>* A' -> m ~>* m' -> Lam A m ~>* Lam A' m'.
Proof.
  move=> r1 r2.
  apply: (star_trans (Lam A' m)).
  apply: (star_hom (Lam^~ m)) r1=>x y. exact: mltt_step_lamL.
  apply: (star_hom (Lam A')) r2=>x y. exact: mltt_step_lamR.
Qed.

Lemma mltt_red_pi A A' B B' :
  A ~>* A' -> B ~>* B' -> Pi A B ~>* Pi A' B'.
Proof.
  move=> r1 r2.
  apply: (star_trans (Pi A' B)).
  apply: (star_hom (Pi^~ B)) r1=>x y. exact: mltt_step_piL.
  apply: (star_hom (Pi A')) r2=>x y. exact: mltt_step_piR.
Qed.

Lemma mltt_red_sig A A' B B' :
  A ~>* A' -> B ~>* B' -> Sig A B ~>* Sig A' B'.
Proof.
  move=> r1 r2.
  apply: (star_trans (Sig A' B)).
  apply: (star_hom (Sig^~ B)) r1=>x y. exact: mltt_step_sigL.
  apply: (star_hom (Sig A')) r2=>x y. exact: mltt_step_sigR.
Qed.

Lemma mltt_red_dpair m m' n n' :
  m ~>* m' -> n ~>* n' -> DPair m n ~>* DPair m' n'.
Proof.
  move=>r1 r2.
  apply: (star_trans (DPair m' n)).
  apply: (star_hom (DPair^~ n)) r1=>x y. exact: mltt_step_dpairL.
  apply: (star_hom (DPair m')) r2=>x y. exact: mltt_step_dpairR.
Qed.

Lemma mltt_red_letin A A' m m' n n' :
  A ~>* A' -> m ~>* m' -> n ~>* n' -> LetIn A m n ~>* LetIn A' m' n'.
Proof.
  move=>r1 r2 r3.
  apply: (star_trans (LetIn A' m n)).
  apply: (star_hom ((LetIn^~ m)^~ n)) r1=>x y. exact: mltt_step_letinA.
  apply: (star_trans (LetIn A' m' n)).
  apply: (star_hom (LetIn A'^~ n)) r2=>x y. exact: mltt_step_letinL.
  apply: (star_hom (LetIn A' m')) r3=>x y. exact: mltt_step_letinR.
Qed.

Lemma mltt_red_tuple A A' B B' :
  A ~>* A' -> B ~>* B' -> Tuple A B ~>* Tuple A' B'.
Proof.
  move=>r1 r2.
  apply: (star_trans (Tuple A' B)).
  apply: (star_hom (Tuple^~ B)) r1=>x y. exact: mltt_step_tupleL.
  apply: (star_hom (Tuple A')) r2=>x y. exact: mltt_step_tupleR.
Qed.

Lemma mltt_red_pair m m' n n' :
  m ~>* m' -> n ~>* n' -> Pair m n ~>* Pair m' n'.
Proof.
  move=>r1 r2.
  apply: (star_trans (Pair m' n)).
  apply: (star_hom (Pair^~ n)) r1=>x y. exact: mltt_step_pairL.
  apply: (star_hom (Pair m')) r2=>x y. exact: mltt_step_pairR.
Qed.

Lemma mltt_red_fst m m' :
  m ~>* m' -> Fst m ~>* Fst m'.
Proof.
  move=>r.
  apply: (star_hom Fst) r=>x y. exact: mltt_step_fst.
Qed.

Lemma mltt_red_snd m m' :
  m ~>* m' -> Snd m ~>* Snd m'.
Proof.
  move=>r.
  apply: (star_hom Snd) r=>x y. exact: mltt_step_snd.
Qed.

Lemma mltt_red_id A A' m m' n n' :
  A ~>* A' -> m ~>* m' -> n ~>* n' -> Id A m n ~>* Id A' m' n'.
Proof.
  move=>r1 r2 r3.
  apply: (star_trans (Id A' m n)).
  apply: (star_hom ((Id^~ m)^~ n)) r1=>x y. exact: mltt_step_idA.
  apply: (star_trans (Id A' m' n)).
  apply: (star_hom (Id A'^~ n)) r2=>x y. exact: mltt_step_idL.
  apply: (star_hom (Id A' m')) r3=>x y. exact: mltt_step_idR.
Qed.

Lemma mltt_red_refl m m' :
  m ~>* m' -> Refl m ~>* Refl m'.
Proof.
  move=>r.
  apply: (star_hom Refl) r=>x y. exact: mltt_step_refl.
Qed.

Lemma mltt_red_rw A A' H H' P P' :
  A ~>* A' -> H ~>* H' -> P ~>* P' -> Rw A H P ~>* Rw A' H' P'.
Proof.
  move=>r1 r2 r3.
  apply: (star_trans (Rw A' H P)).
  apply: (star_hom ((Rw^~ H)^~ P)) r1=>x y. exact: mltt_step_rwA.
  apply: (star_trans (Rw A' H' P)).
  apply: (star_hom (Rw A'^~P)) r2=>x y. exact: mltt_step_rwH.
  apply: (star_hom (Rw A' H')) r3=>x y. exact: mltt_step_rwP.
Qed.

Lemma mltt_red_subst m n σ : m ~>* n -> m.[σ] ~>* n.[σ].
Proof.
  move=>st.
  elim: st σ=>{n}; eauto.
  move=> n n' r ih st σ.
  move:(ih σ)=>{}ih.
  move:(mltt_step_subst σ st)=>r'.
  apply: star_trans.
  apply: ih.
  by apply: star1.
Qed.

Lemma sred_up σ τ : sred σ τ -> sred (up σ) (up τ).
Proof. move=> A [|n] //=. asimpl. apply: mltt_red_subst. exact: A. Qed.

Lemma sred_upn n σ τ : sred σ τ -> sred (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ sr. by asimpl.
  move=>n ih σ τ /ih/sred_up. by asimpl.
Qed.

#[export] Hint Resolve
  mltt_red_app mltt_red_lam mltt_red_pi
  mltt_red_sig mltt_red_dpair mltt_red_letin
  mltt_red_tuple mltt_red_pair mltt_red_fst mltt_red_snd
  mltt_red_id mltt_red_refl mltt_red_rw
  sred_up sred_upn : mltt_red_congr.

Lemma mltt_red_compat σ τ s : sred σ τ -> mltt_red s.[σ] s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto 9 with mltt_red_congr. Qed.

Definition sconv (σ τ : var -> term) := forall x, σ x === τ x.

Lemma mltt_conv_app m m' n n' :
  m === m' -> n === n' -> App m n === App m' n'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (App m' n)).
  apply: (conv_hom (App^~ n)) r1=>x y. exact: mltt_step_appL.
  apply: conv_hom r2. exact: mltt_step_appR.
Qed.

Lemma mltt_conv_lam A A' m m' :
  A === A' -> m === m' -> Lam A m === Lam A' m'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Lam A' m)).
  apply: (conv_hom (Lam^~ m)) r1=>x y. exact: mltt_step_lamL.
  apply: (conv_hom (Lam A')) r2=>x y. exact: mltt_step_lamR.
Qed.

Lemma mltt_conv_pi A A' B B' :
  A === A' -> B === B' -> Pi A B === Pi A' B'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Pi A' B)).
  apply: (conv_hom (Pi^~ B)) r1=>x y. exact: mltt_step_piL.
  apply: (conv_hom (Pi A')) r2=>x y. exact: mltt_step_piR.
Qed.

Lemma mltt_conv_sig A A' B B' :
  A === A' -> B === B' -> Sig A B === Sig A' B'.
Proof.
  move=> r1 r2.
  apply: (conv_trans (Sig A' B)).
  apply: (conv_hom (Sig^~ B)) r1=>x y. exact: mltt_step_sigL.
  apply: (conv_hom (Sig A')) r2=>x y. exact: mltt_step_sigR.
Qed.

Lemma mltt_conv_dpair m m' n n' :
  m === m' -> n === n' -> DPair m n === DPair m' n'.
Proof.
  move=>r1 r2.
  apply: (conv_trans (DPair m' n)).
  apply: (conv_hom (DPair^~ n)) r1=>x y. exact: mltt_step_dpairL.
  apply: (conv_hom (DPair m')) r2=>x y. exact: mltt_step_dpairR.
Qed.

Lemma mltt_conv_letin A A' m m' n n' :
  A === A' -> m === m' -> n === n' -> LetIn A m n === LetIn A' m' n'.
Proof.
  move=>r1 r2 r3.
  apply: (conv_trans (LetIn A' m n)).
  apply: (conv_hom ((LetIn^~ m)^~ n)) r1=>x y. exact: mltt_step_letinA.
  apply: (conv_trans (LetIn A' m' n)).
  apply: (conv_hom (LetIn A'^~ n)) r2=>x y. exact: mltt_step_letinL.
  apply: (conv_hom (LetIn A' m')) r3=>x y. exact: mltt_step_letinR.
Qed.

Lemma mltt_conv_tuple A A' B B' :
  A === A' -> B === B' -> Tuple A B === Tuple A' B'.
Proof.
  move=>r1 r2.
  apply: (conv_trans (Tuple A' B)).
  apply: (conv_hom (Tuple^~ B)) r1=>x y. exact: mltt_step_tupleL.
  apply: (conv_hom (Tuple A')) r2=>x y. exact: mltt_step_tupleR.
Qed.

Lemma mltt_conv_pair m m' n n' :
  m === m' -> n === n' -> Pair m n === Pair m' n'.
Proof.
  move=>r1 r2.
  apply: (conv_trans (Pair m' n)).
  apply: (conv_hom (Pair^~ n)) r1=>x y. exact: mltt_step_pairL.
  apply: (conv_hom (Pair m')) r2=>x y. exact: mltt_step_pairR.
Qed.

Lemma mltt_conv_fst m m' :
  m === m' -> Fst m === Fst m'.
Proof.
  move=>r.
  apply: (conv_hom Fst) r=>x y. exact: mltt_step_fst.
Qed.

Lemma mltt_conv_snd m m' :
  m === m' -> Snd m === Snd m'.
Proof.
  move=>r.
  apply: (conv_hom Snd) r=>x y. exact: mltt_step_snd.
Qed.

Lemma mltt_conv_id A A' m m' n n' :
  A === A' -> m === m' -> n === n' -> Id A m n === Id A' m' n'.
Proof.
  move=>r1 r2 r3.
  apply: (conv_trans (Id A' m n)).
  apply: (conv_hom ((Id^~ m)^~ n)) r1=>x y. exact: mltt_step_idA.
  apply: (conv_trans (Id A' m' n)).
  apply: (conv_hom (Id A'^~ n)) r2=>x y. exact: mltt_step_idL.
  apply: (conv_hom (Id A' m')) r3=>x y. exact: mltt_step_idR.
Qed.

Lemma mltt_conv_refl m m' :
  m === m' -> Refl m === Refl m'.
Proof.
  move=>r.
  apply: (conv_hom Refl) r=>x y. exact: mltt_step_refl.
Qed.

Lemma mltt_conv_rw A A' H H' P P' :
  A === A' -> H === H' -> P === P' -> Rw A H P === Rw A' H' P'.
Proof.
  move=>r1 r2 r3.
  apply: (conv_trans (Rw A' H P)).
  apply: (conv_hom ((Rw^~ H)^~ P)) r1=>x y. exact: mltt_step_rwA.
  apply: (conv_trans (Rw A' H' P)).
  apply: (conv_hom (Rw A'^~ P)) r2=>x y. exact: mltt_step_rwH.
  apply: (conv_hom (Rw A' H')) r3=>x y. exact: mltt_step_rwP.
Qed.

Lemma mltt_conv_subst σ m n :
  m === n -> m.[σ] === n.[σ].
Proof.
  move=>c.
  apply: conv_hom c.
  exact: mltt_step_subst.
Qed.

Lemma sconv_up σ τ : sconv σ τ -> sconv (up σ) (up τ).
Proof. move=> A [|x] //=. asimpl. exact: mltt_conv_subst. Qed.

Lemma sconv_upn n σ τ : sconv σ τ -> sconv (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ sr. by asimpl.
  move=>n ih σ τ /ih/sconv_up. by asimpl.
Qed.

#[export] Hint Resolve
  mltt_conv_app mltt_conv_lam mltt_conv_pi
  mltt_conv_sig mltt_conv_dpair mltt_conv_letin
  mltt_conv_tuple mltt_conv_pair mltt_conv_fst mltt_conv_snd
  mltt_conv_id mltt_conv_refl mltt_conv_rw
  sconv_up sconv_upn : mltt_conv_congr.

Lemma mltt_conv_compat σ τ s :
  sconv σ τ -> s.[σ] === s.[τ].
Proof. elim: s σ τ => *; asimpl; eauto 9 with mltt_conv_congr. Qed.

Lemma mltt_conv_beta m n1 n2 : n1 === n2 -> m.[n1/] === m.[n2/].
Proof. move=> c. by apply: mltt_conv_compat => -[]. Qed.

Lemma pstep_reflexive m : pstep m m.
Proof. elim: m; eauto using pstep. Qed.
#[global] Hint Resolve pstep_reflexive.

Lemma mltt_step_pstep m m' : mltt_step m m' -> pstep m m'.
Proof with eauto using pstep, pstep_reflexive. elim... Qed.

Lemma pstep_mltt_red m n : pstep m n -> m ~>* n.
Proof with eauto.
  elim=>{m n}//=; eauto with mltt_red_congr.
  { move=> A m m' n n' p1 r1 p2 r2.
    apply: starES. by constructor.
    apply: (star_trans (m'.[n/])). exact: mltt_red_subst.
    by apply: mltt_red_compat=>-[|]. }
  { move=> A m1 m1' m2 m2' n n' p1 r1 p2 r2 p r.
    apply: starES. by constructor.
    apply: (star_trans (n'.[m2,m1/])). exact: mltt_red_subst.
    by apply: mltt_red_compat=>-[|-[]]. }
  { move=>m m' n p r.
    apply: starES. by constructor. eauto. }
  { move=>m m' n p r.
    apply: starES. by constructor. eauto. }
  { move=>A H H' m p r.
    apply: starES. by constructor. eauto. }
Qed.

Lemma pstep_subst m n σ : pstep m n -> pstep m.[σ] n.[σ].
Proof with eauto using pstep, pstep_reflexive.
  move=>ps. elim: ps σ=>{m n}...
  { move=>A m m' n n' ps1 ih1 ps2 ih2 σ.
    asimpl.
    pose proof (pstep_beta A.[σ] (ih1 (up σ)) (ih2 σ)) as H.
    by asimpl in H. }
  { move=>A m1 m1' m2 m2' n n' pm1 ihm1 pm2 ihm2 pn ihn σ.
    asimpl.
    pose proof (pstep_iota A.[up σ] (ihm1 σ) (ihm2 σ) (ihn (upn 2 σ))).
    by asimpl in H. }
Qed.

Definition psstep (σ τ : var -> term) := forall x, pstep (σ x) (τ x).

Lemma psstep_reflexive σ : psstep σ σ.
Proof with eauto using pstep_reflexive. elim... Qed.

Lemma psstep_up σ τ : psstep σ τ -> psstep (up σ) (up τ).
Proof with eauto using pstep, pstep_reflexive.
  move=> A [|n] //=. asimpl... asimpl; apply: pstep_subst. exact: A.
Qed.

Lemma psstep_upn n σ τ : psstep σ τ -> psstep (upn n σ) (upn n τ).
Proof.
  elim: n σ τ.
  move=>σ τ pss. by asimpl.
  move=>n ihn σ τ /ihn/psstep_up. by asimpl.
Qed.

Lemma pstep_compat m n σ τ :
  pstep m n -> psstep σ τ -> pstep m.[σ] n.[τ].
Proof with eauto 6 using pstep, psstep_up.
  move=> ps. elim: ps σ τ=>{m n}...
  { move=> A m m' n n' ps1 ih1 ps2 ih2 σ τ pss. asimpl.
    pose proof (pstep_beta A.[σ] (ih1 _ _ (psstep_up pss)) (ih2 _ _ pss)) as H.
    by asimpl in H. }
  { move=>A A' m m' n n' pA ihA pm ihm pn ihn σ τ pss. asimpl.
    pose proof (pstep_letin (ihA _ _ (psstep_up pss)) (ihm _ _ pss) (ihn _ _ (psstep_upn 2 pss))).
    by asimpl in H. }
  { move=>A m1 m1' m2 m2' n n' pm1 ihm1 pm2 ihm2 pn ihn σ τ pss. asimpl.
    pose proof (pstep_iota A.[up σ] (ihm1 _ _ pss) (ihm2 _ _ pss) (ihn _ _ (psstep_upn 2 pss))).
    by asimpl in H. }
  { move=>A A' H H' P P' pA ihA pH ihH pP ihP σ τ pss. asimpl.
    pose proof (pstep_rw (ihA _ _ (psstep_upn 2 pss)) (ihH _ _ pss) (ihP _ _ pss)).
    by asimpl in H0. }
Qed.

Lemma psstep_compat s1 s2 σ τ:
  psstep σ τ -> pstep s1 s2 -> psstep (s1 .: σ) (s2 .: τ).
Proof. move=> A B [|n] //=. Qed.

Lemma pstep_subst_term m n n' :
  pstep n n' -> pstep m.[n/] m.[n'/].
Proof with eauto using pstep_compat, psstep_reflexive, psstep_compat.
  move...
Qed.

Lemma pstep_compat_beta m m' n n' :
  pstep m m' -> pstep n n' -> pstep m.[n/] m'.[n'/].
Proof with eauto using pstep_compat, psstep_reflexive, psstep_compat.
  move...
Qed.

Lemma pstep_diamond m m1 m2 :
  pstep m m1 -> pstep m m2 -> exists2 m', pstep m1 m' & pstep m2 m'.
Proof with eauto 6 using
  pstep, pstep_refl,
  pstep_compat, pstep_compat_beta,
  psstep_compat, psstep_reflexive.
  move=>ps. elim: ps m2=>{m m1}...
  { move=>A A' B B' pA ihA pB ihB m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H1.
    have[B0 pB1 pB2]:=ihB _ H3.
    exists (Pi A0 B0)... }
  { move=>A A' m m' pA ihA pm ihm m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H1.
    have[m0 pm1 pm2]:=ihm _ H3.
    exists (Lam A0 m0)... }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    { have[m0 pm1 pm2]:=ihm _ H1.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (App m0 n0)... }
    { inv pm.
      have/ihm[mx pm1 pm2]:pstep (Lam A m0) (Lam A m'0)...
      inv pm1. inv pm2.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m'.[n0/])... } }
  { move=>A m m' n n' pm ihm pn ihn m2 p. inv p.
    { inv H1.
      have[m0 pm1 pm2]:=ihm _ H5.
      have[n0 pn1 pn2]:=ihn _ H3.
      exists (m0.[n0/])... }
    { have[m0 pm1 pm2]:=ihm _ H3.
      have[n0 pn1 pn2]:=ihn _ H4.
      exists (m0.[n0/])... } }
  { move=>A A' B B' pA ihA pB ihB m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H1.
    have[B0 pB1 pB2]:=ihB _ H3.
    exists (Sig A0 B0)... }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    have[m0 pm1 pm2]:=ihm _ H1.
    have[n0 pn1 pn2]:=ihn _ H3.
    exists (DPair m0 n0)... }
  { move=>A A' m m' n n' pA ihA pm ihm pn ihn m2 p. inv p.
    { have[A0 pA1 pA2]:=ihA _ H2.
      have[m0 pm1 pm2]:=ihm _ H4.
      have[n0 pn1 pn2]:=ihn _ H5.
      exists (LetIn A0 m0 n0)... }
    { inv pm.
      have/ihm[mx pm1 pm2]:pstep (DPair m1 m0) (DPair m1' m2')...
      have[n0 pn1 pn2]:=ihn _ H5.
      inv pm1. inv pm2.
      exists n0.[n'2,m'/]... } }
  { move=>A m1 m1' m2 m2' n n' pm1 ihm1 pm2 ihm2 pn ihn m0 p. inv p.
    { inv H4.
      have[m1x pm11 pm12]:=ihm1 _ H1.
      have[m2x pm21 pm22]:=ihm2 _ H6.
      have[n0 pn1 pn2]:=ihn _ H5.
      exists n0.[m2x,m1x/]... }
    { have[m1x pm11 pm12]:=ihm1 _ H4.
      have[m2x pm21 pm22]:=ihm2 _ H5.
      have[n0 pn1 pn2]:=ihn _ H6.
      exists n0.[m2x,m1x/]... } }
  { move=> A A' B B' pA ihA pB ihB m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H1.
    have[B0 pB1 pB2]:=ihB _ H3.
    exists (Tuple A0 B0)... }
  { move=>m m' n n' pm ihm pn ihn m2 p. inv p.
    have[m0 pm1 pm2]:=ihm _ H1.
    have[n0 pn1 pn2]:=ihn _ H3.
    exists (Pair m0 n0)... }
  { move=>m m' pm ihm m2 p. inv p.
    { have[m0 pm1 pm2]:=ihm _ H0. exists (Fst m0)... }
    { inv pm.
      have/ihm[x p1 p2]:pstep (Pair m0 n) (Pair m2 n')...
      inv p1. inv p2.
      exists m'... } }
  { move=>m m' pm ihm m2 p. inv p.
    { have[m0 pm1 pm2]:=ihm _ H0. exists (Snd m0)... }
    { inv pm.
      have/ihm[x p1 p2]:pstep (Pair m0 n) (Pair m'0 m2)...
      inv p1. inv p2.
      exists n'0... } }
  { move=>m m' n pm ihm m2 p. inv p.
    { inv H0. have[m0 p1 p2]:=ihm _ H2. exists m0... }
    { have[m0 p1 p2]:=ihm _ H2. exists m0... } }
  { move=>m m' n pm ihm m2 p. inv p.
    { inv H0. have[m0 p1 p2]:=ihm _ H4. exists m0... }
    { have[m0 p1 p2]:=ihm _ H2. exists m0... } }
  { move=>A A' m m' n n' pA ihA pm ihm pn ihn m2 p. inv p.
    have[A0 pA1 pA2]:=ihA _ H2.
    have[m0 pm1 pm2]:=ihm _ H4.
    have[n0 pn1 pn2]:=ihn _ H5.
    exists (Id A0 m0 n0)... }
  { move=>m m' pm ihm m2 p. inv p.
    have[m0 p1 p2]:=ihm _ H0.
    exists (Refl m0)... }
  { move=>A A' H H' P P' pA ihA pH ihH pP ihP m2 p. inv p.
    { have[A0 pA1 pA2]:=ihA _ H4.
      have[H0 pH1 pH2]:=ihH _ H6.
      have[P0 pP1 pP2]:=ihP _ H7.
      exists (Rw A0 H0 P0)... }
    { inv pP.
      have[H0 pH1 pH2]:=ihH _ H5.
      have/ihP[x p1 p2]:pstep (Refl m) (Refl m')... } }
  { move=>A H H' m pH ihH x p. inv p.
    { inv H7.
      have[H0 pH1 pH2]:=ihH _ H6.
      exists H0... }
    { have[H0 pH1 pH2]:=ihH _ H5.
      exists H0... } }
Qed.

Lemma strip m m1 m2 :
  pstep m m1 -> m ~>* m2 -> exists2 m', m1 ~>* m' & pstep m2 m'.
Proof with eauto using pstep_refl, star.
  move=>p r. elim: r m1 p=>{m2}...
  move=>m1 m2 r1 ih /mltt_step_pstep p1 m' p2.
  move:(ih _ p2)=>[m3 r2 p3].
  move:(pstep_diamond p1 p3)=>[m4 p4 p5].
  exists m4...
  apply: star_trans.
  apply: r2.
  by apply: pstep_mltt_red.
Qed.

Theorem confluence :
  confluent mltt_step.
Proof with eauto using mltt_step, star.
  unfold confluent.
  unfold joinable.
  move=> x y z r.
  elim: r z=>{y}.
  move=>z r. exists z...
  move=>y z r1 ih /mltt_step_pstep p z0 /ih[z1 r2 r3].
  move:(strip p r2)=>[z2 r4 p1].
  exists z2...
  apply: star_trans.
  apply r3.
  apply: pstep_mltt_red...
Qed.

Theorem church_rosser :
  CR mltt_step.
Proof.
  apply confluent_cr.
  apply confluence.
Qed.

Lemma mltt_red_var_inv x y : Var x ~>* y -> y = Var x.
Proof.
  elim=>//{} y z r1 e r2; subst.
  inv r2.
Qed.

Lemma mltt_red_ty_inv A :
  Ty ~>* A -> A = Ty.
Proof.
  elim=>//y z r1 e r2; subst.
  inv r2.
Qed.

Lemma mltt_red_pi_inv A B x :
  Pi A B ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Pi A' B'.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma mltt_red_lam_inv A m x :
  Lam A m ~>* x ->
  exists A' m',
    A ~>* A' /\ m ~>* m' /\ x = Lam A' m'.
Proof.
  elim.
  exists A. exists m=>//.
  move=>y z r1[A'[m'[rA[rm e]]]] r2. subst.
  inv r2.
  exists A'0. exists m'. eauto using star.
  exists A'. exists m'0. eauto using star.
Qed.

Lemma mltt_red_sig_inv A B x :
  Sig A B ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Sig A' B'.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma mltt_red_dpair_inv m n x :
  DPair m n ~>* x ->
  exists m' n',
    m ~>* m' /\ n ~>* n' /\ x = DPair m' n'.
Proof.
  elim.
  exists m. exists n=>//.
  move=> y z rd[m'[n'[r1[r2 e]]]] st; subst.
  inv st.
  exists m'0. exists n'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists m'. exists n'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma mltt_red_tuple_inv A B x :
  Tuple A B ~>* x ->
  exists A' B',
    A ~>* A' /\ B ~>* B' /\ x = Tuple A' B'.
Proof.
  elim.
  exists A. exists B=>//.
  move=> y z rd[A'[B'[r1[r2 e]]]] st; subst.
  inv st.
  exists A'0. exists B'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists B'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma mltt_red_pair_inv m n x :
  Pair m n ~>* x ->
  exists m' n',
    m ~>* m' /\ n ~>* n' /\ x = Pair m' n'.
Proof.
  elim.
  exists m. exists n=>//.
  move=> y z rd[m'[n'[r1[r2 e]]]] st; subst.
  inv st.
  exists m'0. exists n'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists m'. exists n'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma mltt_red_id_inv A m n x :
  Id A m n ~>* x ->
  exists A' m' n',
    A ~>* A' /\ m ~>* m' /\ n ~>* n' /\ x = Id A' m' n'.
Proof.
  elim.
  exists A. exists m. exists n=>//.
  move=>y z rd[A'[m'[n'[r1[r2[r3 e]]]]]] st; subst.
  inv st.
  exists A'0. exists m'. exists n'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists m'0. exists n'.
  repeat constructor; eauto.
  apply: starSE; eauto.
  exists A'. exists m'. exists n'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma mltt_red_refl_inv m x :
  Refl m ~>* x ->
  exists m', m ~>* m' /\ x = Refl m'.
Proof.
  elim.
  exists m=>//.
  move=>y z rd[m'[r e]] st; subst.
  inv st. exists m'0.
  repeat constructor; eauto.
  apply: starSE; eauto.
Qed.

Lemma pi_inj A A' B B' :
  Pi A B === Pi A' B' ->
    A === A' /\ B === B'.
Proof.
  move/church_rosser=>
    [x/mltt_red_pi_inv[A1[B1[rA1[rB1->]]]]
      /mltt_red_pi_inv[A2[B2[rA2[rB2[]]]]]] eA eB; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rB1.
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma sig_inj A A' B B' :
  Sig A B === Sig A' B' ->
    A === A' /\ B === B'.
Proof.
  move/church_rosser=>
    [x/mltt_red_sig_inv[A1[B1[rA1[rB1->]]]]
      /mltt_red_sig_inv[A2[B2[rA2[rB2[]]]]]] eA eB; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rB1.
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma tuple_inj A A' B B' :
  Tuple A B === Tuple A' B' ->
    A === A' /\ B === B'.
Proof.
  move/church_rosser=>
    [x/mltt_red_tuple_inv[A1[B1[rA1[rB1->]]]]
      /mltt_red_tuple_inv[A2[B2[rA2[rB2[]]]]]] eA eB; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rB1.
  apply: conv_sym. by apply: star_conv.
Qed.

Lemma id_inj A A' m m' n n' :
  Id A m n === Id A' m' n' ->
    A === A' /\ m === m' /\ n === n'.
Proof.
  move/church_rosser=>
    [x/mltt_red_id_inv[A1[m1[n1[rA1[rm1[rn1->]]]]]]
      /mltt_red_id_inv[A2[m2[n2[rA2[rm2[rn2[]]]]]]]] eA em en; subst.
  repeat split.
  apply: conv_trans.
  apply: star_conv. by apply: rA1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rm1.
  apply: conv_sym. by apply: star_conv.
  apply: conv_trans.
  apply: star_conv. by apply: rn1.
  apply: conv_sym. by apply: star_conv.
Qed.
