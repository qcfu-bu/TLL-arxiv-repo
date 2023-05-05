From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive head_sim : term -> term -> Prop :=
| head_sim_var x : head_sim (Var x) (Var x)
| head_sim_sort s : head_sim (Sort s) (Sort s)
| head_sim_pi0 A1 A2 B1 B2 s :
  head_sim A1 A2 ->
  head_sim B1 B2 ->
  head_sim (Pi0 A1 B1 s) (Pi0 A2 B2 s)
| head_sim_pi1 A1 A2 B1 B2 s :
  head_sim A1 A2 ->
  head_sim B1 B2 ->
  head_sim (Pi1 A1 B1 s) (Pi1 A2 B2 s)
| head_sim_lam0 A m s : head_sim (Lam0 A m s) (Lam0 A m s)
| head_sim_lam1 A m s : head_sim (Lam1 A m s) (Lam1 A m s)
| head_sim_app m n : head_sim (App m n) (App m n)
| head_sim_sig0 A1 A2 B1 B2 s1 s2 :
  head_sim (Sig0 A1 B1 s1) (Sig0 A2 B2 s2)
| head_sim_sig1 A1 A2 B1 B2 s1 s2 :
  head_sim (Sig1 A1 B1 s1) (Sig1 A2 B2 s2)
| head_sim_pair0 m n t : head_sim (Pair0 m n t) (Pair0 m n t)
| head_sim_pair1 m n t : head_sim (Pair1 m n t) (Pair1 m n t)
| head_sim_letin A m n : head_sim (LetIn A m n) (LetIn A m n)
| head_sim_with A1 A2 B1 B2 s :
  head_sim A1 A2 ->
  head_sim B1 B2 ->
  head_sim (With A1 B1 s) (With A2 B2 s)
| head_sim_apair m n s : head_sim (APair m n s) (APair m n s)
| head_sim_fst m : head_sim (Fst m) (Fst m)
| head_sim_snd m : head_sim (Snd m) (Snd m)
| head_sim_id A1 A2 m n :
  head_sim A1 A2 ->
  head_sim (Id A1 m n) (Id A2 m n)
| head_sim_refl m : head_sim (Refl m) (Refl m)
| head_sim_rw A H P : head_sim (Rw A H P) (Rw A H P)
| head_sim_box : head_sim Box Box
| head_sim_ptr l : head_sim (Ptr l) (Ptr l).

Inductive sim (m n : term) : Prop :=
| Sim x y : m === x -> head_sim x y -> y === n -> sim m n.

Lemma head_sim_reflexive m : head_sim m m.
Proof with eauto using head_sim. elim: m... Qed.
#[global] Hint Resolve head_sim_reflexive.

Lemma head_sim_sym m n : head_sim m n -> head_sim n m.
Proof with eauto using head_sim. elim=>{m n}... Qed.

Lemma head_sim_subst m1 m2 σ : head_sim m1 m2 -> head_sim m1.[σ] m2.[σ].
Proof with eauto using head_sim.
  move=>hs. elim: hs σ=>{m1 m2}...
Qed.

Lemma sim_reflexive m : sim m m.
Proof with eauto. econstructor... Qed.
#[global] Hint Resolve sim_reflexive.

Lemma sim_sym m n : sim m n -> sim n m.
Proof with eauto.
  move=>sm. inv sm.
  econstructor.
  apply: conv_sym...
  apply: head_sim_sym...
  apply: conv_sym...
Qed.

Lemma sim_transL x y z : sim x y -> y === z -> sim x z.
Proof with eauto.
  move=>sm eq. inv sm.
  econstructor...
  apply: conv_trans...
Qed.

Lemma sim_transR x y z : sim x y -> z === x -> sim z y.
Proof with eauto using head_sim.
  move=>sm eq. inv sm.
  econstructor.
  apply: conv_trans...
  apply: H0.
  apply: H1.
Qed.

Lemma sim_subst x y σ : sim x y -> sim x.[σ] y.[σ].
Proof with eauto.
  move=>sm. inv sm.
  econstructor.
  apply: sta_conv_subst...
  apply: head_sim_subst...
  apply: sta_conv_subst...
Qed.

Ltac solve_sim :=
  match goal with
  | [ H : sim _ _ |- _ ] => inv H
  end;
  match goal with
  | [ H : head_sim _ _ |- _ ] => inv H
  end;
  try solve[solve_conv];
  match goal with
  | [ eq1 : ?x === ?z, eq2 : ?z === ?y |- _ ] =>
    pose proof (conv_trans _ eq1 eq2); solve_conv
  end.

Lemma sim_sort s t : sim (Sort s) (Sort t) -> s = t.
Proof with eauto.
  move e1:(Sort s)=>m.
  move e2:(Sort t)=>n sm.
  inv sm.
  elim: H0 s t H H1=>//{x y}.
  { move=>*. exfalso. solve_conv. }
  { move=>s r t/sort_inj->/sort_inj->//. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>m n s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>A m n s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>m s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>m s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>*. exfalso. solve_conv. }
  { move=>*. exfalso. solve_conv. }
  { move=>A H P s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
  { move=>l s t eq1 eq2.
    have/sort_inj//:=conv_trans _ eq1 eq2. }
Qed.

Lemma sim_pi0_inj A1 A2 B1 B2 s1 s2 :
  sim (Pi0 A1 B1 s1) (Pi0 A2 B2 s2) ->
  sim A1 A2 /\ sim B1 B2 /\ s1 = s2.
Proof with eauto using sim.
  move=>sm. inv sm.
  elim: H0 A1 A2 B1 B2 s1 s2 H H1=>{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>A1 A2 B1 B2 s hA ihA hB ihB A0 A3 B0 B3 s1 s2
      /pi0_inj[eqA1[eqB1 e1]]/pi0_inj[eqA2[eqB2 e2]]; subst.
    repeat split... }
  { move=>m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>m A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>m A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A H P A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>l A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi0_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
Qed.

Lemma sim_pi1_inj A1 A2 B1 B2 s1 s2 :
  sim (Pi1 A1 B1 s1) (Pi1 A2 B2 s2) ->
  sim A1 A2 /\ sim B1 B2 /\ s1 = s2.
Proof with eauto using sim.
  move=>sm. inv sm.
  elim: H0 A1 A2 B1 B2 s1 s2 H H1=>{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>A1 A2 B1 B2 s hA ihA hB ihB A0 A3 B0 B3 s1 s2
      /pi1_inj[eqA1[eqB1 e1]]/pi1_inj[eqA2[eqB2 e2]]; subst.
    repeat split... }
  { move=>m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>m A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>m A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A H P A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>l A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/pi1_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
Qed.

Lemma sim_with_inj A1 A2 B1 B2 s1 s2 :
  sim (With A1 B1 s1) (With A2 B2 s2) ->
  sim A1 A2 /\ sim B1 B2 /\ s1 = s2.
Proof with eauto using sim.
  move=>sm. inv sm.
  elim: H0 A1 A2 B1 B2 s1 s2 H H1=>{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/with_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A m n A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/with_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A1 A2 B1 B2 s hA ihA hB ihB A0 A3 B0 B3 s1 s2
      /with_inj[eqA1[eqB1 e1]]/with_inj[eqA2[eqB2 e2]]; subst.
    repeat split... }
  { move=>m A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/with_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>m A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/with_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A H P A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/with_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/with_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>l A1 A2 B1 B2 s1 s2 eq1 eq2.
    have/with_inj[eqA[eqB->]]:=conv_trans _ eq1 eq2.
    repeat split... }
Qed.

Lemma sim_id_inj A1 A2 m1 m2 n1 n2 :
  sim (Id A1 m1 n1) (Id A2 m2 n2) ->
  sim A1 A2 /\ m1 === m2 /\ n1 === n2.
Proof with eauto using sim.
  move=>sm. inv sm.
  elim: H0 A1 A2 m1 m2 n1 n2 H H1=>{x y}.
  all: try solve[intros; exfalso; solve_conv].
  { move=>m n A1 A2 m1 m2 n1 n2 eq1 eq2.
    have/id_inj[eqA[eqm eqn]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A m n A1 A2 m1 m2 n1 n2 eq1 eq2.
    have/id_inj[eqA[eqm eqn]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>m A1 A2 m1 m2 n1 n2 eq1 eq2.
    have/id_inj[eqA[eqm eqn]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>m A1 A2 m1 m2 n1 n2 eq1 eq2.
    have/id_inj[eqA[eqm eqn]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A1 A2 m n hs ih A0 A3 m1 m2 n1 n2
      /id_inj[eqA1[eqm1 eqn1]]/id_inj[eqA2[eqm2 eqn2]].
    repeat split...
    apply: conv_trans...
    apply: conv_trans... }
  { move=>A H P A1 A2 m1 m2 n1 n2 eq1 eq2.
    have/id_inj[eqA[eqm eqn]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>A1 A2 m1 m2 n1 n2 eq1 eq2.
    have/id_inj[eqA[eqm eqn]]:=conv_trans _ eq1 eq2.
    repeat split... }
  { move=>l A1 A2 m1 m2 n1 n2 eq1 eq2.
    have/id_inj[eqA[eqm eqn]]:=conv_trans _ eq1 eq2.
    repeat split... }
Qed.

Lemma sta_sort_uniq Γ s A :
  Γ ⊢ Sort s : A -> sim (Sort U) A.
Proof with eauto.
  move e:(Sort s)=>n ty. elim: ty s e=>//{Γ n A}.
  move=>Γ A B m s eq tym ihm tyB ihB t e; subst.
  have eq':=ihm _ erefl.
  apply: sim_transL...
Qed.

Lemma sta_has_uniq Γ x A B : sta_has Γ x A -> sta_has Γ x B -> A = B.
Proof with eauto.
  move=>hs. elim: hs B=>{Γ x A}.
  { move=>Γ A B hs. inv hs... }
  { move=>Γ A B x hs ih C hs'. inv hs'.
    rewrite (ih _ H3)... }
Qed.

Lemma sta_var_uniq Γ A B x :
  Γ ⊢ Var x : B -> sta_has Γ x A -> sim A B.
Proof with eauto using sim_reflexive.
  move e:(Var x)=>n ty. elim: ty A x e=>//{Γ n B}.
  { move=>Γ x A wf hs1 A0 x0 [e] hs2; subst.
    rewrite (sta_has_uniq hs1 hs2)... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 x e hs; subst.
    have eq':=ihm _ _ erefl hs.
    apply: sim_transL... }
Qed.

Lemma sta_lam0_uniq Γ A B C m s :
  Γ ⊢ Lam0 A m s : C -> (forall C, (A :: Γ) ⊢ m : C -> sim B C) -> sim (Pi0 A B s) C.
Proof with eauto.
  move e:(Lam0 A m s)=>n ty. elim: ty A B m s e=>//{Γ n C}.
  { move=>Γ A B m s tym ihm A0 B0 m0 s0 [e1 e2 e3] h; subst.
    have eq:=h _ tym. inv eq.
    econstructor. apply: sta_conv_pi0...
    constructor... apply: sta_conv_pi0... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 s0 e h; subst.
    have eq':=ihm _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_pi0_uniq Γ A B C s :
  Γ ⊢ Pi0 A B s : C -> sim (Sort s) C.
Proof with eauto.
  move e:(Pi0 A B s)=>n ty. elim: ty A B s e=>//{Γ n C}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_pi1_uniq Γ A B C s :
  Γ ⊢ Pi1 A B s : C -> sim (Sort s) C.
Proof with eauto.
  move e:(Pi1 A B s)=>n ty. elim: ty A B s e=>//{Γ n C}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_lam1_uniq Γ A B C m s :
  Γ ⊢ Lam1 A m s : C -> (forall C, (A :: Γ) ⊢ m : C -> sim B C) -> sim (Pi1 A B s) C.
Proof with eauto.
  move e:(Lam1 A m s)=>n ty. elim: ty A B m s e=>//{Γ n C}.
  { move=>Γ A B m s tym ihm A0 B0 m0 s0 [e1 e2 e3] h; subst.
    have eq:=h _ tym. inv eq.
    econstructor. apply: sta_conv_pi1...
    constructor... apply: sta_conv_pi1... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 s0 e h; subst.
    have eq':=ihm _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_app0_uniq Γ A B C m n s :
  Γ ⊢ App m n : C -> (forall C, Γ ⊢ m : C -> sim (Pi0 A B s) C) -> sim B.[n/] C.
Proof with eauto.
  move e:(App m n)=>x ty. elim: ty A B m n s e=>//{Γ x C}.
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have/sim_pi0_inj[_[eq' _]]:=h _ tym.
    apply: sim_subst... }
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have eq:=h _ tym.
    exfalso. solve_sim. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 e h; subst.
    have eq':=ihm _ _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_app1_uniq Γ A B C m n s :
  Γ ⊢ App m n : C -> (forall C, Γ ⊢ m : C -> sim (Pi1 A B s) C) -> sim B.[n/] C.
Proof with eauto.
  move e:(App m n)=>x ty. elim: ty A B m n s e=>//{Γ x C}.
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have eq:=h _ tym.
    exfalso. solve_sim. }
  { move=>Γ A B m n s tym ihm tyn ihn A0 B0 m0 n0 s0 [e1 e2] h; subst.
    have/sim_pi1_inj[_[eq' _]]:=h _ tym.
    apply: sim_subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 e h; subst.
    have eq':=ihm _ _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_sig0_uniq Γ A B C s :
  Γ ⊢ Sig0 A B s : C -> sim (Sort s) C.
Proof with eauto.
  move e:(Sig0 A B s)=>m ty. elim: ty A B s e=>//{Γ m C}.
  { move=>Γ A B s r t ord tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_sig1_uniq Γ A B C s :
  Γ ⊢ Sig1 A B s : C -> sim (Sort s) C.
Proof with eauto.
  move e:(Sig1 A B s)=>m ty. elim: ty A B s e=>//{Γ m C}.
  { move=>Γ A B s r t ord1 ord2 tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_pair0_uniq Γ A B C m n s :
  Γ ⊢ Pair0 m n s : C ->
  (forall X Y, Γ ⊢ m : X -> Γ ⊢ n : Y -> sim A X /\ sim B.[m/] Y) ->
  sim (Sig0 A B s) C.
Proof with eauto.
  move e:(Pair0 m n s)=>x ty. elim: ty A B m n s e=>//{Γ C x}.
  { move=>*.
    econstructor. eauto.
    constructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 e h; subst.
    have eq':=ihm _ _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_pair1_uniq Γ A B C m n s :
  Γ ⊢ Pair1 m n s : C ->
  (forall X Y, Γ ⊢ m : X -> Γ ⊢ n : Y -> sim A X /\ sim B.[m/] Y) ->
  sim (Sig1 A B s) C.
Proof with eauto.
  move e:(Pair1 m n s)=>x ty. elim: ty A B m n s e=>//{Γ C x}.
  { move=>*.
    econstructor. eauto.
    constructor. eauto. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 m0 n s0 e h; subst.
    have eq':=ihm _ _ _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_letin_uniq Γ m n A B :
  Γ ⊢ LetIn A m n : B -> sim A.[m/] B.
Proof with eauto.
  move e:(LetIn A m n)=>x ty. elim: ty A m n e=>//{Γ B x}.
  { move=>Γ A B C m n s t
      tyC ihC tym ihm tyn ihn A0 m0 n0[e1 e2 e3]; subst... }
  { move=>Γ A B C m n s t
      tyC ihC tym ihm tyn ihn A0 m0 n0[e1 e2 e3]; subst... }
  { move=>Γ A B m s k tym ihm tyB _ A0 m0 n e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_with_uniq Γ A B C s :
  Γ ⊢ With A B s : C -> sim (Sort s) C.
Proof with eauto.
  move e:(With A B s)=>x ty. elim: ty A B s e=>//{Γ C x}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 s0 e; subst.
    have eq':=ihm _ _ _ erefl.
    apply: sim_transL... }
Qed.

Lemma sta_apair_uniq Γ A B C m n s :
  Γ ⊢ APair m n s : C ->
  (forall X Y, Γ ⊢ m : X -> Γ ⊢ n : Y -> sim A X /\ sim B Y) ->
  sim (With A B s) C.
Proof with eauto.
  move e:(APair m n s)=>x ty. elim: ty m n s e=>//{Γ C x}.
  { move=>Γ A0 B0 m n t tym ihm tyn ihn m0 n0 s0[e1 e2 e3]h; subst.
    have[e1 e2]:=h _ _ tym tyn. inv e1. inv e2.
    econstructor. apply: sta_conv_with...
    constructor... apply: sta_conv_with... }
  { move=>Γ A0 B0 m s eq tym ihm tyB ihB m0 n s0 e h; subst.
    have eq':=ihm _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_fst_uniq Γ A B C m s :
  Γ ⊢ Fst m : C -> (forall X, Γ ⊢ m : X -> sim (With A B s) X) -> sim A C.
Proof with eauto.
  move e:(Fst m)=>x ty. elim: ty m e=>//{Γ x C}.
  { move=>Γ A0 B0 m t tym ihm m0[e]h; subst.
    have/sim_with_inj[//]:=h _ tym. }
  { move=>Γ A0 B0 m s0 eq tym ihm tyB ihB m0 e h; subst.
    have eq':=ihm _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_snd_uniq Γ A B C m s :
  Γ ⊢ Snd m : C -> (forall X, Γ ⊢ m : X -> sim (With A B s) X) -> sim B C.
Proof with eauto.
  move e:(Snd m)=>x ty. elim: ty m e=>//{Γ x C}.
  { move=>Γ A0 B0 m t tym ihm m0[e]h; subst.
    have/sim_with_inj[_[//]]:=h _ tym. }
  { move=>Γ A0 B0 m s0 eq tym ihm tyB ihB m0 e h; subst.
    have eq':=ihm _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_id_uniq Γ A B m n :
  Γ ⊢ Id A m n : B -> sim (Sort U) B.
Proof with eauto.
  move e:(Id A m n)=>x ty. elim: ty A m n e=>//{Γ x B}.
  move=>Γ A B m s eq tym ihm tyB ihB A0 m0 n e; subst.
  have eq':=ihm _ _ _ erefl.
  apply: sim_transL...
Qed.

Lemma sta_refl_uniq Γ A B m :
  Γ ⊢ Refl m : B -> (forall X, Γ ⊢ m : X -> sim A X) -> sim (Id A m m) B.
Proof with eauto.
  move e:(Refl m)=>x ty. elim: ty m e=>//{Γ x B}.
  { move=>Γ A0 m tym ihm m0[e]h; subst.
    have eq:=h _ tym. inv eq.
    econstructor. apply: sta_conv_id...
    constructor... apply: sta_conv_id... }
  { move=>Γ A0 B m s eq tym ihm tyB ihB m0 e h; subst.
    have eq':=ihm _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_rw_uniq Γ A B C H P m n :
  Γ ⊢ Rw B H P : C -> (forall X, Γ ⊢ P : X -> sim (Id A m n) X) -> sim B.[P,n/] C.
Proof with eauto.
  move e:(Rw B H P)=>x ty. elim: ty B H P e=>//{Γ x C}.
  { move=>Γ A0 B H P m0 n0 s tyB ihB tyH ihH tyP ihP B0 H0 P0[e1 e2 e3]h; subst.
    have/sim_id_inj[_[eq1 eq2]]:=h _ tyP.
    have sc:sconv (P .: n .: ids) (P .: n0 .: ids) by move=>[|[|]]//.
    econstructor.
    apply: sta_conv_compat...
    all: eauto... }
  { move=>Γ A0 B m0 s eq tym ihm tyB ihB B0 H P e h; subst.
    have eq':=ihm _ _ _ erefl h.
    apply: sim_transL... }
Qed.

Lemma sta_uniq Γ m A B :
  Γ ⊢ m : A -> Γ ⊢ m : B -> sim A B.
Proof with eauto.
  move=>ty. elim: ty B=>{Γ m A}.
  { move=>Γ s B tyB.
    apply: sta_sort_uniq... }
  { move=>Γ x A wf hs B ty.
    apply: sta_var_uniq... }
  { move=>Γ A B s r t tyA ihA tyB ihB B0 ty.
    apply: sta_pi0_uniq... }
  { move=>Γ A B s r t tyA ihA tyB ihB B0 ty.
    apply: sta_pi1_uniq... }
  { move=>Γ A B m s tym ihm B0 ty.
    apply: sta_lam0_uniq... }
  { move=>Γ A B m s tym ihm B0 ty.
    apply: sta_lam1_uniq... }
  { move=>Γ A B m n s tym ihm tyn ihn B0 ty.
    apply: sta_app0_uniq... }
  { move=>Γ A B m n s tym ihm tyn ihn B0 ty.
    apply: sta_app1_uniq... }
  { move=>Γ A B s r t ord tyA ihA tyB ihB B0 ty.
    apply: sta_sig0_uniq... }
  { move=>Γ A B s r t ord1 ord2 tyA ihA tyB ihB B0 ty.
    apply: sta_sig1_uniq... }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn B0 ty.
    apply: sta_pair0_uniq... }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn B0 ty.
    apply: sta_pair1_uniq... }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn B0 ty.
    apply: sta_letin_uniq... }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn B0 ty.
    apply: sta_letin_uniq... }
  { move=>Γ A B s r t tyA ihA tyB ihB B0 ty.
    apply: sta_with_uniq... }
  { move=>Γ A B m n t tym ihm tyn ihn B0 ty.
    apply: sta_apair_uniq... }
  { move=>Γ A B m t tym ihm B0 ty.
    apply: sta_fst_uniq... }
  { move=>Γ A B m t tym ihm B0 ty.
    apply: sta_snd_uniq... }
  { move=>Γ A m n s tyA ihA tym ihm tyn ihn B ty.
    apply: sta_id_uniq... }
  { move=>Γ A m tym ihm B ty.
    apply: sta_refl_uniq... }
  { move=>Γ A B H P m n s tyB ihB tyH ihH tyP ihP B0 ty.
    apply: sta_rw_uniq... }
  { move=>Γ A B m s eq tym1 ihm tyB ihB B0 tym2.
    apply: sim_transR.
    apply: ihm...
    apply: conv_sym... }
Qed.

Theorem sta_unicity Γ m s t :
  Γ ⊢ m : Sort s -> Γ ⊢ m : Sort t -> s = t.
Proof.
  move=>tym1 tym2.
  apply: sim_sort.
  apply: sta_uniq tym1 tym2.
Qed.
