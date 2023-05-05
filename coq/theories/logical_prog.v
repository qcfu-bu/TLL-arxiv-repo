(* This file presents the progress theorem of the logical level. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_sr logical_sn.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac inv_logical_val :=
  match goal with
  | [ H : logical_val _ |- _ ] => inv H
  end.

Lemma logical_pi0_canonical m A B C s :
  nil ⊢ m : C -> C === Pi0 A B s -> logical_val m ->
  exists A n, m = Lam0 A n s.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A B s=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e A0 B s eq vl. subst. inv shs. }
  { move=>Γ A B m s tym ihm e1 A0 B0 s0/pi0_inj[eqA[eqB e2]] vl. subst.
    exists A. exists m... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB e A0 B0 s0 eq2 vl. subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_pi1_canonical m A B C s :
  nil ⊢ m : C -> C === Pi1 A B s -> logical_val m ->
  exists A n, m = Lam1 A n s.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A B s=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ A B m s tym ihm e1 A0 B0 s0/pi1_inj[eqA[eqB e2]] vl. subst.
    exists A. exists m... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB e A0 B0 s0 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_sig0_canonical m A B C s :
  nil ⊢ m : C -> C === Sig0 A B s -> logical_val m ->
  exists m1 m2, m = Pair0 m1 m2 s.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A B s=>//{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ A B m n t tyS _ tym _ tyn _ e1 A0 B0 s0/sig0_inj[eqA[eqB e2]] vl.
    subst. exists m. exists n... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB e A0 B0 s0 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_sig1_canonical m A B C s :
  nil ⊢ m : C -> C === Sig1 A B s -> logical_val m ->
  exists m1 m2, m = Pair1 m1 m2 s.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A B s=>//{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ A B m n t tyS _ tym _ tyn _ e1 A0 B0 s0/sig1_inj[eqA[eqB e2]] vl.
    subst. exists m. exists n... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB e A0 B0 s0 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_with_canonical m A B C s :
  nil ⊢ m : C -> C === With A B s -> logical_val m ->
  exists m1 m2, m = APair m1 m2 s.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A B s=>//{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ A B m n t tym _ tyn _ e1 A0 B0 s0/with_inj[eqA[eqB e2]] vl.
    subst. exists m. exists n... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB e A0 B0 s0 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_id_canonical m C A x y :
  nil ⊢ m : C -> C === Id A x y -> logical_val m ->
  exists n, m = Refl n.
Proof with eauto.
  move e:(nil)=>Γ ty. elim: ty e A x y=>{Γ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_logical_val)].
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ A m tym ihm e A0 x y eq vl.
    exists m... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB e A0 x y eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

(* Logical Progress *)
Lemma logical_prog m A : nil ⊢ m : A -> (exists n, m ~> n) \/ logical_val m.
Proof with eauto using logical_step, logical_val.
  move e:(nil)=>Γ ty. elim: ty e=>{Γ m A}.
  { move=>Γ s wf e. right... }
  { move=>Γ x A wf shs e. subst. inv shs. }
  { move=>Γ A B s r t tyA ihA tyB ihB e. right... }
  { move=>Γ A B s r t tyA ihA tyB ihB e. right... }
  { move=>Γ A B m s tym ihm e. right... }
  { move=>Γ A B m s tym ihm e. right... }
  { move=>Γ A B m n s tym ihm tyn ihn e. subst.
    have[[m0 stm]|vlm]:=ihm erefl.
    { left. exists (App m0 n)... }
    { have[[n0 stn]|vln]:=ihn erefl.
      { left. exists (App m n0)... }
      { have[A0[n0 e]]:=logical_pi0_canonical tym (convR _ _) vlm. subst.
        left. exists (n0.[n/])... } } }
  { move=>Γ A B m n s tym ihm tyn ihn e. subst.
    have[[m0 stm]|vlm]:=ihm erefl.
    { left. exists (App m0 n)... }
    { have[[n0 stn]|vln]:=ihn erefl.
      { left. exists (App m n0)... }
      { have[A0[n0 e]]:=logical_pi1_canonical tym (convR _ _) vlm. subst.
        left. exists (n0.[n/])... } } }
  { move=>Γ A B s r t leq tyA ihA tyB ihB e. right... }
  { move=>Γ A B s r t leq1 leq2 tyA ihA tyB ihB e. right... }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn e. subst.
    have[[m' stm]|vlm]:=ihm erefl.
    { left. exists (Pair0 m' n t)... }
    { right... } }
  { move=>Γ A B m n t tyS ihS tym ihm tyn ihn e. subst.
    have[[m' stm]|vlm]:=ihm erefl.
    { left. exists (Pair1 m' n t)... }
    { have[[n' stn]|vln]:=ihn erefl.
      { left. exists (Pair1 m n' t)... }
      { right... } } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn e. subst.
    have[[m' stm]|vlm]:=ihm erefl.
    { left. exists (LetIn C m' n)... }
    { have[m1[m2 e]]:=logical_sig0_canonical tym (convR _ _) vlm. subst.
      left. exists n.[m2,m1/]... } }
  { move=>Γ A B C m n s t tyC ihC tym ihm tyn ihn e. subst.
    have[[m' stm]|vlm]:=ihm erefl.
    { left. exists (LetIn C m' n)... }
    { have[m1[m2 e]]:=logical_sig1_canonical tym (convR _ _) vlm. subst.
      left. exists n.[m2,m1/]... } }
  { move=>Γ A B s r t tyA ihA tyB ihB e. right... }
  { move=>Γ A B m n t tym ihm tyn ihn e. right... }
  { move=>Γ A B m t tym ihm e. subst.
    have[[m' stm]|vlm]:=ihm erefl.
    { left. exists (Fst m')... }
    { have[m1[m2 e]]:=logical_with_canonical tym (convR _ _) vlm. subst.
      left. exists m1... } }
  { move=>Γ A B m t tym ihm e. subst.
    have[[m' stm]|vlm]:=ihm erefl.
    { left. exists (Snd m')... }
    { have[m1[m2 e]]:=logical_with_canonical tym (convR _ _) vlm. subst.
      left. exists m2... } }
  { move=>Γ A m n s tyA ihA tym ihm tyn ihn e. right... }
  { move=>Γ A m tym ihm e. right... }
  { move=>Γ A B H P m n s tyB ihB tyH ihH tyP ihP e. subst.
    have[[P0 stP]|vlP]:=ihP erefl.
    { left. exists (Rw B H P0)... }
    { have[n0 e]:=logical_id_canonical tyP (convR _ _) vlP. subst.
      left. exists H... } }
  { move=>Γ A B m s eq tym ihm tyB ihB e.
    apply: ihm... }
Qed.

Lemma logical_vnX m A :
   sn logical_step m -> nil ⊢ m : A -> (exists n, m ~>* n /\ logical_val n).
Proof with eauto.
  move=>pf. elim: pf A=>{m}.
  move=>m h ih A tym.
  have[[m0 stm]|vlm]:=logical_prog tym.
  { have tym0:=logical_sr tym stm.
    have[n[rn vln]]:=ih _ stm _ tym0.
    exists n. split...
    apply: starES... }
  { exists m... }
Qed.

(* Any logically well-typed closed term can either logically reduce or are already values.
   This will be useful when proving theorems concerning program level equality eliminators. *)
Lemma logical_vn m A :
  nil ⊢ m : A -> (exists n, m ~>* n /\ logical_val n).
Proof with eauto.
  move=>tym.
  apply: logical_vnX...
  apply: logical_sn...
Qed.
