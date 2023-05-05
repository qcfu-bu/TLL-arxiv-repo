From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_sr dyn_sr.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Ltac inv_dyn_val :=
  match goal with
  | [ H : dyn_val _ |- _ ] => inv H
  end.

Lemma dyn_pi0_canonical m A B C s :
  nil ; nil ⊢ m : C -> C === Pi0 A B s -> dyn_val m ->
  exists A n, m = Lam0 A n s.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A B s e1 e2=>//{Γ Δ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_dyn_val)].
  { move=>Γ Δ x s A wf shs dhs A0 B s0 e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m s k tym ihm A0 B0 s0
      e1 e2/pi0_inj[eq1[eq2 e3]] vl; subst.
    exists A. exists m... }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 e1 e2 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_pi1_canonical m A B C s :
  nil ; nil ⊢ m : C -> C === Pi1 A B s -> dyn_val m ->
  exists A n, m = Lam1 A n s.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A B s e1 e2=>//{Γ Δ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_dyn_val)].
  { move=>Γ Δ x s A wf shs dhs A0 B s0 e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m s t k tym ihm A0 B0 s0
      e1 e2/pi1_inj[eq1[eq2 e3]] vl; subst.
    exists A. exists m... }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 e1 e2 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_sig0_canonical m A B C s :
  nil ; nil ⊢ m : C -> C === Sig0 A B s -> dyn_val m ->
  exists m1 m2, m = Pair0 m1 m2 s.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A B s e1 e2=>//{Γ Δ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_dyn_val)].
  { move=>Γ Δ x s A wf shs dhs A0 B s0 e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m n t tyS tym ihm tyn A0 B0 s
      e1 e2/sig0_inj[eq1[eq2 e3]] vl; subst.
    exists m. exists n... }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 e1 e2 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_sig1_canonical m A B C s :
  nil ; nil ⊢ m : C -> C === Sig1 A B s -> dyn_val m ->
  exists m1 m2, m = Pair1 m1 m2 s.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A B s e1 e2=>//{Γ Δ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_dyn_val)].
  { move=>Γ Δ x s A wf shs dhs A0 B s0 e1 e2; subst. inv shs. }
  { move=>Γ Δ1 Δ2 Δ A B m n t mrg tyS tym ihm tyn ihn A0 B0 s
      e1 e2/sig1_inj[eq1[eq2 e3]]vl; subst.
    exists m. exists n... }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 e1 e2 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_with_canonical m A B C s :
  nil ; nil ⊢ m : C -> C === With A B s -> dyn_val m ->
  exists m1 m2, m = APair m1 m2 s.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty A B s e1 e2=>//{Γ Δ m C}.
  all: try solve[intros; exfalso; (solve_conv||inv_dyn_val)].
  { move=>Γ Δ x s A wf shs dhs A0 B s0 e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m n t k tym ihm tyn ihn A0 B0 s
      e1 e2/with_inj[eq1[eq2 e3]]vl; subst.
    exists m. exists n... }
  { move=>Γ Δ A B m s eq1 tym ihm tyB A0 B0 s0 e1 e2 eq2 vl.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_prog m A : nil ; nil ⊢ m : A -> (exists n, m ~>> n) \/ dyn_val m.
Proof with eauto using dyn_step, dyn_val.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty. elim: ty e1 e2=>{Γ Δ m A}.
  { move=>Γ Δ x s A wf shs dhs e1 e2; subst. inv shs. }
  { move=>Γ Δ A B m s k tym ihm e1 e2; subst.
    right... }
  { move=>Γ Δ A B m s t k tym ihm e1 e2; subst.
    right... }
  { move=>Γ Δ A B m n s tym ihm tyn e1 e2; subst.
    have[[x st]|vl]:=ihm erefl erefl.
    { left. exists (App x n)... }
    { left.
      have[A0[n0 e]]:=dyn_pi0_canonical tym (convR _ _) vl.
      subst. exists (n0.[n/])... } }
  { move=>Γ Δ1 Δ2 Δ A B m n s mrg tym ihm tyn ihn e1 e2; subst.
    inv mrg. have[[m' stm]|vlm]:=ihm erefl erefl.
    { left. exists (App m' n)... }
    { left. have[[n' stn]|vln]:=ihn erefl erefl.
      exists (App m n')...
      have[A0[n0 e]]:=dyn_pi1_canonical tym (convR _ _) vlm.
      subst. exists (n0.[n/])... } }
  { move=>Γ Δ A B m n t tyS tym ihm tyn e1 e2; subst.
    have[[m' stm]|vlm]:=ihm erefl erefl.
    { left. exists (Pair0 m' n t)... }
    { right... } }
  { move=>Γ Δ1 Δ2 Δ A B m n t mrg tyS tym ihm tyn ihn e1 e2; subst.
    inv mrg.
    have[[m' stm]|vlm]:=ihm erefl erefl.
    { left. exists (Pair1 m' n t)... }
    { have[[n' stn]|vln]:=ihn erefl erefl.
      { left. exists (Pair1 m n' t)... }
      { right... } } }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r t mrg tyC tym ihm tyn ihn e1 e2; subst.
    inv mrg. have[[m' stm]|vlm]:=ihm erefl erefl.
    { left. exists (LetIn C m' n)... }
    { have[m1[m2 e]]:=dyn_sig0_canonical tym (convR _ _) vlm. subst.
      left. exists n.[m2,m1/]... } }
  { move=>Γ Δ1 Δ2 Δ A B C m n s r1 r2 t mrg tyC tym ihm tyn ihn e1 e2; subst.
    inv mrg. have[[m' stm]|vlm]:=ihm erefl erefl.
    { left. exists (LetIn C m' n)... }
    { have[m1[m2 e]]:=dyn_sig1_canonical tym (convR _ _) vlm. subst.
      left. exists n.[m2,m1/]... } }
  { move=>Γ Δ A B m n t k tym ihm tyn ihn e1 e2; subst. right... }
  { move=>Γ Δ A B m t tym ihm e1 e2; subst.
    have[[m' stm]|vlm]:=ihm erefl erefl.
    { left. exists (Fst m')... }
    { have[m1[m2 e]]:=dyn_with_canonical tym (convR _ _) vlm. subst.
      left. exists m1... } }
  { move=>Γ Δ A B m t tym ihm e1 e2; subst.
    have[[m' stm]|vlm]:=ihm erefl erefl.
    { left. exists (Snd m')... }
    { have[m1[m2 e]]:=dyn_with_canonical tym (convR _ _) vlm. subst.
      left. exists m2... } }
  { move=>Γ Δ A B H P m n s tyB tyH ihH tyP e1 e2. subst.
    left. exists H... }
  { move=>Γ Δ A B m s eq tym ihm tyB e1 e2; subst... }
Qed.
