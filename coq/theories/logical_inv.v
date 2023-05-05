(* The file presents various inversion lemmas for the logical level. *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma logical_pi0_inv Γ A B C s :
  Γ ⊢ Pi0 A B s : C ->
  exists t, (A :: Γ) ⊢ B : Sort t /\ C === Sort s.
Proof with eauto.
  move e:(Pi0 A B s)=>m ty.
  elim: ty A B s e=>//{Γ C m}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0 [e1 e2 e3]; subst.
    exists t... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 s0 e; subst.
    have[t[tyB0 eq2]]:=ihm _ _ _ erefl.
    exists t. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma logical_pi1_inv Γ A B C s :
  Γ ⊢ Pi1 A B s : C ->
  exists t, (A :: Γ) ⊢ B : Sort t /\ C === Sort s.
Proof with eauto.
  move e:(Pi1 A B s)=>m ty.
  elim: ty A B s e=>//{Γ C m}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 s0 [e1 e2 e3]; subst.
    exists t... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 s0 e; subst.
    have[t[tyB0 eq2]]:=ihm _ _ _ erefl.
    exists t. split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq2. }
Qed.

Lemma logical_sig0_inv Γ A B C t :
  Γ ⊢ Sig0 A B t : C ->
  exists s r, s ⊑ t /\ Γ ⊢ A : Sort s /\ (A :: Γ) ⊢ B : Sort r /\ C === Sort t.
Proof with eauto.
  move e:(Sig0 A B t)=>m ty.
  elim: ty A B t e=>//{Γ C m}.
  { move=>Γ A B s r t ord tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst.
    exists s. exists r... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 t e; subst.
    have[s0[r[ord[tyA0[tyB0 eq']]]]]:=ihm _ _ _ erefl.
    exists s0. exists r. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq'. }
Qed.

Lemma logical_sig1_inv Γ A B C t :
  Γ ⊢ Sig1 A B t : C ->
  exists s r,
    s ⊑ t /\ r ⊑ t /\
    Γ ⊢ A : Sort s /\ (A :: Γ) ⊢ B : Sort r /\ C === Sort t.
Proof with eauto.
  move e:(Sig1 A B t)=>m ty.
  elim: ty A B t e=>//{Γ C m}.
  { move=>Γ A B s r t ord1 ord2 tyA ihA tyB ihB A0 B0 s0[e1 e2 e3]; subst.
    exists s. exists r... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 t e; subst.
    have[s0[r[ord1[ord2[tyA0[tyB0 eq']]]]]]:=ihm _ _ _ erefl.
    exists s0. exists r. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq'. }
Qed.

Lemma logical_with_inv Γ A B C t :
  Γ ⊢ With A B t : C ->
  exists s r, Γ ⊢ A : Sort s /\ Γ ⊢ B : Sort r /\ C === Sort t.
Proof with eauto.
  move e:(With A B t)=>n tyW.
  elim: tyW A B t e=>//{Γ C n}.
  { move=>Γ A B s r t tyA ihA tyB ihB A0 B0 t0[e1 e2 e3]; subst.
    exists s. by exists r. }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 B0 t e; subst.
    have[x[y[tyA[tyB0 eq']]]]:=ihm _ _ _ erefl.
    exists x. exists y. repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq'. }
Qed.

Lemma logical_id_inv Γ A B m n :
  Γ ⊢ Id A m n : B ->
  Γ ⊢ m : A /\ Γ ⊢ n : A /\ B === Sort U.
Proof with eauto.
  move e:(Id A m n)=>x tyI.
  elim: tyI A m n e=>//{Γ x B}.
  { move=>Γ A m n s tyA ihA tym ihm tyn ihn A0 m0 n0[e1 e2 e3]; subst... }
  { move=>Γ A B m s eq tym ihm tyB ihB A0 m0 n e; subst.
    have[tym0[tyn eq']]:=ihm _ _ _ erefl.
    repeat split...
    apply: conv_trans.
    apply: conv_sym...
    exact: eq'. }
Qed.

Lemma logical_lam0_pi1_false Γ A1 A2 B C m s1 s2 :
  Γ ⊢ Lam0 A1 m s1 : C -> C === Pi1 A2 B s2 -> False.
Proof with eauto.
  move e:(Lam0 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 e=>//{Γ C n}.
  { move=>*. solve_conv. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A1 A2 B0 m0 s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_lam1_pi0_false Γ A1 A2 B C m s1 s2 :
  Γ ⊢ Lam1 A1 m s1 : C -> C === Pi0 A2 B s2 -> False.
Proof with eauto.
  move e:(Lam1 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 e=>//{Γ C n}.
  { move=>*. solve_conv. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A1 A2 B0 m0 s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_pair0_sig1_false Γ A B C m1 m2 s1 s2 :
  Γ ⊢ Pair0 m1 m2 s1 : C -> C === Sig1 A B s2 -> False.
Proof with eauto.
  move e:(Pair0 m1 m2 s1)=>n tyP.
  elim: tyP A B m1 m2 s1 s2 e=>//{Γ C n}.
  { move=>*. solve_conv. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 m1 m2 s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_pair1_sig0_false Γ A B C m1 m2 s1 s2 :
  Γ ⊢ Pair1 m1 m2 s1 : C -> C === Sig0 A B s2 -> False.
Proof with eauto.
  move e:(Pair1 m1 m2 s1)=>n tyP.
  elim: tyP A B m1 m2 s1 s2 e=>//{Γ C n}.
  { move=>*. solve_conv. }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A0 B0 m1 m2 s1 s2 e eq2; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.
