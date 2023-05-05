(* This file presents the type validity theorem of the logical level.
   Additional inversion lemmas can be proven using type validity *)

From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS logical_inv.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Theorem 2 (Type Validity) *)
Theorem logical_valid Γ m A : Γ ⊢ m : A -> exists s, Γ ⊢ A : Sort s.
Proof with eauto using logical_type.
  move=>ty. elim: ty=>{Γ m A}...
  { move=>Γ x A wf hs.
    apply: logical_wf_ok... }
  { move=>Γ A B m s tym [t tyB].
    have wf:=logical_type_wf tyB.
    exists s. inv wf... }
  { move=>Γ A B m s tym [t tyB].
    have wf:=logical_type_wf tyB.
    exists s. inv wf... }
  { move=>Γ A B m n s
      tym[s0/logical_pi0_inv[t[tyB/sort_inj e1]]]tyn _; subst.
    exists t. apply: logical_esubst...
    by autosubst. }
  { move=>Γ A B m n s
      tym[s0/logical_pi1_inv[t[tyB/sort_inj e1]]]tyn _; subst.
    exists t. apply: logical_esubst...
    by autosubst. }
  { move=>Γ A B C m n s t tyC _ tym _ _ _.
    have//={}tyC:=logical_subst tyC tym. exists s... }
  { move=>Γ A B C m n s t tyC _ tym _ _ _.
    have//={}tyC:=logical_subst tyC tym. exists s... }
  { move=>Γ A B m n t _[s tyA]_[r tyB]. exists t... }
  { move=>Γ A B m t _[s/logical_with_inv[r[_[tyA _]]]]. exists r... }
  { move=>Γ A B m t _[s/logical_with_inv[_[r[_[tyB _]]]]]. exists r... }
  { move=>Γ A m tym[s tyA]. exists U... }
  { move=>Γ A B H P m n s tyB _ tyH _ tyP[r tyI].
    have[tym[tyn _]]:=logical_id_inv tyI. exists s.
    replace (Sort s) with (Sort s).[P,n/] by autosubst.
    apply: logical_substitution...
    repeat constructor; asimpl... }
Qed.

(* More inversion lemmas are provable with Type Validity. *)

Lemma logical_lam0_invX Γ A1 A2 B C m s1 s2 t :
  Γ ⊢ Lam0 A1 m s1 : C ->
  C === Pi0 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t ->
  (A2 :: Γ) ⊢ m : B.
Proof with eauto.
  move e:(Lam0 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t e=>//{Γ C n}.
  { move=>Γ A B m s tym _ A1 A2 B0 m0
      s1 s2 t[e1 e2 e3]/pi0_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=logical_type_wf tym. inv wf.
    have wf:=logical_type_wf tyB0. inv wf.
    apply: logical_ctx_conv.
    apply: conv_sym...
    exact: H4.
    apply: logical_conv...
    apply: logical_ctx_conv... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_lam1_invX Γ A1 A2 B C m s1 s2 t :
  Γ ⊢ Lam1 A1 m s1 : C ->
  C === Pi1 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t ->
  (A2 :: Γ) ⊢ m : B.
Proof with eauto.
  move e:(Lam1 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t e=>//{Γ C n}.
  { move=>Γ A B m s tym _ A1 A2 B0 m0
      s1 s2 t[e1 e2 e3]/pi1_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=logical_type_wf tym. inv wf.
    have wf:=logical_type_wf tyB0. inv wf.
    apply: logical_ctx_conv.
    apply: conv_sym...
    exact: H4.
    apply: logical_conv...
    apply: logical_ctx_conv... }
  { move=>Γ A B m s eq1 tym ihm tyB ihB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_lam0_inv Γ m A1 A2 B s1 s2 :
  Γ ⊢ Lam0 A2 m s2 : Pi0 A1 B s1 -> (A1 :: Γ) ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t/logical_pi0_inv[r[tyB _]]]:=logical_valid ty.
  apply: logical_lam0_invX...
Qed.

Lemma logical_lam1_inv Γ m A1 A2 B s1 s2 :
  Γ ⊢ Lam1 A2 m s2 : Pi1 A1 B s1 -> (A1 :: Γ) ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t/logical_pi1_inv[r[tyB _]]]:=logical_valid ty.
  apply: logical_lam1_invX...
Qed.

Lemma logical_pair0_invX Γ m n s C :
  Γ ⊢ Pair0 m n s : C ->
  forall A B r t,
    C === Sig0 A B r ->
    Γ ⊢ Sig0 A B r : Sort t ->
    s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move e:(Pair0 m n s)=>x ty.
  elim: ty m n s e=>//{Γ C x}.
  { move=>Γ A B m n t ty1 _ tym _ tyn _ m0 n0 s[e1 e2 e3]A0 B0 r t0
      /sig0_inj[e4[e5 e6]]ty2; subst.
    have[s[r0[ord[tyA0[tyB0/sort_inj e]]]]]:=logical_sig0_inv ty2; subst.
    have tym0:Γ ⊢ m : A0 by apply: logical_conv; eauto.
    repeat split...
    apply: logical_conv.
    apply: logical_conv_subst.
    all: eauto.
    apply: logical_esubst...
    by autosubst. }
  { move=>Γ A B m s eq tym ihm _ _ m0 n s0 e A0 B0 r t eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_pair1_invX Γ m n s C :
  Γ ⊢ Pair1 m n s : C ->
  forall A B r t,
    C === Sig1 A B r ->
    Γ ⊢ Sig1 A B r : Sort t ->
    s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move e:(Pair1 m n s)=>x ty.
  elim: ty m n s e=>//{Γ C x}.
  { move=>Γ A B m n t ty1 _ tym _ tyn _ m0 n0 s[e1 e2 e3]A0 B0 r t0
      /sig1_inj[e4[e5 e6]]ty2; subst.
    have[s[r0[ord1[ord2[tyA0[tyB0/sort_inj e]]]]]]:=logical_sig1_inv ty2; subst.
    have tym0:Γ ⊢ m : A0 by apply: logical_conv; eauto.
    repeat split...
    apply: logical_conv.
    apply: logical_conv_subst.
    all: eauto.
    apply: logical_esubst...
    by autosubst. }
  { move=>Γ A B m s eq tym ihm _ _ m0 n s0 e A0 B0 r t eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_pair0_inv Γ A B m n s r :
  Γ ⊢ Pair0 m n s : Sig0 A B r ->
  s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move=>ty.
  have[t tyS]:=logical_valid ty.
  apply: logical_pair0_invX...
Qed.

Lemma logical_pair1_inv Γ A B m n s r :
  Γ ⊢ Pair1 m n s : Sig1 A B r ->
  s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move=>ty.
  have[t tyS]:=logical_valid ty.
  apply: logical_pair1_invX...
Qed.

Lemma logical_apair_invX Γ m n s C :
  Γ ⊢ APair m n s : C ->
  forall A B r t,
    C === With A B r ->
    Γ ⊢ With A B r : Sort t ->
    s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.
Proof with eauto.
  move e:(APair m n s)=>x ty.
  elim: ty m n s e=>//{Γ C x}.
  { move=>Γ A B m n t tym ihm tyn ihn m0 n0 s[e1 e2 e3]A0 B0 r t0
      /with_inj[e4[e5 e6]]ty; subst.
    have[s[r0[tyA0[tyB0 _]]]]:=logical_with_inv ty.
    repeat split...
    apply: logical_conv...
    apply: logical_conv... }
  { move=>Γ A B m s eq1 tym ihm _ _ m0 n s0 e A0 B0 r t eq' tyw; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_apair_inv Γ m n A B s r :
  Γ ⊢ APair m n s : With A B r ->
  s = r /\ Γ ⊢ m : A /\ Γ ⊢ n : B.
Proof with eauto.
  move=>ty.
  have[t tyW]:=logical_valid ty.
  apply: logical_apair_invX...
Qed.

Lemma logical_refl_invX Γ n C :
  Γ ⊢ Refl n : C ->
  forall A m1 m2 s,
    C === Id A m1 m2 ->
    Γ ⊢ Id A m1 m2 : Sort s ->
    Γ ⊢ n : A /\ n === m1 /\ n === m2.
Proof with eauto.
  move e:(Refl n)=>x ty.
  elim: ty n e=>//{Γ x C}.
  { move=>Γ A m tym ihm n[e1]A0 m1 m2 s/id_inj[e2[e3 e4]]tyI; subst.
    have[tym1 _]:=logical_id_inv tyI.
    have[r tyA0]:=logical_valid tym1.
    repeat split...
    apply: logical_conv... }
  { move=>Γ A B m s eqw tym ihm _ _ n e A0 m1 m2 s0 eq' tyI.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma logical_refl_inv Γ A m1 m2 n :
  Γ ⊢ Refl n : Id A m1 m2 -> Γ ⊢ n : A /\ n === m1 /\ n === m2.
Proof with eauto.
  move=>ty.
  have[s tyI]:=logical_valid ty.
  apply: logical_refl_invX...
Qed.
