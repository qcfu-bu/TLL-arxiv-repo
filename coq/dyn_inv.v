From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS sta_uniq sta_sr dyn_subst.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma dyn_lam0_invX Γ Δ A1 A2 B C m s1 s2 t :
  Γ ; Δ ⊢ Lam0 A1 m s1 : C ->
  C === Pi0 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t ->
  (A2 :: Γ) ; _: Δ ⊢ m : B.
Proof with eauto.
  move e:(Lam0 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t e=>//{Γ Δ C n}.
  { move=>Γ Δ A B m s k tym _ A1 A2 B0 m0
      s1 s2 t[e1 e2 e3]/pi0_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=dyn_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    apply: dyn_ctx_conv0.
    apply: conv_sym...
    exact: H4.
    apply: dyn_conv...
    apply: sta_ctx_conv... }
  { move=>Γ Δ A B m s eq tym ihm tyB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_lam1_invX Γ Δ A1 A2 B C m s1 s2 t :
  Γ ; Δ ⊢ Lam1 A1 m s1 : C ->
  C === Pi1 A2 B s2 ->
  (A2 :: Γ) ⊢ B : Sort t ->
  exists r, (A2 :: Γ) ; A2 :{r} Δ ⊢ m : B.
Proof with eauto.
  move e:(Lam1 A1 m s1)=>n tyL.
  elim: tyL A1 A2 B m s1 s2 t e=>//{Γ Δ C n}.
  { move=>Γ Δ A B m s t k tym _ A1 A2 B0 m0
      s1 s2 t0[e1 e2 e3]/pi1_inj[eq1[eq2 e4]]tyB0; subst.
    have wf:=dyn_type_wf tym. inv wf.
    have wf:=sta_type_wf tyB0. inv wf.
    have[A0 rd1 rd2]:=church_rosser eq1.
    have tyA0t:=sta_rd H4 rd1.
    have tyA0s:=sta_rd H3 rd2.
    have e:=sta_unicity tyA0t tyA0s. subst.
    exists s.
    apply: dyn_ctx_conv1.
    apply: conv_sym...
    exact: H3.
    apply: dyn_conv...
    apply: sta_ctx_conv... }
  { move=>Γ Δ A B m s eq tym ihm tyB A1 A2 B0 m0
      s1 s2 t e eq2 tyB0; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_lam0_inv Γ Δ m A1 A2 B s1 s2 :
  Γ ; Δ ⊢ Lam0 A2 m s2 : Pi0 A1 B s1 -> (A1 :: Γ) ; _: Δ ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t/sta_pi0_inv[r[tyB _]]]:=dyn_valid ty.
  apply: dyn_lam0_invX...
Qed.

Lemma dyn_lam1_inv Γ Δ m A1 A2 B s1 s2 :
  Γ ; Δ ⊢ Lam1 A2 m s2 : Pi1 A1 B s1 -> exists r, (A1 :: Γ) ; A1 :{r} Δ ⊢ m : B.
Proof with eauto.
  move=>ty.
  have[t/sta_pi1_inv[r[tyB _]]]:=dyn_valid ty.
  apply: dyn_lam1_invX...
Qed.

Lemma dyn_pair0_invX Γ Δ A B m n s r t C :
  Γ ; Δ ⊢ Pair0 m n s : C ->
  C === Sig0 A B r ->
  Γ ⊢ Sig0 A B r : Sort t ->
  s = r /\ Γ ; Δ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move e:(Pair0 m n s)=>x ty.
  elim: ty A B m n s r t e=>//{Γ Δ x C}.
  { move=>Γ Δ A B m n t ty1 tym ihm tyn A0 B0 m0 n0 s r t0[e1 e2 e3]
      /sig0_inj[e4[e5 e6]]ty2; subst.
    have[s[r0[ord[tyA0[tyB0/sort_inj e]]]]]:=sta_sig0_inv ty2. subst.
    have tym0:Γ ; Δ ⊢ m : A0 by apply: dyn_conv; eauto.
    repeat split...
    apply: sta_conv.
    apply: sta_conv_subst.
    all: eauto.
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ Δ A B m s eq tym ihm tyB A0 B0 m0 n s0 r t e eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_pair1_invX Γ Δ A B m n s r t C :
  Γ ; Δ ⊢ Pair1 m n s : C ->
  C === Sig1 A B r ->
  Γ ⊢ Sig1 A B r : Sort t ->
  exists Δ1 Δ2,
    Δ1 ∘ Δ2 => Δ /\ s = r /\
    Γ ; Δ1 ⊢ m : A /\ Γ ; Δ2 ⊢ n : B.[m/].
Proof with eauto.
  move e:(Pair1 m n s)=>x ty.
  elim: ty A B m n s r t e=>//{Γ Δ x C}.
  { move=>Γ Δ1 Δ2 Δ A B m n t mrg ty1 tym _ tyn _ A0 B0 m0 n0 s r t0
      [e1 e2 e3]/sig1_inj[e4[e5 e6]]ty2; subst.
    exists Δ1. exists Δ2.
    have[s[r0[ord1[ord2[tyA0[tyB0/sort_inj e]]]]]]:=sta_sig1_inv ty2. subst.
    have tym0:Γ ; Δ1 ⊢ m : A0 by apply: dyn_conv; eauto.
    repeat split...
    apply: dyn_conv.
    apply: sta_conv_subst.
    all: eauto.
    apply: sta_esubst...
    by autosubst. }
  { move=>Γ Δ A B m s eq tym ihm tyB A0 B0 m0 n s0 r t e eq' ty.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_pair0_inv Γ Δ A B m n s r :
  Γ ; Δ ⊢ Pair0 m n s : Sig0 A B r ->
  s = r /\ Γ ; Δ ⊢ m : A /\ Γ ⊢ n : B.[m/].
Proof with eauto.
  move=>ty.
  have[t tyS]:=dyn_valid ty.
  apply: dyn_pair0_invX...
Qed.

Lemma dyn_pair1_inv Γ Δ A B m n s r :
  Γ ; Δ ⊢ Pair1 m n s : Sig1 A B r ->
  exists Δ1 Δ2,
    Δ1 ∘ Δ2 => Δ /\ s = r /\
    Γ ; Δ1 ⊢ m : A /\ Γ ; Δ2 ⊢ n : B.[m/].
Proof with eauto.
  move=>ty.
  have[t tyS]:=dyn_valid ty.
  apply: dyn_pair1_invX...
Qed.

Lemma dyn_apair_invX Γ Δ A B m n s r t C :
  Γ ; Δ ⊢ APair m n s : C ->
  C === With A B r ->
  Γ ⊢ With A B r : Sort t ->
  s = r /\ Γ ; Δ ⊢ m : A /\ Γ ; Δ ⊢ n : B.
Proof with eauto.
  move e:(APair m n s)=>x ty.
  elim: ty A B m n s r t e=>//{Γ Δ x C}.
  { move=>Γ Δ A B m n t k tym ihm tyn ihn A0 B0 m0 n0 s r t0
      [e1 e2 e3]/with_inj[e4[e5 e6]]ty; subst.
    have[s[r0[tyA0[tyB0 _]]]]:=sta_with_inv ty.
    repeat split...
    apply: dyn_conv...
    apply: dyn_conv... }
  { move=>Γ Δ A B m s eq tym ihm _ A0 B0 m0 n s0 r t e eq' tyw; subst.
    apply: ihm...
    apply: conv_trans... }
Qed.

Lemma dyn_apair_inv Γ Δ A B m n s r :
  Γ ; Δ ⊢ APair m n s : With A B r ->
  s = r /\ Γ ; Δ ⊢ m : A /\ Γ ; Δ ⊢ n : B.
Proof with eauto.
  move=>ty.
  have[t tyW]:=dyn_valid ty.
  apply: dyn_apair_invX...
Qed.
