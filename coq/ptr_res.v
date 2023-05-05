From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS era_type.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive pad (H : dyn_ctx) : dyn_ctx -> Prop :=
| pad_O : pad H H
| pad_U H' m : pad H H' -> pad H (m :U H')
| pad_N H' : pad H H' -> pad H (_: H').

Inductive free : dyn_ctx -> nat -> term -> dyn_ctx -> Prop :=
| free_U H m l :
  l = size H ->
  free (m :U H) l m (m :U H)
| free_L H m l :
  l = size H ->
  free (m :L H) l m (_: H)
| free_S H H' m n l :
  free H l m H' ->
  free (n :: H) l m (n :: H').

Reserved Notation "H ; m ~ n" (at level 50, m, n at next level).
Inductive resolve : dyn_ctx -> term -> term -> Prop :=
| resolve_var H x :
  H ▷ U ->
  H ; Var x ~ Var x
| resolve_lam0 H m m' s :
  H ▷ s ->
  H ; m ~ m' ->
  H ; Lam0 Box m s ~ Lam0 Box m' s
| resolve_lam1 H m m' s :
  H ▷ s ->
  H ; m ~ m' ->
  H ; Lam1 Box m s ~ Lam1 Box m' s
| resolve_app0 H m m' :
  H ; m ~ m' ->
  H ; App m Box ~ App m' Box
| resolve_app1 H1 H2 H m m' n n' :
  H1 ∘ H2 => H ->
  H1 ; m ~ m' ->
  H2 ; n ~ n' ->
  H ; App m n ~ App m' n'
| resolve_pair0 H m m' t :
  H ; m ~ m' ->
  H ; Pair0 m Box t ~ Pair0 m' Box t
| resolve_pair1 H1 H2 H m m' n n'  t :
  H1 ∘ H2 => H ->
  H1 ; m ~ m' ->
  H2 ; n ~ n' ->
  H ; Pair1 m n t ~ Pair1 m' n' t
| resolve_letin H1 H2 H m m' n n' :
  H1 ∘ H2 => H ->
  H1 ; m ~ m' ->
  H2 ; n ~ n' ->
  H ; LetIn Box m n ~ LetIn Box m' n'
| resolve_apair H m m' n n' t :
  H ▷ t ->
  H ; m ~ m' ->
  H ; n ~ n' ->
  H ; APair m n t ~ APair m' n' t
| resolve_fst H m m' :
  H ; m ~ m' ->
  H ; Fst m ~ Fst m'
| resolve_snd H m m' :
  H ; m ~ m' ->
  H ; Snd m ~ Snd m'
| resolve_rw H m m' :
  H ; m ~ m' ->
  H ; Rw Box m Box ~ Rw Box m' Box
| resolve_ptr H H' l m m' :
  free H l m H' ->
  H' ; m ~ m' ->
  H ; Ptr l ~ m'
where "H ; m ~ n" := (resolve H m n).

Inductive resolved : term -> Prop :=
| resolved_var x :
  resolved (Var x)
| resolved_lam0 m s :
  resolved m ->
  resolved (Lam0 Box m s)
| resolved_lam1 m s :
  resolved m ->
  resolved (Lam1 Box m s)
| resolved_app0 m :
  resolved m ->
  resolved (App m Box)
| resovled_app1 m n :
  resolved m ->
  resolved n ->
  resolved (App m n)
| resolved_pair0 m t :
  resolved m ->
  resolved (Pair0 m Box t)
| resolved_pair1 m n t :
  resolved m ->
  resolved n ->
  resolved (Pair1 m n t)
| resolved_letin m n :
  resolved m ->
  resolved n ->
  resolved (LetIn Box m n)
| resolved_apair m n t :
  resolved m ->
  resolved n ->
  resolved (APair m n t)
| resolved_fst m :
  resolved m ->
  resolved (Fst m)
| resolved_snd m :
  resolved m ->
  resolved (Snd m)
| resolved_rw m :
  resolved m ->
  resolved (Rw Box m Box).

Lemma pad_key H H' s : pad H H' -> H ▷ s -> H' ▷ s.
Proof with eauto using key.
  move=>pd. elim: pd s=>//{H'}...
  move=>H' m pd ih [|] k...
Qed.

Lemma pad_mergeL H1 H2 H H1p :
  pad H1 H1p -> H1 ∘ H2 => H ->
  exists H2p Hp, pad H2 H2p /\ pad H Hp /\ H1p ∘ H2p => Hp.
Proof with eauto 6 using pad, merge.
  move=>pd. elim: pd H2 H=>{H1p}.
  { move=>H2 H mrg. exists H2. exists H... }
  { move=>H' m pd1 ih H2 H mrg.
    have[H2p[Hp[pd2[pd mrg']]]]:=ih _ _ mrg.
    exists (m :U H2p). exists (m :U Hp)... }
  { move=>H' pd1 ih H2 H mrg.
    have[H2p[Hp[pd2[pd mrg']]]]:=ih _ _ mrg.
    exists (_: H2p). exists (_: Hp)... }
Qed.

Lemma pad_mergeR H1 H2 H H2p :
  pad H2 H2p -> H1 ∘ H2 => H ->
  exists H1p Hp, pad H1 H1p /\ pad H Hp /\ H1p ∘ H2p => Hp.
Proof with eauto.
  move=>pd/merge_sym mrg.
  have[H1p[Hp[pd1[pd2/merge_sym mrg']]]]:=pad_mergeL pd mrg.
  exists H1p. exists Hp...
Qed.

Lemma pad_merge H1 H2 H Hp :
  pad H Hp -> H1 ∘ H2 => H ->
  exists H1p H2p, pad H1 H1p /\ pad H2 H2p /\ H1p ∘ H2p => Hp.
Proof with eauto 6 using pad, merge.
  move=>pd. elim: pd H1 H2=>{Hp}.
  { move=>H1 H2 mrg. exists H1. exists H2... }
  { move=>H' m pd ih H1 H2 mrg.
    have[H1p[H2p[pd1[pd2 mrg']]]]:=ih _ _ mrg.
    exists (m :U H1p). exists (m :U H2p)... }
  { move=>H' pd ih H1 H2 mrg.
    have[H1p[H2p[pd1[pd2 mrg']]]]:=ih _ _ mrg.
    exists (_: H1p). exists (_: H2p)... }
Qed.

Lemma ptr_resolve_resolved H m m' : H ; m ~ m' -> resolved m'.
Proof with eauto using resolved. elim=>{H m m'}... Qed.

Reserved Notation "H ; x ~ y ~ z : A" (at level 50, x, y, z, A at next level).
Inductive ptr_well_resolved :
  dyn_ctx -> term -> term -> term -> term -> Prop :=
| Ptr_well_resolved H x y z A :
  nil ; nil ⊢ x ~ y : A ->
  H ; z ~ y ->
  H ; x ~ y ~ z : A
where "H ; x ~ y ~ z : A" := (ptr_well_resolved H x y z A).

Lemma resolve_wkU H m m' n : H ; m ~ m' -> (n :U H) ; m ~ m'.
Proof with eauto using resolve, key, merge.
  move=>rs. elim: rs n=>{H m m'}...
  { move=>H m m' [|] k rs ih n... }
  { move=>H m m' [|] k rs ih n... }
  { move=>H m m' n n' [|] k rsm ihm rsn ihn x... }
  { move=>H H' l m m' fr rsm ihm n.
    have{}ih:=ihm n.
    apply: resolve_ptr...
    constructor... }
Qed.

Lemma resolve_wkN H m m' : H ; m ~ m' -> (_: H) ; m ~ m'.
Proof with eauto using resolve, key, merge.
  move=>rs. elim: rs=>{H m m'}...
  move=>H H' l m m' fr rs ih.
  apply: resolve_ptr...
  constructor...
Qed.

Lemma resolve_pad H H' m m' :
  pad H H' -> H ; m ~ m' -> H' ; m ~ m'.
Proof with eauto using resolve_wkU, resolve_wkN.
  move=>pd. elim: pd m m'=>{H'}...
Qed.

Lemma resolve_era_refl H Γ Δ m n A :
  Γ ; Δ ⊢ m ~ n : A -> H ▷ U -> H ; n ~ n.
Proof with eauto using resolve, key_impure, merge_pure_refl.
  move=>er. elim: er H=>//{Γ Δ m n A}...
  { move=>Γ Δ A B m m' [|] k1 erm ihm k2... }
  { move=>Γ Δ A B m m' [|] t k1 erm ihm k2... }
  { move=>Γ Δ A B m m' n n' [|] k1 tym ihm tyn ihn H k2... }
Qed.

Lemma resolve_era_id H Γ Δ x y z A :
  Γ ; Δ ⊢ x ~ y : A -> H ; y ~ z -> y = z.
Proof with eauto using resolve.
  move=>ty. elim: ty H z=>//{Γ Δ x y A}...
  { move=>Γ Δ x s A wf shs dhs H z rs. inv rs... }
  { move=>Γ Δ A B m m' s k erm ihm H z rs. inv rs.
    have->//:=ihm _ _ H6. }
  { move=>Γ Δ A B m m' s t k erm ihm H z rs. inv rs.
    have->//:=ihm _ _ H6. }
  { move=>Γ Δ A B m m' n s erm ihm tyn H z rs. inv rs.
    { have->//:=ihm _ _ H3. }
    { inv H9. } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn H z rs. inv rs.
    { have->//:=ihm _ _ H5. }
    { have->:=ihm _ _ H7.
      have->//:=ihn _ _ H9. } }
  { move=>Γ Δ A B m m' n t tyS erm ihm tyn H z rs. inv rs.
    have->//:=ihm _ _ H5. }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg tyS erm ihm ern ihn H z rs. inv rs.
    have->:=ihm _ _ H9.
    have->//:=ihn _ _ H10. }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg tyC erm ihm ern ihn H z rs. inv rs.
    have->:=ihm _ _ H7.
    have->//:=ihn _ _ H9. }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg tyC erm ihm ern ihn H z rs. inv rs.
    have->:=ihm _ _ H7.
    have->//:=ihn _ _ H9. }
  { move=>Γ Δ A B m m' n n' t k erm ihm ern ihn H z rs. inv rs.
    have->:=ihm _ _ H7.
    have->//:=ihn _ _ H8. }
  { move=>Γ Δ A B m m' t erm ihm H z rs. inv rs.
    have->//:=ihm _ _ H3. }
  { move=>Γ Δ A B m m' t erm ihm H z rs. inv rs.
    have->//:=ihm _ _ H3. }
  { move=>Γ Δ A B x x' P m n s tyB erH ihH tyP H0 z rs. inv rs.
    f_equal... }
Qed.

Lemma free_size H l m H' : free H l m H' -> l < size H.
Proof with eauto.
  elim=>{H l m H'}.
  { move=>H m l->//. }
  { move=>H m l->//. }
  { move=>H H' m n l fr lt//=.
    apply: leq_trans... }
Qed.

Lemma free_inv H H' m n t :
  free (m :{t} H) (size H) n H' ->
  m = n /\
  match t with
  | U => m :{t} H
  | L => _: H
  end = H'.
Proof with eauto.
  elim: H H' m n t=>//=.
  { move=>H' m n t fr. inv fr=>//. inv H5. }
  { move=>a H ih H' m n t fr. inv fr=>//. exfalso. inv H6.
    { have:(size H).+1 - size H = size H - size H by rewrite H7.
      rewrite subnn.
      rewrite subSnn=>//. }
    { have:(size H).+1 - size H = size H - size H by rewrite H7.
      rewrite subnn.
      rewrite subSnn=>//. }
    { move/free_size in H7.
      have lt : size H < (size H).+2 by eauto.
      have h:=leq_trans H7 lt.
      unfold leq in h.
      rewrite subSnn in h.
      move/eqnP in h. inv h. } }
Qed.

Lemma free_empty H H' n : ~free (_: H) (size H) n H'.
Proof with eauto.
  elim: H H' n=>//=.
  { move=>H' n fr. inv fr. inv H5. }
  { move=>a H ih H' n fr. inv fr. inv H6.
    { have:(size H).+1 - size H = size H - size H by rewrite H7.
      rewrite subnn.
      rewrite subSnn=>//. }
    { have:(size H).+1 - size H = size H - size H by rewrite H7.
      rewrite subnn.
      rewrite subSnn=>//. }
    { move/free_size in H7.
      have lt : size H < (size H).+2 by eauto.
      have h:=leq_trans H7 lt.
      unfold leq in h.
      rewrite subSnn in h.
      move/eqnP in h. inv h. } }
Qed.

Lemma free_merge H1 H2 H3 H l m :
  free H1 l m H3 -> H1 ∘ H2 => H ->
  exists H4, free H l m H4 /\ H3 ∘ H2 => H4.
Proof with eauto using free, merge.
  move=>fr. elim: fr H2 H=>{H1 H3 l m}.
  { move=>H m l e H2 H0 mrg; subst. inv mrg.
    exists (m :U Δ). split...
    econstructor.
    have[->_]//:=merge_size H6. }
  { move=>H m l e H2 H0 mrg; subst. inv mrg.
    exists (_: Δ). split...
    econstructor.
    have[->_]//:=merge_size H6. }
  { move=>H H' m n l fr ih H2 H0 mrg. inv mrg.
    { have[H4[fr0 mrg]]:=ih _ _ H6. exists (m0 :U H4). split... }
    { have[H4[fr0 mrg]]:=ih _ _ H6. exists (m0 :L H4). split... }
    { have[H4[fr0 mrg]]:=ih _ _ H6. exists (m0 :L H4). split... }
    { have[H4[fr0 mrg]]:=ih _ _ H6. exists (_: H4). split... } }
Qed.

Lemma free_pure H H' m l : free H l m H' -> H ▷ U -> H' ▷ U.
Proof with eauto using key.
  elim=>//{H H' m l}.
  { move=>H m l e k. inv k. }
  { move=>H H' m n l fr ih k. inv k... }
Qed.

Lemma free_subheap H H1 H2 H' H1' l m n :
  H1 ∘ H2 => H -> free H l m H' -> free H1 l n H1' -> m = n /\ H1' ∘ H2 => H'.
Proof with eauto 6 using merge.
  move=>mrg. elim: mrg l m n H' H1'=>{H H1 H2}.
  { move=>l m n H' H1' fr. inv fr. }
  { move=>Δ1 Δ2 Δ m mrg ih l m0 n H' H1' fr1 fr2.
    have[e1 e2]:=merge_size mrg.
    inv fr1; inv fr2...
    { move/free_size in H5.
      rewrite e1 in H5.
      rewrite ltnn in H5. inv H5. }
    { move/free_size in H5.
      rewrite e1 in H5.
      rewrite ltnn in H5. inv H5. }
    { have[e mrg']:=ih _ _ _ _ _ H5 H6. split... } }
  { move=>Δ1 Δ2 Δ m mrg ih l m0 n H' H1' fr1 fr2.
    have[e1 e2]:=merge_size mrg.
    inv fr1; inv fr2...
    { move/free_size in H5.
      rewrite e1 in H5.
      rewrite ltnn in H5. inv H5. }
    { move/free_size in H5.
      rewrite e1 in H5.
      rewrite ltnn in H5. inv H5. }
    { have[e mrg']:=ih _ _ _ _ _ H5 H6. split... } }
  { move=>Δ1 Δ2 Δ m mrg ih l m0 n H' H1' fr1 fr2.
    have[e1 e2]:=merge_size mrg.
    inv fr1; inv fr2.
    { move/free_size in H5.
      rewrite e1 in H5.
      rewrite ltnn in H5. inv H5. }
    { have[e mrg']:=ih _ _ _ _ _ H5 H6. split... } }
  { move=>Δ1 Δ2 Δ mrg ih l m n H' H1' fr1 fr2.
    inv fr1; inv fr2.
    have[e mrg']:=ih _ _ _ _ _ H5 H6. split... }
Qed.

Lemma resolve_merge_pure H1 H2 H m m' :
  H1 ; m ~ m' -> H1 ∘ H2 => H -> H2 ▷ U -> H ; m ~ m'.
Proof with eauto using resolve, resolve_wkU, resolve_wkN.
  move=>rs. elim: rs H2 H=>{H1 m m'}...
  { move=>H x k1 H2 H0 mrg k2.
    constructor...
    apply: merge_pure... }
  { move=>H m m' s k1 rm ihm H2 H0 mrg k2.
    constructor...
    have->//:=merge_pureR mrg k2. }
  { move=>H m m' s k1 rm ihm H2 H0 mrg k2.
    constructor...
    have->//:=merge_pureR mrg k2. }
  { move=>H1 H2 H m m' n n' mrg1 erm ihm ern ihn H0 H3 mrg2 k.
    have[H4[mrg3 mrg4]]:=merge_splitL mrg2 mrg1.
    econstructor.
    apply: mrg4.
    apply: ihm...
    apply: ern. }
  { move=>H1 H2 H m m' n n' t mrg1 erm ihm ern ihn H0 H3 mrg2 k.
    have[H4[mrg3 mrg4]]:=merge_splitL mrg2 mrg1.
    econstructor.
    apply: mrg4.
    apply: ihm...
    apply: ern. }
  { move=>H1 H2 H m m' n n' mrg1 erm ihm ern ihn H0 H3 mrg2 k.
    have[H4[mrg3 mrg4]]:=merge_splitL mrg2 mrg1.
    econstructor.
    apply: mrg4.
    apply: ihm...
    apply: ern. }
  { move=>H m m' n n' t k1 erm ihm ern ihn H2 H0 mrg k2.
    econstructor...
    have->//:=merge_pureR mrg k2. }
  { move=>H H' l m m' fr erm ihm H2 H0 mrg k.
    econstructor...
    have->//:=merge_pureR mrg k. }
Qed.

Lemma resolve_free H1 H2 H H' l m n :
  free H l m H' -> H1 ; Ptr l ~ n -> H1 ∘ H2 => H ->
  exists H1', H1' ∘ H2 => H' /\ H1' ; m ~ n.
Proof with eauto using merge.
  move=>fr rs mrg. inv rs.
  have[->mrg']:=free_subheap mrg fr H4.
  exists H'0...
Qed.

Inductive nf : nat -> term -> Prop :=
| nf_var i x :
  x < i ->
  nf i (Var x)
| nf_lam0 i m s :
  nf i.+1 m ->
  nf i (Lam0 Box m s)
| nf_lam1 i m s :
  nf i.+1 m ->
  nf i (Lam1 Box m s)
| nf_app0 i m :
  nf i m ->
  nf i (App m Box)
| nf_app1 i m n :
  nf i m ->
  nf i n ->
  nf i (App m n)
| nf_pair0 i m t :
  nf i m ->
  nf i (Pair0 m Box t)
| nf_pair1 i m n t :
  nf i m ->
  nf i n ->
  nf i (Pair1 m n t)
| nf_letin i m n :
  nf i m ->
  nf i.+2 n ->
  nf i (LetIn Box m n)
| nf_apair i m n t :
  nf i m ->
  nf i n ->
  nf i (APair m n t)
| nf_fst i m :
  nf i m ->
  nf i (Fst m)
| nf_snd i m :
  nf i m ->
  nf i (Snd m)
| nf_rw i m :
  nf i m ->
  nf i (Rw Box m Box)
| nf_ptr i l :
  nf i (Ptr l).

Inductive wr_heap : dyn_ctx -> Prop :=
| wr_nil : wr_heap nil
| wr_lam0 H m s :
  nf 1 m ->
  wr_heap H ->
  wr_heap (Lam0 Box m s :{s} H)
| wr_lam1 H m s :
  nf 1 m ->
  wr_heap H ->
  wr_heap (Lam1 Box m s :{s} H)
| wr_pair0 H lm t :
  wr_heap H ->
  wr_heap (Pair0 (Ptr lm) Box t :{t} H)
| wr_pair1 H lm ln t :
  wr_heap H ->
  wr_heap (Pair1 (Ptr lm) (Ptr ln) t :{t} H)
| wr_apair H m n t :
  nf 0 m ->
  nf 0 n ->
  wr_heap H ->
  wr_heap (APair m n t :{t} H)
| wr_N H :
  wr_heap H ->
  wr_heap (_: H).

Lemma nf_typing Γ Δ m n A :
  Γ ; Δ ⊢ m ~ n : A -> nf (size Γ) n.
Proof with eauto using nf.
  elim=>//{Γ Δ m n A}...
  move=>Γ Δ x s A wf shs dhs.
  constructor.
  apply:sta_has_size shs.
Qed.

Lemma free_wr_nf H l m H' :
  free H l m H' -> wr_heap H -> nf 0 m.
Proof with eauto using nf.
  elim=>//{H l m H'}.
  { move=>H m l e wr. inv wr... }
  { move=>H m l e wr. inv wr... }
  { move=>H H' m n l fr ih wr. inv wr... }
Qed.

Lemma wr_merge H1 H2 H :
  H1 ∘ H2 => H -> wr_heap H1 -> wr_heap H2 -> wr_heap H.
Proof with eauto using wr_heap.
  elim=>{H1 H2 H}...
  { move=>H1 H2 H m mrg ih wr1 wr2.
    inv wr1; inv wr2; constructor... }
  { move=>H1 H2 H m mrg ih wr1 wr2.
    inv wr1; inv wr2; constructor... }
  { move=>H1 H2 H m mrg ih wr1 wr2.
    inv wr1; inv wr2; constructor... }
  { move=>H1 H2 H mrg ih wr1 wr2.
    inv wr1; inv wr2; constructor... }
Qed.

Lemma wr_merge_inv H1 H2 H :
  H1 ∘ H2 => H -> wr_heap H -> wr_heap H1 /\ wr_heap H2.
Proof with eauto using wr_heap.
  elim=>{H1 H2 H}...
  { move=>H1 H2 H m mrg ih wr. inv wr.
    { have[wr1 wr2]:=ih H7... }
    { have[wr1 wr2]:=ih H7... }
    { have[wr1 wr2]:=ih H4... }
    { have[wr1 wr2]:=ih H4... }
    { have[wr1 wr2]:=ih H8... } }
  { move=>H1 H2 H m mrg ih wr. inv wr.
    { have[wr1 wr2]:=ih H7... }
    { have[wr1 wr2]:=ih H7... }
    { have[wr1 wr2]:=ih H4... }
    { have[wr1 wr2]:=ih H4... }
    { have[wr1 wr2]:=ih H8... } }
  { move=>H1 H2 H m mrg ih wr. inv wr.
    { have[wr1 wr2]:=ih H7... }
    { have[wr1 wr2]:=ih H7... }
    { have[wr1 wr2]:=ih H4... }
    { have[wr1 wr2]:=ih H4... }
    { have[wr1 wr2]:=ih H8... } }
  { move=>H1 H2 H mrg ih wr. inv wr.
    have[wr1 wr2]:=ih H4... }
Qed.

Lemma free_wr H H' l m : free H l m H' -> wr_heap H -> wr_heap H'.
Proof with eauto using wr_heap.
  elim=>{H l m H'}...
  { move=>H m l e wr. inv wr... }
  { move=>H H' m n l fr ih wr. inv wr... }
Qed.

Lemma nf_weaken i j m : nf i m -> i <= j -> nf j m.
Proof with eauto using nf.
  move=>nfm. elim: nfm j=>{m i}...
  move=>i x lt1 j lt2.
  constructor.
  apply: leq_trans...
Qed.

Lemma resolve_wr_box H m : wr_heap H -> ~H ; m ~ Box.
Proof with eauto.
  move e:(Box)=>n wr rs. elim: rs wr e=>//{H m n}.
  move=>H H' l m m' fr rs ih wr e; subst.
  apply: ih...
  apply: free_wr...
Qed.

Lemma resolve_wr_nfi H m m' i :
  H ; m ~ m' -> wr_heap H -> nf i m' -> nf i m.
Proof with eauto using nf.
  move=>rs. elim: rs i=>{H m m'}...
  { move=>H m m' s k rsm ihm i wr nfL. inv nfL... }
  { move=>H m m' s k rsm ihm i wr nfL. inv nfL... }
  { move=>H m m' rsm ihm i wr nfA. inv nfA... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn i wr nfA. inv nfA...
    { have[wr1 wr2]:=wr_merge_inv mrg wr.
      exfalso. apply: resolve_wr_box... }
    { have[wr1 wr2]:=wr_merge_inv mrg wr... } }
  { move=>H m m' t rsm ihm i wr nfP. inv nfP... }
  { move=>H1 H2 H m m' n n' t mrg rsm ihm rsn ihn i wr nfP. inv nfP.
    have[wr1 wr2]:=wr_merge_inv mrg wr... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn i wr nfL. inv nfL.
    have[wr1 wr2]:=wr_merge_inv mrg wr... }
  { move=>H m m' n n' t k rsm ihm rsn ihn i wr nfP. inv nfP... }
  { move=>H m m' rsm ihm i wr nfF. inv nfF... }
  { move=>H m m' rsm ihm i wr nfS. inv nfS... }
  { move=>H m m' rsm ihm i wr nf. inv nf... }
Qed.

Lemma resolve_wr_nfi' H m m' i :
  H ; m ~ m' -> wr_heap H -> nf i m -> nf i m'.
Proof with eauto using nf.
  move=>rs. elim: rs i=>{H m m'}...
  { move=>H m m' s k rsm ihm i wr nfL. inv nfL... }
  { move=>H m m' s k rsm ihm i wr nfL. inv nfL... }
  { move=>H m m' rsm ihm i wr nfA. inv nfA... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn i wr nfA. inv nfA.
    { inv rsn. }
    { have[wr1 wr2]:=wr_merge_inv mrg wr... } }
  { move=>H m m' t rsm ihm i wr nfP. inv nfP... }
  { move=>H1 H2 H m m' n n' t mrg rsm ihm rsn ihn i wr nfP. inv nfP.
    have[wr1 wr2]:=wr_merge_inv mrg wr... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn i wr nfL. inv nfL.
    have[wr1 wr2]:=wr_merge_inv mrg wr... }
  { move=>H m m' n n' t k rsm ihm rsn ihn i wr nfP. inv nfP... }
  { move=>H m m' rsm ihn i wr nfF. inv nfF... }
  { move=>H m m' rsm ihn i wr nfS. inv nfS... }
  { move=>H m m' rsm ihm i wr nf. inv nf... }
  { move=>H H' l m m' fr rsm ihm i wr nfP.
    apply: ihm.
    { apply: free_wr... }
    { have nf0:=free_wr_nf fr wr.
      apply: nf_weaken... } }
Qed.

Lemma free_wr_ptr H H' l i :
  free H l (Ptr i) H' -> wr_heap H -> False.
Proof with eauto.
  move e:(Ptr i)=>m fr. elim: fr i e=>{H H' l m}.
  { move=>H m l e1 i e2 wr; subst. inv wr. }
  { move=>H m l e1 i e2 wr; subst. inv wr. }
  { move=>H H' m n l fr ih i e wr; subst. inv wr... }
Qed.

Lemma free_wr_var H H' l x :
  free H l (Var x) H' -> wr_heap H -> False.
Proof with eauto.
  move e:(Var x)=>m fr. elim: fr x e=>//{H H' l m}.
  { move=>H m l e1 x e2 wr; subst. inv wr. }
  { move=>H m l e1 x e2 wr; subst. inv wr. }
  { move=>H H' m n l fr ih x e wr; subst.
    apply: ih... inv wr... }
Qed.

Lemma free_wr_lam0 H H' l A m :
  free H l (Lam0 A m U) H' -> wr_heap H -> H = H'.
Proof with eauto.
  move e:(Lam0 A m U)=>n fr. elim: fr A m e=>//{H H' l n}.
  { move=>H m l e1 A m0 e2 wr; subst. inv wr. inv H5. }
  { move=>H H' m n l fr ih A m0 e wr; subst.
    f_equal. apply: ih... inv wr... }
Qed.

Lemma free_wr_lam1 H H' l A m :
  free H l (Lam1 A m U) H' -> wr_heap H -> H = H'.
Proof with eauto.
  move e:(Lam1 A m U)=>n fr. elim: fr A m e=>//{H H' l n}.
  { move=>H m l e1 A m0 e2 wr; subst. inv wr. inv H5. }
  { move=>H H' m n l fr ih A m0 e wr; subst.
    f_equal. apply: ih... inv wr... }
Qed.

Lemma free_wr_pair0 H H' l m n :
  free H l (Pair0 m n U) H' -> wr_heap H -> H = H'.
Proof with eauto.
  move e:(Pair0 m n U)=>x fr. elim: fr m n e=>//{H H' l x}.
  { move=>H m l e1 m0 n e2 wr; subst. inv wr. inv H5. }
  { move=>H H' m n l fr ih m0 n0 e wr; subst.
    f_equal. apply: ih... inv wr... }
Qed.

Lemma free_wr_pair1 H H' l m n :
  free H l (Pair1 m n U) H' -> wr_heap H -> H = H'.
Proof with eauto.
  move e:(Pair1 m n U)=>x fr. elim: fr m n e=>//{H H' l x}.
  { move=>H m l e1 m0 n e2 wr; subst. inv wr. inv H5. }
  { move=>H H' m n l fr ih m0 n0 e wr; subst.
    f_equal. apply: ih... inv wr... }
Qed.

Lemma free_wr_apair H H' l m n :
  free H l (APair m n U) H' -> wr_heap H -> H = H'.
Proof with eauto.
  move e:(APair m n U)=>x fr. elim: fr m n e=>//{H H' l x}.
  { move=>H m l e1 m0 n e2 wr; subst. inv wr. inv H5. }
  { move=>H H' m n l fr ih m0 n0 e wr.
    f_equal. apply: ih... inv wr... }
Qed.

Lemma resolve_var_inv H m x :
  wr_heap H -> H ; m ~ Var x -> H ▷ U.
Proof with eauto.
  move e:(Var x)=>n wr rs.
  elim: rs x e wr=>//{H m n}.
  move=>H H' l m m' fr rsm ih x e wr; subst.
  destruct m; inv rsm.
  exfalso. apply: free_wr_var...
  exfalso. apply: free_wr_ptr...
Qed.

Lemma resolve_lam0_inv H m A n s :
  wr_heap H -> H ; m ~ Lam0 A n s -> H ▷ s.
Proof with eauto using key_impure.
  move e:(Lam0 A n s)=>v wr rs.
  elim: rs A n s e wr=>//{H m v}.
  { move=>H m m' s k rsm ihm A n s0[e1 e2 e3]; subst... }
  { move=>H H' l m m' fr rsm ihm A n s e wr; subst.
    destruct m; inv rsm.
    { destruct s... have->//:=free_wr_lam0 fr wr. }
    { exfalso. apply: free_wr_ptr... } }
Qed.

Lemma resolve_lam1_inv H m A n s :
  wr_heap H -> H ; m ~ Lam1 A n s -> H ▷ s.
Proof with eauto using key_impure.
  move e:(Lam1 A n s)=>v wr rs.
  elim: rs A n s e wr=>//{H m v}.
  { move=>H m m' s k rsm ihm A n s0[e1 e2 e3]; subst... }
  { move=>H H' l m m' fr rsm ihm A n s e wr; subst.
    destruct m; inv rsm.
    { destruct s... have->//:=free_wr_lam1 fr wr. }
    { exfalso. apply: free_wr_ptr... } }
Qed.

Lemma resolve_apair_inv H m n1 n2 t :
  wr_heap H -> H ; m ~ APair n1 n2 t -> H ▷ t.
Proof with eauto using key_impure.
  move e:(APair n1 n2 t)=>v wr rs.
  elim: rs n1 n2 t e wr=>//{H m v}.
  { move=>H m m' n n' s k rsm ihm rsn ihn n1 n2 t
      [e1 e2 e3] wr; subst... }
  { move=>H H' l m m' fr rsm ihm n1 n2 t e wr; subst.
    destruct m; inv rsm.
    { destruct t... have->//:=free_wr_apair fr wr. }
    { exfalso. apply: free_wr_ptr... } }
Qed.

Theorem resolution H x y z A s :
  H ; x ~ y ~ z : A ->
  nil ⊢ A : Sort s ->
  dyn_val y -> wr_heap H -> H ▷ s.
Proof with eauto using key_impure.
  move=>wr. inv wr.
  move:H1 H2.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty.
  elim: ty H z s e1 e2=>{Γ Δ x y A}.
  { move=>Γ Δ x s A wf shs dhs H z s0 e1 e2 rs tyA vl wr; subst.
    inv shs. }
  { move=>Γ Δ A B m m' s k erm _ H z s0 e1 e2 rs tyP vl wr; subst.
    have[_[_/sort_inj e]]:=sta_pi0_inv tyP. subst.
    destruct s...
    apply: resolve_lam0_inv... }
  { move=>Γ Δ A B m m' s t k erm _ H z s0 e1 e2 rs tyP vl wr; subst.
    have[_[_/sort_inj e]]:=sta_pi1_inv tyP. subst.
    destruct s...
    apply: resolve_lam1_inv... }
  { move=>Γ Δ A B m m' n s erm _ tyn
      H z s0 e1 e2 rs tyB vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm _ ern _
      H z s0 e1 e2 rs tyB vl. inv vl. }
  { move=>Γ Δ A B m m' n t tyS1 erm ihm tyn
      H z s e1 e2 rs tyS2 vl wr; subst.
    have[s0[r[ord[tyA[tyB/sort_inj e]]]]]:=sta_sig0_inv tyS2. subst.
    destruct t... inv ord. inv vl.
    inv rs... have wr':=free_wr H2 wr. inv H3.
    { have k':=ihm _ _ _ erefl erefl H7 tyA H1 wr'.
      have->//:=free_wr_pair0 H2 wr. }
    { exfalso. apply: free_wr_ptr... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t mrg tyS1 erm ihm ern ihn
      H z s e1 e2 rs tyS2 vl wr; subst.
    inv mrg. inv vl.
    have[s0[r[ord1[ord2[tyA[tyB/sort_inj e]]]]]]:=sta_sig1_inv tyS2. subst.
    destruct t... inv ord1. inv ord2.
    inv rs.
    { have[wr1 wr2]:=wr_merge_inv H10 wr.
      have tym:=dyn_sta_type (era_dyn_type erm).
      have tyBm:=sta_subst tyB tym. asimpl in tyBm.
      have k1:=ihm _ _ _ erefl erefl H11 tyA H2 wr1.
      have k2:=ihn _ _ _ erefl erefl H12 tyBm H4 wr2.
      apply: merge_pure... }
    { have wr':=free_wr H1 wr. inv H3.
      { have[wr1 wr2]:=wr_merge_inv H12 wr'.
        have tym:=dyn_sta_type (era_dyn_type erm).
        have tyBm:=sta_subst tyB tym. asimpl in tyBm.
        have k1:=ihm _ _ _ erefl erefl H13 tyA H2 wr1.
        have k2:=ihn _ _ _ erefl erefl H14 tyBm H4 wr2.
        have->:=free_wr_pair1 H1 wr.
        apply: merge_pure... }
      { exfalso. apply: free_wr_ptr... } } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t mrg tyC1 erm _ ern _
      H z s0 e1 e2 rs tyC2 vl. inv vl. }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t mrg tyC1 erm _ ern _
      H z s0 e1 e2 rs tyC2 vl. inv vl. }
  { move=>Γ Δ A B m m' n n' t k erm ihm ern ihn H z s e1 e2 rs tyW vl wr.
    have[s0[r[tyA[tyB/sort_inj e]]]]:=sta_with_inv tyW. subst.
    destruct t... inv rs... inv H2.
    { have->//:=free_wr_apair H1 wr. }
    { exfalso. apply: free_wr_ptr... } }
  { move=>Γ Δ A B m m' t erm _ H z s e1 e2 rs tyA vl. inv vl. }
  { move=>Γ Δ A B m m' t erm _ H z s e1 e2 rs tyA vl. inv vl. }
  { move=>Γ Δ A B x x' P m n s tyB erH _ tyP H z s0 e1 e2 rs tyB' vl. inv vl. }
  { move=>Γ Δ A B m m' s eq erm ihm tyB1 H z s0 e1 e2 rs tyB2 vl wr.
    have e:=sta_unicity tyB1 tyB2. subst.
    have[s tyA]:=dyn_valid (era_dyn_type erm).
    have[x r1 r2]:=church_rosser eq.
    have tyx1:=sta_rd tyA r1.
    have tyx2:=sta_rd tyB1 r2.
    have e:=sta_unicity tyx1 tyx2. subst... }
Qed.

Lemma wr_free_dyn_val H l m H' :
  free H l m H' -> wr_heap H -> dyn_val m.
Proof with eauto using wr_heap, dyn_val.
  elim=>{H l m H'}.
  { move=>H m l e wr. inv wr... }
  { move=>H m l e wr. inv wr... }
  { move=>H H' m n l fr ih wr. inv wr... }
Qed.

Lemma resolve_dyn_val H m n :
  H ; m ~ n -> dyn_val m -> wr_heap H -> dyn_val n.
Proof with eauto using dyn_val.
  move=>rsm. elim: rsm=>{H m n}...
  { move=>H m m' rsm _ vl. inv vl. }
  { move=>H1 H2 H m m' n n' mrg rsm _ rsn _ vl. inv vl. }
  { move=>H m m' t rsm ihm vl wr. inv vl... }
  { move=>H1 H2 H m m' n n' t mrg rsm ihm rsn ihn vl wr.
    have[wr1 wr2]:=wr_merge_inv mrg wr. inv vl... }
  { move=>H1 H2 H m m' n n' mrg rsm ihm rsn ihn vl. inv vl. }
  { move=>H m m' rsm ihm vl. inv vl. }
  { move=>H m m' rsm ihm vl. inv vl. }
  { move=>H m m' rsm ihm vl. inv vl. }
  { move=>H H' l m m' fr rsm ihm _ wr.
    have wr':=free_wr fr wr.
    have vl:=wr_free_dyn_val fr wr... }
Qed.

Lemma wr_resolve_ptr H l n :
  wr_heap H -> H ; Ptr l ~ n -> dyn_val n.
Proof with eauto.
  move=>wr rs. inv rs.
  have wr':=free_wr H2 wr.
  have vl:=wr_free_dyn_val H2 wr.
  apply: resolve_dyn_val...
Qed.
