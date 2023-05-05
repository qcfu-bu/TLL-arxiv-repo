From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From Coq Require Import ssrfun Classical Utf8.
Require Export AutosubstSsr ARS dyn_prog era_prog.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Inductive dyn_pstep : term -> term -> Prop :=
| dyn_pstep_var x :
  dyn_pstep (Var x) (Var x)
| dyn_pstep_app m m' n n' :
  dyn_pstep m m' ->
  dyn_pstep n n' ->
  dyn_pstep (App m n) (App m' n')
| dyn_pstep_lam0 A m s :
  dyn_pstep (Lam0 A m s) (Lam0 A m s)
| dyn_pstep_lam1 A m s :
  dyn_pstep (Lam1 A m s) (Lam1 A m s)
| dyn_pstep_beta0 A m n n' s :
  dyn_pstep n n' ->
  dyn_pstep (App (Lam0 A m s) n) m.[n'/]
| dyn_pstep_beta1 A m v s :
  dyn_val v ->
  dyn_pstep (App (Lam1 A m s) v) m.[v/]
| dyn_pstep_pair0 m m' n s :
  dyn_pstep m m' ->
  dyn_pstep (Pair0 m n s) (Pair0 m' n s)
| dyn_pstep_pair1 m m' n n' s :
  dyn_pstep m m' ->
  dyn_pstep n n' ->
  dyn_pstep (Pair1 m n s) (Pair1 m' n' s)
| dyn_pstep_letin A m m' n :
  dyn_pstep m m' ->
  dyn_pstep (LetIn A m n) (LetIn A m' n)
| dyn_pstep_iota0 A m1 m2 n s :
  dyn_val (Pair0 m1 m2 s) ->
  dyn_pstep (LetIn A (Pair0 m1 m2 s) n) n.[m2,m1/]
| dyn_pstep_iota1 A m1 m2 n s :
  dyn_val (Pair1 m1 m2 s) ->
  dyn_pstep (LetIn A (Pair1 m1 m2 s) n) n.[m2,m1/]
| dyn_pstep_apair m n s :
  dyn_pstep (APair m n s) (APair m n s)
| dyn_pstep_fst m m' :
  dyn_pstep m m' ->
  dyn_pstep (Fst m) (Fst m')
| dyn_pstep_snd m m' :
  dyn_pstep m m' ->
  dyn_pstep (Snd m) (Snd m')
| dyn_pstep_proj1 m n s :
  dyn_pstep (Fst (APair m n s)) m
| dyn_step_proj2 m n s :
  dyn_pstep (Snd (APair m n s)) n
| dyn_pstep_rw A H P :
  dyn_pstep (Rw A H P) (Rw A H P)
| dyn_pstep_rwE A H P :
  dyn_pstep (Rw A H P) H
| dyn_pstep_box :
  dyn_pstep Box Box
where "m ~>> n" := (dyn_step m n).

Lemma dyn_red_app m m' n n' :
  m ~>>* m' -> n ~>>* n' -> App m n ~>>* App m' n'.
Proof.
  move=> r1 r2.
  apply: (star_trans (App m' n)).
  apply: (star_hom (App^~ n)) r1=>x y. exact: dyn_step_appL.
  apply: star_hom r2. exact: dyn_step_appR.
Qed.

Lemma dyn_red_pair0 m m' n s :
  m ~>>* m' -> Pair0 m n s ~>>* Pair0 m' n s.
Proof.
  move=> r.
  apply: (star_hom ((Pair0^~ n)^~ s)) r=>x y. exact: dyn_step_pair0L.
Qed.

Lemma dyn_red_pair1 m m' n n' t :
  m ~>>* m' -> n ~>>* n' -> Pair1 m n t ~>>* Pair1 m' n' t.
Proof.
  move=>r1 r2.
  apply: (star_trans (Pair1 m' n t)).
  apply: (star_hom ((Pair1^~ n)^~ t)) r1=>x y. exact: dyn_step_pair1L.
  apply: (star_hom ((Pair1 m')^~ t)) r2=>x y. exact: dyn_step_pair1R.
Qed.

Lemma dyn_red_letin A m m' n :
  m ~>>* m' -> LetIn A m n ~>>* LetIn A m' n.
Proof.
  move=>r.
  apply: (star_hom (LetIn A^~ n)) r=>x y. exact: dyn_step_letinL.
Qed.

Lemma dyn_red_fst m m' : m ~>>* m' -> Fst m ~>>* Fst m'.
Proof.
  move=>r.
  apply: (star_hom Fst) r=>x y. exact: dyn_step_fst.
Qed.

Lemma dyn_red_snd m m' : m ~>>* m' -> Snd m ~>>* Snd m'.
Proof.
  move=>r.
  apply: (star_hom Snd) r=>x y. exact: dyn_step_snd.
Qed.

Lemma dyn_val_pstep m n :
  dyn_val m -> dyn_pstep m n -> dyn_val n /\ m = n.
Proof with eauto using dyn_val.
  move=>vl. elim: vl n=>{m}.
  { move=>x n vl. inv vl... }
  { move=>A B s n p. inv p... }
  { move=>A B s n p. inv p... }
  { move=>m1 m2 s vl ih n p. inv p.
    have[vl' e]:=ih _ H3. subst... }
  { move=>m1 m2 s vl1 ih1 vl2 ih2 n p. inv p.
    have[vl3 e]:=ih1 _ H3. subst.
    have[vl4 e]:=ih2 _ H4. subst... }
  { move=>m1 m2 s n p. inv p... }
  { move=>l n p. inv p. }
Qed.

Lemma era_pstep_reflexive Γ Δ m m' A :
  Γ ; Δ ⊢ m ~ m' : A -> dyn_pstep m' m'.
Proof.
  move=>ty. elim: ty=>{Γ Δ m m' A}; eauto using dyn_pstep.
Qed.

Lemma era_step_pstep Γ Δ m m' n' A :
  Γ ; Δ ⊢ m ~ m' : A -> m' ~>> n' -> dyn_pstep m' n'.
Proof with eauto using dyn_pstep, era_pstep_reflexive.
  move=>ty. elim: ty n'=>{Γ Δ m m' A}...
  all: try solve
         [intros;
          match goal with
          | [ H : _ ~>> _ |- _ ] =>
              inv H; eauto using dyn_pstep, era_pstep_reflexive
          end].
  { move=>Γ Δ A B m m' n s erm ihm tyn n' st. inv st... inv H2. }
Qed.

Lemma era_pstep_red Γ Δ m m' n' A :
  Γ ; Δ ⊢ m ~ m' : A -> dyn_pstep m' n' -> m' ~>>* n'.
Proof with eauto.
  move=>ty. elim: ty n'=>{Γ Δ m m' A}.
  all: try solve
         [intros;
          match goal with
          | [ H : dyn_pstep _ _ |- _ ] => inv H; eauto
          end].
  { move=>Γ Δ A B m m' n s erm ihm tyn n' ps. inv ps.
    { inv H3. apply: dyn_red_app... }
    { inv H2. apply: starES... by constructor. }
    { inv H2. } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn nx ps. inv ps.
    { apply: dyn_red_app... }
    { exfalso.
      have[A1[m1 e]]:=era_lam0_form erm. subst.
      have{}H0:=dyn_sta_type (era_dyn_type erm).
      apply: sta_lam0_pi1_false... }
    { apply: starES... by constructor. } }
  { move=>Γ Δ A B m m' n t tyS erm ihm tyn nx ps. inv ps.
    apply: dyn_red_pair0... }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t
           mrg tyS erm ihm ern ihn nx ps. inv ps.
    apply: dyn_red_pair1... }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t
           mrg tyC erm ihm ern ihn nx ps. inv ps.
    { apply: dyn_red_letin... }
    { inv H3.
      have[m3[m4 e]]:=era_pair0_form erm. subst.
      have[e1[e2[erm' ty]]]:=era_pair0_inv erm. subst.
      apply: star1. constructor... constructor... }
    { exfalso.
      have[m3[m4 e]]:=era_pair1_form erm. subst.
      apply: sta_pair1_sig0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t
           mrg tyC erm ihm ern ihn nx ps. inv ps.
    { apply: dyn_red_letin... }
    { exfalso.
      have[m3[m4 e]]:=era_pair0_form erm. subst.
      apply: sta_pair0_sig1_false... }
    { inv H3.
      have[m3[m4 e]]:=era_pair1_form erm. subst.
      have[Δ3[Δ4[mrg'[e[erm1 erm2]]]]]:=era_pair1_inv erm. subst.
      apply: star1. constructor... constructor... } }
  { move=>Γ Δ A B m m' t erm ihm n ps. inv ps.
    { apply: dyn_red_fst... }
    { apply: starES... by constructor. } }
  { move=>Γ Δ A B m m' t erm ihm n ps. inv ps.
    { apply: dyn_red_snd... }
    { apply: starES... by constructor. } }
  { move=>Γ Δ A B H H' P m n s tyB erH ihH tyP n' ps. inv ps...
    apply: starES... by constructor. }
  { move=>Γ Δ A B m m' s eq erm ihm tyB n' ps... }
Qed.

Lemma era_pstep_diamonad Γ Δ m m' m1 m2 A :
  Γ ; Δ ⊢ m ~ m' : A ->
  dyn_pstep m' m1 -> dyn_pstep m' m2 ->
  exists2 n, dyn_pstep m1 n & dyn_pstep m2 n.
Proof with eauto using dyn_pstep, era_pstep_reflexive.
  move=>ty. elim: ty m1 m2=>{Γ Δ m m' A}.
  { move=>Γ Δ x s A wf shs dhs m1 m2 ps1 ps2.
    inv ps1. inv ps2. exists (Var x)... }
  { move=>Γ Δ A B m m' s k erm ihm m1 m2 ps1 ps2.
    inv ps1. inv ps2. exists (Lam0 Box m' s)... }
  { move=>Γ Δ A B m m' s t k erm ihm m1 m2 ps1 ps2.
    inv ps1. inv ps2. exists (Lam1 Box m' s)... }
  { move=>Γ Δ A B m m' n s erm ihm tyn m1 m2 ps1 ps2. inv ps1; inv ps2.
    { inv H3. inv H5.
      have[nx p1 p2]:=ihm _ _ H1 H2.
      exists (App nx Box)... }
    { inv H1. inv H3. inv H4.
      have[A1[m1 e]]:=era_lam0_form erm. subst.
      have[erm1 _]:=era_lam0_inv erm.
      have{}erm1:=era_subst0 erm1 tyn.
      exists m0.[Box/]... }
    { exfalso.
      have[A1[m1 e]]:=era_lam1_form erm. subst.
      apply: sta_lam1_pi0_false... }
    { inv H1. inv H2. inv H4.
      have[A1[m1 e]]:=era_lam0_form erm. subst.
      have[erm1 _]:=era_lam0_inv erm.
      have{}erm1:=era_subst0 erm1 tyn.
      exists m0.[Box/]... }
    { inv H2. inv H5.
      have[A1[m1 e]]:=era_lam0_form erm. subst.
      have[erm1 _]:=era_lam0_inv erm.
      have{}erm1:=era_subst0 erm1 tyn.
      exists m0.[Box/]... }
    { exfalso.
      have[A1[m1 e]]:=era_lam1_form erm. subst.
      apply: sta_lam1_pi0_false... }
    { exfalso.
      have[A1[m1 e]]:=era_lam1_form erm. subst.
      apply: sta_lam1_pi0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' s mrg erm ihm ern ihn m1 m2 ps1 ps2.
    inv ps1; inv ps2.
    { have[mx pm1 pm2]:=ihm _ _ H1 H2.
      have[nx pn1 pn2]:=ihn _ _ H3 H5.
      exists (App mx nx)... }
    { exfalso.
      have[A1[m1 e]]:=era_lam0_form erm. subst.
      apply: sta_lam0_pi1_false... }
    { inv H1.
      have[A1[m1 e]]:=era_lam1_form erm. subst.
      have[r[erm1 _]]:=era_lam1_inv erm.
      have wf:=dyn_type_wf (era_dyn_type erm1). inv wf.
      have vl:=era_dyn_val ern H4.
      have k:=dyn_val_key (era_dyn_type ern) H6 vl.
      have{}erm:=era_subst1 k mrg erm1 ern.
      have[vl' e]:=dyn_val_pstep H4 H3. subst.
      exists m0.[n'0/]... }
    { exfalso.
      have[A1[m1 e]]:=era_lam0_form erm. subst.
      apply: sta_lam0_pi1_false... }
    { exfalso.
      have[A1[m1 e]]:=era_lam0_form erm. subst.
      apply: sta_lam0_pi1_false... }
    { inv H1.
      have[A1[m1 e]]:=era_lam1_form erm. subst.
      have[r[erm1 _]]:=era_lam1_inv erm.
      have wf:=dyn_type_wf (era_dyn_type erm1). inv wf.
      have[vl' e]:=dyn_val_pstep H2 H4. subst.
      have vl:=era_dyn_val ern vl'.
      have k:=dyn_val_key (era_dyn_type ern) H6 vl.
      have erm':=era_subst1 k mrg erm1 ern.
      exists m0.[n'0/]... }
    { have[A1[m1 e]]:=era_lam1_form erm. subst.
      have[r[erm1 _]]:=era_lam1_inv erm.
      have wf:=dyn_type_wf (era_dyn_type erm1). inv wf.
      have vl:=era_dyn_val ern H2.
      have k:=dyn_val_key (era_dyn_type ern) H6 vl.
      have erm':=era_subst1 k mrg erm1 ern.
      exists m0.[n'/]... } }
  { move=>Γ Δ A B m m' n t tyS erm ihm tyn m1 m2 ps1 ps2.
    inv ps1. inv ps2.
    have[mx ps1 ps2]:=ihm _ _ H3 H4.
    exists (Pair0 mx Box t)... }
  { move=>Γ Δ1 Δ2 Δ A B m m' n n' t
           mrg tyS erm ihm ern ihn m1 m2 ps1 ps2.
    inv ps1. inv ps2.
    have[mx ps1 ps2]:=ihm _ _ H3 H5.
    have[nx ps3 ps4]:=ihn _ _ H4 H6.
    exists (Pair1 mx nx t)... }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r t
           mrg tyC erm ihm ern ihn m1 m2 ps1 ps2.
    inv ps1.
    { inv ps2.
      { have[n0 ps1 ps2]:=ihm _ _ H3 H4. exists (LetIn Box n0 n')... }
      { inv H3. inv H4.
        have[m2[m3 e]]:=era_pair0_form erm. subst.
        have[e1[e2[erm1 tym3]]]:=era_pair0_inv erm. subst.
        have wf:=dyn_type_wf (era_dyn_type ern). inv wf. inv H3.
        have[vl e]:=dyn_val_pstep H0 H5. subst.
        have vl':=era_dyn_val erm1 vl.
        have k:=dyn_val_key (era_dyn_type erm1) H8 vl'.
        have agr:
          Γ ; Δ ⊢ (m3 .: m2 .: ids) ~
                (Box .: m' .: ids) ⊣ (B :: A :: Γ) ; _: A :{r} Δ2.
        { constructor...
          econstructor...
          apply: merge_sym...
          asimpl... }
        exists n'.[Box,m'/]...
        constructor. constructor...
        have ern':=era_substitution ern agr.
        asimpl in ern'.
        apply: era_pstep_reflexive... }
      { exfalso.
        have[m2[m3 e]]:=era_pair1_form erm. subst.
        apply: sta_pair1_sig0_false... } }
    { inv H3.
      have[m1[m4 e]]:=era_pair0_form erm. subst.
      have wf:=dyn_type_wf (era_dyn_type ern). inv wf. inv H3.
      have[e1[e2[erm1 tym4]]]:=era_pair0_inv erm. subst.
      have vl:=era_dyn_val erm1 H0.
      have k:=dyn_val_key (era_dyn_type erm1) H7 vl.
      have agr:
        Γ ; Δ ⊢ (m4 .: m1 .: ids) ~
                (Box .: m0 .: ids) ⊣ (B :: A :: Γ) ; _: A :{r} Δ2.
      { constructor...
        econstructor...
        apply: merge_sym...
        asimpl... }
      have ern':=era_substitution ern agr. asimpl in ern'.
      inv ps2.
      { inv H6.
        have[vl' e]:=dyn_val_pstep H0 H8. subst.
        exists n'.[Box,m'0/]...
        constructor. constructor... }
      { exists n'.[Box,m0/]... } }
    { exfalso.
      have[m4[m5 e]]:=era_pair1_form erm. subst.
      apply: sta_pair1_sig0_false... } }
  { move=>Γ Δ1 Δ2 Δ A B C m m' n n' s r1 r2 t
           mrg tyC erm ihm ern ihn m1 m2 ps1 ps2.
    inv ps1.
    { inv ps2.
      { have[n0 ps1 ps2]:=ihm _ _ H3 H4. exists (LetIn Box n0 n')... }
      { exfalso.
        have[m4[m5 e]]:=era_pair0_form erm. subst.
        apply: sta_pair0_sig1_false... }
      { inv H3. inv H4.
        have wf:=dyn_type_wf (era_dyn_type ern). inv wf. inv H4.
        have[vl1 e]:=dyn_val_pstep H1 H5. subst.
        have[vl2 e]:=dyn_val_pstep H3 H6. subst.
        have[m1[m2 e]]:=era_pair1_form erm. subst.
        have[Δ3[Δ4[mrg1[e[erm1 erm2]]]]]:=era_pair1_inv erm. subst.
        have vl3:=era_dyn_val erm1 H1.
        have vl4:=era_dyn_val erm2 vl2.
        have//=tyB:=sta_subst H8 (dyn_sta_type (era_dyn_type erm1)).
        have k1:=dyn_val_key (era_dyn_type erm1) H10 vl3.
        have k2:=dyn_val_key (era_dyn_type erm2) tyB vl4.
        have[Δx[mrg3 mrg4]]:=merge_splitL mrg mrg1.
        have agr:
          Γ ; Δ ⊢ (m2 .: m1 .: ids) ~
                  (n'0 .: m' .: ids) ⊣ (B :: A :: Γ) ; B :{r2} A :{r1} Δ2.
        { econstructor...
          econstructor...
          apply: merge_sym...
          asimpl... }
        have ern':=era_substitution ern agr. asimpl in ern'.
        exists n'.[n'0,m'/]...
        constructor. constructor... } }
    { exfalso.
      have[m4[m5 e]]:=era_pair0_form erm. subst.
      apply: sta_pair0_sig1_false... }
    { inv H3.
      have wf:=dyn_type_wf (era_dyn_type ern). inv wf. inv H3.
      have[m4[m5 e]]:=era_pair1_form erm. subst.
      have[Δ3[Δ4[mrg1[e[erm1 erm2]]]]]:=era_pair1_inv erm. subst.
      have vl3:=era_dyn_val erm1 H1.
      have vl4:=era_dyn_val erm2 H4.
      have//=tyB:=sta_subst H6 (dyn_sta_type (era_dyn_type erm1)).
      have k1:=dyn_val_key (era_dyn_type erm1) H8 vl3.
      have k2:=dyn_val_key (era_dyn_type erm2) tyB vl4.
      have[Δx[mrg3 mrg4]]:=merge_splitL mrg mrg1.
      have agr:
        Γ ; Δ ⊢ (m5 .: m4 .: ids) ~
                (m3 .: m0 .: ids) ⊣ (B :: A :: Γ) ; B :{r2} A :{r1} Δ2.
      { econstructor...
        econstructor...
        apply: merge_sym...
        asimpl... }
      have ern':=era_substitution ern agr. asimpl in ern'.
      inv ps2.
      { inv H7.
        have[vl1 e]:=dyn_val_pstep H1 H9. subst.
        have[vl2 e]:=dyn_val_pstep H4 H10. subst.
        exists n'.[n'0,m'0/]...
        constructor. constructor... }
      { inv H10. exists n'.[m3,m0/]... } } }
  { move=>Γ Δ A B m m' n n' t k erm ihm ern ihn m1 m2 ps1 ps2.
    inv ps1. inv ps2. exists (APair m' n' t)... }
  { move=>Γ Δ A B m m' t erm ihm m1 m2 ps1 ps2.
    inv ps1; inv ps2.
    { have[mx ps1 ps2]:=ihm _ _ H0 H1. exists (Fst mx)... }
    { have[m1[m3 e]]:=era_apair_form erm. subst.
      have[e[erm1 erm3]]:=era_apair_inv erm. subst.
      inv H0. exists m2... }
    { have[m2[m3 e]]:=era_apair_form erm. subst.
      have[e[erm2 erm3]]:=era_apair_inv erm. subst.
      inv H0. exists m1... }
    { have[m1[m3 e]]:=era_apair_form erm. subst.
      have[e[erm1 erm3]]:=era_apair_inv erm. subst.
      exists m2... } }
  { move=>Γ Δ A B m m' t erm ihm m1 m2 ps1 ps2.
    inv ps1; inv ps2.
    { have[mx ps1 ps2]:=ihm _ _ H0 H1. exists (Snd mx)... }
    { have[m1[m3 e]]:=era_apair_form erm. subst.
      have[e[erm1 erm3]]:=era_apair_inv erm. subst.
      inv H0. exists m2... }
    { have[m2[m3 e]]:=era_apair_form erm. subst.
      have[e[erm2 erm3]]:=era_apair_inv erm. subst.
      inv H0. exists m1... }
    { have[m1[m3 e]]:=era_apair_form erm. subst.
      have[e[erm1 erm3]]:=era_apair_inv erm. subst.
      exists m2... } }
  { move=>Γ Δ A B H H' P m n s tyB erH ihH tyP m1 m2 ps1 ps2.
    inv ps1; inv ps2.
    { exists H'... }
    { exists m2... }
    { exists m1... }
    { exists m2... } }
  { move=>Γ Δ A B m m' s eq erm ihm tyB m1 m2 ps1 ps2... }
Qed.

Lemma dyn_strip m m' m1 m2 A :
  nil ; nil ⊢ m ~ m' : A ->
  dyn_pstep m' m1 -> m' ~>>* m2 ->
  exists2 n, m1 ~>>* n & dyn_pstep m2 n.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty p r.
  elim: r Γ Δ e1 e2 m m1 A ty p=>{m2}.
  { move=>Γ Δ e1 e2 m m1 A erm ps. exists m1... }
  { move=>y z rd ih st Γ Δ e1 e2 m m1 A erm ps2. subst.
    have[m0 rd2 erm0]:=era_rd erm rd.
    have ps1:=era_step_pstep erm0 st.
    have[n0 rd1 ps3]:=ih _ _ erefl erefl _ _ _ erm ps2.
    have[n1 ps4 ps5]:=era_pstep_diamonad erm0 ps1 ps3.
    have rd3:=era_pstep_red erm0 ps3.
    have[n2 rd4 ern]:=era_rd erm0 rd3.
    exists n1.
    apply: star_trans. apply: rd1.
    apply: era_pstep_red...
    apply: ps4. }
Qed.

Theorem era_confluence m m' m1 m2 A :
  nil ; nil ⊢ m ~ m' : A ->
  m' ~>>* m1 -> m' ~>>* m2 ->
  exists2 n, m1 ~>>* n & m2 ~>>* n.
Proof with eauto.
  move e1:(nil)=>Γ.
  move e2:(nil)=>Δ ty r.
  elim: r Γ Δ m m2 A ty e1 e2=>{m1}.
  { move=>Γ Δ m m2 A erm e1 e2 rd1. subst. exists m2... }
  { move=>y z rd1 ih st Γ Δ m m2 A erm e1 e2 rd2. subst.
    have[y0 rd3 ery0]:=era_rd erm rd1.
    have ps1:=era_step_pstep ery0 st.
    have[n rd4 rd5]:=ih _ _ _ _ _ erm erefl erefl rd2.
    have[z' rd6 ps2]:=dyn_strip ery0 ps1 rd4.
    have[y1 rd7 ery1]:=era_rd ery0 rd4.
    have rd8:=era_pstep_red ery1 ps2.
    exists z'...
    apply: star_trans.
    apply: rd5. apply: rd8. }
Qed.
