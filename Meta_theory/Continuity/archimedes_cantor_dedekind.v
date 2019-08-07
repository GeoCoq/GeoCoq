Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Meta_theory.Continuity.grad.
Require Import GeoCoq.Tarski_dev.Ch08_orthogonality.

Section Archimedes_cantor_dedekind.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Inductive cX A C (Alpha Beta : Tpoint -> Prop) : nat -> Tpoint -> Prop :=
| cX_init : cX A C Alpha Beta O A
| cX_same : forall n X Y M, cX A C Alpha Beta n X -> cY A C Alpha Beta n Y -> Midpoint M X Y ->
                Beta M -> cX A C Alpha Beta (S n) X
| cX_other : forall n X Y M, cX A C Alpha Beta n X -> cY A C Alpha Beta n Y -> Midpoint M X Y ->
                Alpha M -> cX A C Alpha Beta (S n) M
with cY A C (Alpha Beta : Tpoint -> Prop) : nat -> Tpoint -> Prop :=
| cY_init : cY A C Alpha Beta O C
| cY_same : forall n X Y M, cX A C Alpha Beta n X -> cY A C Alpha Beta n Y -> Midpoint M X Y ->
                Alpha M -> cY A C Alpha Beta (S n) Y
| cY_other : forall n X Y M, cX A C Alpha Beta n X -> cY A C Alpha Beta n Y -> Midpoint M X Y ->
                Beta M -> cY A C Alpha Beta (S n) M.

Scheme cX_cY_ind := Induction for cX Sort Prop
with cY_cX_ind := Induction for cY Sort Prop.

Combined Scheme cXY_ind from cX_cY_ind, cY_cX_ind.

Lemma archimedes_cantor__dedekind_variant : archimedes_axiom -> cantor_s_axiom -> dedekind_variant.
Proof.
  intros archi cantor Alpha Beta A C HA HC Hdis Hcut.
  assert (Hnab : forall P, Alpha P -> Beta P -> False) by (intros; eapply Hcut; eauto).
  assert (A <> C) by (apply Hcut; assumption).
  pose (Alpha' := cX A C Alpha Beta).
  pose (Beta' := cY A C Alpha Beta).
  assert (Haux : forall X Y M, Alpha X -> Out A Y C -> Midpoint M X Y -> Out A M C).
  { intros X Y M HX HY HM.
    destruct (Hcut X C HX HC).
    apply l6_7 with Y; trivial.
    destruct (eq_dec_points A X).
      subst; assert_diffs; apply l6_7 with Y; Out.
    apply out_bet_out_2 with X; [|Between].
    apply l6_7 with C; Out.
  }
  assert (Ha'a : forall n X, Alpha' n X -> Alpha X) by (induction 1; assumption).
  assert (Hb'b : forall n Y, Beta' n Y -> Beta Y) by (induction 1; assumption).
  assert (Hb'out : forall n Y, Beta' n Y -> Out A Y C) by (induction 1; eauto with out).
  destruct (cantor Alpha' Beta') as [B HB].
  { split.
    { induction n.
        exists A, C; split; constructor.
      destruct IHn as [X [Y [HX HY]]].
      destruct (midpoint_existence X Y) as [M].
      destruct (Hdis M); [apply (Haux X Y); eauto|..].
        exists M, Y; split; [apply cX_other with X Y|apply cY_same with X M]; auto.
        exists X, M; split; [apply cX_same with Y M|apply cY_other with X Y]; auto.
    }
    assert (Hunique : (forall n X, Alpha' n X -> forall X', Alpha' n X' -> X = X')
                   /\ (forall n Y, Beta' n Y -> forall Y', Beta' n Y' -> Y = Y')).
    { apply cXY_ind; [inversion_clear 1; reflexivity| | |inversion_clear 1; reflexivity|..];
       intros n X Y M HX HXind HY HYind HM1 HM2; inversion_clear 1;
       first [assert (X = X') by (apply HXind; assumption)|assert (X = X0) by (apply HXind; assumption)];
       first [assert (Y = Y') by (apply HYind; assumption)|assert (Y = Y0) by (apply HYind; assumption)];
       treat_equalities; try reflexivity; exfalso; eauto.
    }
    destruct Hunique as [Hunia Hunib].
    intros n X X' Y' Y HX HX' HY' HY.
    specialize (Ha'a n).
    specialize (Hb'b n).
    specialize (Hunia n).
    specialize (Hunib n).
    inversion_clear HX'; inversion_clear HY';
     assert (X = X0) by (apply Hunia; assumption); assert (Y = Y0) by (apply Hunib; assumption);
     first [assert (X = X1) by (apply Hunia; assumption)|assert (X = X') by (apply Hunia; assumption)];
     first [assert (Y = Y1) by (apply Hunib; assumption)|assert (Y = Y') by (apply Hunib; assumption)];
     treat_equalities; repeat split; Between; apply Hcut; auto.
  }

  exists B.
  assert (Hdecr : forall P, P <> B -> exists n Xn Yn, Alpha' n Xn /\ Beta' n Yn /\ Lt Xn Yn P B).
  { intros P HP.
    (** Archimedes' axiom is used here *)
    destruct (reach__ex_gradexp_lt A C P B) as [P' [HP' HLt]]; auto.
    cut (exists n X Y, Alpha' n X /\ Beta' n Y /\ Cong X Y A P').
    { intros [n [X [Y [HX [HY]]]]].
      exists n, X, Y; split; [|split]; trivial.
      apply (cong2_lt__lt A P' P B); Cong.
    }
    clear P HP HLt.
    rewrite gradexp__gradexpinv in HP'; induction HP'.
      exists O, A, B0; repeat split; [constructor..|Cong].
    destruct IHHP' as [n [X [Y [HX [HY HXY]]]]]; [assumption..|].
    exists (S n).
    destruct (midpoint_existence X Y) as [M HM].
    destruct (Hdis M); [apply (Haux X Y); eauto|..].
    - exists M, Y; repeat split; [apply cX_other with X Y|apply cY_same with X M|]; auto.
      apply cong_left_commutativity, cong_cong_half_1 with X B0; [|split|Cong]; Midpoint.
    - exists X, M; repeat split; [apply cX_same with Y M|apply cY_other with X Y|]; auto.
      apply cong_cong_half_1 with Y B0; [|split|]; assumption.
  }
  intros X Y HX HY.
  apply (between_exchange3 A).
  - clear Y HY.
    destruct (l5_3 A X B C).
      apply Hcut; assumption.
      apply (HB O); constructor.
      assumption.
    destruct (eq_dec_points X B) as [|HXB]; [subst; Between|].
    destruct (eq_dec_points X A); [subst; Between|].
    exfalso.
    destruct (Hdecr X HXB) as [n [Xn [Yn [HXn [HYn HLt]]]]].
    destruct (Hcut X Yn); [eauto..|].
    apply (lt__nle Xn Yn X B HLt).
    apply le_transitivity with B Yn.
      apply le_left_comm, bet__le1213, (between_exchange3 A); assumption.
      apply bet__le2313, (HB n); assumption.

  - clear X HX.
    destruct (eq_dec_points A B) as [|HAB]; [subst; Between|].
    assert (HOut : Out A B Y).
    { apply l6_7 with C.
        apply bet_out, (HB O); [auto|constructor..].
      destruct (Hdecr A HAB) as [n [Xn [Yn [HXn [HYn HLt]]]]].
      assert (Bet Xn B Yn) by (apply (HB n); assumption).
      assert (Xn <> A) by (intro; treat_equalities; apply (lt__nle Xn Yn Xn B); Le).
      assert (Alpha Xn) by eauto.
      destruct (Hcut Xn Y); trivial.
      destruct (Hcut Xn C); trivial.
      apply l6_7 with Xn; Out.
    }
    destruct HOut as [_ [_ [|]]]; trivial.
    destruct (eq_dec_points Y B) as [|HYB]; [subst; Between|].
    exfalso.
    destruct (Hdecr Y HYB) as [n [Xn [Yn [HXn [HYn HLt]]]]].
    destruct (Hcut Xn Y); [eauto..|].
    apply (lt__nle Xn Yn Y B HLt).
    apply le_transitivity with Xn B.
      apply bet__le2313, (between_exchange3 A); assumption.
      apply bet__le1213, (HB n); assumption.
Qed.

End Archimedes_cantor_dedekind.