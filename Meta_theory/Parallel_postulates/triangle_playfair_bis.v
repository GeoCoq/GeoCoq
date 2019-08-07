Require Import GeoCoq.Axioms.continuity_axioms.
Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch13_1.

Section triangle_playfair_bis.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma legendre_aux :
  greenberg_s_axiom ->
  triangle_postulate ->
  forall A B C P Q,
    Perp Q A P Q -> Perp P B P Q -> Par_strict Q A P B ->
    Par_strict Q A P C -> OS P B Q C -> OS P Q C A -> OS P Q C B ->
    False.
Proof.
  intros greenberg triangle.
  intros A B C P Q HPerpAP HPerpBP HParAB HParAC HOS1 HOS2 HOS3.
  destruct (symmetric_point_construction B P) as [B'].
  assert(HInAngle : InAngle C Q P B) by Side.
  assert (~ Col P B C) by (apply one_side_not_col124 with Q, HOS1).
  assert (~ Col P Q C) by (apply one_side_not_col123 with A, HOS2).
  assert (~ Col P Q A) by (apply one_side_not_col124 with C, HOS2).
  assert(LtA B P C B P Q).
    apply inangle__lta; [Col|apply l11_24, HInAngle].
  assert(Acute B P C).
    exists B, P, Q; split; Perp.
  assert_diffs.
  destruct (greenberg P Q A B P C) as [R []]; Perp; Col.
  assert_diffs.
  assert(OS P Q R A) by (apply invert_one_side, out_one_side; Col).
  assert(OS P C Q R).
    apply l12_6, par_strict_col_par_strict with A; Par; Col.
  destruct (ex_suma B' P R P R Q) as [D [E [F Hsuma1]]]; auto.
  assert(Htri : TriSumA R Q P D E F).
  { exists B', P, R; split; auto.
    apply (conga3_suma__suma B' P Q Q P R B' P R); try (apply conga_refl; auto).
    - exists R.
      assert (TS P Q R B'); [|repeat (split; CongA); Side; Cop].
      apply (l9_8_2 _ _ B).
        apply bet__ts; Between; apply one_side_not_col124 with C, HOS3.
      apply (one_side_transitivity _ _ _ A); [|Side].
      apply (one_side_transitivity _ _ _ C); Side.
    - apply l11_16; auto; apply l8_2.
        apply per_col with B; Perp; Col.
        apply per_col with A; Perp; Col.
  }
  destruct (ex_suma B' P R C P B) as [I [J [K Hsuma2]]]; auto.
  assert(~ Col R P B').
  { apply (par_not_col Q A); Col.
    apply par_strict_col_par_strict with B; Col.
  }
  assert(Hsuma3 : SumA B' P R R P B B' P B) by (apply bet__suma; Between).
  assert(Hsams3 : SAMS B' P R R P B) by (apply bet__sams; Between).
  assert(LeA C P B R P B).
  { apply lea_comm, inangle__lea, os_ts__inangle.
    - apply l9_2, (l9_8_2 _ _ Q); trivial.
      apply invert_two_sides, in_angle_two_sides; Col.
    - apply (one_side_transitivity _ _ _ Q); trivial.
      apply one_side_symmetry, l12_6, par_strict_col_par_strict with A; Par; Col.
  }
  assert(Habs : LtA D E F B' P B).
  { apply (lea456789_lta__lta _ _ _ I J K);
    [|apply (sams_lea2_suma2__lea B' P R C P B _ _ _ B' P R R P B); Lea].
    apply (sams_lea_lta456_suma2__lta B' P R P R Q _ _ _ B' P R C P B); Lea.
    apply (sams_lea2__sams _ _ _ _ _ _ B' P R R P B); Lea.
  }
  apply Habs.
  apply suma_distincts in Hsuma1; spliter.
  apply conga_line; Between.
  apply (triangle R Q P); auto.
Qed.

Lemma legendre_aux1 :
  greenberg_s_axiom ->
  triangle_postulate ->
  forall A1 A2 B1 B2 C1 C2 P,
    Perp2 A1 A2 B1 B2 P -> ~ Col A1 A2 P -> Col P B1 B2 -> Coplanar A1 A2 B1 B2 ->
    Par A1 A2 C1 C2 -> Col P C1 C2 -> ~ TS B1 B2 A1 C1 ->
    Col C1 B1 B2.
Proof.
  intros greenberg triangle.
  intros A1 A2 B1 B2 C1 C2 P HPerp2 HNC HPB HCop HParAC HPC HNts.
  assert(HParAB : Par_strict A1 A2 B1 B2)
    by (apply (col_cop_perp2__pars_bis P); Col).
  apply (par_not_col_strict _ _ _ _ P) in HParAC; Col.
  elim(col_dec C1 B1 B2); auto.
  intro HC1NotB.
  exfalso.
  assert(P<>C1) by (intro; subst C1; Col).
  destruct HPerp2 as [P1 [P2 [HP [HPerpAP HPerpBP]]]].
  assert(HQ := HPerpAP); auto.
  destruct HQ as [Q [_ [_ [HQP[HQA _]]]]].
  assert(P<>Q) by (intro; subst Q; Col).
  apply (perp_col0 _ _ _ _ P Q) in HPerpAP; Col.
  apply (perp_col0 _ _ _ _ P Q) in HPerpBP; Col.
  clear dependent P1.
  clear dependent P2.

  assert_diffs.
  assert(Hos : OS B1 B2 Q C1).
  { apply (one_side_transitivity _ _ _ A1).
    - destruct (eq_dec_points A1 Q).
        subst A1; apply one_side_reflexivity; auto; apply (par_strict_not_col_2 A2); Par.
      apply l12_6, par_strict_right_comm, (par_strict_col_par_strict _ _ _ A2); Col; Par.
    - apply cop_nts__os; Col; [|apply (par_strict_not_col_2 A2); Par].
      apply coplanar_pseudo_trans with A1 A2 P.
        assumption.
        apply coplanar_perm_1, col_cop__cop with B2; Col.
        apply coplanar_perm_1, col_cop__cop with B1; Col; Cop.
        Cop.
        apply coplanar_perm_1, col_cop__cop with C2; Col; Cop.
  }
  assert(~ Col Q C1 P) by (apply (par_not_col A1 A2); auto; apply par_strict_col_par_strict with C2; Col).
  assert(HQNotB : ~ Col B1 B2 Q) by (apply one_side_not_col123 with C1; auto).
  assert(HB3 : exists B3, Col B1 B2 B3 /\ OS P Q C1 B3).
  { destruct (col_dec P Q B1);
    [|apply cop_not_par_same_side with P; Col; apply coplanar_perm_12, coplanar_trans_1 with B2; Col; Cop].
    assert (P = B1) by (apply (l6_21 B1 B2 Q P); Col).
    treat_equalities.
    destruct (cop_not_par_same_side P Q B2 P P C1) as [B3 []]; Col; Cop.
    exists B3; split; Col.
  }
  destruct HB3 as [B3 []].
  assert(~ Col P Q B3) by (apply (one_side_not_col123 _ _ _ C1); Side).
  assert(HA3 : exists A3, Col A1 A2 A3 /\ OS P Q C1 A3).
  { assert (Coplanar A1 A2 C1 P) by (apply col_cop__cop with C2; Col; Cop).
    destruct (col_dec P Q A1);
    [|apply cop_not_par_same_side with Q; Col; apply coplanar_perm_5, col_cop__cop with A2; Col; Cop].
    assert (Q = A1) by (apply (l6_21 A1 A2 P Q); Col).
    treat_equalities.
    destruct (cop_not_par_same_side P Q A2 Q Q C1) as [A3 []]; Col; Cop.
    exists A3; split; Col.
  }
  destruct HA3 as [A3 []].
  assert_diffs.
  apply (legendre_aux greenberg triangle A3 B3 C1 P Q); trivial.
    apply (perp_col2 A1 A2); Col.
    apply (perp_col2 B1 B2); Col.
    apply (par_strict_col4__par_strict A1 A2 B1 B2); Col.
    apply (par_strict_col4__par_strict A1 A2 C1 C2); Col.
    apply (col2_os__os B1 B2); Col.
Qed.

Lemma legendre_aux2 :
  greenberg_s_axiom ->
  triangle_postulate ->
  forall A1 A2 B1 B2 C1 C2 P,
    Perp2 A1 A2 B1 B2 P -> ~ Col A1 A2 P -> Col P B1 B2 -> Coplanar A1 A2 B1 B2 ->
    Par A1 A2 C1 C2 -> Col P C1 C2 ->
    Col C1 B1 B2. (** "half" of playfair_bis *)
Proof.
  intros greenberg triangle.
  intros A1 A2 B1 B2 C1 C2 P HPerp2 HNC HPB HCop HParAC HPC.
  assert(HParAB : Par_strict A1 A2 B1 B2)
    by (apply (col_cop_perp2__pars_bis P); Col).
  apply (legendre_aux1 greenberg triangle A1 A2 _ _ _ C2 P); auto.
  intro Hts.
  assert(HC1NotB : ~ Col C1 B1 B2) by (destruct Hts as [_ []]; auto).
  assert(C1<>P) by (intro; subst C1; Col).
  destruct (symmetric_point_construction C1 P) as [C3].
  assert_diffs.
  assert(HC3NotB : ~ Col C3 B1 B2) by (intro; apply HC1NotB; ColR).
  apply HC3NotB.
  apply (legendre_aux1 greenberg triangle A1 A2 _ _ _ C1 P); Col.
  - apply par_right_comm.
    apply (par_col_par _ _ _ P); Col.
    apply (par_col_par _ _ _ C2); Col.
  - apply l9_9_bis.
    exists C1.
    repeat (split; [assumption|]).
    exists P.
    split; Between.
Qed.

Lemma triangle__playfair_bis :
  greenberg_s_axiom ->
  triangle_postulate ->
  alternative_playfair_s_postulate.
Proof.
  intros greenberg triangle.
  intros A1 A2 B1 B2 C1 C2 P.
  split.
  apply (legendre_aux2 greenberg triangle A1 A2 _ _ _ C2 P); auto.
  apply (legendre_aux2 greenberg triangle A1 A2 _ _ _ C1 P); Par; Col.
Qed.

End triangle_playfair_bis.