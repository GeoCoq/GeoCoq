Require Export GeoCoq.Axioms.continuity_axioms.
Require Export GeoCoq.Main.Meta_theory.Parallel_postulates.parallel_postulates.

Section Szmielew.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Definition hyperbolic_plane_postulate := forall A1 A2 P,
  ~ Col A1 A2 P -> exists B1 B2 C1 C2,
    Par A1 A2 B1 B2 /\ Col P B1 B2 /\
    Par A1 A2 C1 C2 /\ Col P C1 C2 /\
    ~ Col C1 B1 B2.

Lemma aah__hpp :
  hypothesis_of_acute_saccheri_quadrilaterals ->
  hyperbolic_plane_postulate.
Proof.
  intros aah A1 A2 P HNCol.
  destruct (l8_18_existence A1 A2 P HNCol) as [Q [HCol1 HPerp]].
  destruct (diff_col_ex3 A1 A2 Q HCol1) as [X [HXA1 [HXA2 [HXQ HCol2]]]].
  destruct (symmetric_point_construction X Q) as [Y [HBet HCong]].
  assert_diffs.
  assert (HCol3 : Col A1 A2 Y) by ColR.
  assert (HInt : Per P Q X /\ Per P Q Y).
    split; apply perp_per_1, perp_sym, perp_col2 with A1 A2; Perp.
  destruct HInt as [HPer HPer'].
  destruct (per__ex_saccheri Q P X) as [B1 HSac]; auto.
  destruct (per__ex_saccheri Q P Y) as [C1 HSac']; auto.
  exists B1; exists P; exists C1; exists P; repeat split; Col.
    apply sac__par1423 in HSac; apply par_symmetry, par_col2_par_bis with Q X; Col; Par.
    apply sac__par1423 in HSac'; apply par_symmetry, par_col2_par_bis with Q Y; Col; Par.
  intro HCol.
  assert (HBet0 : Bet B1 P C1).
  { apply sac__pars1234 in HSac; apply sac__pars1234 in HSac'.
    apply col_two_sides_bet with Q; Col.
    apply l9_8_2 with X; [|apply l12_6; Par].
    apply l9_2, l9_8_2 with Y; [|apply l12_6; Par].
    repeat split; auto; try (intro; apply HNCol; ColR).
    exists Q; split; Col; Between.
  }
  assert (B1 <> P) by (apply sac_distincts in HSac; spliter; auto).
  assert (C1 <> P) by (apply sac_distincts in HSac'; spliter; auto).
  assert (HLta : LtA B1 P C1 X Q Y); [|destruct HLta as [_ HNConga]; apply HNConga; CongA].
  assert (~ Col P Q X) by (apply per_not_col; auto).
  assert (HTS : TS Q P X Y) by (apply bet__ts; Col).
  apply sams_lta2_suma2__lta with B1 P Q Q P C1 P Q X P Q Y; SumA.
  - apply acute_per__lta; auto; apply acute_sym, (aah Q P B1 X HSac).
  - apply acute_per__lta; auto; apply (aah Q P C1 Y HSac').
Qed.

Theorem szmielew_s_theorem :
  aristotle_s_axiom ->
  (forall P : Prop,
    (playfair_s_postulate -> P) ->
    (hyperbolic_plane_postulate -> ~ P)->
    (P <-> playfair_s_postulate)).
Proof.
intro H; intros.
assert (L := aah__hpp).
assert (HE := aristotle__acute_or_right H).
assert (HG := aristotle__greenberg H).
elim (equivalent_postulates_assuming_greenberg_s_axiom
        HG playfair_s_postulate postulate_of_right_saccheri_quadrilaterals);
unfold List.In; tauto.
Qed.

End Szmielew.
