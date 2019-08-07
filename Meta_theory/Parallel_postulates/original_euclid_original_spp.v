Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.

Section original_euclid_original_spp.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma original_euclid__original_spp : euclid_s_parallel_postulate -> alternative_strong_parallel_postulate.
Proof.
  intros oe A B C D P Q R Hos HSuma HNBet.
  assert(HA' := symmetric_point_construction A B).
  destruct HA' as [A'].
  assert(HD' := symmetric_point_construction D C).
  destruct HD' as [D'].
  assert (Hdiff := HSuma).
  apply suma_distincts in Hdiff.
  spliter.
  assert_diffs.
  elim(lea_total B C D C B A'); auto.
  { intro.
    assert(HY := oe A B C D P Q R).
    destruct HY as [Y []]; auto.
      apply (sams_chara _ _ _ _ _ _ A'); Between.
    exists Y; split; Col.
  }

  intro.
  assert(SAMS D' C B C B A') by (apply (sams_chara _ _ _ _ _ _ D); Between).
  assert(HSuma' := ex_suma A' B C B C D').
  destruct HSuma' as [P' [Q' [R' HSuma']]]; auto.
  assert(Hdiff := HSuma').
  apply suma_distincts in Hdiff.
  spliter.
  assert(HY := oe A' B C D' P' Q' R').
  destruct HY as [Y []]; SumA; [..|exists Y; split; ColR].
  { assert(HNCol1 : ~ Col B C A) by (apply (one_side_not_col123 _ _ _ D); auto).
    assert(HNCol2 : ~ Col B C D) by (apply (one_side_not_col123 _ _ _ A); Side).
    exists D.
    split.
    - apply l9_2; apply (l9_8_2 _ _ A); auto.
      apply bet__ts; Between; Col.
    - apply l9_2, invert_two_sides, bet__ts; Between; Col.
  }
  intro.
  apply HNBet.
  apply (suma_suppa__bet A B C B C D); trivial.
  assert (SuppA A' B C B C D') by (apply bet_suma__suppa with P' Q' R'; assumption).
  apply (conga2_suppa__suppa B C D' A' B C).
    apply (suppa2__conga456 A' B C); trivial; apply suppa_right_comm, bet__suppa; Between.
    apply suppa2__conga123 with B C D'; trivial; apply suppa_left_comm, bet__suppa; Between.
    apply suppa_sym; assumption.
Qed.

End original_euclid_original_spp.