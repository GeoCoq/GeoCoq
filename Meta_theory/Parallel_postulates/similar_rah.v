Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.saccheri.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section similar_rah.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

(**
This is an adaptation of the proof of Martin's Theorem 23.6.
It is more complicated because Martin use the properties of the deflect of a triangle,
which are difficult to handle in our formalization.
*)

Lemma similar__rah_aux : forall A B C D E F,
  ~ Col A B C -> CongA A B C D E F -> CongA B C A E F D -> CongA C A B F D E ->
  LeA B C A A B C -> Lt D E A B -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intros A B C D E F HNCol HCongaB HCongaC HCongaA Hlea Hlt.
  assert_diffs.
  destruct (segment_construction_3 A B D E) as [G []]; auto.
  rename H into HFD.
  destruct (segment_construction_3 A C D F) as [H []]; auto.
  apply (cong2_lt__lt _ _ _ _ A G A B) in Hlt; Cong.
  assert(Bet A G B) by (apply (l6_13_1); Le; apply l6_6; auto).
  assert(B <> G) by (intro; subst; destruct Hlt; Cong).
  assert(HCongaA' : CongA C A B H A G) by (apply out2__conga; apply l6_6; auto).
  destruct(l11_49 F D E H A G) as [_ [HConga1 HConga2]]; Cong.
    apply (conga_trans _ _ _ C A B); CongA.
  apply (conga_trans _ _ _ _ _ _ A G H) in HCongaB; auto.
  apply (conga_trans _ _ _ _ _ _ G H A) in HCongaC; CongA.
  clear dependent D; clear dependent E; clear dependent F.
  rename HCongaA' into HCongaA.

  assert(HNCol1 : ~ Col A G H) by (apply (ncol_conga_ncol A B C); auto).
  assert(HNCol2 : ~ Col B G H) by (intro; apply HNCol1; ColR).
  assert(Par_strict G H B C).
  { apply (par_not_col_strict _ _ _ _ B); Col.
    apply par_symmetry.
    apply (l12_22_b _ _ _ _ A); CongA.
    apply out_one_side; auto.
  }
  assert(HNCol3 : ~ Col G H C) by (apply (par_strict_not_col_4 _ _ B); auto).
  assert(HNCol4 : ~ Col B C G) by (apply (par_strict_not_col_3 _ H); auto).
  assert(HNCol5 : ~ Col H B C) by (apply (par_strict_not_col_2 G); auto).
  assert_diffs.
  assert(Out C H A).
  { apply (col_one_side_out _ B); Col.
    apply invert_one_side.
    apply (one_side_transitivity _ _ _ G).
      apply l12_6; Par.
      apply out_one_side; Col; apply bet_out; Between.
  }
  assert(Bet A H C) by (apply out2__bet; apply l6_6; auto).
  assert(SAMS B G H H C B).
  { apply (sams_chara _ _ _ _ _ _ A); Between.
    apply (l11_30 B C A A B C); auto; apply conga_right_comm; auto.
    apply out2__conga; [apply out_trivial|]; auto.
  }
  assert(CongA A G H G B C).
    apply (l11_10 A G H A B C); try (apply out_trivial); CongA; apply bet_out; Between.
  assert(CongA G H A B C H).
    apply (l11_10 G H A B C A); try (apply out_trivial); CongA.
  assert(SAMS B G H C B G) by (apply (conga2_sams__sams B G H H G A); CongA; SumA).
  assert(SAMS C H G B C H) by (apply (conga2_sams__sams C H G G H A); CongA; SumA).
  destruct(ex_suma B C G C G B) as [I [J [K]]]; auto.
  destruct(ex_suma H C G C G H) as [L [M [N]]]; auto.
  suma.assert_diffs.
  destruct(ex_suma I J K G B C) as [O [P [Q]]]; auto.
  destruct(ex_suma L M N G H C) as [R [S [T]]]; auto.
  destruct(ex_suma I J K L M N) as [U [V [W]]]; auto.
  suma.assert_diffs.
  assert(HInter : SAMS I J K L M N /\ SumA H G B B C H U V W).
  { assert(TS G C B H).
    { apply invert_two_sides, l9_31; Side.
      apply (col_one_side _ A); Col.
      apply invert_one_side; apply out_one_side; try (apply l6_6); Col.
    }
    assert(SAMS H G B B C G).
    { apply (sams_lea2__sams _ _ _ _ _ _ H G B B C H); try (apply lea_refl); SumA.
      apply inangle__lea.
      apply os_ts__inangle; Side.
    }
    destruct(ex_suma B C G H G B) as [X [Y [Z]]]; auto.
    assert(SumA B G C C G H H G B) by SumA.
    assert(SAMS B G C C G H).
    { apply os_ts__sams; trivial.
      apply (col_one_side _ A); Col.
      apply invert_one_side, out_one_side; Col.
    }
    assert(SAMS I J K C G H) by (apply (sams_assoc B C G C G B _ _ _ _ _ _ H G B); SumA).
    assert(SumA I J K C G H X Y Z) by (apply (suma_assoc B C G C G B _ _ _ _ _ _ _ _ _ H G B); SumA).
    assert(SAMS B C G H C G) by (apply sams_right_comm, os_ts__sams; Side).
    assert(SumA B C G H C G H C B) by SumA.
    split.
    - assert(SAMS X Y Z H C G) by (apply (sams_assoc H G B B C G _ _ _ _ _ _ H C B); SumA).
      apply (sams_assoc _ _ _ C G H H C G X Y Z); SumA.
    - assert(SumA X Y Z H C G U V W) by (apply (suma_assoc I J K C G H _ _ _ _ _ _ _ _ _ L M N); SumA).
      apply (suma_assoc _ _ _ B C G H C G _ _ _ X Y Z); SumA.
  }
  destruct HInter.

  elim(saccheri_s_three_hypotheses).
  - intro aah.
    exfalso.
    apply(nlta U V W).
    apply (sams_lta2_suma2__lta I J K L M N _ _ _ H G B B C H); SumA.
    { destruct (t22_14__sams_nbet aah C G B I J K O P Q) as [HIsi HNBet]; Col.
      apply (sams_lea_lta789_suma2__lta123 _ _ _ G B C O P Q _ _ _ G B C A G B); Lea.
        split; Lea; intro; apply HNBet; apply (bet_conga__bet A G B); CongA.
        apply (conga3_suma__suma B G H H G A A G B); CongA; SumA.
    }
    destruct (t22_14__sams_nbet aah C G H L M N R S T) as [HIsi HNBet]; Col.
    apply (sams_lea_lta789_suma2__lta123 _ _ _ G H C R S T _ _ _ G H C A H C); Lea.
      split; Lea; intro; apply HNBet; apply (bet_conga__bet A H C); CongA.
      apply (conga3_suma__suma A H G G H C A H C); CongA; SumA.

  - intro HUn.
    destruct HUn as [|oah]; auto.
    exfalso.
    apply(nlta U V W).
    apply (sams_lta2_suma2__lta H G B B C H _ _ _ I J K L M N); SumA; apply nlea__lta; auto; intro.
    { apply (t22_14__nsams oah C G B I J K); Col.
      apply (sams_lea2__sams _ _ _ _ _ _ H G B G B C); Lea; SumA.
    }
    apply (t22_14__nsams oah C G H L M N); Col.
    apply (sams_lea2__sams _ _ _ _ _ _ B C H G H C); Lea; SumA.
Qed.

Lemma similar__rah : postulate_of_existence_of_similar_triangles -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intro similar.
  destruct similar as [A [B [C [D [E [F]]]]]].
  spliter.
  assert_diffs.
  elim (lea_total B C A A B C); auto; intro; [elim (le_cases D E A B)|elim (le_cases D F A C)].
  - intro.
    apply (similar__rah_aux A B C D E F); auto.
    split; Cong.

  - intro.
    apply (similar__rah_aux D E F A B C); CongA.
      apply (ncol_conga_ncol A B C); auto.
      apply (l11_30 B C A A B C); auto.
      split; auto.

  - intro.
    apply (similar__rah_aux A C B D F E); Col; CongA.
      apply lea_comm; trivial.
    split; auto; intro; destruct(l11_50_1 A C B D F E); Col; CongA; Cong.

  - intro.
    apply (similar__rah_aux D F E A C B); CongA.
      apply (ncol_conga_ncol A C B); Col; CongA.
      apply (l11_30 A B C B C A); CongA.
      split; auto; intro; destruct(l11_50_1 A C B D F E); Col; CongA; Cong.
Qed.

End similar_rah.