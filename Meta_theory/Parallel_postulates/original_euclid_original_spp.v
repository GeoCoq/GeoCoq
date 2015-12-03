Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section original_euclid_original_spp.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma original_euclid__original_spp : original_euclid -> original_spp.
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
      apply (isi_chara _ _ _ _ _ _ A'); Between.
    assert_cols.
    exists Y; auto.
  }

  intro.
  assert(Isi D' C B C B A') by (apply (isi_chara _ _ _ _ _ _ D); Between).
  assert(HSuma' := ex_suma A' B C B C D').
  destruct HSuma' as [P' [Q' [R' HSuma']]]; auto.
  assert(Hdiff := HSuma').
  apply suma_distincts in Hdiff.
  spliter.
  assert(HY := oe A' B C D' P' Q' R').
  destruct HY as [Y []]; Suma.
  3: exists Y; split; ColR.
  { assert(HNCol1 : ~ Col B C A) by (apply (one_side_not_col _ _ _ D); auto).
    assert(HNCol2 : ~ Col B C D) by (apply (one_side_not_col _ _ _ A); Side).
    exists D.
    split.
    apply l9_2; apply (l9_8_2 _ _ A); auto.
    - repeat split; Col.
      intro; apply HNCol1; ColR.
      exists B; Col; Between.
    - repeat split; Col.
      intro; apply HNCol2; ColR.
      exists C.
      split; Col; Between.
  }
  intro.
  apply HNBet.
  apply (bet_conga_bet P' Q' R'); auto.
  apply (suma2__conga A B C B C D); auto.
  apply suma__suma456123.
  apply (conga3_suma__suma A' B C B C D' P' Q' R'); auto.
  3: apply conga_refl; auto.
  - assert(HNCol : ~ Col B C D) by (apply (one_side_not_col _ _ _ A); Side).
    assert(two_sides C B D D').
    { repeat split; Col.
      intro; apply HNCol; ColR.
      exists C; Col; Between.
    }
    apply (isi2_suma2__conga123 _ _ _ _ _ _ B C D' P' Q' R'); auto.
      Suma.
    { apply isi__isi321456.
      repeat split; Col.
        right; intro; assert_cols; Col.
      exists D'.
      split; Conga; split.
      apply l9_9; auto.
      intro HNts; destruct HNts as [_ [_ []]]; assert_cols; Col.
    }
    apply suma__suma321456789.
    exists D'.
    split; Conga; split.
    apply l9_9; auto.
    apply conga_line; Between.

  - assert(HNCol : ~ Col B C A) by (apply (one_side_not_col _ _ _ D); auto).
    assert(two_sides B C A A').
    { repeat split; Col.
      intro; apply HNCol; ColR.
      exists B; Col; Between.
    }
    apply (isi2_suma2__conga456 A' B C _ _ _ _ _ _ P' Q' R'); auto.
      Suma.
    { apply isi__isi321456.
      apply isi__isi456123.
      repeat split; Col.
        right; intro; assert_cols; Col.
      exists A'.
      split; Conga; split.
      apply l9_9; auto.
      intro HNts; destruct HNts as [_ [_ []]]; assert_cols; Col.
    }
    apply suma__suma456123.
    exists A'.
    split; Conga; split.
    apply l9_9; auto.
    apply conga_line; Between.
Qed.

End original_euclid_original_spp.