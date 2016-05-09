Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section alternate_interior_angles_postulate_triangle.

Context `{T2D:Tarski_2D}.

Lemma alternate_interior__triangle : alternate_interior_angles_postulate -> triangle_postulate.
Proof.
  intros aia A B C D E F HTrisuma.
  elim(Col_dec A B C).
    intro; apply (col_trisuma__bet A B C); auto.
  intro HNCol.
  destruct HTrisuma as [D1 [E1 [F1 []]]].
  suma.assert_diffs.
  assert(HX := l8_18_existence A C B).
  destruct HX as [X []]; Col.
  assert(HB0 := perp_exists B B X).
  destruct HB0 as [B0 HPar].
  intro; subst X; Col.
  apply (l12_9 A C) in HPar; auto.
  apply (par_not_col_strict _ _ _ _ B) in HPar; Col.
  assert(~ Col C B B0) by (apply (par_not_col A C); Col).
  assert(~ Col A B B0) by (apply (par_not_col A C); Col).
  assert_diffs.

  assert(HB1 : exists B1, Col B0 B B1 /\ TS B C A B1) by (apply (not_par_other_side _ _ _ _ B); Col).
  destruct HB1 as [B1 [HCol1 Hts1]].
  assert(~ Col B1 B C) by (destruct Hts1 as [_ [_ []]]; auto).
  assert(HB2 := symmetric_point_construction B1 B).
  destruct HB2 as [B2].
  assert_diffs.
  assert(TS B A B1 B2).
  { repeat split; auto.
    intro; assert(Col A B B0); auto; ColR.
    intro; assert(Col A B B0); auto; ColR.
    exists B.
    split; Col; Between.
  }
  assert(TS B A C B2).
  { apply (l9_8_2 _ _ B1); auto.
    apply os_ts1324__os; Side.
    apply l12_6.
    apply par_strict_symmetry.
    apply (par_strict_col_par_strict _ _ _ B0); Col; Par.
  }
  apply (bet_conga_bet B1 B B2); Between.
  apply (suma2__conga D1 E1 F1 C A B); auto.
  assert(CongA A B B2 C A B).
  { apply conga_left_comm; apply aia; try (apply l9_2; auto).
    apply par_symmetry; apply (par_col_par _ _ _ B0); try (apply par_strict_par); auto; ColR.
  }
  apply (conga3_suma__suma B1 B A A B B2 B1 B B2); try (apply conga_refl); auto.
    exists B2; repeat (split; CongA); apply l9_9; auto.
  apply (suma2__conga A B C B C A); auto.
  apply (conga3_suma__suma A B C C B B1 A B B1); CongA.
  exists B1; repeat (split; CongA); apply l9_9; auto.
  apply conga_comm.
  apply aia; Side.
  apply par_symmetry.
  apply (par_col_par _ _ _ B0); Col.
  apply par_strict_par; Par.
Qed.

End alternate_interior_angles_postulate_triangle.
