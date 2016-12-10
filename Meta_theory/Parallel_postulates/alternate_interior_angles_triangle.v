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
  destruct(ex_conga_ts B C A C B A) as [B1 [HConga HTS]]; Col.
  assert (HPar : Par A C B B1) by (apply par_left_comm, par_symmetry, l12_21_b; Side; CongA).
  apply (par_not_col_strict _ _ _ _ B) in HPar; Col.
  assert(HNCol1 : ~ Col C B B1) by (apply (par_not_col A C); Col).
  assert(HNCol2 : ~ Col A B B1) by (apply (par_not_col A C); Col).
  assert(HB2 := segment_construction B1 B B1 B).
  destruct HB2 as [B2 [HBet HCong]].
  assert_diffs.

  assert(HTS1 : TS B A B1 B2).
  { repeat split; Col.
    intro; apply HNCol2; ColR.
    exists B; Col.
  }
  assert(HTS2 : TS B A C B2).
  { apply (l9_8_2 _ _ B1); auto.
    apply os_ts1324__os; Side.
  }
  apply (bet_conga_bet B1 B B2); auto.
  apply (suma2__conga D1 E1 F1 C A B); auto.
  assert(CongA A B B2 C A B).
  { apply conga_left_comm, aia; Side.
    apply par_symmetry, (par_col_par _ _ _ B1); Col; Par.
  }
  apply (conga3_suma__suma B1 B A A B B2 B1 B B2); try (apply conga_refl); auto.
    exists B2; repeat (split; CongA); apply l9_9; auto.
  apply (suma2__conga A B C B C A); auto.
  apply (conga3_suma__suma A B C C B B1 A B B1); CongA.
  exists B1; repeat (split; CongA); apply l9_9; Side.
Qed.

End alternate_interior_angles_postulate_triangle.
