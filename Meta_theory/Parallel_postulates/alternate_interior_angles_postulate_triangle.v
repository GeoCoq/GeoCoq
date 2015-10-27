Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section alternate_interior_angles_postulate_triangle.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma playfair__triangle : alternate_interior_angles_postulate -> triangle_postulate.
Proof.
  intros aia A B C D E F HTrisuma.
  destruct HTrisuma as [D1 [E1 [F1 []]]].
  suma.assert_diffs.
  elim(Col_dec A B C).
  { intro.
    elim(out_dec A C B).
    { intro.
      apply (bet_conga_bet D1 E1 F1).
      2: apply (out546_suma__conga _ _ _ C A B); auto.
      elim(out_dec C B A).
      { intro.
        apply (bet_conga_bet A B C).
        apply out2__bet; apply l6_6; auto.
        apply (out546_suma__conga _ _ _ B C A); auto.
      }
      intro.
      assert(Bet B C A) by (apply not_out_bet; Col).
      apply (bet_conga_bet B C A); auto.      
      apply (out213_suma__conga A B C); auto.
      apply l6_6; apply bet_out; auto.
    }
    intro.
    assert(Bet C A B) by (apply not_out_bet; Col).
    apply (bet_conga_bet C A B); auto.
    apply (out213_suma__conga D1 E1 F1); auto.
    apply (out_conga_out B C A); auto.
    apply l6_6; apply bet_out; auto.
    apply (out213_suma__conga A B C); auto.
    apply bet_out; Between.
  }
  intro HNCol.

  assert(HX := l8_18_existence A C B).
  destruct HX as [X []]; Col.
  assert(HB0 := perp_exists B B X).
  destruct HB0 as [B0 HPar].
  intro; subst X; Col.
  apply (l12_9 A C) in HPar; try (apply all_coplanar); auto.
  apply (par_not_col_strict _ _ _ _ B) in HPar; Col.
  assert(~ Col C B B0) by (apply (par_not_col A C); Col).
  assert(~ Col A B B0) by (apply (par_not_col A C); Col).
  assert_diffs.

  assert(HB1 : exists B1, Col B0 B B1 /\ two_sides B C A B1) by (apply (not_par_other_side _ _ _ _ B); Col).
  destruct HB1 as [B1 [HCol1 Hts1]].
  assert(~ Col B1 B C) by (destruct Hts1 as [_ [_ []]]; auto).
  assert(HB2 := symmetric_point_construction B1 B).
  destruct HB2 as [B2].
  assert_diffs.
  assert(two_sides B A B1 B2).
  { repeat split; auto.
    intro; assert(Col A B B0); auto; ColR.
    intro; assert(Col A B B0); auto; ColR.
    exists B.
    split; Col; Between.
  }
  assert(two_sides B A C B2).
  { apply (l9_8_2 _ _ B1); auto.
    apply os_ts1324__os; Side.
    apply l12_6.
    apply par_strict_symmetry.
    apply (par_strict_col_par_strict _ _ _ B0); Col; Par.
  }
  apply (bet_conga_bet B1 B B2); Between.
  apply (suma2__conga D1 E1 F1 C A B); auto.
  apply (conga3_suma__suma B1 B A A B B2 B1 B B2); try (apply conga_refl; auto).
    exists B2; repeat (split; Conga); apply l9_9; auto.
    2: apply conga_left_comm; apply aia; try (apply l9_2; auto).
    2: apply par_symmetry; apply (par_col_par _ _ _ B0); try (apply par_strict_par); auto; ColR.
  apply (suma2__conga A B C B C A); auto.
  apply (conga3_suma__suma A B C C B B1 A B B1); Conga.
  exists B1; repeat (split; Conga); apply l9_9; auto.
  apply conga_comm.
  apply aia; Side.
  apply par_symmetry.
  apply (par_col_par _ _ _ B0); Col.
  apply par_strict_par; Par.
Qed.

End alternate_interior_angles_postulate_triangle.