Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section alternate_interior_angles_proclus.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma alternate_interior__proclus : greenberg_s_postulate -> alternate_interior_angles_postulate ->
   proclus_postulate.
Proof.
  intros greenberg aia.
  intros A B C D P Q HPar HP HQ.
  elim(Col_dec C D P).
    intro HConf; exists P; split; Col.
  intro HStrict.
  assert(HParS : Par_strict A B C D).
  { apply par_strict_symmetry.
    apply (par_not_col_strict _ _ _ _ P); auto.
    apply par_symmetry; auto.
  }
  assert (HP1 := l8_18_existence C D P).
  destruct HP1 as [P1 []]; auto.
  elim(Col_dec P Q P1).
    intro; exists P1; split; auto.
  intro HNCol1.
  assert_diffs.
  assert(HQ1 : exists Q1, Col Q P Q1 /\ one_side A B P1 Q1).
  { apply (not_par_same_side _ _ _ _ P); Col.
    apply not_col_permutation_1.
    apply (par_not_col C D); Col; Par.
  }
  destruct HQ1 as [Q1 []].
  assert(~Col A B Q1) by (apply (one_side_not_col _ _ _ P1); Side).
  assert(P<>Q1) by (intro; subst Q1; auto).
  assert(~ Col P P1 Q1) by (intro; apply HNCol1; ColR).

  assert(HNCol2 : ~Col P1 A B) by (apply (par_not_col C D); Par; Col).
  assert(HA1 : exists A1, Col A B A1 /\ one_side P P1 Q1 A1).
  { elim(Col_dec P P1 A).
    2: intro; apply (not_par_same_side _ _ _ _ P); Col.
    intro.
    assert(HA1 := not_par_same_side P P1 B A P Q1).
    destruct HA1 as [A1 []]; Col.
    intro; apply HNCol2; ColR.
    exists A1; split; Col.
  }
  destruct HA1 as [A1 []].
  assert(~Col P P1 A1) by (apply (one_side_not_col _ _ _ Q1); Side).
  assert(HNCol3 : ~Col P C D) by (apply (par_not_col A B); Col).
  assert(HC1 : exists C1, Col C D C1 /\ one_side P P1 Q1 C1).
  { elim(Col_dec P P1 C).
    2: intro; apply (not_par_same_side _ _ _ _ P1); Col.
    intro.
    assert(HC1 := not_par_same_side P P1 D C P1 Q1).
    destruct HC1 as [C1 []]; Col.
    intro; apply HNCol3; ColR.
    exists C1; split; Col.
  }
  destruct HC1 as [C1 []].
  assert(HNCol4 : ~Col P P1 C1) by (apply (one_side_not_col _ _ _ Q1); Side).
  assert(HC2 := symmetric_point_construction C1 P1).
  destruct HC2 as [C2].
  assert_cols.
  assert_diffs.
  assert(~ Col C2 P P1) by (intro; apply HNCol4; ColR).
  assert(Col C D C2) by ColR.
  assert(InAngle Q1 P1 P A1) by (apply os2__inangle; Side; apply (col2_os__os A B); Col).
  assert(lta A1 P Q1 A1 P P1).
  { split.
    exists Q1; split; Conga; apply l11_24; auto.
    intro HConga.
    apply l11_22_aux in HConga.
    destruct HConga as [Habs|Habs].
    assert_cols; Col.
    apply l9_9 in Habs.
    apply Habs.
    apply one_side_symmetry.
    apply (col2_os__os A B); auto.
  }
  assert(acute A1 P Q1).
  { exists A1.
    exists P.
    exists P1.
    split; auto.
    apply (l11_17 P P1 C2).
    - apply perp_per_1; auto.
      apply perp_sym.
      apply (perp_col2 C D); Perp.

    - apply conga_sym.
      apply conga_right_comm.
      apply aia.
      2: apply (par_col4__par A B C D); Col.
      apply (l9_8_2 _ _ C1).
      repeat split; Col; exists P1; split; Col; Between.
      apply (one_side_transitivity _ _ _ Q1); Side.
   }
   assert (HS := greenberg P P1 C1 A1 P Q1).
   destruct HS as [S []]; auto.
     intro; apply HQ; ColR.
     apply perp_per_1; auto; apply perp_sym; apply (perp_col2 C D); Perp.
   assert(Col C D S) by ColR.
   assert_diffs.
   assert(one_side P P1 S C1) by (apply invert_one_side; apply out_one_side; Col).
   assert(HY : InAngle Q1 P1 P S).
   { assert(one_side P P1 S C1) by (apply invert_one_side; apply out_one_side; Col).
     assert(~ Col P P1 S) by (apply (one_side_not_col _ _ _ C1); auto).
     apply os2__inangle.
     apply (one_side_transitivity _ _ _ C1); Side.
     exists A1.
     assert(one_side P P1 S A1).
     { apply (one_side_transitivity _ _ _ C1); auto.
       apply (one_side_transitivity _ _ _ Q1); Side.
     }
     assert(two_sides P S P1 A1) by (apply l9_31; auto; apply l12_6; apply (par_strict_col4__par_strict A B C D); auto).
     split; auto.
     assert(Hlta : lta A1 P S A1 P Q1).
     { apply (conga_preserves_lta P S P1 A1 P Q1); try (apply conga_refl); auto.
       apply conga_sym.
       apply conga_right_comm.
       apply aia; Side.
       apply (par_col4__par A B C D); auto.
     }
     destruct Hlta as [Hlea HNConga].
     apply invert_two_sides.
     apply in_angle_two_sides; auto.
     2: apply not_col_permutation_1; apply (par_not_col C D); Col; apply (par_strict_col2_par_strict _ _ A B); Par.
     - intro.
       elim (out_dec P S Q1); intro Habs.
       assert_diffs; apply HNConga; apply (out_conga A1 P S A1 P S); try (apply out_trivial); Conga.
       apply not_out_bet in Habs; Col.
       assert(~ one_side P P1 S A1); auto.
       apply l9_9.
       apply l9_2.
       apply (l9_8_2 _ _ Q1); auto.
       repeat split; Col.
       exists P.
       split; Col; Between.

     - apply l11_24.
       apply (lea_in_angle _ _ _ P1 S P); Lea.
       apply aia; Side; apply (par_col4__par A B C D); auto.
       apply (one_side_transitivity _ _ _ P1).
       apply one_side_symmetry; apply (col2_os__os A B); auto.
       apply l12_6; apply (par_strict_col4__par_strict A B C D); auto.
   }
   destruct HY as [_ [_ [_ [Y [HY1 HY2]]]]].
   exists Y.
   split.
   2: ColR.
   destruct HY2.
   subst Y; Col.
   ColR.
Qed.

End alternate_interior_angles_proclus.
