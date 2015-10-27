Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section triangle_playfair_bis.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma legendre_aux1 : greenberg_s_postulate -> triangle_postulate ->
   forall A1 A2 B1 B2 C1 C2 P, Perp2 A1 A2 B1 B2 P -> Col P B1 B2 ->
   Par A1 A2 C1 C2 -> Col P C1 C2 -> ~ two_sides B1 B2 A1 C1 ->
   Col C1 B1 B2.
Proof.
  intros greenberg triangle.
  intros A1 A2 B1 B2 C1 C2 P HPerp2 HPB HParAC HPC HCts.
  assert (HParAB : Par A1 A2 B1 B2) by (apply (perp2_par _ _ _ _ P); auto).
  elim(Col_dec P A1 A2).
  { intro HConf.
    assert_diffs.
    apply (not_strict_par _ _ _ _ P) in HParAB; Col.
    apply (not_strict_par _ _ _ _ P) in HParAC; Col.
    spliter.
    apply(col3 A1 A2); auto.
  }
  intro HStrict.
  apply (par_not_col_strict _ _ _ _ P) in HParAB; Col.
  apply (par_not_col_strict _ _ _ _ P) in HParAC; Col.
  elim(Col_dec C1 B1 B2); auto.
  intro HC1NotB.
  exfalso.
  assert(P<>C1) by (intro; subst C1; Col).
  destruct HPerp2 as [P1 [P2 [HP [HPerpAP HPerpBP]]]].
  assert(HQ := HPerpAP); auto.
  destruct HQ as [Q [_ [_ [HQP[HQA _]]]]].
  assert(HP' := HPerpBP); auto.
  destruct HP' as [P' HPerpP].
  assert(P'=P) by (apply (l8_14_2_1b _ P1 P2 B1 B2); Col).
  subst P'.
  destruct HPerpP as [_ [_ [HPP _]]].
  assert(P<>Q) by (intro; subst Q; auto).
  apply (perp_col0 _ _ _ _ P Q) in HPerpAP; Col.
  apply (perp_col0 _ _ _ _ P Q) in HPerpBP; Col.
  clear dependent P1.
  clear dependent P2.

  assert_diffs.
  assert(Hos : one_side B1 B2 Q C1).
  { apply (one_side_transitivity _ _ _ A1).
    - elim(eq_dec_points A1 Q).
      intro; subst A1; apply one_side_reflexivity; auto; apply (par_strict_not_col_2 A2); Par.
      intro.
      apply l12_6.
      apply par_strict_right_comm.
      apply (par_strict_col_par_strict _ _ _ A2); Col; Par.

    - apply not_two_sides_one_side; Col.
      apply (par_strict_not_col_2 A2); Par.
  }
  assert(~ Col Q C1 P) by (apply (par_not_col A1 A2); auto; apply (par_strict_col_par_strict _ _ _ C2); Col).
  assert(~ Col B1 B2 Q) by (apply (one_side_not_col _ _ _ C1); auto).

  assert(HB3 : exists B3, Col B1 B2 B3 /\ one_side P Q C1 B3).
  { elim(Col_dec P Q B1).
    2: intro; apply (not_par_same_side _ _ _ _ P); Col.
    intro.
    assert(HB3 := not_par_same_side P Q B2 B1 P C1).
    destruct HB3 as [B3 []]; Col.
    intro; assert(Col B1 B2 Q); Col; ColR.
    exists B3; split; Col.
  }
  destruct HB3 as [B3 []].
  assert(HB4 := symmetric_point_construction B3 P).
  destruct HB4 as [B4].
  assert(~ Col P Q B3) by (apply (one_side_not_col _ _ _ C1); Side).
  assert(HA3 : exists A3, Col A1 A2 A3 /\ one_side P Q C1 A3).
  { elim(Col_dec P Q A1).
    2: intro; apply (not_par_same_side _ _ _ _ Q); Col.
    intro.
    assert(HA3 := not_par_same_side P Q A2 A1 Q C1).
    destruct HA3 as [A3 []]; Col.
    intro; apply HStrict; ColR.
    exists A3; split; Col.
  }
  destruct HA3 as [A3 []].
  assert(~ Col P Q A3) by (apply (one_side_not_col _ _ _ C1); Side).
  assert_diffs.

  assert(two_sides P C1 Q B3).
  { apply l9_31; auto.
    apply one_side_symmetry.
    apply (col2_os__os B1 B2); Col.
  }
  assert(HInAngle : InAngle C1 Q P B3) by (apply os_ts__inangle; Side).
  assert(lta B3 P C1 B3 P Q).
  { split.
    exists C1; split; try (apply l11_24); Conga.
    intro HConga.
    apply l11_22_aux in HConga.
    destruct HConga as [Habs|Habs].
    assert_cols; Col.
    apply l9_9 in Habs.
    apply Habs.
    apply one_side_symmetry.
    apply (col2_os__os B1 B2); Col.
  }
  assert(acute B3 P C1).
  { exists B3.
    exists P.
    exists Q.
    split; auto.
    apply perp_per_2; auto.
    apply (perp_col2 B1 B2); Col.
  }
  assert(HR:= greenberg P Q A3 B3 P C1).
  destruct HR as [R []]; auto.
    intro; assert_cols; apply HC1NotB; ColR.
    apply perp_per_1; auto; apply (perp_col2_bis _ _ _ _ A1 A2); Perp; ColR.
  assert(P<>R) by (intro; subst R; assert_cols; Col).
  assert(one_side P Q R A3) by (apply invert_one_side; apply out_one_side; Col).
  assert_diffs.
  assert(one_side P C1 R Q).
    apply l12_6; apply (par_strict_col4__par_strict C1 C2 A1 A2); Col; Par; ColR.
  assert(Hsuma1 := ex_suma B4 P R P R Q).
  destruct Hsuma1 as [A [B [C Hsuma1]]]; auto.
  assert(Htri : Trisuma R Q P A B C).
  { exists B4.
    exists P.
    exists R.
    split; auto.
    apply (conga3_suma__suma B4 P Q Q P R B4 P R); try (apply conga_refl; auto).
    - exists R.
      repeat (split; Conga).
      apply l9_9.
      apply l9_2.
      apply (l9_8_2 _ _ B3).
      { repeat split; Col.
        intro; assert(Col P Q B3); Col; ColR.
        exists P.
        split; Col; Between.
      }
      apply (one_side_transitivity _ _ _ A3); Side.
      apply (one_side_transitivity _ _ _ C1); Side.

    - apply l11_16; auto.
      apply perp_per_2; auto; apply (perp_col2 B1 B2); Col; ColR.
      apply perp_per_1; auto; apply (perp_col2 A1 A2); Col; ColR.
  }
  assert(Hsuma2 := ex_suma B4 P R C1 P B3).
  destruct Hsuma2 as [D [E [F Hsuma2]]]; auto.
  assert(~ Col R P B4).
  { apply (par_not_col A1 A2); auto.
    apply (par_strict_col2_par_strict _ _ B1 B2); auto; ColR.
    ColR.
  }
  assert(~ one_side P R B4 B3).
  { apply l9_9.
    repeat split; Col.
    intro; assert(Col R P B4); Col; ColR.
    exists P.
    split; Col; Between.
  }
  assert(Hsuma3 : Suma B4 P R R P B3 B4 P B3) by (exists B3; repeat (split; Conga)).
  assert(Hisi3 : Isi B4 P R R P B3).
  { repeat split; auto.
    right; intro; assert_cols; Col.
    exists B3; repeat (split; Conga).
    intro Habs.
    destruct Habs as [_ [_ [Habs _]]].
    assert_cols; Col.
  }
  assert(lea C1 P B3 R P B3).
  { apply lea_comm.
    exists C1.
    split; Conga.
    apply os_ts__inangle.
    - apply l9_2.
      apply (l9_8_2 _ _ Q); Side.
    - apply (one_side_transitivity _ _ _ Q); apply (col2_os__os B1 B2); Col.
      apply l12_6.
      apply (par_strict_col2_par_strict _ _ A1 A2); Col; Par.
      ColR.
  }

  assert(Habs : lta A B C B4 P B3).
  { apply (lea456789_lta__lta _ _ _ D E F).
    2: apply (isi_lea2_suma2__lea B4 P R C1 P B3 _ _ _ B4 P R R P B3); Lea.
    apply (isi_lea_lta456_suma2__lta B4 P R P R Q _ _ _ B4 P R C1 P B3); Lea.
    apply lta_right_comm; auto.
    apply (isi_lea2__isi _ _ _ _ _ _ B4 P R R P B3); Lea.
  }
  destruct Habs as [_ Habs].
  apply Habs.
  suma.assert_diffs.
  spliter.
  apply conga_line; Between.
  apply (triangle R Q P); auto.
Qed.

Lemma legendre_aux2 : greenberg_s_postulate -> triangle_postulate -> forall A1 A2 B1 B2 C1 C2 P,
   Perp2 A1 A2 B1 B2 P -> Col P B1 B2 -> Par A1 A2 C1 C2 -> Col P C1 C2 ->
   Col C1 B1 B2. (* "half" of playfair_bis *)
Proof.
  intros greenberg triangle.
  intros A1 A2 B1 B2 C1 C2 P HPerp2 HPB HParAC HPC.
  assert (HParAB : Par A1 A2 B1 B2) by (apply (perp2_par _ _ _ _ P); auto).
  elim(Col_dec P A1 A2).
  { intro HConf.
    assert_diffs.
    apply (not_strict_par _ _ _ _ P) in HParAB; Col.
    apply (not_strict_par _ _ _ _ P) in HParAC; Col.
    spliter.
    apply(col3 A1 A2); auto.
  }
  intro HStrict.
  elim(two_sides_dec B1 B2 A1 C1).
  { intro Hts.
    exfalso.
    assert(HC1NotB : ~ Col C1 B1 B2) by (destruct Hts as [_ [_ []]]; auto).
    assert(C1<>P) by (intro; subst C1; Col).
    assert(HC3 := (symmetric_point_construction C1 P)).
    destruct HC3 as [C3].
    assert_diffs.
    assert(HC3NotB : ~ Col C3 B1 B2) by (intro; apply HC1NotB; ColR).
    apply HC3NotB.
    apply (legendre_aux1 greenberg triangle A1 A2 _ _ _ C1 P); Col.
    - apply par_right_comm.
      apply (par_col_par _ _ _ P); Col.
      apply (par_col_par _ _ _ C2); Col.
    - apply l9_9_bis.
      exists C1.
      repeat (split; auto).
      exists P.
      split; Between.
  }
  intro.
  apply (legendre_aux1 greenberg triangle A1 A2 _ _ _ C2 P); auto.
Qed.

Lemma triangle_playfair_bis : greenberg_s_postulate -> triangle_postulate -> playfair_bis.
Proof.
  intros greenberg triangle.
  unfold playfair_bis.
  intros A1 A2 B1 B2 C1 C2 P.
  split.
  apply (legendre_aux2 greenberg triangle A1 A2 _ _ _ C2 P); auto.
  apply (legendre_aux2 greenberg triangle A1 A2 _ _ _ C1 P); Par; Col.
Qed.

End triangle_playfair_bis.
