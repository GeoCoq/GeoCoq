Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section inverse_projection_postulate_proclus_bis.

Context `{T2D:Tarski_2D}.

Lemma inverse_projection_postulate__proclus_bis : inverse_projection_postulate -> alternative_proclus_postulate.
Proof.
  intros ip A B C D P Q HPerp2 HInter HNCol.
  elim(Col_dec C D P).
    intro; exists P; split; Col.
  intro HNCol1.
  assert(Par_strict C D A B).
  { apply (par_not_col_strict _ _ _ _ P); auto.
    apply par_symmetry.
    apply (perp2_par _ _ _ _ P); auto.
  }
  destruct HPerp2 as [P1 [P2 [HP [HPerpAP HPerpCP]]]].
  assert(HC0 := HPerpCP); auto.
  destruct HC0 as [C0 [_ [_ [HC0P [HC0C _]]]]].
  assert(HP' := HPerpAP); auto.
  destruct HP' as [P' HPerpP].
  assert(P'=P) by (apply (l8_14_2_1b _ P1 P2 A B); Col).
  subst P'.
  destruct HPerpP as [_ [_ [HPP _]]].
  assert(P<>C0) by (intro; subst C0; Col).
  apply (perp_col0 _ _ _ _ P C0) in HPerpAP; Col.
  apply (perp_col0 _ _ _ _ P C0) in HPerpCP; Col.
  clear dependent P1.
  clear dependent P2.

  assert(P<>Q) by (intro; subst; auto).
  elim(Col_dec P Q C0).
    intro; exists C0; Col.
  intro HNCol2.
  assert(HNCol3 : ~ Col C0 A B) by (apply (par_not_col C D); auto).
  assert(HQ0 := not_par_same_side A B Q P P C0).
  destruct HQ0 as [Q0 []]; Col.
  assert(HNCol4 : ~ Col A B Q0) by (apply (one_side_not_col _ _ _ C0); Side).
  assert(P<>Q0) by (intro; subst; auto).
  assert(HNCol5 : ~ Col P C0 Q0) by (intro; apply HNCol2; ColR).
  assert_diffs.
  assert(HC1 : exists C1, Col C D C1 /\ C1 <> C0).
  { elim(eq_dec_points C C0).
      intro; subst C0; exists D; split; Col.
      intro; exists C; split; Col.
  }
  destruct HC1 as [C1 []].
  assert(HA0 : exists A0, Col A B A0 /\ OS P C0 Q0 A0).
  { elim(Col_dec P C0 A).
    - intro.
      assert(~ Col P C0 B) by (intro; apply HNCol3; ColR).
      assert (HA0 := not_par_same_side P C0 B A P Q0).
      destruct HA0 as [A0 []]; Col.
      exists A0.
      split; Col.
    - intro.
      apply (not_par_same_side _ _ _ _ P); Col.
  }
  destruct HA0 as [A0 []].
  assert(HNCol6 : ~ Col P C0 A0) by (apply (one_side_not_col _ _ _ Q0); Side).
  assert_diffs.

  assert(HY := ip C0 P Q0 C0 C1).
  destruct HY as [Y []]; auto.

    {
    exists C0, P, A0; split.
    assert(HPer := l8_16_1 A B C0 A0 P); destruct HPer; Col; Perp.
    split.

      {
      exists Q0; split; CongA.
      apply os2__inangle; Side.
      apply (col2_os__os A B); auto.
      }

      {
      intro.
      assert(Habs := l11_22_aux C0 P Q0 A0).
      destruct Habs as [Habs|Habs]; auto.
      apply HNCol4; ColR.
      apply l9_9 in Habs; apply Habs; Side.
      }
    }

    {
    apply out_trivial; auto.
    }

    {
    assert(HPer := l8_16_1 C D P C1 C0); destruct HPer; Col; Perp.
    }

    {
    exists Y; split; assert_diffs; ColR.
    }
Qed.

End inverse_projection_postulate_proclus_bis.
