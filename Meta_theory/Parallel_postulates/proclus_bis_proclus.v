Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section proclus_bis_proclus.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma proclus_bis__proclus : proclus_bis -> proclus_postulate.
Proof.
  intros proclus_bis A B C D P Q HPar HInter HNCol.
  elim(Col_dec C D P).
    intro; exists P; Col.
  intro HNCol1.
  apply par_symmetry in HPar.
  apply (par_not_col_strict _ _ _ _ P) in HPar; auto.
  assert(HC0 := l8_18_existence C D P).
  destruct HC0 as [C0 []]; auto.
  assert(HNCol2 : ~ Col C0 A B) by (apply (par_not_col C D); Col).
  assert_diffs.
  assert(HA0 : exists A0, Col A B A0 /\ ~ Col C0 P A0).
  { elim(Col_dec C0 P A).
    - intro.
      assert(~ Col C0 P B) by (intro; apply HNCol2; ColR).
      exists B.
      split; Col.

    - intro.
      exists A.
      split; Col.
  }
  destruct HA0 as [A0 []].
  assert(HA' := l10_15 C0 P P A0).
  destruct HA' as [A' []]; Col.
  assert_diffs.
  elim(Col_dec A0 P A').
  - intro.
    apply (proclus_bis A0 P); Col.
    2: intro; apply HNCol; ColR.
    exists C0.
    exists P.
    split; Col.
    split.
    2: Perp.
    apply perp_right_comm.
    apply (perp_col1 _ _ _ A'); Perp; Col.

  - intro.
    exfalso.
    assert(HY := proclus_bis A' P C D P A0).
    destruct HY as [Y []]; Col.
      exists C0; exists P; repeat split; Col; Perp.
    assert(Habs : ~ Col Y A B) by (apply (par_not_col C D); Col).
    apply Habs; ColR.
Qed.

End proclus_bis_proclus.
