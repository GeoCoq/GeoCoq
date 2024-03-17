Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Main.Tarski_dev.Ch13_1.

Section inverse_projection_postulate_proclus_bis.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma inverse_projection_postulate__proclus_bis :
  inverse_projection_postulate -> alternative_proclus_postulate.
Proof.
  intros ip A B C D P Q HPerp2 HNC1 HCop1 HInter HNC2 HCop2.
  assert(Par_strict C D A B)
    by (apply (col_cop_perp2__pars_bis P); [..|apply coplanar_perm_16|apply perp2_sym]; assumption).
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
  elim(col_dec P Q C0).
    intro; exists C0; Col.
  intro HNCol1.
  assert(HNCol2 : ~ Col C0 A B) by (apply (par_not_col C D); auto).
  assert(HQ0 := cop_not_par_same_side A B Q P P C0).
  destruct HQ0 as [Q0 []]; Col.
    CopR.
  assert(HNCol3 : ~ Col A B Q0) by (apply (one_side_not_col123 _ _ _ C0); Side).
  assert(P<>Q0) by (intro; subst; auto).
  assert(HNCol4 : ~ Col P C0 Q0) by (intro; apply HNCol1; ColR).
  assert_diffs.
  assert(HC1 : exists C1, Col C D C1 /\ C1 <> C0).
  { elim(eq_dec_points C C0).
      intro; subst C0; exists D; split; Col.
      intro; exists C; split; Col.
  }
  destruct HC1 as [C1 []].
  assert(HA0 : exists A0, Col A B A0 /\ OS P C0 Q0 A0).
  { elim(col_dec P C0 A).
    - intro.
      assert(~ Col P C0 B) by (intro; apply HNCol2; ColR).
      assert (HA0 := cop_not_par_same_side P C0 B A P Q0).
      destruct HA0 as [A0 []]; Col.
        apply coplanar_perm_22, col_cop__cop with A; Col; Cop.
      exists A0.
      split; Col.
    - intro.
      apply (cop_not_par_same_side _ _ _ _ P); Col.
      apply coplanar_perm_16, coplanar_trans_1 with B; [Col|Cop..].
  }
  destruct HA0 as [A0 []].
  assert(HNCol6 : ~ Col P C0 A0) by (apply (one_side_not_col123 _ _ _ Q0); Side).
  assert_diffs.

  assert(HY := ip C0 P Q0 C0 C1).
  destruct HY as [Y []]; [|Out..|apply (l8_16_1 C D); Col|CopR|exists Y; split; ColR].
  exists C0, P, A0; split.
  apply (l8_16_1 A B); Col; Perp.
  split.

    {
    apply inangle__lea.
    apply os2__inangle; Side.
    apply (col2_os__os A B); auto.
    }

    {
    intro.
    assert(Out P Q0 A0) by (apply (conga_os__out C0); Side).
    apply HNCol3; ColR.
    }
Qed.

End inverse_projection_postulate_proclus_bis.
