Require Export Meta_theory.Parallel_postulates.Euclid_def.

Section posidonius_postulate_rah.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma posidonius_postulate__rah : posidonius_postulate -> saccheri_s_right_angle_hypothesis.
Proof.
  intro posid.
  destruct posid as [A [D [B [C [HSac posid]]]]].
  apply (per_sac__rah A B C D); auto.
  destruct (midpoint_existence B C) as [M HM].
  destruct (midpoint_existence A D) as [N HN].
  assert(HPerp := mid2_sac__perp_lower A B C D M N HSac HM HN).
  assert(Hdiff := sac_distincts A B C D HSac).
  spliter.
  assert_diffs.
  apply (t22_7__per _ _ _ D M N); Between.
    apply perp_per_1; auto; apply (perp_col1 _ _ _ D); Col; Perp.
    apply cong_left_commutativity; apply posid; Col; Perp.
Qed.

End posidonius_postulate_rah.
