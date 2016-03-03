Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section proclus_midpoints.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma playfair_s_postulate_implies_midpoints_converse_postulate :
  playfair_s_postulate ->
  midpoints_converse_postulate.
Proof.
intros HP A; intros.
destruct (midpoint_existence A C) as [X HAC].
assert (X = Q).
 assert (Par_strict A B X P).
  apply triangle_mid_par with C; assumption.
 assert_diffs.
 assert_cols.
 apply l6_21 with A C P Q.
  intro.
  assert (Col A B C) by ColR.
  contradiction.
  assert (Par A B Q P /\ A <> B /\ Q <> P) by (apply par_distincts; finish).
  spliter; intuition.
  Col.
  Col.
  destruct (HP A B Q P X P P) as [HCol1 HCol2]; Col; apply par_strict_par; Par.
  Col.
treat_equalities; assumption.
Qed.

End proclus_midpoints.
