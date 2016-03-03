Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section par_trans_proclus.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma inter_dec_implies_not_par_inter_exists :
  decidability_of_intersection ->
  (forall A1 B1 A2 B2, ~ Par A1 B1 A2 B2 ->
  exists X, Col X A1 B1 /\ Col X A2 B2).
Proof.
intro HID; intros.
induction (eq_dec_points A1 B1).
subst; exists A2; Col.
induction (eq_dec_points A2 B2).
subst; exists A1; Col.
induction (HID A1 B1 A2 B2).

  assumption.

  exfalso.
  apply H.
  unfold Par.
  left.
  unfold Par_strict.
  repeat split; try apply all_coplanar; assumption.
Qed.

Lemma par_trans_implies_par_not_par :
  postulate_of_transitivity_of_parallelism ->
  forall A B C D P Q, Par A B C D -> ~Par A B P Q -> ~Par C D P Q.
Proof.
intro HP; intros A B C D P Q HPar HNPar.
intro HNPar'.
apply HNPar.
apply HP with C D; Par.
Qed.

Lemma inter_dec_plus_par_trans_imply_proclus :
  decidability_of_intersection ->
  postulate_of_transitivity_of_parallelism ->
  proclus_postulate.
Proof.
intros HID HPTP A; intros.
assert (~ Par A B P Q)
  by (apply col_not_col_not_par; [exists P; Col | exists Q; Col]).
assert(~ Par C D P Q) by (apply par_trans_implies_par_not_par with A B; Par).
destruct (inter_dec_implies_not_par_inter_exists HID C D P Q H3) as [Y HY].
exists Y; spliter; Col.
Qed.

End par_trans_proclus.
