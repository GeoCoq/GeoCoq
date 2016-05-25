Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section existential_saccheri_rah.

Context `{T2D:Tarski_2D}.

Lemma existential_saccheri__rah : postulate_of_existence_of_a_right_saccheri_quadrilateral -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intro HABCD.
  destruct HABCD as [A [B [C [D [HSac HPer]]]]].
  apply (per_sac__rah A B C D HSac HPer).
Qed.

End existential_saccheri_rah.
