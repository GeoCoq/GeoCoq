Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section thales_existence_rah.

Context `{MT:Tarski_2D}.


Lemma thales_existence__rah : existential_thales_postulate -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intro thales.
  destruct thales as [A [B [C [M]]]].
  spliter.
  apply (t22_17__rah A B C M); assumption.
Qed.

End thales_existence_rah.
