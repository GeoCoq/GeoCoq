Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section thales_existence_rah.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma thales_existence__rah : thales_existence -> saccheri_s_right_angle_hypothesis.
Proof.
  intro thales.
  destruct thales as [A [B [C [M]]]].
  spliter.
  apply (t22_17__rah A B C M); assumption.
Qed.

End thales_existence_rah.
