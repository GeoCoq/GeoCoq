Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section existential_triangle_rah.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma existential_triangle__rah : existential_triangle -> saccheri_s_right_angle_hypothesis.
Proof.
  intro et.
  destruct et as [A [B [C [D [E [F]]]]]].
  spliter.
  apply (t22_14__rah A B C D E F); auto.
Qed.

End existential_triangle_rah.
