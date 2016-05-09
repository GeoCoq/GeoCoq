Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section existential_triangle_rah.

Context `{T2D:Tarski_2D}.

Lemma existential_triangle__rah : postulate_of_existence_of_a_triangle_whose_angles_sum_to_2_rights -> postulate_of_right_saccheri_quadrilaterals.
Proof.
  intro et.
  destruct et as [A [B [C [D [E [F]]]]]].
  spliter.
  apply (t22_14__rah A B C D E F); auto.
Qed.

End existential_triangle_rah.
