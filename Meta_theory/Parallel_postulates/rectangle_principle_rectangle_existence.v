Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section rectangle_principle_rectangle_existence.

Context `{T2D:Tarski_2D}.

Lemma rectangle_principle__rectangle_existence : postulate_of_right_lambert_quadrilaterals -> postulate_of_existence_of_a_right_lambert_quadrilateral.
Proof.
  intros rectangle.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  destruct (midpoint_existence B C) as [M HM].
  destruct (midpoint_existence A D) as [N HN].
  assert(HLam := mid2_sac__lam6521 A B C D M N HSac HM HN).
  exists N; exists M; exists B; exists A.
  split.
    assumption.
    apply (rectangle N); assumption.
Qed.

End rectangle_principle_rectangle_existence.
