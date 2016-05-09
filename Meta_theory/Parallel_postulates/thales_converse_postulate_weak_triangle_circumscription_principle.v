Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section thales_converse_postulate_weak_triangle_circumscription_principle.

Context `{T2D:Tarski_2D}.

Lemma thales_converse_postulate__weak_triangle_circumscription_principle :
  thales_converse_postulate -> weak_triangle_circumscription_principle.
Proof.
intros HP A B C A1 A2 B1 B2 HNC HPer HPerpB1 HPerpB2.
destruct (midpoint_existence A B) as [M HM]; exists M;
assert (H := HP A B C M HNC HM HPer); split;
[apply cong_perp_bisect_col with B C|apply cong_perp_bisect_col with A C]; Cong.
destruct HM as [_ HM]; eCong.
Qed.

End thales_converse_postulate_weak_triangle_circumscription_principle.