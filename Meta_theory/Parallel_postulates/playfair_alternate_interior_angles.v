Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section playfair_alternate_interior_angles.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma playfair__alternate_interior :  playfair_s_postulate -> alternate_interior_angles_postulate.
Proof.
intros playfair A B C D Hts HPar.
assert(~ Col B A C) by (destruct Hts as [_ []]; auto).
assert(HD' := ex_conga_ts B A C A C B).
destruct HD' as [D' []]; Col.
apply (conga_trans _ _ _ D' C A).
Conga.
assert_diffs.
apply (out_conga D C A D C A); try (apply out_trivial); Conga.
apply (col_one_side_out _ A).
2: apply invert_one_side; exists B; split; Side.
assert (HP := playfair A B C D C D' C).
destruct HP; Col.
apply l12_21_b; Conga; Side.
Qed.

End playfair_alternate_interior_angles.