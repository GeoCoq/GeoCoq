Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section thales_converse_postulate_thales_existence.

Context `{T2D:Tarski_2D}.

Lemma thales_converse_postulate__thales_existence : thales_converse_postulate -> existential_thales_postulate.
Proof.
  intro thales.
  destruct lower_dim as [C [A [B0]]].
  assert(HNCol : ~ Col C A B0) by (unfold Col; assumption).
  destruct (l10_15 C A C B0) as [B []]; Col.
  assert(~ Col C A B) by (apply (one_side_not_col _ _ _ B0); Side).
  assert(Per A C B) by Perp.
  destruct (midpoint_existence A B) as [M].
  exists A; exists B; exists C; exists M.
  repeat (split; Col).
  apply (thales _ B); Col.
Qed.

End thales_converse_postulate_thales_existence.
