Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section triangle_existential_triangle.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma triangle__existential_triangle : triangle_postulate -> existential_triangle.
Proof.
  intro triangle.
  destruct lower_dim as [A [B [C]]].
  assert(~ Col A B C) by (unfold Col; assumption).
  assert_diffs.
  destruct (ex_trisuma A B C) as [D [E [F]]]; auto.
  exists A; exists B; exists C; exists D; exists E; exists F.
  repeat split.
    assumption.
    assumption.
    apply (triangle A B C); assumption.
Qed.

End triangle_existential_triangle.
