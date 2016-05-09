Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section rah_existential_saccheri.

Context `{T2D:Tarski_2D}.

Lemma rah__existential_saccheri : postulate_of_right_saccheri_quadrilaterals -> postulate_of_existence_of_a_right_saccheri_quadrialteral.
Proof.
  intro rah.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  exists A; exists B; exists C; exists D.
  split.
    assumption.
    apply (rah A B C D HSac).
Qed.

End rah_existential_saccheri.
