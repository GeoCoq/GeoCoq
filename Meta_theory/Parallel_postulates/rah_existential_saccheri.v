Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section rah_existential_saccheri.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma rah__existential_saccheri : saccheri_s_right_angle_hypothesis -> existential_saccheri.
Proof.
  intro rah.
  destruct ex_saccheri as [A [B [C [D HSac]]]].
  exists A; exists B; exists C; exists D.
  split.
    assumption.
    apply (rah A B C D HSac).
Qed.

End rah_existential_saccheri.
