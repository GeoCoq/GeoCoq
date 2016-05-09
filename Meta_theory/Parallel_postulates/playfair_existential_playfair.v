Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section playfair_existential_playfair.

Context `{T2D:Tarski_2D}.

Lemma playfair__existential_playfair :
  playfair_s_postulate ->
  existential_playfair_s_postulate.
Proof.
intros HF; destruct lower_dim as [A1 [A2 [P HNC]]]; exists A1, A2, P.
split; Col; intros B1 B2 C1 C2 HPar1 HC1 HPar2 HC2; apply HF with A1 A2 P; auto.
Qed.

End playfair_existential_playfair.