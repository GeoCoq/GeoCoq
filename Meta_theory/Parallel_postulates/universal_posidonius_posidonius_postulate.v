Require Export Meta_theory.Parallel_postulates.Euclid_def.

Section universal_posidonius_posidonius_postulate.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma universal_posidonius__posidonius_postulate : universal_posidonius -> posidonius_postulate.
Proof.
  intro posid.
  destruct (ex_saccheri) as [A1 [B1 [B2 [A2 HSac]]]].
  exists A1; exists A2; exists B1; exists B2.
  split; auto.
  intros A3 B3 HA HB HPerp.
  apply (posid _ A2 _ _ B2); assumption.
Qed.

End universal_posidonius_posidonius_postulate.
