Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section playfair_playfair_bis.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma playfair__playfair_bis : playfair_s_postulate -> playfair_bis.
Proof.
intro playfair.
unfold playfair_bis.
intros A1 A2 B1 B2 C1 C2 P; intros.
apply (playfair A1 A2 _ _ _ _ P); auto.
apply (perp2_par _ _ _ _ P); auto.
Qed.

End playfair_playfair_bis.