Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section playfair_bis_playfair.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma playfair_bis__playfair : playfair_bis -> playfair_s_postulate.
Proof.
intros playfair_bis.
unfold playfair_s_postulate.
intros A1 A2 B1 B2 C1 C2 P HParAB HPB HParAC HPC.
assert_diffs.
assert(HX := perp_exists P A1 A2).
destruct HX as [X]; auto.
assert_diffs.
assert(HD := perp_exists P P X).
destruct HD as [D]; auto.
assert_diffs.
assert(Perp2 A1 A2 P D P).
  {
  exists X.
  exists P.
  split; Col.
  split; Perp.
  }
assert(Col B1 P D /\ Col B2 P D) by (apply (playfair_bis A1 A2 _ _ _ _ P); Col).
assert(Col C1 P D /\ Col C2 P D) by (apply (playfair_bis A1 A2 _ _ _ _ P); Col).
spliter.
split; apply(col3 P D); Col.
Qed.


End playfair_bis_playfair.