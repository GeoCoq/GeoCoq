Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section playfair_par_trans.

Context `{T2D:Tarski_2D}.

(** This is Legendre theorem XXV http://gallica.bnf.fr/ark:/12148/bpt6k202689z/f29.image *)

Lemma playfair_implies_par_trans :
  playfair_s_postulate -> postulate_of_transitivity_of_parallelism.
Proof.
intros HP A1; intros.
apply par_distincts in H.
apply par_distincts in H0.
spliter.
induction (Col_dec A1 A2 C1).

  right.
  assert (Col A1 C1 C2 /\ Col A2 C1 C2) by (apply (HP B1 B2 C1 C2 A1 A2 C1);Par;Col;apply par_symmetry;assumption).
  intuition.

  left.
  repeat split; try assumption; try apply all_coplanar.
  intro HX.
  ex_and HX X.
  assert (Col C1 A1 A2 /\ Col C2 A1 A2) by (apply (HP B1 B2 A1 A2 C1 C2 X);Par;Col;apply par_symmetry;assumption).
  intuition.
Qed.

End playfair_par_trans.
