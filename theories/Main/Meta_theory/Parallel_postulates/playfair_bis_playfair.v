Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Main.Tarski_dev.Ch12_parallel.

Section playfair_bis_playfair.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Lemma playfair_bis__playfair : alternative_playfair_s_postulate -> playfair_s_postulate.
Proof.
intros playfair_bis.
intros A1 A2 B1 B2 C1 C2 P HParAB HPB HParAC HPC.
elim (col_dec A1 A2 P); [intro HCol; treat_equalities|intro HNC1].

  {
  elim HParAB; [intros [_ HF]; exfalso; apply HF; exists P; Col|].
  intros [_ [_ [HCol1 HCol2]]].
  elim HParAC; [intros [_ HF]; exfalso; apply HF; exists P; Col|].
  intros [_ [_ [HCol3 HCol4]]].
  assert_diffs; split; ColR.
  }

  {
  destruct (perp_exists P A1 A2) as [X HPerp1]; [assert_diffs; auto|].
  generalize dependent A2; revert A1.
  cut (forall A1 A2, Par A1 A2 B1 B2 -> Par A1 A2 C1 C2 -> ~ Col A1 A2 P -> Perp P X A1 A2 ->
                     ~ Col P X A1 -> Col C1 B1 B2 /\ Col C2 B1 B2).
  {
  intros Haux A1 A2 HParAB HParAC HNC1 HPerp1.
  elim (perp_not_col2 _ _ _ _ HPerp1); [apply (Haux A1 A2)|apply (Haux A2 A1)]; Par; Col; Perp.
  }

  intros A1 A2 HParAB HParAC HNC1 HPerp1 HNC2.
  assert (HCop1 : Coplanar P X A1 A2) by Cop.
  assert(HD := ex_perp_cop P X P A1).
  assert_diffs.
  destruct HD as [D [HPerp2 HCop2]]; auto.
  assert_diffs.
  assert(Perp2 A1 A2 P D P).
    {
    exists X.
    exists P.
    split; Col.
    split; Perp.
    }
  assert(Col B1 P D /\ Col B2 P D)
    by (apply (playfair_bis A1 A2 _ _ _ _ P); Col; CopR).
  assert(Col C1 P D /\ Col C2 P D)
    by (apply (playfair_bis A1 A2 _ _ _ _ P); Col; CopR).
  spliter.
  split; apply(col3 P D); Col.
  }
Qed.

End playfair_bis_playfair.
