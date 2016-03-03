Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section playfair_playfair_ter.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Definition playfair_ter := forall A1 A2 B1 B2 C1 C2 P,
  A1 <> A2 -> B1 <> B2 -> C1 <> C2 ->
  Col P B1 B2 -> Col P C1 C2 ->
  ~ Col A1 B1 B2 \/ ~ Col A2 B1 B2 ->
  ~ Col A1 C1 C2 \/ ~ Col A2 C1 C2 ->
  ~ Col C1 B1 B2 \/ ~ Col C2 B1 B2 ->
  ~ (~ (exists I, Col I A1 A2 /\ Col I B1 B2) /\
     ~ (exists I, Col I A1 A2 /\ Col I C1 C2)).

Lemma playfair__playfair_ter :
  playfair_s_postulate -> playfair_ter.
Proof.
intros HP A1 A2 B1 B2 C1 C2 P HA HB HC HP1 HP2 HNC1 HNC2 HNC3.
intros [HAB HAC].
assert (H : ~ (Col C1 B1 B2 /\ Col C2 B1 B2));
[intros [HF1 HF2]; intuition HNC3|apply H; clear H].
apply (HP A1 A2 B1 B2 C1 C2 P); Col; left;
repeat (split; Col); apply all_coplanar.
Qed.

Lemma playfair_ter__playfair :
  playfair_ter -> playfair_s_postulate.
Proof.
intros HP A1 A2 B1 B2 C1 C2 P HPar1 HP1 HPar2 HP2.
elim (Col_dec A1 B1 B2); intro HNC1.

  {
  assert (HA : A1 <> A2) by (assert_diffs; auto).
  assert (HB : B1 <> B2) by (assert_diffs; auto).
  assert (HC : C1 <> C2) by (assert_diffs; auto).
  apply (not_strict_par _ _ _ _ A1) in HPar1; Col.
  destruct HPar1 as [HC1 HC2]; clear HNC1.
  apply (not_strict_par _ _ _ _ P) in HPar2; spliter; try split; ColR.
  }

  {
  elim (Col_dec A1 C1 C2); intro HNC2.

    {
    assert (HA : A1 <> A2) by (assert_diffs; auto).
    assert (HB : B1 <> B2) by (assert_diffs; auto).
    assert (HC : C1 <> C2) by (assert_diffs; auto).
    apply (not_strict_par _ _ _ _ A1) in HPar2; Col.
    destruct HPar2 as [HC1 HC2]; clear HNC2.
    apply (not_strict_par _ _ _ _ P) in HPar1; spliter; try split; ColR.
    }

    {
    assert (H : ~ (~ Col C1 B1 B2 \/ ~ Col C2 B1 B2) ->
                Col C1 B1 B2 /\ Col C2 B1 B2);
    [induction (Col_dec C1 B1 B2); induction (Col_dec C2 B1 B2); intuition|
     apply H; clear H; intro HNC3; apply (HP A1 A2 B1 B2 C1 C2 P)];
    try solve [assert_diffs; Col].
    apply par_symmetry in HPar1; apply par_symmetry in HPar2.
    apply (par_not_col_strict _ _ _ _ A1) in HPar1; Col.
    apply (par_not_col_strict _ _ _ _ A1) in HPar2; Col.
    destruct HPar1 as [_ [_ [_ HI1]]]; destruct HPar2 as [_ [_ [_ HI2]]].
    split; intros [I [HC1 HC2]]; [apply HI1| apply HI2]; exists I; Col.
    }
  }
Qed.

End playfair_playfair_ter.
