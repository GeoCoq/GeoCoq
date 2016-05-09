Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section par_trans_NID.

Context `{T2D:Tarski_2D}.

Lemma par_trans__par_dec :
  postulate_of_transitivity_of_parallelism ->
  decidability_of_parallelism.
Proof.
intros HTP A B C D.
elim (eq_dec_points A B); intro HAB;
[treat_equalities; right; intro; assert_diffs; intuition|].
elim (eq_dec_points C D); intro HCD;
[treat_equalities; right; intro; assert_diffs; intuition|].
destruct (parallel_existence_spec A B C HAB) as [D' [HCD' HPar]].
elim (Col_dec C D D'); intro HCol;
[left; apply par_col_par with D'; Par; Col|
 right; intro; apply HCol; apply par_id_3; apply HTP with A B; Par].
Qed.

Lemma par_trans__NID :
  postulate_of_transitivity_of_parallelism ->
  decidability_of_not_intersection.
Proof.
intros HTP A B C D.
elim (par_trans__par_dec HTP A B C D); intro HPar.

  {
  elim HPar; [unfold Par_strict; intro; spliter; left; assumption|].
  intro; spliter; right; intro HNNI; apply HNNI; exists A; Col.
  }

  {
  elim (eq_dec_points A B); intro HAB;
  [treat_equalities; right; intro HNNI; apply HNNI; exists C; Col|].
  elim (eq_dec_points C D); intro HCD;
  [treat_equalities; right; intro HNNI; apply HNNI; exists A; Col|].
  right; intro HNNI; apply HPar; left; repeat (split; finish).
  apply all_coplanar.
  }
Qed.

Definition playfair_ter := forall A1 A2 B1 B2 C1 C2 P,
  A1 <> A2 -> B1 <> B2 -> C1 <> C2 ->
  Col P B1 B2 -> Col P C1 C2 ->
  ~ Col A1 B1 B2 \/ ~ Col A2 B1 B2 ->
  ~ Col A1 C1 C2 \/ ~ Col A2 C1 C2 ->
  ~ Col C1 B1 B2 \/ ~ Col C2 B1 B2 ->
  ~ (~ (exists I, Col I A1 A2 /\ Col I B1 B2) /\
     ~ (exists I, Col I A1 A2 /\ Col I C1 C2)).

Definition playfair_quater_qf A1 A2 B1 B2 C1 C2 P :=
  A1 <> A2 /\ B1 <> B2 /\ C1 <> C2 /\
  Col P B1 B2 /\ Col P C1 C2 /\
  ~ (Col A1 B1 B2 /\ Col A2 B1 B2) /\
  ~ (Col A1 C1 C2 /\ Col A2 C1 C2) /\
  ~ (Col C1 B1 B2 /\ Col C2 B1 B2) /\
  ~ (exists I, Col I A1 A2 /\ Col I B1 B2) /\
  ~ (exists I, Col I A1 A2 /\ Col I C1 C2).

Definition playfair_quater := ~ exists A1 A2 B1 B2 C1 C2 P,
  playfair_quater_qf A1 A2 B1 B2 C1 C2 P.

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

Lemma playfair__playfair_quater :
  playfair_s_postulate -> playfair_quater.
Proof.
intro HP; intro HPQ; destruct HPQ as [A1 [A2 [B1 [B2 [C1 [C2 [P HPQ]]]]]]].
assert (H:= HP A1 A2 B1 B2 C1 C2 P); clear HP.
destruct HPQ as [HD1 [HD2 [HD3 [HC1 [HC2 [HNC1 [HNC2 [HNC3 [HNI1 HNI2]]]]]]]]].
apply HNC3; apply H; clear H; Col; left;
repeat (split; try assumption; try apply all_coplanar); auto.
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

Lemma not_ex_forall_not_7 :
  forall (T : Type) (P : T -> T -> T -> T -> T -> T -> T -> Prop),
  ~(exists x1 : T, exists x2 : T, exists x3 : T,
    exists x4 : T, exists x5 : T, exists x6 : T,
    exists x7 :T, P x1 x2 x3 x4 x5 x6 x7) <->
  forall x1 : T, forall x2 : T, forall x3 : T,
  forall x4 : T, forall x5 : T, forall x6 : T,
  forall x7 : T, ~ P x1 x2 x3 x4 x5 x6 x7.
Proof.
intros; split; intro H1; intros; intro H2;
[apply H1; exists x1, x2, x3, x4, x5, x6, x7; auto|].
destruct H2 as [x1 [x2 [x3 [x4 [x5 [x6 [x7 H2]]]]]]].
apply (H1 x1 x2 x3 x4 x5 x6 x7); auto.
Qed.

Lemma playfair_quater__playfair :
  playfair_quater -> playfair_s_postulate.
Proof.
intros HP A1 A2 B1 B2 C1 C2 P HPar1 HP1 HPar2 HP2.
assert (H : playfair_quater <->
              forall A1 A2 B1 B2 C1 C2 P,
                ~ playfair_quater_qf A1 A2 B1 B2 C1 C2 P)
  by (apply not_ex_forall_not_7). rewrite H in HP; clear H.
assert (H : Col C1 B1 B2 /\ Col C2 B1 B2 <-> ~ ~ (Col C1 B1 B2 /\ Col C2 B1 B2))
  by (induction (Col_dec C1 B1 B2); induction (Col_dec C2 B1 B2); tauto).
apply H; clear H; intro HNC; apply (HP A1 A2 B1 B2 C1 C2 P).
repeat try (split; [assert_diffs; assumption|]).
assert (HNC1 : ~ Col A1 B1 B2).
  {
  intro.
  assert (HA : A1 <> A2) by (assert_diffs; auto).
  assert (HB : B1 <> B2) by (assert_diffs; auto).
  assert (HC : C1 <> C2) by (assert_diffs; auto).
  apply (not_strict_par _ _ _ _ A1) in HPar1; Col; spliter.
  apply (not_strict_par _ _ _ _ P) in HPar2; spliter; try ColR.
  apply HNC; split; ColR.
  }
assert (HNC2 : ~ Col A2 B1 B2).
  {
  intro.
  assert (HA : A1 <> A2) by (assert_diffs; auto).
  assert (HB : B1 <> B2) by (assert_diffs; auto).
  assert (HC : C1 <> C2) by (assert_diffs; auto).
  apply (not_strict_par _ _ _ _ A2) in HPar1; Col; spliter.
  apply (not_strict_par _ _ _ _ P) in HPar2; spliter; try ColR.
  apply HNC; split; ColR.
  }
assert (HNC3 : ~ Col A1 C1 C2).
  {
  intro.
  assert (HA : A1 <> A2) by (assert_diffs; auto).
  assert (HB : B1 <> B2) by (assert_diffs; auto).
  assert (HC : C1 <> C2) by (assert_diffs; auto).
  apply (not_strict_par _ _ _ _ A1) in HPar2; Col; spliter.
  apply (not_strict_par _ _ _ _ P) in HPar1; spliter; try ColR.
  apply HNC; split; ColR.
  }
assert (HNC4 : ~ Col A2 C1 C2).
  {
  intro.
  assert (HA : A1 <> A2) by (assert_diffs; auto).
  assert (HB : B1 <> B2) by (assert_diffs; auto).
  assert (HC : C1 <> C2) by (assert_diffs; auto).
  apply (not_strict_par _ _ _ _ A2) in HPar2; Col; spliter.
  apply (not_strict_par _ _ _ _ P) in HPar1; spliter; try ColR.
  apply HNC; split; ColR.
  }
apply par_symmetry in HPar1; apply (par_not_col_strict _ _ _ _ A1) in HPar1;
Col; apply par_strict_symmetry in HPar1; destruct HPar1 as [_ [_ [_ HPar1]]].
apply par_symmetry in HPar2; apply (par_not_col_strict _ _ _ _ A1) in HPar2;
Col; apply par_strict_symmetry in HPar2; destruct HPar2 as [_ [_ [_ HPar2]]].
tauto.
Qed.

End par_trans_NID.