Require Import quadrilaterals_inter_dec.

Section UnitTests.

Context `{MT:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

Goal forall A B I, A <> B -> is_midpoint I A B -> I <> A /\ I <> B.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B I, B <> A -> is_midpoint I A B -> I <> A /\ I <> B.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B I, I<>A -> is_midpoint I A B -> I <> B /\ A <> B.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B I, I<>B -> is_midpoint I A B -> I <> A /\ A <> B.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B I, A<>I -> is_midpoint I A B -> I <> B /\ A <> B.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B I, B<>I -> is_midpoint I A B -> I <> A /\ A <> B.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B I, A<>B -> is_midpoint I A B -> A <> I /\ I <> B.
Proof.
intros.
assert_diffs.
split;auto.
Qed.

Goal forall A B:Tpoint, A<>B -> B<>A -> True.
Proof.
intros.
not_exist_hyp_comm A B ||
clear H.
not_exist_hyp_comm A B ||
clear H0.
not_exist_hyp_comm A B.
auto.
Qed.

Goal forall A B C Q, 
 B <> A -> Col A B C -> is_midpoint Q A C -> 
 A <> C -> B <> C -> is_midpoint A B C -> 
 Q <> C.
Proof.
intros.
assert_diffs.
assumption.
Qed.

Goal forall A B C D, Perp A B C D -> A<>B /\ C<>D.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B C D, A<>B -> Perp A B C D -> A<>B /\ C<>D.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B C D, A<>B -> Perp B A C D -> A<>B /\ C<>D.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B C D, A<>B -> Perp B A D C -> A<>B /\ C<>D.
Proof.
intros.
assert_diffs.
split;intuition.
Qed.

Goal forall A B C D, A<>B -> C<>D -> Perp B A D C -> A<>B /\ C<>D.
Proof.
intros.
assert_diffs.
split;intuition.
Qed.

Goal forall A B C D, D<>C -> Perp B A D C -> A<>B /\ C<>D.
Proof.
intros.
assert_diffs.
split;intuition.
Qed.

Goal forall X A B C D, Perp_in X A B C D -> A<>B /\ C<>D.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B C D, Par A B C D -> A<>B /\ C<>D.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B C D, Par_strict A B C D -> A<>B /\ C<>D.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B C, out A B C -> B<>A /\ C<>A.
Proof.
intros.
assert_diffs.
split;assumption.
Qed.

Goal forall A B C, out A B C -> Col B A C.
Proof.
intros.
assert_cols.
Col.
Qed.

Goal forall A B C D, ~ Col A B C -> ~ Col A B D ->
  A<> D.
Proof.
intros.
assert_diffs.
intuition.
Qed.

Goal forall A B C D I, 
  is_midpoint I A B -> Par A B C D -> I<>A.
Proof.
intros.
assert_diffs.
assumption.
Qed.

Goal forall A B C D I, 
  is_midpoint I A B -> Par A I C D -> B<>A.
Proof.
intros.
assert_diffs.
intuition.
Qed.

Goal forall A B C D,
 Cong A B C D -> C<>D -> A<>B.
Proof.
intros.
assert_diffs.
intuition.
Qed.

Goal forall A B C D,
 Cong A B C D -> D<>C -> A<>B.
Proof.
intros.
assert_diffs.
intuition.
Qed.

Goal forall A B C D,
 Cong A B C D -> A<>B -> C<>D.
Proof.
intros.
assert_diffs.
intuition.
Qed.

Goal forall A B C D,
 Cong A B C D -> B<>A -> C<>D.
Proof.
intros.
assert_diffs.
intuition.
Qed.

Goal forall A B C D E,
 ~ Col A B C ->
 ~ Col B D E -> A<>B ->
  Col A B D -> Col A B E -> Col A B C.
Proof.
intros.
search_contradiction.
Qed.

Goal forall  A B C D E,
 ~ Col A B C ->
 ~ Col B D E -> A<>B ->
  Col A B D -> Col A B E -> C<>D.
Proof.
intros.
assert_diffs.
assert_all_diffs_by_contradiction'.
finish.
Qed.

Goal forall  A B C D,
 Par_strict A B C D ->
 ~ Col A B C.
Proof.
intros.
assert_diffs.
Col.
Qed.

Goal forall A B C, (A<>B -> B<>C -> A<>C -> Col A B C) -> Col A B C.
Proof.
intros.
assert_diffs_by_cases.
intuition.
Qed.

Goal forall A B C D I, I <> A -> I <> B -> I <> C -> I <> D -> Col I A B -> Col I C D -> ~ Col A B C -> ~ Col A B D.
Proof.
intros.
assert_diffs.
assert_all_not_cols_by_contradiction.
finish.
Qed.

Goal forall A B C D I, I <> A -> I <> B -> I <> C -> I <> D -> Col I A B -> Col I C D -> ~ Col A B C ->  A <> D.
Proof.
intros.
assert_diffs.
assert_all_diffs_by_contradiction'.
finish.
Qed.

Goal forall A B C D, Parallelogram A B C D -> Cong A B C D.
Proof.
intros.
assert_congs_perm.
finish.
Qed.

Goal forall A B C, is_midpoint A B C -> Cong A B C A.
Proof.
intros.
assert_congs_perm.
finish.
Qed.

End UnitTests.