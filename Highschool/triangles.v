Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section Triangles.

Context `{T2D:Tarski_2D}.

Section ABC.

Variable A B C : Tpoint.

Definition isosceles A B C :=
 Cong A B B C.

Lemma isosceles_sym :
  isosceles A B C ->
  isosceles C B A.
Proof.
unfold isosceles.
intros.
Cong.
Qed.

Lemma isosceles_conga :
  A<>C -> A <> B ->
  isosceles A B C ->
  CongA C A B A C B.
Proof.
intros.
apply cong3_conga.
auto.
auto.
unfold Cong_3.
unfold isosceles in H.
Cong.
Qed.

Definition equilateral A B C :=
 Cong A B B C /\ Cong B C C A.

Definition equilateral_strict A B C :=
 equilateral A B C /\ A <> B.

Lemma equilateral_strict_equilateral :
 equilateral_strict A B C ->
 equilateral A B C.
Proof.
unfold equilateral_strict in *. tauto.
Qed.

Lemma equilateral_cong:
  equilateral A B C ->
  Cong A B B C /\ Cong B C C A /\ Cong C A A B.
Proof.
unfold equilateral;intros;intuition Cong.
assert (T:=cong_transitivity A B B C C A H0 H1).
Cong.
Qed.

Lemma equilateral_rot :
 equilateral A B C ->
 equilateral B C A.
Proof.
intro.
apply equilateral_cong in H.
unfold equilateral.
intuition Cong.
Qed.

Lemma equilateral_swap :
 equilateral A B C ->
 equilateral B A C.
Proof.
intro.
apply equilateral_cong in H.
unfold equilateral.
intuition Cong.
Qed.

Lemma equilateral_rot_2 :
 equilateral A B C ->
 equilateral C B A.
Proof.
intro.
apply equilateral_cong in H.
unfold equilateral.
intuition Cong.
Qed.

Lemma equilateral_swap_2 :
 equilateral A B C ->
 equilateral A C B.
Proof.
intro.
apply equilateral_cong in H.
unfold equilateral.
intuition Cong.
Qed.

Lemma equilateral_swap_rot :
 equilateral A B C ->
 equilateral C A B.
Proof.
intro.
apply equilateral_cong in H.
unfold equilateral.
intuition Cong.
Qed.

Hint Resolve equilateral_swap equilateral_swap_2
 equilateral_swap_rot equilateral_rot equilateral_rot_2 : equilateral.

Lemma equilateral_isosceles_1 :
  equilateral A B C ->
  isosceles A B C.
Proof.
unfold equilateral, isosceles.
tauto.
Qed.

Lemma equilateral_isosceles_2 :
  equilateral A B C ->
  isosceles B C A.
Proof.
unfold equilateral, isosceles.
tauto.
Qed.

Lemma equilateral_isosceles_3 :
  equilateral A B C ->
  isosceles C A B.
Proof.
intros.
apply equilateral_cong in H.
unfold isosceles.
tauto.
Qed.

Hint Resolve equilateral_isosceles_1 equilateral_isosceles_2 equilateral_isosceles_3 : equilateral.

Lemma equilateral_strict_neq :
 equilateral_strict A B C ->
 A <> B /\ B <> C /\ A <> C.
Proof.
intros.
unfold equilateral_strict, equilateral in H.
decompose [and] H;clear H.
repeat split;Cong.
eauto using cong_diff.
eapply cong_diff.
assert (T:=cong_transitivity A B B C C A H2 H3).
apply H1.
assert (T:=cong_transitivity A B B C C A H2 H3).
Cong.
Qed.

Hint Resolve equilateral_strict_neq : equilateral.

Lemma equilateral_strict_swap_1 :
 equilateral_strict A B C ->
 equilateral_strict A C B.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
unfold equilateral_strict in *.
intuition (eauto with equilateral).
Qed.

Lemma equilateral_strict_swap_2 :
 equilateral_strict A B C ->
 equilateral_strict B A C.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
unfold equilateral_strict in *.
intuition (eauto with equilateral).
Qed.

Lemma equilateral_strict_swap_3 :
 equilateral_strict A B C ->
 equilateral_strict B C A.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
unfold equilateral_strict in *.
intuition (eauto with equilateral).
Qed.

Lemma equilateral_strict_swap_4 :
 equilateral_strict A B C ->
 equilateral_strict C A B.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
unfold equilateral_strict in *.
intuition (eauto with equilateral).
Qed.

Lemma equilateral_strict_swap_5 :
 equilateral_strict A B C ->
 equilateral_strict C B A.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
unfold equilateral_strict in *.
intuition (eauto with equilateral).
Qed.

Hint Resolve equilateral_strict_swap_1 equilateral_strict_swap_2
equilateral_strict_swap_3 equilateral_strict_swap_4 equilateral_strict_swap_5 : equilateral.

Lemma equilateral_strict_conga_1 :
 equilateral_strict A B C ->
 CongA C A B A C B.
Proof.
intros.
assert (T:= equilateral_strict_neq H).
apply equilateral_strict_equilateral in H.
apply equilateral_isosceles_1 in H.
apply isosceles_conga.
tauto.
tauto.
assumption.
Qed.

End ABC.

Lemma equilateral_strict_conga_2 :
 forall A B C,
 equilateral_strict A B C ->
 CongA B A C A B C.
Proof.
intros.
apply equilateral_strict_swap_1 in H.
apply equilateral_strict_conga_1 in H.
assumption.
Qed.

Lemma equilateral_strict_conga_3 :
 forall A B C,
 equilateral_strict A B C ->
 CongA C B A B C A.
Proof.
intros.
apply equilateral_strict_swap_2 in H.
apply equilateral_strict_conga_1 in H.
assumption.
Qed.

End Triangles.