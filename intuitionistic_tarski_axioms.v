Require Export tarski_axioms.

Section Play.

Context `{M: intuitionistic_Tarski_neutral_dimensionless}.

Lemma  bet_diff : forall A B C, IBet A B C -> A<>C.
Proof.
intros.
intro.
subst.
apply (Ibetween_identity C B H).
Qed.

Lemma Ibet_diff : forall A B C, IBet A B C -> A<>B.
Proof.
intros.
intro.
subst.
assert (T:=Ibetween_inner_transitivity B B B C H H).
apply (Ibetween_identity B B).
assumption.
Qed.

Lemma Ibet_diff_2 : forall A B C, IBet A B C -> B<>C.
Proof.
intros.
apply Ibetween_symmetry in H.
eapply Ibet_diff in H.
intuition.
Qed.

Lemma nnbet_diff : forall A B C, ~ ~ IBet A B C  -> A<>B.
Proof.
intros.
intro.
subst.
apply H.
intro.
apply Ibet_diff in H0.
intuition.
Qed.


End Play.
