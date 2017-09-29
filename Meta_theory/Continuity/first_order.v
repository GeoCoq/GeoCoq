Require Export GeoCoq.Axioms.continuity_axioms.

Section first_order.

Context `{Tn:Tarski_neutral_dimensionless}.

Lemma dedekind__fod : dedekind_s_axiom -> first_order_dedekind.
Proof.
  intros dedekind Xi Upsilon HXi HUpsilon HA.
  apply dedekind, HA.
Qed.

(** This is the FOF predicate with type Type *)

Inductive FOF0 : Prop -> Type :=
  eq_fof : forall A B:Tpoint, FOF0 (A = B)
| bet_fof : forall A B C, FOF0 (Bet A B C)
| cong_fof : forall A B C D, FOF0 (Cong A B C D)
| not_fof : forall P, FOF0 P -> FOF0 (~ P)
| and_fof : forall P Q, FOF0 P -> FOF0 Q -> FOF0 (P /\ Q)
| or_fof : forall P Q, FOF0 P -> FOF0 Q -> FOF0 (P \/ Q)
| implies_fof : forall P Q, FOF0 P -> FOF0 Q -> FOF0 (P -> Q)
| forall_fof : forall P, (forall (A:Tpoint), FOF0 (P A)) -> FOF0 (forall A, P A)
| exists_fof : forall P, (forall (A:Tpoint), FOF0 (P A)) -> FOF0 (exists A, P A).

(** This is a type whose members describe first-order formulas *)

Inductive FOF1 :=
  eq_fof1 : Tpoint -> Tpoint -> FOF1
| bet_fof1 : Tpoint -> Tpoint -> Tpoint -> FOF1
| cong_fof1 : Tpoint -> Tpoint -> Tpoint -> Tpoint -> FOF1
| not_fof1 : FOF1 -> FOF1
| and_fof1 : FOF1 -> FOF1 -> FOF1
| or_fof1 : FOF1 -> FOF1 -> FOF1
| implies_fof1 : FOF1 -> FOF1 -> FOF1
| forall_fof1 : (Tpoint -> FOF1) -> FOF1
| exists_fof1 : (Tpoint -> FOF1) -> FOF1.

(** This function injects FOF1 into Prop *)

Fixpoint fof1_prop (F:FOF1) := match F with
  eq_fof1 A B => A = B
| bet_fof1 A B C => Bet A B C
| cong_fof1 A B C D => Cong A B C D
| not_fof1 F1 => ~ fof1_prop F1
| and_fof1 F1 F2 => fof1_prop F1 /\ fof1_prop F2
| or_fof1 F1 F2 => fof1_prop F1 \/ fof1_prop F2
| implies_fof1 F1 F2 => fof1_prop F1 -> fof1_prop F2
| forall_fof1 P => forall A, fof1_prop (P A)
| exists_fof1 P => exists A, fof1_prop (P A) end.

(** Every first-order formula is equivalent to a Prop built with fof1_prop *)

Lemma fof0__fof1 : forall F, FOF0 F -> { F1 | F <-> fof1_prop F1 }.
Proof.
  intros F HFOF.
  induction HFOF.
  - exists (eq_fof1 A B); intuition.
  - exists (bet_fof1 A B C); intuition.
  - exists (cong_fof1 A B C D); intuition.
  - destruct IHHFOF as [F1]; exists (not_fof1 F1); simpl; intuition.
  - destruct IHHFOF1 as [F1]; destruct IHHFOF2 as [F2]; exists (and_fof1 F1 F2); simpl; intuition.
  - destruct IHHFOF1 as [F1]; destruct IHHFOF2 as [F2]; exists (or_fof1 F1 F2); simpl; intuition.
  - destruct IHHFOF1 as [F1]; destruct IHHFOF2 as [F2]; exists (implies_fof1 F1 F2); simpl; intuition.
  - exists (forall_fof1 (fun A => proj1_sig (X A))).
    simpl; split.
    + intros HP A.
      destruct (X A); simpl.
      apply i, (HP A).
    + intros HF A.
      specialize f with A; specialize HF with A.
      revert HF.
      destruct (X A).
      simpl.
      intuition.
  - exists (exists_fof1 (fun A => proj1_sig (X A))).
    simpl; split.
    + intro HP.
      destruct HP as [A HP].
      exists A.
      destruct (X A); simpl.
      apply i, HP.
    + intro HF.
      destruct HF as [A HF].
      exists A.
      specialize f with A.
      revert HF.
      destruct (X A).
      simpl.
      intuition.
Qed.

(** Every Prop built with fof1_prop is a first-order formula *)

Lemma fof1__fof0 : forall F1, FOF0 (fof1_prop F1).
Proof.
  induction F1; constructor; assumption.
Qed.

End first_order.