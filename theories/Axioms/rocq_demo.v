(* Progression of Rocq theorems for the Rocq -> Lean translation demo.
   All standalone, using only Coq's stdlib. *)

(* L1: nat identity, induction on a single variable. *)
Lemma add_0_r : forall n : nat, n + 0 = n.
Proof.
  induction n as [|k IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* L2: commutativity of addition, requires nested induction. *)
Lemma add_comm : forall n m : nat, n + m = m + n.
Proof.
  induction n as [|n IH]; intros m.
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite IH. induction m as [|m IH2].
    + reflexivity.
    + simpl. rewrite IH2. reflexivity.
Qed.

(* L3: list length distributes over append; requires list induction. *)
Require Import List.
Import ListNotations.

Lemma length_app : forall (A : Type) (l l' : list A),
  length (l ++ l') = length l + length l'.
Proof.
  intros A l l'.
  induction l as [|x xs IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(* L4: classical De Morgan (the constructive direction). *)
Lemma de_morgan : forall P Q : Prop, ~ (P \/ Q) <-> ~ P /\ ~ Q.
Proof.
  intros P Q. split.
  - intro H. split; intro; apply H; [left | right]; assumption.
  - intros [HnP HnQ] [HP | HQ].
    + apply HnP; assumption.
    + apply HnQ; assumption.
Qed.

(* L5: existential lift; mixes ~, /\, exists. *)
Lemma exists_not_all : forall (P : nat -> Prop),
  (exists n, P n) -> ~ (forall n, ~ P n).
Proof.
  intros P [n Hn] Hall.
  apply (Hall n). assumption.
Qed.
