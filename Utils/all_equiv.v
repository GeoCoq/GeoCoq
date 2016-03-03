Require Export List.

Definition all_equiv (l: list Prop) :=
  forall x y, In x l -> In y l -> (x <-> y).

Definition all_equiv' (l: list Prop) : Prop.
Proof.
induction l; [exact True|].
induction l; [exact True|].
exact ((a <-> a0) /\ IHl).
Defined.


Lemma all_equiv_equiv : forall l, all_equiv l <-> all_equiv' l.
Proof.
assert (IH : forall a a0 l,
  all_equiv' (a::a0::l) <-> (a <-> a0) /\ all_equiv' (a0::l))
  by (intros a a0 l; induction l; simpl; tauto).
unfold all_equiv; intro l; induction l; [simpl; tauto|].
induction l; [simpl|clear IHl0; rewrite IH; split]; clear IH.

  {
  split; [auto|intros _ x y Hx Hy].
  elim Hx; [clear Hx; intro Hx; rewrite <- Hx|intuition].
  elim Hy; [clear Hy; intro Hy; rewrite <- Hy|]; intuition.
  }

  {
  intro H; split; [apply H; simpl; tauto|].
  apply IHl; intros x y Hx Hy; apply H; right; assumption.
  }

  {
  intros [H Hl] x y [Ha|Hx] [Ha'|Hy];
  try (rewrite <- Ha; clear Ha);
  try (rewrite <- Ha'; clear Ha'); [tauto| | |];
  try (cut (a0 <-> y); [try tauto|apply IHl; try assumption; left; reflexivity]);
  try (cut (a0 <-> x); [tauto|apply IHl; try assumption; left; reflexivity]).
  }
Qed.

Definition stronger (l1 l2 : list Prop) :=
  forall x y, In x l1 -> In y l2 -> (x -> y).

Definition all_equiv_under (l1 l2 : list Prop) :=
  forall x y z, In x l1 -> In y l2 -> In z l2 -> (x -> (y <-> z)).
