Require Export List.

Definition all_equiv (l: list Prop) :=
  forall x y, In x l -> In y l -> (x <-> y).

Definition stronger (l1 l2 : list Prop) :=
  forall x y, In x l1 -> In y l2 -> (x -> y).

Definition all_equiv_under (l1 l2 : list Prop) :=
  forall x y z, In x l1 -> In y l2 -> In z l2 -> (x -> (y <-> z)).