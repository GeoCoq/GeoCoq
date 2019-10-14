Require Import NArith.
Require Import GeoCoq.Utils.sets.
Require Import GeoCoq.Meta_theory.Models.tarski_to_coinc_theory_for_col.
Require Import GeoCoq.Tactics.Coinc.CoincR.

Section CoincR_for_col.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Definition ss_ok_for_col ss interp :=
  @ss_ok Tarski_is_a_Arity_for_col
         Tarski_is_a_Coinc_predicates_for_col ss interp.

Lemma ss_ok_empty_for_col : forall interp, ss_ok_for_col empty interp.
Proof. exact ss_ok_empty. Qed.

Lemma collect_coincs_for_col : forall A B C pa pb pc ss interp,
  Col A B C ->
  interp pa = A ->
  interp pb = B ->
  interp pc = C ->
  ss_ok_for_col ss interp ->
  ss_ok_for_col (add (@CPToSS 3 (pa, (pb, pc))) ss) interp.
Proof.
intros A B C pa pb pc ss interp HCol HA HB HC HSS.
apply (@collect_coincs Tarski_is_a_Arity_for_col
                       Tarski_is_a_Coinc_predicates_for_col);
[apply Tarski_is_a_Coinc_theory_for_col|simpl|auto].
rewrite HA; rewrite HB; rewrite HC; auto.
Qed.

Definition st_ok_for_col st interp :=
  @st_ok Tarski_is_a_Arity_for_col
         Tarski_is_a_Coinc_predicates_for_col st interp.

Lemma st_ok_empty_for_col : forall interp, st_ok_for_col empty interp.
Proof. exact st_ok_empty. Qed.

Lemma collect_wds_for_col : forall A B pa pb st interp,
  A <> B ->
  interp pa = A ->
  interp pb = B ->
  st_ok_for_col st interp ->
  st_ok_for_col ((@add ST) (pa, pb) st) interp.
Proof.
intros A B pa pb st interp HDiff HA HB HST.
apply (@collect_wds Tarski_is_a_Arity_for_col
                    Tarski_is_a_Coinc_predicates_for_col);
[apply Tarski_is_a_Coinc_theory_for_col|simpl|auto].
rewrite HA; rewrite HB; auto.
Qed.

Definition test_coinc_for_col ss st (pa pb pc : positive) :=
  @test_coinc Tarski_is_a_Arity_for_col ss st (pa, (pb, pc)).

Definition interp_CP_for_col (pa pb pc : positive) interp :=
  @interp_CP Tarski_is_a_Arity_for_col 2 (pa, (pb, pc)) interp.

Lemma test_coinc_ok_for_col : forall pa pb pc ss st interp,
  ss_ok_for_col ss interp ->
  st_ok_for_col st interp ->
  test_coinc_for_col ss st pa pb pc = true ->
  Col (interp pa) (interp pb) (interp pc).
Proof.
intros pa pb pc ss st interp HSS HST HTest.
assert (HCol := @test_coinc_ok Tarski_is_a_Arity_for_col
                               Tarski_is_a_Coinc_predicates_for_col
                               Tarski_is_a_Coinc_theory_for_col
                               ss st interp (pa, (pb, pc)) HSS HST HTest).
simpl in HCol; auto.
Qed.

End CoincR_for_col.

Ltac assert_ss_ok Tpoint Col lvar int ss t HSS :=
  match goal with
    | HCol : Col ?A ?B ?C |- _ =>
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let ss' := fresh in
      set (ss' := add (@CPToSS 3 (pa, (pb, pc))) ss);
      apply PropToTagged in HCol;
      let t' := apply (collect_coincs_for_col A B C pa pb pc ss int HCol);
                [reflexivity..|t] in
      assert_ss_ok Tpoint Col lvar int ss' t' HSS
    | _                        =>
      assert (HSS : ss_ok_for_col ss int) by t
  end.

Ltac assert_st_ok Tpoint lvar int st t HST :=
  match goal with
    | HDiff : ?A <> ?B |- _ =>
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let st' := fresh in
      set (st' := (@add (@ST Tarski_is_a_Arity_for_col)) (pa, pb) st);
      apply PropToTagged in HDiff;
      let t' := apply (collect_wds_for_col A B pa pb st int HDiff);
                [reflexivity..|t] in
      assert_st_ok Tpoint lvar int st' t' HST
    | _                     =>
      assert (HST : st_ok_for_col st int) by t
  end.

Ltac Col_refl_build Tpoint Col :=
  match goal with
    | Default : Tpoint |- Col ?A ?B ?C =>
      let lvar := build_numbered_points_list Tpoint in
      let xlvar := fresh in
      set (xlvar := lvar);
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let int := fresh in
      set (int := (@interp Tarski_is_a_Arity_for_col) xlvar Default);
      let tss := exact (ss_ok_empty_for_col int) in
      let HSS := fresh in
      assert_ss_ok Tpoint Col lvar int (@empty SS) tss HSS;
      let emptyST := constr:(@empty (@ST Tarski_is_a_Arity_for_col)) in
      let tst := exact (st_ok_empty_for_col int) in
      let HST := fresh in
      assert_st_ok Tpoint lvar int emptyST tst HST;
      apply (test_coinc_ok_for_col pa pb pc _ _ int HSS HST)
  end.

Ltac Col_refl_compute :=
  let c := ((vm_compute; reflexivity) || fail 2 "Can not be deduced") in
  c.

Ltac Col_refl Tpoint Col := Col_refl_build Tpoint Col; Col_refl_compute.

(*
Section Test.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Goal forall Q R A B C D E F G H I J K L M N,
  D <> E -> J <> K -> Q <> R -> G <> H ->
  Col Q R A -> Col Q R B -> Col Q R C ->
  Col Q R D -> Col Q R E -> Col Q R F ->
  Col G H I -> Col G I J -> Col A B K ->
  Col I J K -> Col L M N -> Col K L M ->
  Col Q A B.
Proof.
intros.
Time Col_refl Tpoint Col.
Qed.

End Test.
*)