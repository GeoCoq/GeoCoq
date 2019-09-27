Require Import GeoCoq.Tarski_dev.Ch09_plane.
Require Import NArith.
Require Import GeoCoq.Utils.sets.
Require Import GeoCoq.Meta_theory.Models.tarski_to_coinc_theory_for_concyclic.
Require Import GeoCoq.Tactics.Coinc.CoincR.

Section CoincR_for_concyclic.

Context `{TE:Tarski_euclidean}.

Definition ss_ok_for_concy ss interp :=
  @ss_ok Tarski_is_a_Arity_for_concy
         Tarski_is_a_Coinc_predicates_for_concy ss interp.

Lemma ss_ok_empty_for_concy : forall interp, ss_ok_for_concy empty interp.
Proof. exact ss_ok_empty. Qed.

Lemma collect_coincs_for_concy : forall A B C D pa pb pc pd ss interp,
  Concyclic_gen A B C D ->
  interp pa = A ->
  interp pb = B ->
  interp pc = C ->
  interp pd = D ->
  ss_ok_for_concy ss interp ->
  ss_ok_for_concy (add (@CPToSS 4 (pa, (pb, (pc, pd)))) ss) interp.
Proof.
intros A B C D pa pb pc pd ss interp HConcy HA HB HC HD HSS.
apply (@collect_coincs Tarski_is_a_Arity_for_concy
                       Tarski_is_a_Coinc_predicates_for_concy);
[apply Tarski_is_a_Coinc_theory_for_concy|simpl|auto].
rewrite HA; rewrite HB; rewrite HC; rewrite HD; auto.
Qed.

Definition st_ok_for_concy st interp :=
  @st_ok Tarski_is_a_Arity_for_concy
         Tarski_is_a_Coinc_predicates_for_concy st interp.

Lemma st_ok_empty_for_concy : forall interp, st_ok_for_concy empty interp.
Proof. exact st_ok_empty. Qed.

Lemma collect_wds_for_concy : forall A B C pa pb pc st interp,
  ~ Col A B C ->
  interp pa = A ->
  interp pb = B ->
  interp pc = C ->
  st_ok_for_concy st interp ->
  st_ok_for_concy ((@add ST) (pa, (pb, pc)) st) interp.
Proof.
intros A B C pa pb pc st interp HNCol HA HB HC HST.
apply (@collect_wds Tarski_is_a_Arity_for_concy
                    Tarski_is_a_Coinc_predicates_for_concy);
[apply Tarski_is_a_Coinc_theory_for_concy|simpl|auto].
rewrite HA; rewrite HB; rewrite HC; auto.
Qed.

Definition test_coinc_for_concy ss st (pa pb pc pd : positive) :=
  @test_coinc Tarski_is_a_Arity_for_concy ss st (pa, (pb, (pc, pd))).

Definition interp_CP_for_concy (pa pb pc pd : positive) interp :=
  @interp_CP Tarski_is_a_Arity_for_concy 3 (pa, (pb, (pc, pd))) interp.

Lemma test_coinc_ok_for_concy : forall pa pb pc pd ss st interp,
  ss_ok_for_concy ss interp ->
  st_ok_for_concy st interp ->
  test_coinc_for_concy ss st pa pb pc pd = true ->
  Concyclic_gen (interp pa) (interp pb) (interp pc) (interp pd).
Proof.
intros pa pb pc pd ss st interp HSS HST HTest.
assert (HConcy := @test_coinc_ok Tarski_is_a_Arity_for_concy
                               Tarski_is_a_Coinc_predicates_for_concy
                               Tarski_is_a_Coinc_theory_for_concy
                               ss st interp (pa, (pb, (pc, pd))) HSS HST HTest).
simpl in HConcy; auto.
Qed.

End CoincR_for_concyclic.

Ltac assert_ss_ok Tpoint Concyclic_gen lvar :=
  repeat
  match goal with
    | HConcy : Concyclic_gen ?A ?B ?C ?D, HOK : ss_ok_for_concy ?SS ?Interp |- _ =>
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let pd := List_assoc Tpoint D lvar in
      apply PropToTagged in HConcy;
      apply (collect_coincs_for_concy A B C D pa pb pc pd SS Interp HConcy) in HOK;
      try reflexivity
  end.

Ltac assert_st_ok Tpoint Col lvar :=
  repeat
  match goal with
    | HNCol : ~ Col ?A ?B ?C, HOK : st_ok_for_concy ?ST ?Interp |- _ =>
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      apply PropToTagged in HNCol;
      apply (collect_wds_for_concy A B C pa pb pc ST Interp HNCol) in HOK;
      try reflexivity
  end.

Ltac Concy_refl Tpoint Col Concyclic_gen :=
  match goal with
    | Default : Tpoint |- Concyclic_gen ?A ?B ?C ?D =>
      let lvar := build_numbered_points_list Tpoint in
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let pd := List_assoc Tpoint D lvar in
      let c := ((vm_compute;reflexivity) || fail 2 "Can not be deduced") in
      let HSS := fresh in
      assert (HSS := ss_ok_empty_for_concy (interp lvar Default));
      assert_ss_ok Tpoint Concyclic_gen lvar;
      let HST := fresh in
      assert (HST := st_ok_empty_for_concy (interp lvar Default));
      assert_st_ok Tpoint Concyclic_gen lvar;
      match goal with
        | HOKSS : ss_ok_for_concy ?SS ?Interp, HOKST : st_ok_for_concy ?ST ?Interp |- _ =>
          apply (test_coinc_ok_for_concy pa pb pc pd SS ST
                                       Interp HOKSS HOKST); c
      end
  end.
(*
Section Test.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Goal forall P24 P23 P22 P21 P20 P19 P18 P17 P16 P15 P14 P13 P12 P11 P10 P9 P8 P7 P6 P5 P4 P3 P2 P1 P0,
  Coplanar P1 P0 P2 P12 -> Coplanar P8 P2 P0 P1 -> ~ Col P18 P20 P19 ->
  Coplanar P19 P2 P1 P0 -> Coplanar P1 P15 P2 P0 -> Coplanar P23 P13 P12 P14 ->
  ~ Col P10 P9 P11 -> Coplanar P1 P2 P18 P0 -> Coplanar P11 P2 P1 P0 ->
  ~ Col P2 P1 P0 -> Coplanar P0 P1 P2 P6 -> Coplanar P16 P2 P1 P0 ->
  Coplanar P15 P22 P16 P17 -> Coplanar P2 P1 P0 P17 -> Coplanar P20 P0 P2 P1 ->
  Coplanar P1 P2 P0 P4 -> Coplanar P13 P1 P2 P0 -> ~ Col P7 P8 P6 ->
  Coplanar P2 P9 P1 P0 -> Coplanar P2 P10 P0 P1 -> Coplanar P1 P0 P14 P2 ->
  Coplanar P1 P7 P0 P2 -> ~ Col P4 P5 P3 -> Coplanar P0 P3 P1 P2 ->
  Coplanar P24 P11 P9 P10 -> ~ Col P14 P13 P12 -> ~ Col P15 P17 P16 ->
  Coplanar P18 P21 P20 P19 -> Coplanar P0 P5 P2 P1 ->
  Coplanar P21 P22 P23 P24.
Proof.
intros.
Time Cop_refl Tpoint Col Coplanar.
Qed.

End Test.
*)