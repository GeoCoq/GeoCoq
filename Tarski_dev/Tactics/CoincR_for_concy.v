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

Lemma ss_ok_empty_for_concy : forall interp, ss_ok_for_concy SS.empty interp.
Proof. exact ss_ok_empty. Qed.

Lemma collect_coincs_for_concy : forall A B C D pa pb pc pd ss interp,
  Concyclic_gen A B C D ->
  interp pa = A ->
  interp pb = B ->
  interp pc = C ->
  interp pd = D ->
  ss_ok_for_concy ss interp ->
  ss_ok_for_concy (SS.add (@CPToSS 4 (pa, (pb, (pc, pd)))) ss) interp.
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

Lemma st_ok_empty_for_concy : forall interp, st_ok_for_concy STempty interp.
Proof. exact st_ok_empty. Qed.

Lemma collect_wds_for_concy : forall A B C pa pb pc st interp,
  ~ Col A B C ->
  interp pa = A ->
  interp pb = B ->
  interp pc = C ->
  st_ok_for_concy st interp ->
  st_ok_for_concy (STadd (pa, (pb, pc)) st) interp.
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

Ltac assert_ss_ok Tpoint Concyclic_gen lvar int ss t HSS :=
  match goal with
    | HC : Concyclic_gen ?A ?B ?C ?D |- _ =>
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let pd := List_assoc Tpoint D lvar in
      let ss' := fresh in
      set (ss' := SS.add (@CPToSS 4 (pa, (pb, (pc, pd)))) ss);
      apply PropToTagged in HC;
      let t' := apply (collect_coincs_for_concy A B C D pa pb pc pd ss int HC);
                [reflexivity..|t] in
      assert_ss_ok Tpoint Concyclic_gen lvar int ss' t' HSS
    | _                                   =>
      assert (HSS : ss_ok_for_concy ss int) by t
  end.

Ltac assert_st_ok Tpoint Col lvar int st t HST :=
  match goal with
    | HNCol : ~ Col ?A ?B ?C |- _ =>
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let st' := fresh in
      set (st' := @STadd Tarski_is_a_Arity_for_concy (pa, (pb, pc)) st);
      apply PropToTagged in HNCol;
      let t' := apply (collect_wds_for_concy A B C pa pb pc st int HNCol);
                [reflexivity..|t] in
      assert_st_ok Tpoint Col lvar int st' t' HST
    | _                           =>
      assert (HST : st_ok_for_concy st int) by t
  end.

Ltac Concy_refl_build Tpoint Col Concyclic_gen :=
  match goal with
    | Default : Tpoint |- Concyclic_gen ?A ?B ?C ?D =>
      let lvar := build_numbered_points_list Tpoint in
      let xlvar := fresh in
      set (xlvar := lvar);
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let pd := List_assoc Tpoint D lvar in
      let int := fresh in
      set (int := (@interp Tarski_is_a_Arity_for_concy) xlvar Default);
      let tss := exact (ss_ok_empty_for_concy int) in
      let HSS := fresh in
      assert_ss_ok Tpoint Concyclic_gen lvar int SS.empty tss HSS;
      let emptyST := constr:(@STempty Tarski_is_a_Arity_for_concy) in
      let tst := exact (st_ok_empty_for_concy int) in
      let HST := fresh in
      assert_st_ok Tpoint Col lvar int emptyST tst HST;
      apply (test_coinc_ok_for_concy pa pb pc pd _ _ int HSS HST)
  end.

Ltac Concy_refl_compute :=
  let c := ((vm_compute; reflexivity) || fail 2 "Can not be deduced") in
  c.

Ltac Concy_refl Tpoint Col Concyclic_gen :=
  Concy_refl_build Tpoint Col Concyclic_gen; Concy_refl_compute.

(*
Section Test.

Context `{TE:Tarski_euclidean}.

Goal forall P24 P23 P22 P21 P20 P19 P18 P17 P16 P15 P14 P13 P12 P11 P10 P9 P8 P7 P6 P5 P4 P3 P2 P1 P0,
  Concyclic_gen P1 P0 P2 P12 -> Concyclic_gen P8 P2 P0 P1 -> ~ Col P18 P20 P19 ->
  Concyclic_gen P19 P2 P1 P0 -> Concyclic_gen P1 P15 P2 P0 -> Concyclic_gen P23 P13 P12 P14 ->
  ~ Col P10 P9 P11 -> Concyclic_gen P1 P2 P18 P0 -> Concyclic_gen P11 P2 P1 P0 ->
  ~ Col P2 P1 P0 -> Concyclic_gen P0 P1 P2 P6 -> Concyclic_gen P16 P2 P1 P0 ->
  Concyclic_gen P15 P22 P16 P17 -> Concyclic_gen P2 P1 P0 P17 -> Concyclic_gen P20 P0 P2 P1 ->
  Concyclic_gen P1 P2 P0 P4 -> Concyclic_gen P13 P1 P2 P0 -> ~ Col P7 P8 P6 ->
  Concyclic_gen P2 P9 P1 P0 -> Concyclic_gen P2 P10 P0 P1 -> Concyclic_gen P1 P0 P14 P2 ->
  Concyclic_gen P1 P7 P0 P2 -> ~ Col P4 P5 P3 -> Concyclic_gen P0 P3 P1 P2 ->
  Concyclic_gen P24 P11 P9 P10 -> ~ Col P14 P13 P12 -> ~ Col P15 P17 P16 ->
  Concyclic_gen P18 P21 P20 P19 -> Concyclic_gen P0 P5 P2 P1 ->
  Concyclic_gen P21 P22 P23 P24.
Proof.
intros.
Time Concy_refl Tpoint Col Concyclic_gen.
Qed.

End Test.
*)
