Require Import GeoCoq.Tarski_dev.Ch03_bet.
Require Import NArith.
Require Import GeoCoq.Utils.sets.
Require Import GeoCoq.Meta_theory.Models.tarski_to_cong_theory.
Require Import GeoCoq.Tactics.Coinc.CongR.

Ltac assert_ss_ok Tpoint Cong lvar int ss t HSS :=
  match goal with
    | HCong : Cong ?A ?B ?C ?D |- _ =>
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let pd := List_assoc Tpoint D lvar in
      let ss' := fresh in
      set (ss' := (@add SSP (@add SP (pa, pb) (@add SP (pc, pd) (@empty SP)))
                        ss));
      apply PropToTagged in HCong;
      let t' := apply (collect_congs A B C D HCong pa pb pc pd ss int);
                [reflexivity..|t] in
      assert_ss_ok Tpoint Cong lvar int ss' t' HSS
    | _                             =>
      assert (HSS : @ss_ok Tpoint Cong ss int) by t
  end.

Ltac Cong_refl_build Tpoint Cong :=
  match goal with
    | Default : Tpoint |- Cong ?A ?B ?C ?D =>
      let lvar := build_numbered_points_list Tpoint in
      let xlvar := fresh in
      set (xlvar := lvar);
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let pd := List_assoc Tpoint D lvar in
      let int := fresh in
      set (int := interp xlvar Default);
      let tss := exact (@ss_ok_empty Tpoint Cong int) in
      let HSS := fresh in
      assert_ss_ok Tpoint Cong lvar int (@empty SSP) tss HSS;
      apply (test_cong_ok _ int pa pb pc pd HSS)
  end.

Ltac Cong_refl_compute :=
  let c := ((vm_compute; reflexivity) || fail 2 "Can not be deduced") in
  c.

Ltac Cong_refl Tpoint Cong := Cong_refl_build Tpoint Cong; Cong_refl_compute.

(*
Section Test.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Goal forall P5 P4 P3 P2 P1 P0,
  Cong P1 P0 P2 P3 -> Cong P4 P5 P0 P1 -> Cong P5 P4 P3 P2.
Proof.
intros.
Time Cong_refl Tpoint Cong.
Qed.

End Test.
*)