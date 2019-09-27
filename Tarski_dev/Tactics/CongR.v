Require Import GeoCoq.Tarski_dev.Ch03_bet.
Require Import NArith.
Require Import GeoCoq.Utils.sets.
Require Import GeoCoq.Meta_theory.Models.tarski_to_cong_theory.
Require Import GeoCoq.Tactics.Coinc.CongR.

Ltac assert_ss_ok Tpoint Cong lvar :=
  repeat
  match goal with
    | HCong : Cong ?A ?B ?C ?D, HOK : ss_ok ?SS ?Interp |- _ =>
        let pa := List_assoc Tpoint A lvar in
        let pb := List_assoc Tpoint B lvar in
        let pc := List_assoc Tpoint C lvar in
        let pd := List_assoc Tpoint D lvar in
         apply PropToTagged in HCong;
         apply (collect_congs A B C D HCong pa pb pc pd SS Interp) in HOK;
         try reflexivity
  end.

Ltac Cong_refl Tpoint Cong :=
  match goal with
    | Default : Tpoint |- Cong ?A ?B ?C ?D =>
        let lvar := build_numbered_points_list Tpoint in
        let pa := List_assoc Tpoint A lvar in
        let pb := List_assoc Tpoint B lvar in
        let pc := List_assoc Tpoint C lvar in
        let pd := List_assoc Tpoint D lvar in
        let c := ((vm_compute;reflexivity) || fail 2 "Can not be deduced") in
        let HSS := fresh in
          assert (HSS := @ss_ok_empty Tpoint Cong (interp lvar Default));
          assert_ss_ok Tpoint Cong lvar;
          match goal with
            | HOKSS : ss_ok ?SS ?Interp |- _ =>
              apply (test_cong_ok SS Interp pa pb pc pd HOKSS); c
          end
  end.
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