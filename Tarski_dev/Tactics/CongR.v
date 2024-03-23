Require Import NArith.
Require Import GeoCoq.Utils.sets.
Require Import GeoCoq.Meta_theory.Models.tarski_to_cong_theory.
Require Import GeoCoq.Tactics.Coinc.CongR.

Ltac List_assoc Tpoint elt lst :=
  match constr:(lst) with
    | nil => fail
    | (cons (@pairT Tpoint positive ?X1 ?X2) ?X3) =>
      match X1 with
        | elt => X2
        | _ => List_assoc Tpoint elt X3
      end
  end.

Ltac assert_ss_ok Tpoint Cong lvar int ss t HSS CT :=
  match goal with
    | |- Cong ?A ?B ?C ?D -> _ =>
      let HCong := fresh in
      intro HCong;
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let pd := List_assoc Tpoint D lvar in
      let ss' := constr:(SSP.add (SP.add (pa, pb) (SP.add (pc, pd) SP.empty))
                                 ss) in
      let t' := apply (@collect_congs Tpoint Cong CT A B C D HCong pa pb pc pd ss int);
                [reflexivity..|t] in
      assert_ss_ok Tpoint Cong lvar int ss' t' HSS CT
    | _                        =>
      assert (HSS : @ss_ok Tpoint Cong ss int) by t; clear -CT HSS
  end.

Ltac Cong_refl_compute Tpoint Cong lvar int HSS :=
  match goal with
  | |- Cong ?A ?B ?C ?D =>
    let pa := List_assoc Tpoint A lvar in
    let pb := List_assoc Tpoint B lvar in
    let pc := List_assoc Tpoint C lvar in
    let pd := List_assoc Tpoint D lvar in
    let c := ((vm_compute; reflexivity) || fail 2 "Can not be deduced") in
    apply (test_cong_ok _ int pa pb pc pd HSS); c
  end.

Ltac Cong_refl_aux Tpoint Cong CT Ps (*Is*) cpt :=
  match goal with
    | |- (forall (P : Tpoint), _) =>
      intro P;
      let Ps' := uconstr:(@cons (prod Tpoint positive)
                                (@pairT Tpoint positive P cpt)
                                Ps) in
      let scpt := eval compute in (Pos.succ cpt) in
          Cong_refl_aux Tpoint Cong CT Ps' (*Is'*) scpt
    | Default : Tpoint |- _       =>
      let HPs := fresh in
      set (HPs := Ps);
      let int := fresh in
      set (int := @interp Tpoint HPs Default);
      let tss := exact (@ss_ok_empty Tpoint Cong int) in
      let HSS := fresh in
      assert_ss_ok Tpoint Cong Ps int SSP.empty tss HSS CT;
      Cong_refl_compute Tpoint Cong Ps int HSS
  end.

Ltac generalize_all Tpoint :=
  match goal with
    | H : Tpoint |- _ => revert H; generalize_all Tpoint
    | _               => idtac
  end.

Ltac revert_all Tpoint Cong CT :=
  match goal with
    | H : Cong _ _ _ _               |- _ =>
      revert H; revert_all Tpoint Cong CT
    | _                                   =>
      clear -CT; generalize_all Tpoint
  end.

Ltac Cong_refl Tpoint Cong :=
  let Pnil := constr:(@nil (@prod Tpoint positive)) in
  let CT := fresh in
  assert (CT : Cong_theory Tpoint Cong) by (typeclasses eauto);
  revert_all Tpoint Cong CT;
  Cong_refl_aux Tpoint Cong CT Pnil (*Inil*) (1%positive).

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
