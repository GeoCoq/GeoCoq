Require Import NArith.
Require Import GeoCoq.Utils.sets.
Require Import GeoCoq.Meta_theory.Models.tarski_to_cong_theory.
Require Import GeoCoq.Tactics.Coinc.CongR.

Ltac add_to_distinct_list x xs :=
  match xs with
    | nil     => constr:(x::xs)
    | x::_    => fail 1
    | ?y::?ys => let zs := add_to_distinct_list x ys in constr:(y::zs)
  end.

Ltac collect_points_list Tpoint xs :=
  match goal with
    | N : Tpoint |- _ => let ys := add_to_distinct_list N xs in
                           collect_points_list Tpoint ys
    | _               => xs
  end.

Ltac collect_points Tpoint := collect_points_list Tpoint (@nil Tpoint).

Ltac number_aux Tpoint lvar cpt :=
  match constr:(lvar) with
    | nil          => constr:(@nil (prodT Tpoint positive))
    | cons ?H ?T => let scpt := eval vm_compute in (Pos.succ cpt) in
                    let lvar2 := number_aux Tpoint T scpt in
                      constr:(cons (@pairT  Tpoint positive H cpt) lvar2)
  end.

Ltac number Tpoint lvar := number_aux Tpoint lvar (1%positive).

Ltac build_numbered_points_list Tpoint := let lvar := collect_points Tpoint in number Tpoint lvar.

Ltac List_assoc Tpoint elt lst :=
  match constr:(lst) with
    | nil => fail
    | (cons (@pairT Tpoint positive ?X1 ?X2) ?X3) =>
      match constr:(elt = X1) with
        | (?X1 = ?X1) => constr:(X2)
        | _ => List_assoc Tpoint elt X3
      end
  end.

Definition Tagged P : Prop := P.

Lemma PropToTagged : forall P : Prop, P -> Tagged P.
Proof. trivial. Qed.

Ltac assert_ss_ok Tpoint Cong lvar :=
  repeat
  match goal with
    | HCong : Cong ?A ?B ?C ?D, HOK : ss_ok ?SS ?Interp |- _ =>
        let pa := List_assoc Tpoint A lvar in
        let pb := List_assoc Tpoint B lvar in
        let pc := List_assoc Tpoint C lvar in
        let pd := List_assoc Tpoint D lvar in
         apply PropToTagged in HCong;
         apply (collect_congs A B C D HCong pa pb pc pd SS Interp) in HOK; try reflexivity
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
          assert (HSS := @ss_ok_empty Tpoint Cong (interp lvar Default)); assert_ss_ok Tpoint Cong lvar;
          match goal with
            | HOKSS : ss_ok ?SS ?Interp |- _ =>
              apply (test_cong_ok SS Interp pa pb pc pd HOKSS); c
          end
  end.