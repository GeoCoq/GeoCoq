Require Import NArith.
Require Import GeoCoq.Meta_theory.Models.tarski_to_col_theory.
Require Import GeoCoq.Tactics.Coinc.ColR.
Require Import List.

(*
Class Reify_nat (A : Type) (a : A) (l : list A) (n : nat) := {}.

Instance Reify_hd (A : Type) (a : A) (l : list A) : Reify_nat A a (a :: l) 0.
Qed.

Instance Reify_tl (A : Type) (a1 a2 : A) (l : list A) (n : nat)
         `{Reify_nat A a1 l n} : Reify_nat A a1 (a2 :: l) (S n) | 1.
Qed.

Class Reify_pos (A : Type) (a : A) (l : list A) (p : positive) := {}.

Instance Reify (A : Type) (a : A) (l : list A) (n : nat) `{Reify_nat A a l n} :
  Reify_pos A a l (BinPos.Pos.of_succ_nat n).
Qed.

Ltac reify A a lvar :=
let c := constr:(_ : @Reify_pos A a lvar _) in
lazymatch type of c with Reify_pos _ _ _ ?p => p end.
*)

Require Import GeoCoq.Utils.sets.

Ltac List_assoc Tpoint elt lst :=
  match constr:(lst) with
    | nil => fail
    | (cons (@pairT Tpoint positive ?X1 ?X2) ?X3) =>
      match X1 with
        | elt => X2
        | _ => List_assoc Tpoint elt X3
      end
  end.

(*
Ltac subst_in_cols Tpoint Col :=
  repeat
  match goal with
    | HOKSS : ss_ok ?SS ?Interp, HOKSP : sp_ok ?SP ?Interp, HL : eq_tagged ?Lvar, HEQ : ?A = ?B |- _ =>
      let pa := List_assoc Tpoint A Lvar in
      let pb := List_assoc Tpoint B Lvar in
        apply (subst_ss_ok A B HEQ pa pb SS Interp) in HOKSS; try reflexivity;
        apply (subst_sp_ok A B HEQ pa pb SP Interp) in HOKSP; try reflexivity;
        subst B
  end.

Ltac clear_cols_aux Tpoint Col :=
  repeat
  match goal with
    | HOKSS : ss_ok ?SS ?Interp, HOKSP : sp_ok ?SP ?Interp, HL : eq_tagged ?Lvar |- _ =>
      clear HOKSS; clear HOKSP; clear HL
  end.

Ltac tag_hyps_gen Tpoint Col :=
  repeat
  match goal with
    | HDiff : ?A <> ?B |- _ => apply PropToTagged in HDiff
    | HCol : Col ?A ?B ?C |- _ => apply PropToTagged in HCol
  end.

Ltac untag_hyps_gen Tpoint Col := unfold Tagged in *.

Ltac show_all' :=
  repeat
  match goal with
    | Hhidden : Something |- _ => show Hhidden
  end.

Ltac clear_cols_gen Tpoint Col := show_all'; clear_cols_aux Tpoint Col.
*)

(*
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

Definition Tagged P : Prop := P.

Lemma PropToTagged : forall P : Prop, P -> Tagged P.
Proof. trivial. Qed.

Ltac assert_ss_ok Tpoint Col lvar int ss t HSS :=
  match goal with
    | HCol : Col ?A ?B ?C |- _ =>
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let ss' := fresh in
      set (ss' := (@add SS (@add S pa (@add S pb (@add S pc (@empty S)))) ss));
      apply PropToTagged in HCol;
      let t' := apply (collect_cols A B C HCol pa pb pc ss int);
                [reflexivity..|t] in
      assert_ss_ok Tpoint Col lvar int ss' t' HSS
    | _                        =>
      assert (HSS : @ss_ok Tpoint Col ss int) by t
  end.

Ltac assert_sp_ok Tpoint lvar int sp t HSP :=
  match goal with
    | HDiff : ?A <> ?B |- _ =>
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let sp' := fresh in
      set (sp' := (@add SP (pa, pb) sp));
      apply PropToTagged in HDiff;
      let t' := apply (collect_diffs A B HDiff pa pb sp int);
                [reflexivity..|t] in
      assert_sp_ok Tpoint lvar int sp' t' HSP
    | _                        =>
      assert (HSP : @sp_ok Tpoint sp int) by t
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
      set (int := interp xlvar Default);
      let tss := exact (@ss_ok_empty Tpoint Col int) in
      let HSS := fresh in
      assert_ss_ok Tpoint Col lvar int (@empty SS) tss HSS;
      let tsp := exact (@sp_ok_empty Tpoint int) in
      let HSP := fresh in
      assert_sp_ok Tpoint lvar int (@empty SP) tsp HSP;
      apply (test_col_ok _ _ int pa pb pc HSS HSP)
  end.

Ltac Col_refl_compute :=
  let c := ((vm_compute; reflexivity) || fail 2 "Can not be deduced") in
  c.

Ltac Col_refl Tpoint Col := Col_refl_build Tpoint Col; Col_refl_compute.
*)

Ltac generalize_all Tpoint :=
  match goal with
    | H : Tpoint |- _ => revert H; generalize_all Tpoint
    | _               => idtac
  end.

Ltac revert_all Tpoint Col CT :=
  match goal with
    | H : Col _ _ _                  |- _ => revert H; revert_all Tpoint Col CT
    | H : not (@Logic.eq Tpoint _ _) |- _ => revert H; revert_all Tpoint Col CT
    | _                                   => clear -CT; generalize_all Tpoint
  end.

Ltac assert_sp_ok Tpoint lvar int sp t HSP CT :=
  match goal with
    | |- not (@Logic.eq Tpoint ?A ?B) -> _ =>
      let HDiff := fresh in
      intro HDiff;
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let sp' := constr:(@add SP (pa, pb) sp) in
      let t' := apply (collect_diffs A B HDiff pa pb sp int);
                [reflexivity..|t] in
      assert_sp_ok Tpoint lvar int sp' t' HSP CT
    | _                                    =>
      assert (HSP : @sp_ok Tpoint sp int) by t; clear -CT HSP
  end.

Ltac assert_ss_ok Tpoint Col lvar int ss t HSS HSP CT :=
  match goal with
    | |- Col ?A ?B ?C -> _ =>
      let HCol := fresh in
      intro HCol;
      let pa := List_assoc Tpoint A lvar in
      let pb := List_assoc Tpoint B lvar in
      let pc := List_assoc Tpoint C lvar in
      let ss' := constr:(@add SS (@add S pa (@add S pb (@add S pc (@empty S)))) ss) in
      let t' := apply (@collect_cols Tpoint Col CT A B C HCol pa pb pc ss int);
                [reflexivity..|t] in
      assert_ss_ok Tpoint Col lvar int ss' t' HSS HSP CT
    | _                    =>
      assert (HSS : @ss_ok Tpoint Col ss int) by t; clear -CT HSP HSS
  end.

Ltac Col_refl_compute Tpoint Col lvar int HSS HSP :=
  match goal with
  | |- Col ?A ?B ?C =>
    let pa := List_assoc Tpoint A lvar in
    let pb := List_assoc Tpoint B lvar in
    let pc := List_assoc Tpoint C lvar in
    let c := ((vm_compute; reflexivity) || fail 2 "Can not be deduced") in
    apply (test_col_ok _ _ int pa pb pc HSS HSP); c
  end.

Ltac Col_refl_aux Tpoint Col CT Ps (*Is*) cpt :=
  match goal with
    | |- (forall (P : Tpoint), _) =>
      intro P;
(*
      let Ps' := uconstr:(@cons Tpoint P Ps) in
*)
      let Ps' := uconstr:(@cons (prod Tpoint positive)
                                (@pairT Tpoint positive P cpt)
                                Ps) in
      let scpt := eval compute in (Pos.succ cpt) in
          Col_refl_aux Tpoint Col CT Ps' (*Is'*) scpt
    | Default : Tpoint |- _       =>
      let HPs := fresh in
      set (HPs := Ps);
      let int := fresh in
      set (int := @interp Tpoint HPs Default);
      let tsp := exact (@sp_ok_empty Tpoint int) in
      let HSP := fresh in
      assert_sp_ok Tpoint Ps int (@empty SP) tsp HSP CT;
      let tss := exact (@ss_ok_empty Tpoint Col int) in
      let HSS := fresh in
      assert_ss_ok Tpoint Col Ps int (@empty SS) tss HSS HSP CT;
      Col_refl_compute Tpoint Col Ps int HSS HSP
  end.

(*
Notation "A => B" := (A -> B) (at level 99, no associativity, only printing) : tptp_fol_scope.
Notation "A & B" := (and A B) (at level 80, right associativity, only printing) : tptp_fol_scope.
Notation "wd( A , B )" := (A <> B) (only printing) : tptp_fol_scope.
Notation "col( A , B , C )" := (Definitions.Col A B C) (only printing) : tptp_fol_scope.

Set Printing Depth 1000.

Global Open Scope tptp_fol_scope.
*)

Ltac Print_Goal :=
  match goal with
  | |- ?G => idtac "fof(pipo,conjecture," G ")"
  end.

Ltac Col_refl Tpoint Col :=
(*
  let Pnil := constr:(@nil Tpoint) in
*)
  let Pnil := constr:(@nil (@prod Tpoint positive)) in
  let CT := fresh in
  assert (CT : Col_theory Tpoint Col) by (typeclasses eauto);
  revert_all Tpoint Col CT;(* Print_Goal;*) Col_refl_aux Tpoint Col CT Pnil (*Inil*) (1%positive).

(*
Ltac deduce_cols_aux Tpoint Col :=
  match goal with
    | Default : Tpoint |- _ =>
        let lvar := build_numbered_points_list Tpoint in
        let HSS := fresh in
          assert (HSS := @ss_ok_empty Tpoint Col (interp lvar Default)); assert_ss_ok Tpoint Col lvar;
        let HSP := fresh in
          assert (HSP := @sp_ok_empty Tpoint (interp lvar Default)); assert_sp_ok Tpoint Col lvar;
        let HL := fresh in
          assert (HL : lvar = lvar) by reflexivity;
          apply (@eq_eq_tagged Tpoint) in HL
  end.

Ltac deduce_cols Tpoint Col := deduce_cols_aux Tpoint Col.

Ltac deduce_cols_hide_aux Tpoint Col :=
  match goal with
    | Default : Tpoint |- _ =>
        let lvar := build_numbered_points_list Tpoint in
        let HSS := fresh in
          assert (HSS := @ss_ok_empty Tpoint Col (interp lvar Default)); assert_ss_ok Tpoint Col lvar;
        let HSP := fresh in
          assert (HSP := @sp_ok_empty Tpoint (interp lvar Default)); assert_sp_ok Tpoint Col lvar;
        let HL := fresh in
          assert (HL : lvar = lvar) by reflexivity;
          apply (@eq_eq_tagged Tpoint) in HL;
          hide HSS; hide HSP; hide HL
  end.

Ltac deduce_cols_hide_gen Tpoint Col := deduce_cols_hide_aux Tpoint Col.

Ltac update_cols_aux Tpoint Col :=
  match goal with
    | HOKSS : ss_ok ?SS ?Interp, HOKSP : sp_ok ?SP ?Interp, HEQ : eq_tagged ?Lvar |- _ =>
      assert_ss_ok Tpoint Col Lvar; assert_sp_ok Tpoint Col Lvar; subst_in_cols Tpoint Col; hide HOKSS; hide HOKSP; hide HEQ
  end.

Ltac update_cols_gen Tpoint Col := show_all'; update_cols_aux Tpoint Col.

Ltac cols_aux Tpoint Col :=
  match goal with
    | HOKSS : ss_ok ?SS ?Interp, HOKSP : sp_ok ?SP ?Interp, HL : eq_tagged ?Lvar |- Col ?A ?B ?C =>
      let pa := List_assoc Tpoint A Lvar in
      let pb := List_assoc Tpoint B Lvar in
      let pc := List_assoc Tpoint C Lvar in
      let c := ((vm_compute;reflexivity) || fail 1 "Can not be deduced") in
        apply (test_col_ok SS SP Interp pa pb pc ); [assumption|assumption|c];
        hide HOKSS; hide HOKSP; hide HL
  end.

Ltac cols_gen Tpoint Col := show_all'; cols_aux Tpoint Col.

Ltac Col_refl_test Tpoint Col := deduce_cols_hide_gen Tpoint Col; cols_gen Tpoint Col.
*)

(*
Section Test.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Goal forall A B C D,
  A <> B ->
  Col A B C -> Col A B D ->
  Col B C D.
Proof.
intros.
Time Col_refl Tpoint Col.
Qed.

End Test.
*)

(*
Section Test.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Set Ltac Profiling.
Set Printing All.

Goal forall P73 P106 P79 P29 P62 P88 P117 P139 P69 P9 P59 P17 P96 P48 P114 P85 P54 P16 P58 P43 P3 P99 P136 P12 P100 P32 P65 P57 P109 P40 P113 P64 P77 P18 P1 P86 P35 P121 P20 P36 P98 P14 P52 P128 P63 P132 P129 P75 P97 P7 P46 P60 P111 P34 P104 P61 P41 P44 P10 P135 P49 P84 P112 P0 P123 P116 P5 P68 P140 P22 P124 P31 P82 P137 P134 P94 P51 P70 P47 P50 P115 P130 P126 P83 P105 P55 P93 P39 P108 P11 P15 P122 P6 P21 P72 P19 P4 P80 P56 P131 P103 P37 P90 P42 P38 P133 P138 P8 P26 P71 P81 P28 P24 P125 P45 P2 P33 P74 P110 P30 P78 P66 P27 P25 P120 P92 P53 P118 P127 P107 P95 P89 P76 P13 P87 P101 P119 P91 P67 P102 P23, Col P30 P127 P118 -> Col P25 P2 P120 -> P103 <> P131 -> Col P130 P15 P11 -> Col P84 P34 P112 -> Col P111 P128 P60 -> Col P74 P110 P71 -> Col P43 P3 P17 -> Col P25 P120 P33 -> P92 <> P53 -> Col P138 P80 P133 -> Col P70 P55 P93 -> Col P120 P25 P110 -> Col P0 P31 P82 -> Col P132 P34 P104 -> P1 <> P18 -> Col P139 P54 P85 -> P41 <> P61 -> P52 <> P14 -> P66 <> P27 -> Col P0 P61 P123 -> P48 <> P114 -> P88 <> P117 -> P116 <> P5 -> P118 <> P127 -> Col P96 P117 P17 -> P78 <> P30 -> Col P40 P113 P100 -> P15 <> P11 -> Bet P0 P1 P2 -> Col P97 P36 P75 -> Col P23 P91 P102 -> P87 <> P13 -> P80 <> P56 -> Col P49 P135 P111 -> Col P39 P19 P4 -> P125 <> P45 -> Col P96 P29 P17 -> P21 <> P72 -> P113 <> P40 -> Col P119 P118 P101 -> Col P83 P122 P6 -> Col P114 P69 P48 -> Col P135 P140 P68 -> Col P77 P121 P20 -> P43 <> P3 -> Col P72 P21 P108 -> Col P112 P68 P140 -> P74 <> P110 -> Col P100 P58 P12 -> Col P93 P55 P115 -> P46 <> P7 -> Col P45 P133 P125 -> Col P75 P41 P61 -> Col P136 P48 P99 -> Col P107 P66 P95 -> Col P127 P118 P27 -> Col P28 P24 P42 -> Col P109 P35 P86 -> Col P51 P105 P83 -> P68 <> P140 -> Col P43 P57 P109 -> Col P57 P109 P3 -> Col P47 P82 P70 -> Col P52 P18 P14 -> P89 <> P76 -> P91 <> P67 -> Col P2 P33 P81 -> Col P110 P74 P24 -> Col P131 P8 P26 -> Col P5 P116 P44 -> Col P121 P20 P40 -> Col P102 P23 P101 -> P99 <> P136 -> P138 <> P133 -> P119 <> P101 -> Col P88 P114 P48 -> P19 <> P4 -> Col P105 P122 P6 -> P55 <> P93 -> Col P19 P42 P38 -> Col P10 P44 P7 -> Col P47 P70 P22 -> Col P114 P3 P43 -> P57 <> P109 -> P94 <> P51 -> P65 <> P32 -> P129 <> P132 -> Col P19 P4 P15 -> Col P102 P23 P89 -> Col P55 P21 P72 -> Col P29 P62 P79 -> Col P82 P31 P5 -> Col P63 P20 P128 -> P47 <> P70 -> Col P8 P2 P33 -> P31 <> P82 -> Col P132 P129 P121 -> P139 <> P69 -> Col P40 P99 P113 -> Col P7 P14 P46 -> Col P50 P115 P134 -> Col P54 P99 P136 -> Col P13 P23 P102 -> Col P76 P89 P120 -> Col P100 P85 P12 -> Col P13 P92 P87 -> Col P84 P124 P22 -> Col P129 P98 P132 -> Col P139 P69 P73 -> Col P53 P78 P92 -> P71 <> P81 -> Col P122 P103 P131 -> Col P113 P35 P86 -> Col P42 P38 P56 -> Col P109 P57 P136 -> Col P61 P41 P46 -> P12 <> P100 -> P120 <> P25 -> Col P108 P126 P39 -> Col P68 P94 P51 -> P97 <> P75 -> Col P137 P116 P134 -> P6 <> P122 -> P26 <> P8 -> Col P56 P80 P11 -> Col P90 P8 P26 -> Col P86 P63 P128 -> P84 <> P112 -> P0 <> P123 -> Col P66 P125 P27 -> Col P86 P57 P35 -> P98 <> P36 -> Col P124 P94 P51 -> Col P65 P32 P16 -> Col P49 P135 P60 -> Col P124 P123 P22 -> P115 <> P50 -> P54 <> P85 -> Col P128 P35 P63 -> Col P104 P34 P97 -> Col P126 P130 P137 -> Col P39 P50 P108 -> P104 <> P34 -> P102 <> P23 -> Col P64 P98 P36 -> Col P102 P76 P23 -> P128 <> P63 -> P59 <> P9 -> Col P59 P54 P85 -> Col P129 P60 P111 -> Col P12 P64 P77 -> P130 <> P126 -> Col P106 P88 P117 -> Col P138 P24 P28 -> P2 <> P33 -> Col P47 P83 P105 -> Col P83 P94 P105 -> Col P67 P107 P91 -> Col P87 P102 P23 -> Col P8 P103 P26 -> Col P75 P97 P52 -> Col P31 P115 P50 -> Col P32 P1 P18 -> Col P71 P38 P81 -> Col P96 P62 P17 -> Col P102 P119 P23 -> Col P102 P23 P67 -> Col P90 P21 P37 -> P24 <> P28 -> Col P95 P101 P119 -> Col P111 P60 P63 -> Col P65 P77 P64 -> Col P1 P36 P98 -> P137 <> P134 -> Col P89 P76 P53 -> Col P37 P81 P71 -> Col P10 P0 P123 -> P35 <> P86 -> P17 <> P96 -> Col P49 P140 P68 -> Col P78 P30 P45 -> P107 <> P95 -> P111 <> P60 -> P58 <> P16 -> P22 <> P124 -> Col P6 P131 P103 -> P90 <> P37 -> P62 <> P29 -> Col P84 P112 P41 -> Col P53 P92 P74 -> Col P58 P16 P9 -> Col P135 P49 P104 -> Col P122 P6 P93 -> Col P87 P127 P13 -> P10 <> P44 -> Col P25 P76 P89 -> Col P51 P94 P140 -> Col P96 P43 P3 -> P49 <> P135 -> Col P30 P78 P28 -> P108 <> P39 -> P42 <> P38 -> P20 <> P121 -> Col P33 P2 P26 -> P83 <> P105 -> P77 <> P64 -> Col P4 P90 P37 -> Col P72 P103 P131 -> Col P79 P106 P73.
Proof.
intros.
Time Col_refl Tpoint Col.
Show Ltac Profile.
Time Qed.

End Test.
*)