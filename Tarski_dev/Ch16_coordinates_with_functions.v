Require Import Description.
Require Import Ring.
Require Import Field.
Require Import Nsatz.
Require Import Rtauto.
Require Import GeoCoq.Tarski_dev.Annexes.midpoint_theorems.
Require Export GeoCoq.Tarski_dev.Ch16_coordinates.

Ltac cnf2 f :=
  match f with
   | ?A \/ (?B /\ ?C) =>
     let c1 := cnf2 (A\/B) in
     let c2 := cnf2 (A\/C) in constr:(c1/\c2)
   | (?B /\ ?C) \/ ?A =>
     let c1 := cnf2 (B\/A) in
     let c2 := cnf2 (C\/A) in constr:(c1/\c2)
   | (?A \/ ?B) \/ ?C =>
     let c1 := cnf2 (B\/C) in cnf2 (A \/ c1)
   | _ => f
  end
with cnf f :=
  match f with
   | ?A \/ ?B =>
     let c1 := cnf A in
       let c2 := cnf B in
         cnf2 (c1 \/ c2)
   | ?A /\ ?B =>
     let c1 := cnf A in
       let c2 := cnf B in
         constr:(c1 /\ c2)
   | _ => f
  end.

Ltac scnf :=
  match goal with
    | |- ?f => let c := cnf f in
      assert c; [repeat split|]
  end.

Section T17.

Context `{MT:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

Variable O E E' : Tpoint.
Variable ncolOEE' : ~ Col O E E'.

Lemma sum_col: forall A B C, sum O E E' A B C -> Col O E C.
Proof. intros; unfold sum, Ar2 in *; spliter; Col. Qed.

Lemma sum_f : forall A B, Col O E A -> Col O E B -> {C | sum O E E' A B C}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split; [apply sum_exists; auto|unfold uniqueness; apply sum_unicity].
Qed.

Lemma prod_col: forall A B C, prod O E E' A B C -> Col O E C.
Proof. intros;  unfold prod, Ar2 in *; spliter; Col. Qed.

Lemma prod_f : forall A B, Col O E A -> Col O E B -> {C | prod O E E' A B C}.
Proof.
intros.
apply constructive_definite_description; rewrite <- unique_existence.
split; [apply prod_exists; auto|unfold uniqueness; apply prod_unicity].
Qed.

Lemma diff_col: forall A B C, diff O E E' A B C -> Col O E C.
Proof.
intros A B C H; destruct H as [MB HMB]; spliter; apply sum_col with A MB; auto.
Qed.

Lemma diff_f : forall A B, Col O E A -> Col O E B -> {C | diff O E E' A B C}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split; [apply diff_exists; auto|unfold uniqueness; apply diff_unicity].
Qed.

Lemma opp_col : forall A B, opp O E E' A B -> Col O E B.
Proof. intros; unfold opp, sum, Ar2 in *; spliter; Col. Qed.

Lemma opp_f : forall A, Col O E A -> {B | opp O E E' A B}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split; [apply opp_exists|unfold uniqueness; apply opp_unicity]; auto.
Qed.

(** One needs to define a predicate for which MA is uniquely defined. *)
Definition inv O E E' A MA :=
  (A <> O /\ prod O E E' MA A E) \/ (A = O /\ MA = O).

Lemma inv_exists_with_notation : forall A,
  Col O E A -> exists B, inv O E E' A B.
Proof.
intros; induction (eq_dec_points A O); [subst; exists O; right; auto|].
destruct (inv_exists O E E' A) as [IA HIA]; try (exists IA; left); auto.
Qed.

Lemma inv_col : forall A B, inv O E E' A B -> Col O E B.
Proof.
intros A B H; elim (eq_dec_points A O); intro HNEq;
[induction H; spliter; [subst; intuition|treat_equalities; Col]|].
elim H; clear H; intro H; [clear HNEq|spliter; subst; intuition].
destruct H as [IA [HNEq HIA]]; unfold Ar2 in *; spliter; Col.
Qed.

Lemma inv_unicity : forall A B1 B2,
  inv O E E' A B1 -> inv O E E' A B2 -> B1 = B2.
Proof.
intros A B1 B2 HB1 HB2; elim (eq_dec_points A O); intro HNEq;
[induction HB1; induction HB2; spliter; treat_equalities; intuition|].
elim HB1; clear HB1; intro HB1; [clear HNEq|spliter; subst; intuition].
elim HB2; clear HB2; intro HB2; [|spliter; subst; intuition].
destruct HB1 as [HNEq HB1]; destruct HB2 as [H HB2]; clear H.
apply prod_unicityA with O E E' A E; assumption.
Qed.

Lemma inv_f : forall A, Col O E A -> {B | inv O E E' A B}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split; [apply inv_exists_with_notation|
        unfold uniqueness; apply inv_unicity]; auto.
Qed.

Definition div O E E' A B C :=
  exists IB : Tpoint, inv O E E' B IB /\ prod O E E' A IB C.

Lemma div_exists : forall A B,
  Col O E A -> Col O E B -> exists C, div O E E' A B C.
Proof.
intros A B HColA HColB; destruct (inv_exists_with_notation B) as [IB HIB]; auto.
destruct (prod_exists O E E' ncolOEE' A IB) as [C HC];
try (exists C; exists IB); Col.
apply inv_col with B; assumption.
Qed.

Lemma div_unicity : forall A B C1 C2,
  div O E E' A B C1 -> div O E E' A B C2 -> C1 = C2.
Proof.
intros A B C1 C2 HC1 HC2.
destruct HC1 as [IB [HIB HB1]]; destruct HC2 as [IB' [HIB' HC2]].
apply (inv_unicity B IB IB' HIB) in HIB'; treat_equalities.
apply prod_unicity with O E E' A IB; assumption.
Qed.

Lemma div_col : forall A B C : Tpoint, div O E E' A B C -> Col O E C.
Proof.
intros A B C H; destruct H as [IB [HIB HC]]; apply prod_col with A IB; auto.
Qed.

Lemma div_f : forall A B, Col O E A -> Col O E B -> {C | div O E E' A B C}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split; [apply div_exists|unfold uniqueness; apply div_unicity]; auto.
Qed.

End T17.

Section T18.

Context `{MT:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

Variable O E E' SS U1 U2 : Tpoint.
Variable ncolOEE' : ~ Col O E E'.
Variable orthonormal_grid : Cs O E SS U1 U2.

Definition F : Type := {P : Tpoint | Col O E P}.

Definition eqF (x y : F) := (proj1_sig x) = (proj1_sig y).

Instance eqF_Reflexive : Reflexive eqF.
Proof. unfold Reflexive, eqF; auto. Qed.

Instance eqF_Symmetric : Symmetric eqF.
Proof. unfold Symmetric, eqF; auto. Qed.

Instance eqF_Transitive : Transitive eqF.
Proof. unfold Transitive, eqF; intros x y z H; rewrite H; auto. Qed.

Global Instance eqF_Equivalence : Equivalence eqF.
Proof.
exact (Build_Equivalence F eqF eqF_Reflexive eqF_Symmetric eqF_Transitive).
Qed.

Lemma eq_dec_F : forall A B, eqF A B \/ ~ eqF A B.
Proof.
intros; unfold eqF; simpl.
destruct A as [A HA]; destruct B as [B HB]; simpl.
exact (eq_dec_points A B).
Qed.

Lemma neg_and_eqF : forall A B C D,
  ~ (eqF A B /\ eqF C D) <-> ~ eqF A B \/ ~ eqF C D.
Proof.
intros A B C D; split; intro H;
induction (eq_dec_F A B); induction (eq_dec_F C D); intuition.
Qed.

Definition leF (x y : F) := leP O E E' (proj1_sig x) (proj1_sig y).

Instance leF_Antisymmetric : Antisymmetric F eqF leF.
Proof. unfold Antisymmetric, leF, eqF; intros x y; apply leP_asym. Qed.

Instance leF_Transitive : Transitive leF.
Proof. unfold Transitive, leF; intros x y z; apply leP_trans. Qed.

Lemma coordinates_of_point_f : forall P,
  {C | Cd O E SS U1 U2 P (fst C) (snd C)}.
Proof.
intros; apply constructive_definite_description; rewrite <- unique_existence.
split.

  {
  destruct (coordinates_of_point O E SS U1 U2 P orthonormal_grid) as [X [Y H]].
  exists (X,Y); auto.
  }

  {
  intros x y Hx Hy; destruct x as [Xx Xy]; destruct y as [Yx Yy]; simpl in *.
  assert (T:=eq_points_coordinates O E SS U1 U2 P Xx Xy P Yx Yy Hx Hy).
  assert (U: Xx = Yx /\ Xy = Yy) by intuition.
  destruct U; subst; auto.
  }
Qed.

Lemma coordinates_of_point_F : forall P,
  {C: F*F | Cd O E SS U1 U2 P (proj1_sig (fst C)) (proj1_sig (snd C))}.
Proof.
intros; destruct (coordinates_of_point_f P) as [C HC].
assert (T:=HC); apply Cd_Col in HC; destruct HC as [HCol1 HCol2].
exists (exist (fun P => Col O E P) (fst C) HCol1,
        exist (fun P => Col O E P) (snd C) HCol2); simpl; assumption.
Qed.

Definition OF : F.
Proof. exists O; Col. Defined.

Definition OneF : F.
Proof. exists E; Col. Defined.

Definition addF (x y : F) : F.
Proof.
destruct (sum_f O E E' ncolOEE'
                (proj1_sig x) (proj1_sig y)
                (proj2_sig x) (proj2_sig y)) as [P HP]; exists P.
apply (sum_col O E E' (proj1_sig x) (proj1_sig y) P HP).
Defined.

Definition TwoF := addF OneF OneF.

Global Instance addF_morphism : Proper (eqF ==> eqF ==> eqF) addF.
Proof.
unfold Proper, respectful, eqF, addF; intros x y Hxy x' y' Hx'y'.
destruct x as [x Hx]; destruct x' as [x' Hx'];
destruct y as [y Hy]; destruct y' as [y' Hy']; simpl in *.
destruct (sum_f O E E' ncolOEE' x x' Hx Hx').
destruct (sum_f O E E' ncolOEE' y y' Hy Hy'); simpl.
treat_equalities; eauto using sum_unicity.
Defined.

Lemma neq20 : ~ eqF (addF OneF OneF) OF.
Proof.
unfold addition, add_notation, addF, eqF; simpl.
destruct (sum_f O E E' ncolOEE' E E (col_trivial_2 O E)
                (col_trivial_2 O E)) as [EPE HEPE]; simpl.
intro; treat_equalities; apply double_null_null in HEPE.
treat_equalities; Col.
Qed.

Definition mulF (x y : F) : F.
Proof.
destruct (prod_f O E E' ncolOEE'
                 (proj1_sig x) (proj1_sig y)
                 (proj2_sig x) (proj2_sig y)) as [P HP]; exists P.
apply (prod_col O E E' (proj1_sig x) (proj1_sig y) P HP).
Defined.

Global Instance mulF_morphism : Proper (eqF ==> eqF ==> eqF) mulF.
Proof.
unfold Proper, respectful, eqF, mulF; intros x y Hxy x' y' Hx'y'.
destruct x as [x Hx]; destruct x' as [x' Hx'];
destruct y as [y Hy]; destruct y' as [y' Hy']; simpl in *.
destruct (prod_f O E E' ncolOEE' x x' Hx Hx').
destruct (prod_f O E E' ncolOEE' y y' Hy Hy'); simpl.
treat_equalities; eauto using prod_unicity.
Defined.

Definition subF (x y : F) : F.
Proof.
destruct (diff_f O E E' ncolOEE'
                 (proj1_sig x) (proj1_sig y)
                 (proj2_sig x) (proj2_sig y)) as [P HP]; exists P.
apply (diff_col O E E' (proj1_sig x) (proj1_sig y) P HP).
Defined.

Global Instance subF_morphism : Proper (eqF ==> eqF ==> eqF) subF.
Proof.
unfold Proper, respectful, eqF, subF; intros x y Hxy x' y' Hx'y'.
destruct x as [x Hx]; destruct x' as [x' Hx'];
destruct y as [y Hy]; destruct y' as [y' Hy']; simpl in *.
destruct (diff_f O E E' ncolOEE' x x' Hx Hx').
destruct (diff_f O E E' ncolOEE' y y' Hy Hy'); simpl.
treat_equalities; eauto using diff_unicity.
Defined.

Definition oppF (x : F) : F.
Proof.
destruct (opp_f O E E' ncolOEE' (proj1_sig x) (proj2_sig x)) as [P HP].
exists P; apply (opp_col O E E' (proj1_sig x) P HP).
Defined.

Global Instance oppF_morphism : Proper (eqF ==> eqF ) oppF.
Proof.
unfold Proper, respectful, eqF, oppF; intros x y Hxy.
destruct x as [x Hx]; destruct y as [y Hy]; simpl in *.
destruct (opp_f O E E' ncolOEE' x Hx).
destruct (opp_f O E E' ncolOEE' y Hy); simpl.
treat_equalities; eauto using opp_unicity.
Defined.

Definition invF (x : F) : F.
Proof.
destruct (inv_f O E E' ncolOEE' (proj1_sig x) (proj2_sig x)) as [P HP].
exists P; apply (inv_col O E E' ncolOEE' (proj1_sig x) P HP).
Defined.

Global Instance invF_morphism : Proper (eqF ==> eqF ) invF.
Proof.
unfold Proper, respectful, eqF, invF; intros x y Hxy.
destruct x as [x Hx]; destruct y as [y Hy]; simpl in *.
destruct (inv_f O E E' ncolOEE' x Hx).
destruct (inv_f O E E' ncolOEE' y Hy); simpl.
treat_equalities; eauto using inv_unicity.
Defined.

Definition divF (x y : F) : F.
Proof.
destruct (div_f O E E' ncolOEE'
                 (proj1_sig x) (proj1_sig y)
                 (proj2_sig x) (proj2_sig y)) as [P HP]; exists P.
apply (div_col O E E' (proj1_sig x) (proj1_sig y) P HP).
Defined.

Global Instance divF_morphism : Proper (eqF ==> eqF ==> eqF) divF.
Proof.
unfold Proper, respectful, eqF, divF; intros x y Hxy x' y' Hx'y'.
destruct x as [x Hx]; destruct x' as [x' Hx'];
destruct y as [y Hy]; destruct y' as [y' Hy']; simpl in *.
destruct (div_f O E E' ncolOEE' x x' Hx Hx').
destruct (div_f O E E' ncolOEE' y y' Hy Hy'); simpl.
treat_equalities; eauto using div_unicity.
Defined.

Lemma ringF : (ring_theory OF OneF addF mulF subF oppF eqF).
Proof.
split; unfold OF, OneF, addF, mulF, subF, oppF, eqF, sig_rect;
intro x; try intro y; try intro z.

  {
  destruct x as [x Hx]; simpl.
  elim (sum_f O E E' ncolOEE' O x (col_trivial_3 O E) Hx).
  intros; simpl; apply sum_unicity with O E E' O x; try assumption.
  apply sum_O_B; assumption.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; simpl.
  elim (sum_f O E E' ncolOEE' x y Hx Hy).
  elim (sum_f O E E' ncolOEE' y x Hy Hx).
  intros; simpl; apply sum_unicity with O E E' x y; try assumption.
  apply sum_comm; assumption.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; destruct z as [z Hz]; simpl.
  destruct (sum_f O E E' ncolOEE' y z Hy Hz) as [yPz HyPz]; simpl.
  destruct (sum_f O E E' ncolOEE' x yPz Hx
                  (sum_col O E E' y z yPz HyPz)) as [xPyPz HxPyPz].
  destruct (sum_f O E E' ncolOEE' x y Hx Hy) as [xPy HxPy]; simpl.
  destruct (sum_f O E E' ncolOEE' xPy z
                  (sum_col O E E' x y xPy HxPy) Hz) as [xPyPz' HxPyPz']; simpl.
  apply sum_unicity with O E E' x yPz; try assumption.
  apply (sum_assoc O E E' x y z xPy yPz xPyPz'); assumption.
  }

  {
  destruct x as [x Hx]; simpl.
  destruct (prod_f O E E' ncolOEE' E x (col_trivial_2 O E) Hx) as [x' Hx'].
  simpl; apply prod_unicity with O E E' E x; try assumption.
  apply prod_1_l; assumption.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; simpl.
  destruct (prod_f O E E' ncolOEE' x y Hx Hy) as [xMy HxMy].
  destruct (prod_f O E E' ncolOEE' y x Hy Hx) as [yMx HyMx]; simpl.
  apply prod_unicity with O E E' x y; try assumption.
  apply prod_comm; assumption.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; destruct z as [z Hz]; simpl.
  destruct (prod_f O E E' ncolOEE' y z Hy Hz) as [yMz HyMz]; simpl.
  destruct (prod_f O E E' ncolOEE' x yMz Hx
                   (prod_col O E E' y z yMz HyMz)) as [xMyMz HxMyMz].
  destruct (prod_f O E E' ncolOEE' x y Hx Hy) as [xMy HxMy]; simpl.
  destruct (prod_f O E E' ncolOEE' xMy z
                   (prod_col O E E' x y xMy HxMy) Hz) as [xMyMz' HxMyMz'].
  simpl; apply prod_unicity with O E E' x yMz; try assumption.
  apply (prod_assoc O E E' x y z xMy yMz xMyMz'); assumption.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; destruct z as [z Hz]; simpl.
  destruct (sum_f O E E' ncolOEE' x y Hx Hy) as [xPy HxPy]; simpl.
  destruct (prod_f O E E' ncolOEE' xPy z
                   (sum_col O E E' x y xPy HxPy) Hz) as [xPyMz HxPyMz].
  destruct (prod_f O E E' ncolOEE' x z Hx Hz) as [xMz HxMz]; simpl.
  destruct (prod_f O E E' ncolOEE' y z Hy Hz) as [yMz HyMz]; simpl.
  destruct (sum_f O E E' ncolOEE' xMz yMz (prod_col O E E' x z xMz HxMz)
                  (prod_col O E E' y z yMz HyMz)) as [xPyMz' HxPyMz']; simpl.
  apply sum_unicity with O E E' xMz yMz; try assumption.
  apply distr_r with x y z xPy; assumption.
  }

  {
  destruct x as [x Hx]; destruct y as [y Hy]; simpl.
  destruct (diff_f O E E' ncolOEE' x y Hx Hy) as [xSy HxSy].
  destruct (opp_f O E E' ncolOEE' y Hy) as [Oy HOy]; simpl.
  destruct (sum_f O E E' ncolOEE' x Oy Hx
                  (opp_col O E E' y Oy HOy)) as [xSy' HxSy']; simpl.
  destruct HxSy as [Oy' [HOy' HxSy]].
  assert (Oy = Oy'); [apply opp_unicity with O E E' y|
                      subst; apply sum_unicity with O E E' x Oy']; assumption.
  }

  {
  destruct x as [x Hx]; simpl.
  destruct (opp_f O E E' ncolOEE' x Hx) as [Ox HOx]; simpl.
  destruct (sum_f O E E' ncolOEE' x Ox Hx
                  (opp_col O E E' x Ox HOx)) as [O' HO']; simpl.
  unfold opp in HOx; apply sum_unicity with O E E' x Ox; try assumption.
  apply sum_comm; assumption.
  }
Qed.

Lemma fieldF : (field_theory OF OneF addF mulF subF oppF divF invF eqF).
Proof.
split; unfold OF, OneF, mulF, divF, invF, eqF, sig_rect; simpl;
[apply ringF|assert_diffs; auto|intros p q|intros p Hp].

  {
  destruct (div_f O E E' ncolOEE' (proj1_sig p) (proj1_sig q)
                  (proj2_sig p) (proj2_sig q)) as [pDq HpDq]; simpl.
  destruct (inv_f O E E' ncolOEE'
                  (proj1_sig q)(proj2_sig q)) as [Iq HIq]; simpl.
  destruct (prod_f O E E' ncolOEE' (proj1_sig p) Iq (proj2_sig p)
                   (inv_col O E E' ncolOEE'
                            (proj1_sig q) Iq HIq)) as [pDq' HpDq'].
  simpl; destruct HpDq as [Iq' [HIq' HpDq]].
  assert (Iq = Iq'); [apply inv_unicity with O E E' (proj1_sig q)|
                      subst; apply prod_unicity with O E E' (proj1_sig p) Iq'];
  assumption.
  }

  {
  destruct (inv_f O E E' ncolOEE'
                  (proj1_sig p) (proj2_sig p)) as [Ip HIp]; simpl.
  destruct (prod_f O E E' ncolOEE' Ip (proj1_sig p)
                   (inv_col O E E' ncolOEE'
                            (proj1_sig p) Ip HIp) (proj2_sig p)) as [E'' HE''].
  simpl; elim HIp; clear HIp; intro HIp;
  [|spliter; treat_equalities; intuition].
  destruct HIp as [H HIp]; clear H.
  apply prod_unicity with O E E' Ip (proj1_sig p); assumption.
  }
Qed.

Add Ring GeometricRing : ringF.
Add Field GeometricField : fieldF.

Global Instance Fops: (@Ring_ops F OF OneF addF mulF subF oppF eqF).

Global Instance FRing : (Ring (Ro:=Fops)).
Proof.
split; [exact eqF_Equivalence|exact addF_morphism|exact mulF_morphism|
        exact subF_morphism|exact oppF_morphism|exact (Radd_0_l ringF)|
        exact (Radd_comm ringF)|exact (Radd_assoc ringF)|exact (Rmul_1_l ringF)|
        |exact (Rmul_assoc ringF)|exact (Rdistr_l ringF)|
        |exact (Rsub_def ringF)|exact (Ropp_def ringF)].
  {
  intros; rewrite (Rmul_comm ringF); apply (Rmul_1_l ringF).
  }

  {
  intros; rewrite (Rmul_comm ringF); rewrite (Rdistr_l ringF).
  rewrite (Rmul_comm ringF); rewrite (Radd_comm ringF);
  rewrite (Rmul_comm ringF); rewrite (Radd_comm ringF); reflexivity.
  }
Defined.

Global Instance Fcri: (Cring (Rr:=FRing)).
Proof. exact (Rmul_comm ringF). Defined.

Notation "0" := OF : FScope.
Notation "1" := OneF : FScope.
Notation "2" := TwoF : FScope.
Infix "+" := addF : FScope.
Infix "*" := mulF : FScope.
Infix "-" := subF : FScope.
Notation "- x" := (oppF x) : FScope.
Infix "/" := divF : FScope.
Infix "<=" := leF : FScope.

Infix "=F=" := eqF (at level 70) : FScope.

Open Scope FScope.

Lemma Fmult_integral : forall A B, A * B =F= 0 -> A =F= 0 \/ B =F= 0.
Proof.
intros A B HAB; apply prod_null with E E'.
destruct A as [x Hx]; destruct B as [y Hy]; simpl.
red in HAB; unfold eq_notation, eqF, multiplication, mul_notation, mulF in HAB.
destruct (prod_f O E E' ncolOEE'
             (proj1_sig (exist (fun P : Tpoint => Col O E P) x Hx))
             (proj1_sig (exist (fun P : Tpoint => Col O E P) y Hy))
             (proj2_sig (exist (fun P : Tpoint => Col O E P) x Hx))
             (proj2_sig (exist (fun P : Tpoint => Col O E P) y Hy))).
simpl in *; subst; assumption.
Qed.

Global Instance Fintegral : (Integral_domain (Rcr:=Fcri)).
Proof. split; [exact Fmult_integral|assert_diffs; auto]. Defined.

Lemma subF__eq0 : forall x y:F, x - y =F= 0 <-> x =F= y.
Proof. intros; split; intro; nsatz. Qed.

Lemma mulF__eq0 : forall x y z t:F,
  (x - y) * (z - t) =F= 0 <-> x =F= y \/ z =F= t.
Proof.
intros x y z t; split; intro H; [|destruct H; nsatz].
setoid_replace (x =F= y) with (x-y =F= 0); [|symmetry; apply subF__eq0].
setoid_replace (z =F= t) with (z-t =F= 0); [|symmetry; apply subF__eq0].
apply Fmult_integral; assumption.
Qed.

Lemma neqO_mul_neqO : forall x y:F,  ~ x =F= 0 -> ~ y =F= 0 -> ~ x * y =F= 0.
Proof. intros x y Hx Hy Hxy; apply Fmult_integral in Hxy; intuition. Qed.

Lemma oppF_neq0 : forall f, ~ f =F= 0 <-> ~ - f =F= 0.
Proof. intro; split; intro HF; intro H; apply HF; clear HF; nsatz. Qed.

Lemma characterization_of_congruence_F : forall A B C D,
  Cong A B C D <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let (Dc, _) := coordinates_of_point_F D in
  let (Dx, Dy) := Dc in
  (Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) -
  ((Cx - Dx) * (Cx - Dx) + (Cy - Dy) * (Cy - Dy)) =F= 0.
Proof.
intros.
elim (coordinates_of_point_F A); intros Ac HAc.
elim (coordinates_of_point_F B); intros Bc HBc.
elim (coordinates_of_point_F C); intros Cc HCc.
elim (coordinates_of_point_F D); intros Dc HDc.
destruct Ac as [[Ax HAx] [Ay HAy]].
destruct Bc as [[Bx HBx] [By HBy]].
destruct Cc as [[Cx HCx] [Cy HCy]].
destruct Dc as [[Dx HDx] [Dy HDy]].
rewrite subF__eq0; unfold addF, mulF, subF, eqF; simpl.
destruct (diff_f O E E' ncolOEE' Ax Bx HAx HBx) as [AxMBx HAxMBx]; simpl.
destruct (prod_f O E E' ncolOEE' AxMBx AxMBx
                 (diff_col O E E' Ax Bx AxMBx HAxMBx)
                 (diff_col O E E' Ax Bx AxMBx HAxMBx)) as [ABx HABx]; simpl.
destruct (diff_f O E E' ncolOEE' Ay By HAy HBy) as [AyMBy HAyMBy]; simpl.
destruct (prod_f O E E' ncolOEE' AyMBy AyMBy
                 (diff_col O E E' Ay By AyMBy HAyMBy)
                 (diff_col O E E' Ay By AyMBy HAyMBy)) as [ABy HABy]; simpl.
destruct (sum_f O E E' ncolOEE' ABx ABy
                (prod_col O E E' AxMBx AxMBx ABx HABx)
                (prod_col O E E' AyMBy AyMBy ABy HABy)) as [AB2 HAB2]; simpl.
destruct (diff_f O E E' ncolOEE' Cx Dx HCx HDx) as [CxMDx HCxMDx]; simpl.
destruct (prod_f O E E' ncolOEE' CxMDx CxMDx
                 (diff_col O E E' Cx Dx CxMDx HCxMDx)
                 (diff_col O E E' Cx Dx CxMDx HCxMDx)) as [CDx HCDx].
destruct (diff_f O E E' ncolOEE' Cy Dy HCy HDy) as [CyMDy HCyMDy]; simpl.
destruct (prod_f O E E' ncolOEE' CyMDy CyMDy
                 (diff_col O E E' Cy Dy CyMDy HCyMDy)
                 (diff_col O E E' Cy Dy CyMDy HCyMDy)) as [CDy HCDy]; simpl.
destruct (sum_f O E E' ncolOEE' CDx CDy
            (prod_col O E E' CxMDx CxMDx CDx HCDx)
            (prod_col O E E' CyMDy CyMDy CDy HCDy)) as [CD2 HCD2]; simpl.
apply (characterization_of_congruence O E E' SS U1 U2
                                        A Ax Ay B Bx By
                                        C Cx Cy D Dx Dy
                                        AxMBx ABx AyMBy ABy AB2
                                        CxMDx CDx CyMDy CDy CD2); auto.
Qed.

Lemma characterization_of_betweenness_F : forall A B C,
  Bet A B C <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  exists T, 0 <= T /\ T <= 1 /\
            T * (Cx - Ax) =F= Bx - Ax /\ T * (Cy - Ay) =F= By - Ay.
Proof.
intros.
elim (coordinates_of_point_F A); intros Ac HAc.
elim (coordinates_of_point_F B); intros Bc HBc.
elim (coordinates_of_point_F C); intros Cc HCc.
destruct Ac as [[Ax HAx] [Ay HAy]].
destruct Bc as [[Bx HBx] [By HBy]].
destruct Cc as [[Cx HCx] [Cy HCy]].
unfold mulF, subF, eqF, leF; simpl.
destruct (diff_f O E E' ncolOEE' Bx Ax HBx HAx) as [BxMAx HBxMAx]; simpl.
destruct (diff_f O E E' ncolOEE' By Ay HBy HAy) as [ByMAy HByMAy]; simpl.
destruct (diff_f O E E' ncolOEE' Cx Ax HCx HAx) as [CxMAx HCxMAx]; simpl.
destruct (diff_f O E E' ncolOEE' Cy Ay HCy HAy) as [CyMAy HCyMAy]; simpl.
split; intro HBet; [|destruct HBet as [T HBet]].

  {
  apply -> (characterization_of_betweenness O E E' SS U1 U2
                                            A Ax Ay B Bx By C Cx Cy
                                            BxMAx ByMAy CxMAx CyMAy) in HBet;
  auto; destruct HBet as [T [H [HCol [HGe0 [HLe1 [HTx HTy]]]]]]; clear H.
  exists (exist (fun P => Col O E P) T HCol); simpl; do 2 (split; auto).
  destruct (prod_f O E E' ncolOEE' T CxMAx HCol
                   (diff_col O E E' Cx Ax CxMAx HCxMAx)) as [Tx HTx'].
  destruct (prod_f O E E' ncolOEE' T CyMAy HCol
                   (diff_col O E E' Cy Ay CyMAy HCyMAy)) as [Ty HTy']; simpl.
  split; [apply prod_unicity with O E E' T CxMAx|
          apply prod_unicity with O E E' T CyMAy]; assumption.
  }

  {
  destruct (prod_f O E E' ncolOEE' (proj1_sig T) CxMAx (proj2_sig T)
                   (diff_col O E E' Cx Ax CxMAx HCxMAx)) as [Tx HTx'].
  destruct (prod_f O E E' ncolOEE' (proj1_sig T) CyMAy (proj2_sig T)
                   (diff_col O E E' Cy Ay CyMAy HCyMAy)) as [Ty HTy'].
  simpl in *; destruct HBet as [HGe0 [HLe1 [HTx HTy]]]; treat_equalities.
  apply <- (characterization_of_betweenness O E E' SS U1 U2
                                            A Ax Ay B Bx By C Cx Cy
                                            Tx Ty CxMAx CyMAy); auto.
  exists (proj1_sig T); repeat (split; auto); [assert_diffs; auto|].
  apply (proj2_sig T).
  }
Qed.

Lemma characterization_of_collinearity_F : forall A B C,
  Col A B C <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  (Ax - Bx) * (By - Cy) - (Ay - By) * (Bx - Cx) =F= 0.
Proof.
intros.
elim (coordinates_of_point_F A); intros Ac HAc.
elim (coordinates_of_point_F B); intros Bc HBc.
elim (coordinates_of_point_F C); intros Cc HCc.
destruct Ac as [[Ax HAx] [Ay HAy]].
destruct Bc as [[Bx HBx] [By HBy]].
destruct Cc as [[Cx HCx] [Cy HCy]].
rewrite subF__eq0; unfold addF, mulF, subF, eqF; simpl.
destruct (diff_f O E E' ncolOEE' Ax Bx HAx HBx) as [AxMBx HAxMBx]; simpl.
destruct (diff_f O E E' ncolOEE' By Cy HBy HCy) as [ByMCy HByMCy]; simpl.
destruct (prod_f O E E' ncolOEE' AxMBx ByMCy
                 (diff_col O E E' Ax Bx AxMBx HAxMBx)
                 (diff_col O E E' By Cy ByMCy HByMCy)) as [P1 HP1]; simpl.
destruct (diff_f O E E' ncolOEE' Ay By HAy HBy) as [AyMBy HAyMBy]; simpl.
destruct (diff_f O E E' ncolOEE' Bx Cx HBx HCx) as [BxMCx HBxMCx]; simpl.
destruct (prod_f O E E' ncolOEE' AyMBy BxMCx
                 (diff_col O E E' Ay By AyMBy HAyMBy)
                 (diff_col O E E' Bx Cx BxMCx HBxMCx)) as [P2 HP2]; simpl.
apply (characterization_of_collinearity O E E' SS U1 U2
                                        A Ax Ay B Bx By C Cx Cy
                                        AxMBx AyMBy BxMCx ByMCy P1 P2); auto.
Qed.

Lemma characterization_of_midpoint_F : forall A B I,
  is_midpoint I A B <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Ic, _) := coordinates_of_point_F I in
  let (Ix, Iy) := Ic in
  Ix * 2 - (Ax + Bx) =F= 0 /\ Iy * 2 - (Ay + By) =F= 0.
Proof.
intros.
elim (coordinates_of_point_F A); intros Ac HAc.
elim (coordinates_of_point_F B); intros Bc HBc.
elim (coordinates_of_point_F I); intros Ic HIc.
destruct Ac as [[Ax HAx] [Ay HAy]].
destruct Bc as [[Bx HBx] [By HBy]].
destruct Ic as [[Ix HIx] [Iy HIy]].
setoid_rewrite subF__eq0; unfold TwoF, OneF, addF, mulF, eqF; simpl.
destruct (sum_f O E E' ncolOEE' E E (col_trivial_2 O E)
                (col_trivial_2 O E)) as [ET2 HET2]; simpl.
destruct (prod_f O E E' ncolOEE' Ix ET2 HIx
                 (sum_col O E E' E E ET2 HET2)) as [IxT2 HIxT2].
destruct (sum_f O E E' ncolOEE' Ax Bx HAx HBx) as [AxPBx HAxPBx].
destruct (prod_f O E E' ncolOEE' Iy ET2 HIy
                 (sum_col O E E' E E ET2 HET2)) as [IyT2 HIyT2].
destruct (sum_f O E E' ncolOEE' Ay By HAy HBy) as [AyPBy HAyPBy]; simpl.
apply characterization_of_midpoint with O E E' SS U1 U2 Ax Ay
                                          Bx By Ix Iy ET2; auto.
Qed.

Lemma characterization_of_right_triangle_F : forall A B C,
  Per A B C <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  (Ax - Bx) * (Bx - Cx) + (Ay - By) * (By - Cy) =F= 0.
Proof.
intros; unfold Per.
destruct (symmetric_point_construction C B) as [D HM]; revert HM.
setoid_rewrite characterization_of_congruence_F.
setoid_rewrite characterization_of_midpoint_F.
elim (coordinates_of_point_F A); intros [Ax Ay] _.
elim (coordinates_of_point_F B); intros [Bx By] _.
elim (coordinates_of_point_F C); intros [Cx Cy] _; intro H.
split; [clear H; clear D;
        intro H; destruct H as [D [H1 H2]];
        revert H2; revert H1|
        intro H1; exists D; split;
        [assumption|revert H1; revert H]];
elim (coordinates_of_point_F D); intros Dc _;
destruct Dc as [Dx Dy]; intros; spliter; nsatz.
simpl; apply neqO_mul_neqO; apply neq20.
Qed.

Lemma characterization_of_equality_F : forall A B,
  A = B <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  Ax =F= Bx /\ Ay =F= By.
Proof.
intros A B; unfold eqF.
elim (coordinates_of_point_F A); intros [[Ax HAx] [Ay HAy]] HAc.
elim (coordinates_of_point_F B); intros [[Bx HBx] [By HBy]] HBc.
rewrite (eq_points_coordinates O E SS U1 U2 A Ax Ay B Bx By HAc HBc).
split; intro; spliter; split; treat_equalities; simpl; auto.
Qed.

Lemma characterization_of_neq_F_bis : forall A B,
  A <> B <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  ~ (Ax =F= Bx) \/ ~ (Ay =F= By).
Proof.
intros A B; rewrite characterization_of_equality_F; unfold eqF.
elim (coordinates_of_point_F A); intros [[Ax HAx] [Ay HAy]] _.
elim (coordinates_of_point_F B); intros [[Bx HBx] [By HBy]] _.
simpl; split; intro; spliter; [|intuition].
destruct (eq_dec_points Ax Bx); destruct (eq_dec_points Ay By); intuition.
Qed.

Lemma characterization_of_equality_F_aux : forall Ax Ay Bx By,
  Ax =F= Bx /\ Ay =F= By <->
  (Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= OF.
Proof.
intros [Ax HAx] [Ay HAy] [Bx HBx] [By HBy]; unfold subF, mulF, addF, eqF; simpl.
destruct (diff_f O E E' ncolOEE' Ax Bx HAx HBx) as [AxMBx HAxMBx]; simpl.
destruct (prod_f O E E' ncolOEE' AxMBx AxMBx
                 (diff_col O E E' Ax Bx AxMBx HAxMBx)
                 (diff_col O E E' Ax Bx AxMBx HAxMBx)) as [ABx HABx]; simpl.
destruct (diff_f O E E' ncolOEE' Ay By HAy HBy) as [AyMBy HAyMBy]; simpl.
destruct (prod_f O E E' ncolOEE' AyMBy AyMBy
                 (diff_col O E E' Ay By AyMBy HAyMBy)
                 (diff_col O E E' Ay By AyMBy HAyMBy)) as [ABy HABy]; simpl.
destruct (sum_f O E E' ncolOEE' ABx ABy
                (prod_col O E E' AxMBx AxMBx ABx HABx)
                (prod_col O E E' AyMBy AyMBy ABy HABy)) as [s Hs]; simpl.
split; intro H; [|apply eq_sym in H]; spliter; try split; treat_equalities.

  {
  apply sum_unicity with O E E' O O; [|apply sum_A_O; Col].
  assert (AxMBx = O /\ AyMBy = O).
    {
    split; [apply diff_unicity with O E E' Ax Ax|
            apply diff_unicity with O E E' Ay Ay]; try apply diff_null; Col.
    }
  spliter; subst; assert (ABx = O /\ ABy = O);
  [|spliter; subst; assumption].
  split; apply prod_unicity with O E E' O O;
  [|apply prod_0_l| |apply prod_0_l]; Col.
  }

  {
  elim (eq_dec_points Ax Bx); intro Hx; [assumption|exfalso].
  apply (O_not_positive O E); elim (eq_dec_points O AyMBy); intro Hy.

    {
    treat_equalities; apply prod_O_l_eq in HABy; subst.
    apply sum_A_O_eq in Hs; subst; try apply square_pos with E' AxMBx; Col.
    intro; treat_equalities; apply diff_null_eq in HAxMBx; intuition.
    }

    {
    apply sum_pos_pos with E' ABx ABy;
    [apply square_pos with E' AxMBx|apply square_pos with E' AyMBy|assumption];
    try assumption; intro; treat_equalities;
    apply diff_null_eq in HAxMBx; intuition.
    }
  }

  {
  subst; elim (eq_dec_points Ay By); intro Hy; [assumption|exfalso].
  apply (O_not_positive O E); elim (eq_dec_points O AxMBx); intro Hx.

    {
    treat_equalities; apply prod_O_l_eq in HABx; subst.
    apply sum_O_B_eq in Hs; subst; try apply square_pos with E' AyMBy; Col.
    intro; treat_equalities; apply diff_null_eq in HAyMBy; intuition.
    }

    {
    apply sum_pos_pos with E' ABx ABy;
    [apply square_pos with E' AxMBx|apply square_pos with E' AyMBy|assumption];
    try assumption; intro; treat_equalities;
    apply diff_null_eq in HAyMBy; intuition.
    }
  }
Qed.

Lemma characterization_of_equality_F_bis : forall A B,
  A = B <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  (Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= OF.
Proof.
intros A B; rewrite characterization_of_equality_F.
elim (coordinates_of_point_F A); intros [Ax Ay] _.
elim (coordinates_of_point_F B); intros [Bx By] _.
apply characterization_of_equality_F_aux.
Qed.

Lemma characterization_of_neq_F : forall A B,
  A <> B <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  ~ ((Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= OF).
Proof.
intros; rewrite characterization_of_equality_F_bis.
elim (coordinates_of_point_F A); intros [Ax Ay] _.
elim (coordinates_of_point_F B); intros [Bx By] _; simpl; split; auto.
Qed.

Lemma characterization_of_parallelism_F_aux : forall A B C D,
  Par A B C D <->
  A <> B /\ C <> D /\
  exists P, is_midpoint C A P /\ exists Q, is_midpoint Q B P /\ Col C D Q.
Proof.
intros; split; intro H; [do 2 (split; try solve [assert_diffs; auto])|
                         destruct H as [HAB [HCD [P [HP [Q [HQ HCol]]]]]]].

  {
  destruct (symmetric_point_construction A C) as [P HP];
  exists P; split; [assumption|]; destruct (midpoint_existence B P) as [Q HQ].
  exists Q; split; [assumption|].
  assert (Par B A Q C) by (apply triangle_mid_par with P; assert_diffs; Col).
  destruct (parallel_unicity A B C D C Q C); finish.
  }

  {
  assert (Par B A Q C) by (apply triangle_mid_par with P; assert_diffs; Col).
  apply par_col_par with Q; finish.
  }
Qed.

Lemma characterization_of_parallelism_F_bis : forall A B C D,
  Par A B C D <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let (Dc, _) := coordinates_of_point_F D in
  let (Dx, Dy) := Dc in
  (Ax - Bx) * (Cy - Dy) - (Ay - By) * (Cx - Dx) =F= 0 /\
  (~ (Ax =F= Bx) \/ ~ (Ay =F= By)) /\ (~ (Cx =F= Dx) \/ ~ (Cy =F= Dy)).
Proof.
intros; rewrite characterization_of_parallelism_F_aux.
split; [intro H; destruct H as [HAB [HCD [P [HP [Q [HQ HCol]]]]]]|].

  {
  revert HCol; revert HQ; revert HP; revert HCD; revert HAB.
  setoid_rewrite characterization_of_neq_F_bis.
  setoid_rewrite characterization_of_midpoint_F.
  setoid_rewrite characterization_of_collinearity_F.
  elim (coordinates_of_point_F A); intros [Ax Ay] _.
  elim (coordinates_of_point_F B); intros [Bx By] _.
  elim (coordinates_of_point_F C); intros [Cx Cy] _.
  elim (coordinates_of_point_F D); intros [Dx Dy] _.
  elim (coordinates_of_point_F P); intros [Px Py] _.
  elim (coordinates_of_point_F Q); intros [Qx Qy] _.
  intros HAB HCD [HPx HPy] [HQx HQy] HCol; split; [|split; assumption].
  rewrite <- neg_and_eqF in HAB; rewrite <- neg_and_eqF in HCD.
  cut ((Ax - Bx) * (Cy - Dy) - (Ay - By) * (Cx - Dx) =F= 0 \/
       ((Ax =F= Bx) /\ (Ay =F= By)) \/
       ((Cx =F= Dx) /\ (Cy =F= Dy))); [intuition|].
  scnf; try solve[clear HAB; clear HCD; repeat rewrite <- mulF__eq0; nsatz;
                  simpl; try rewrite <- oppF_neq0;
                  apply neqO_mul_neqO; apply neq20].
  clear HPx; clear HPy; clear HQx; clear HQy; clear HCol.
  destruct H as [[H1 H2] [H3 H4]];
  elim H1; clear H1; [auto|intro H1];
  elim H2; clear H2; [auto|intro H2];
  elim H3; clear H3; [auto|intro H3];
  elim H4; clear H4; [auto|intro H4; exfalso; rtauto].
  }

  {
  destruct (symmetric_point_construction A C) as [P HP]; revert HP.
  destruct (midpoint_existence B P) as [Q HQ]; revert HQ.
  setoid_rewrite characterization_of_neq_F_bis.
  setoid_rewrite characterization_of_midpoint_F.
  setoid_rewrite characterization_of_collinearity_F.
  elim (coordinates_of_point_F A); intros [Ax Ay] _.
  elim (coordinates_of_point_F B); intros [Bx By] _.
  elim (coordinates_of_point_F C); intros [Cx Cy] _.
  elim (coordinates_of_point_F D); intros [Dx Dy] _.
  intros HP HQ [HPar [HAB HCD]]; split; [assumption|split; [assumption|]].
  exists P; revert HQ; revert HP.
  elim (coordinates_of_point_F P); intros [Px Py] _; intros HQ [HPx HPy].
  split; [split; assumption|]; exists Q; revert HQ.
  elim (coordinates_of_point_F Q); intros [Qx Qy] _; intros [HQx HQy].
  split; [split; assumption|].
  rewrite <- neg_and_eqF in HAB; rewrite <- neg_and_eqF in HCD.
  cut ((Cx - Dx) * (Dy - Qy) - (Cy - Dy) * (Dx - Qx) =F= 0 \/
       ((Ax =F= Bx) /\ (Ay =F= By)) \/
       ((Cx =F= Dx) /\ (Cy =F= Dy))); [intuition|].
  scnf; try solve [clear HAB; clear HCD; repeat rewrite <- mulF__eq0; nsatz;
                   simpl; repeat try apply neqO_mul_neqO; apply neq20].
  clear HPx; clear HPy; clear HQx; clear HQy; clear HPar.
  destruct H as [[H1 H2] [H3 H4]];
  elim H1; clear H1; [auto|intro H1];
  elim H2; clear H2; [auto|intro H2];
  elim H3; clear H3; [auto|intro H3];
  elim H4; clear H4; [auto|intro H4; exfalso; rtauto].
  }
Qed.

Lemma characterization_of_parallelism_F : forall A B C D,
  Par A B C D <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let (Dc, _) := coordinates_of_point_F D in
  let (Dx, Dy) := Dc in
  (Ax - Bx) * (Cy - Dy) - (Ay - By) * (Cx - Dx) =F= 0 /\
  ~ ((Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= OF) /\
  ~ ((Cx - Dx) * (Cx - Dx) + (Cy - Dy) * (Cy - Dy) =F= OF).
Proof.
intros; rewrite characterization_of_parallelism_F_bis.
elim (coordinates_of_point_F A); intros [Ax Ay] _.
elim (coordinates_of_point_F B); intros [Bx By] _.
elim (coordinates_of_point_F C); intros [Cx Cy] _.
elim (coordinates_of_point_F D); intros [Dx Dy] _.
setoid_rewrite <- characterization_of_equality_F_aux.
setoid_rewrite <- neg_and_eqF; tauto.
Qed.

Lemma characterization_of_perpendicularity_F_bis : forall A B C D,
  Perp A B C D <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let (Dc, _) := coordinates_of_point_F D in
  let (Dx, Dy) := Dc in
  (Ax - Bx) * (Cx - Dx) + (Ay - By) * (Cy - Dy) =F= OF /\
  (~ (Ax =F= Bx) \/ ~ (Ay =F= By)) /\ (~ (Cx =F= Dx) \/ ~ (Cy =F= Dy)).
Proof.
intros; split; [intro H; destruct H as [X [HAB [HCD [HC1 [HC2 HPer]]]]]|].

  {
  assert (HA : Col A A B) by Col; assert (HB : Col B A B) by Col.
  assert (HC : Col C C D) by Col; assert (HD : Col D C D) by Col.
  assert (HPer1:=HPer A C HA HC); assert (HPer2:=HPer B C HB HC); clear HC.
  assert (HPer3:=HPer A D HA HD); assert (HPer4:=HPer B D HB HD); clear HD.
  clear HA; clear HB; clear HPer; revert HPer4; revert HPer3;
  revert HPer2; revert HPer1; revert HC2; revert HC1; revert HCD; revert HAB.
  setoid_rewrite characterization_of_neq_F_bis.
  setoid_rewrite characterization_of_collinearity_F.
  setoid_rewrite characterization_of_right_triangle_F.
  elim (coordinates_of_point_F A); intros [Ax Ay] _.
  elim (coordinates_of_point_F B); intros [Bx By] _.
  elim (coordinates_of_point_F C); intros [Cx Cy] _.
  elim (coordinates_of_point_F D); intros [Dx Dy] _.
  elim (coordinates_of_point_F X); intros [Xx Xy] _.
  intros; split; [nsatz|split; assumption].
  }

  {
  unfold Perp, Perp_in; intro HPerp.
  assert (HX : ~ Par A B C D); revert HPerp.
    {
    intro H; assert (HAB : A <> B); revert H.
      {
      rewrite characterization_of_neq_F_bis.
      elim (coordinates_of_point_F A); intros [Ax Ay] _.
      elim (coordinates_of_point_F B); intros [Bx By] _.
      elim (coordinates_of_point_F C); intros [Cx Cy] _.
      elim (coordinates_of_point_F D); intros [Dx Dy] _.
      intro; spliter; auto.
      }
    rewrite characterization_of_parallelism_F_bis.
    rewrite characterization_of_neq_F in HAB; revert HAB.
    elim (coordinates_of_point_F A); intros [Ax Ay] _.
    elim (coordinates_of_point_F B); intros [Bx By] _.
    elim (coordinates_of_point_F C); intros [Cx Cy] _.
    elim (coordinates_of_point_F D); intros [Dx Dy] _.
    intros HAB [HPerp [_ HCD]]; intros [HPar _]; apply HAB.
    cut ((Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= 0 \/
         ((Cx =F= Dx) /\ (Cy =F= Dy))); [intuition|].
    rewrite <- neg_and_eqF in HCD; scnf; [| |exfalso; rtauto];
    clear HCD; repeat rewrite <- mulF__eq0; nsatz.
    }
  setoid_rewrite characterization_of_neq_F_bis.
  setoid_rewrite characterization_of_collinearity_F.
  setoid_rewrite characterization_of_right_triangle_F.
  apply not_par_inter_exists in HX; destruct HX as [X [H1 H2]].
  revert H2; revert H1; setoid_rewrite characterization_of_collinearity_F.
  elim (coordinates_of_point_F A); intros [Ax Ay] _.
  elim (coordinates_of_point_F B); intros [Bx By] _.
  elim (coordinates_of_point_F C); intros [Cx Cy] _.
  elim (coordinates_of_point_F D); intros [Dx Dy] _.
  intros H1 H2 [HPerp [HAB HCD]].
  exists X; repeat split; auto; intros U V; revert H2; revert H1.
  elim (coordinates_of_point_F X); intros [Xx Xy] _; intros H1 H2.
  elim (coordinates_of_point_F U); intros [Ux Uy] _.
  elim (coordinates_of_point_F V); intros [Vx Vy] _; intros H3 H4.
  rewrite <- neg_and_eqF in HAB; rewrite <- neg_and_eqF in HCD.
  cut ((Ux - Xx) * (Xx - Vx) + (Uy - Xy) * (Xy - Vy) =F= 0 \/
       ((Ax =F= Bx) /\ (Ay =F= By)) \/
       ((Cx =F= Dx) /\ (Cy =F= Dy))); [intuition|].
  scnf; try solve [clear HAB; clear HCD; repeat rewrite <- mulF__eq0; nsatz].
  clear HPerp; clear H1; clear H2; clear H3; clear H4.
  destruct H as [[H1 H2] [H3 H4]];
  elim H1; clear H1; [auto|intro H1];
  elim H2; clear H2; [auto|intro H2];
  elim H3; clear H3; [auto|intro H3];
  elim H4; clear H4; [auto|intro H4; exfalso; rtauto].
  }
Qed.

Lemma characterization_of_perpendicularity_F : forall A B C D,
  Perp A B C D <->
  let (Ac, _) := coordinates_of_point_F A in
  let (Ax, Ay) := Ac in
  let (Bc, _) := coordinates_of_point_F B in
  let (Bx, By) := Bc in
  let (Cc, _) := coordinates_of_point_F C in
  let (Cx, Cy) := Cc in
  let (Dc, _) := coordinates_of_point_F D in
  let (Dx, Dy) := Dc in
  (Ax - Bx) * (Cx - Dx) + (Ay - By) * (Cy - Dy) =F= OF /\
  ~ ((Ax - Bx) * (Ax - Bx) + (Ay - By) * (Ay - By) =F= OF) /\
  ~ ((Cx - Dx) * (Cx - Dx) + (Cy - Dy) * (Cy - Dy) =F= OF).
Proof.
intros; rewrite characterization_of_perpendicularity_F_bis.
elim (coordinates_of_point_F A); intros [Ax Ay] _.
elim (coordinates_of_point_F B); intros [Bx By] _.
elim (coordinates_of_point_F C); intros [Cx Cy] _.
elim (coordinates_of_point_F D); intros [Dx Dy] _.
setoid_rewrite <- characterization_of_equality_F_aux.
setoid_rewrite <- neg_and_eqF; tauto.
Qed.

Ltac decompose_coordinates :=
  repeat
  match goal with
    H: _ |- context[ (coordinates_of_point_F ?X) ] =>
      let fx := fresh X "x" in
      let fy := fresh X "y" in
      destruct (coordinates_of_point_F X) as [[fx fy] _]
  end.

Ltac convert_to_algebra :=
  try setoid_rewrite characterization_of_betweenness_F;
  try setoid_rewrite characterization_of_congruence_F;
  try setoid_rewrite characterization_of_midpoint_F;
  try setoid_rewrite characterization_of_collinearity_F;
  try setoid_rewrite characterization_of_right_triangle_F;
  try setoid_rewrite characterization_of_perpendicularity_F;
  try setoid_rewrite characterization_of_parallelism_F;
  try setoid_rewrite characterization_of_equality_F;
  try setoid_rewrite characterization_of_neq_F.

Ltac express_disj_as_a_single_poly := repeat rewrite <- mulF__eq0.

Lemma centroid_theorem : forall A B C A1 B1 C1 G,
  is_midpoint A1 B C ->
  is_midpoint B1 A C ->
  is_midpoint C1 A B ->
  Col A A1 G ->
  Col B B1 G ->
  Col C C1 G \/ Col A B C.
Proof.
intros A B C A1 B1 C1 G; convert_to_algebra; decompose_coordinates.
intros; spliter. express_disj_as_a_single_poly; nsatz.
Qed.

Lemma put_neg_in_goal : forall A B, A \/ B -> (~ A -> B).
Proof. tauto. Qed.

Ltac put_negs_in_goal :=
  repeat
  match goal with
    H: ~ ?X |- _ => revert H; apply put_neg_in_goal
  end.

(** We only need to prove discrimination results
as so far the only constant different from 0 or 1 which occurs is 2. *)
Ltac prove_discr_for_powers_of_2 :=
  simpl; try rewrite <- oppF_neq0; repeat apply neqO_mul_neqO; apply neq20.

Lemma Euler_circle: forall A B C A1 B1 C1 A2 B2 C2 A3 B3 C3 H O,
  ~ Col A B C ->
  Col A B C2 -> Col B C A2 -> Col A C B2 ->
  Perp A B C C2 -> Perp B C A A2 -> Perp A C B B2 ->
  Perp A B C2 H -> Perp B C A2 H -> Perp A C B2 H ->
  is_midpoint A3 A H -> is_midpoint B3 B H -> is_midpoint C3 C H ->
  is_midpoint C1 A B -> is_midpoint A1 B C -> is_midpoint B1 C A ->
  Cong O A1 O B1 -> Cong O A1 O C1 ->
  Cong O A2 O A1 /\ Cong O B2 O A1 /\ Cong O C2 O A1 /\
  Cong O A3 O A1 /\ Cong O B3 O A1 /\ Cong O C3 O A1.
Proof.
intros A B C A1 B1 C1 A2 B2 C2 A3 B3 C3 H O0; convert_to_algebra.
decompose_coordinates; intros; spliter.
clear H24; clear H25; clear H26; clear H27; clear H28; clear H29;
clear H30; clear H31; clear H32; clear H33; clear H34; clear H35;
put_negs_in_goal.
scnf; [| | | | | |spliter; rtauto]; express_disj_as_a_single_poly;
nsatz; prove_discr_for_powers_of_2.
Qed.

End T18.