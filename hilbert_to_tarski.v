Require Import Ch12_parallel_inter_dec.
Require Import Morphisms.
Require Import hilbert_axioms. 

Section T.

Context `{MT:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

(** We need a notion of line. *)

Definition Line := @Couple Tpoint.
Definition Lin := build_couple Tpoint.

Definition Incident (A : Tpoint) (l : Line) := Col A (P1 l) (P2 l).

(** * Group I Combination *)

(** For every pair of distinct points there is a line containing them. *)
					      
Lemma axiom_line_existence : forall A B, A<>B -> exists l, Incident A l /\ Incident B l.
Proof.
intros.
exists (Lin A B H).
unfold Incident.
intuition.
Qed.

(** We need a notion of equality over lines. *)
					      
Definition Eq : relation Line := fun l m => forall X, Incident X l <-> Incident X m.

Infix "=l=" := Eq (at level 70):type_scope.

Lemma incident_eq : forall A B l, forall H : A<>B, 
 Incident A l -> Incident B l ->
 (Lin A B H) =l= l. 
Proof.
intros.
unfold Eq.
intros.
unfold Incident in *.
replace (P1 (Lin A B H)) with A.
replace (P2 (Lin A B H)) with B.
2:auto.
2:auto.
split;intro.
assert (T:=Cond l).
cases_equality X B.
subst X.
auto.
assert (Col (P1 l) A B).
eapply col_transitivity_1;try apply T;Col.
assert (Col (P2 l) A B) by eCol.
assert (Col B (P2 l) X).
eCol.
assert (Col B (P1 l) X).
eCol.
eapply col_transitivity_2.
assert (B<>X) by auto.
apply H8.
Col.
Col.


assert (U:=Cond l).
cases_equality X (P1 l).
smart_subst X.
eCol.

assert (Col (P1 l) X A).
eCol.
assert (Col (P1 l) X B).
eCol.
eapply col_transitivity_1.
apply H3.
Col.
Col.
Qed.

(** Our equality is an equivalence relation. *)
  
Lemma eq_transitivity : forall l m n, l =l= m -> m =l= n -> l =l= n.
Proof.
unfold Eq,Incident.
intros.
assert (T:=H X).
assert (V:= H0 X).
split;intro;intuition.
Qed.

Lemma eq_reflexivity : forall l, l =l= l.
Proof.
intros.
unfold Eq.
intuition.
Qed.

Lemma eq_symmetry : forall l m, l =l= m -> m =l= l.
unfold Eq.
intros.
assert (T:=H X).
intuition.
Qed.

Instance Eq_Equiv : Equivalence Eq.
Proof.
split.
unfold Reflexive.
apply eq_reflexivity.
unfold Symmetric.
apply eq_symmetry.
unfold Transitive.
apply eq_transitivity.
Qed.


(** The equality is compatible with Incident *)
	   
Lemma eq_incident : forall A l m, l =l= m -> 
 (Incident A l <-> Incident A m).
Proof.
intros.
split;intros;
unfold Eq in *;
assert (T:= H A);
intuition.
Qed.

Instance incident_Proper (A:Tpoint) :
Proper (Eq ==>iff) (Incident A).
intros a b H .
apply eq_incident.
assumption.
Qed.


(** There is only one line going through two points. *)
	   
Lemma axiom_line_unicity : forall A B l m, A <> B ->
 (Incident A l) -> (Incident B l) -> (Incident A m) -> (Incident B m) -> 
 l =l= m.
Proof.
intros.
assert ((Lin A B H) =l= l).
eapply incident_eq;assumption.
assert ((Lin A B H) =l= m).
eapply incident_eq;assumption.
rewrite <- H4.
assumption.
Qed.

(** Every line contains at least two points. *)

Lemma axiom_two_points_on_line : forall l, 
  exists A, exists B, Incident B l /\ Incident A l /\ A <> B.
Proof.
intros.
exists (P1 l).
exists (P2 l).
unfold Incident.
repeat split;Col.
exact (Cond l).
Qed.

(** Definition of the collinearity predicate.
 We say that three points are collinear if they belongs to the same line. *)
  
Definition Col_H := fun A B C => 
  exists l, Incident A l /\ Incident B l /\ Incident C l.

(** We show that the notion of collinearity we just defined is equivalent to the
 notion of collinearity of Tarski. *)
		    
Lemma cols_coincide_1 : forall A B C, Col_H A B C -> Col A B C.
Proof.
intros.
unfold Col_H in H.
DecompExAnd H l.
unfold Incident in *.
assert (T:=Cond l).
assert (Col (P1 l) A B).
eapply col_transitivity_1;try apply T;Col.
assert (Col (P1 l) A C).
eapply col_transitivity_1;try apply T;Col.
cases_equality (P1 l) A.
smart_subst A.
eapply col_transitivity_1;try apply T;Col.
eapply col_transitivity_2;try apply H2;Col.
Qed.

Lemma cols_coincide_2 : forall A B C, Col A B C -> Col_H A B C.
Proof.
intros.
unfold Col_H.
cases_equality A B.
subst B.
cases_equality A C.
subst C.
assert (exists B, A<>B).
eapply another_point.
DecompEx H0 B.
exists (Lin A B H1).
unfold Incident;intuition.
exists (Lin A C H0).
unfold Incident;intuition.
exists (Lin A B H0).
unfold Incident;intuition.
Qed.


(** There exists three non collinear points. *)
  
Lemma axiom_plan :
 exists A , exists B, exists C, ~ Col_H A B C.
Proof.
assert (T:=lower_dim).
DecompEx T A.
DecompEx H B.
DecompEx H0 C.
assert (~ Col_H A B C).
unfold not;intro.
assert (Col A B C).
apply cols_coincide_1.
auto.
intuition.

exists A.
exists B.
exists C.
auto.
Qed.

(** * Group II Order *)

(** Definition of the Between predicate of Hilbert.
    Note that it is different from the Between of Tarski.
    The Between of Hilbert is strict. *)
  
Definition Between_H A B C  :=
  Bet A B C /\ A <> B /\ B <> C /\ A <> C.
 
Lemma axiom_between_col :
 forall A B C, Between_H A B C -> Col_H A B C.
Proof.
intros.
unfold Col_H, Between_H in *.
DecompAndAll.
exists (Lin A B H2).
unfold Incident.
intuition.
Qed.

(** If B is between A and C, it is also between C and A. *)
				       
Lemma axiom_between_comm : forall A B C, Between_H A B C -> Between_H C B A.
Proof.
unfold Between_H in |- *.
intros.
intuition.
Qed.

Lemma axiom_between_out :
 forall A B, A <> B -> exists C, Between_H A B C.
Proof.
intros.
prolong A B C A B.
exists C.
unfold Between_H.
repeat split; 
auto; 
intro; 
treat_equalities; 
tauto.
Qed.

Lemma axiom_between_only_one :
 forall A B C,
 Between_H A B C -> ~ Between_H B C A /\ ~ Between_H B A C.
Proof.
unfold Between_H in |- *.
intros.
split;
intro;
spliter.
assert (B=C) by 
 (apply (between_egality B C A);Between).
solve [intuition].

assert (A = B) by
 (apply (between_egality A B C);Between).
intuition.
Qed.

Lemma between_one : forall A B C,
 A<>B -> A<>C -> B<>C -> Col A B C ->
 Between_H A B C \/ Between_H B C A \/ Between_H B A C.
Proof.
intros.
unfold Col, Between_H in *.
intuition.
Qed.


Lemma axiom_between_one : forall A B C,
 A<>B -> A<>C -> B<>C -> Col_H A B C ->
 Between_H A B C \/ Between_H B C A \/ Between_H B A C.
Proof.
intros.
apply between_one;try assumption.
apply cols_coincide_1.
assumption.
Qed.

(** Axiom of Pasch, (Hilbert version). *)

(** First we define a predicate which means that the line l intersects the segment AB. *)

Definition cut := fun l A B => ~Incident A l /\ ~Incident B l /\ exists I, Incident I l /\ Between_H A I B.

(** We show that this definition is equivalent to the predicate two_sides of Tarski. *)

Lemma cut_two_sides : forall l A B, cut l A B <-> two_sides (P1 l) (P2 l) A B.
Proof.
intros.
unfold cut.
unfold two_sides.
split.
intros.
spliter.
repeat split; intuition.
apply (Cond l).
assumption.
ex_and H1 T.
exists T.
unfold Incident in H1.
unfold Between_H in *.
intuition.

intros.
spliter.
ex_and H2 T.
unfold Incident.
repeat split; try assumption.
exists T.
split.
assumption.
unfold Between_H.
repeat split.
assumption.
intro.
subst.
contradiction.
intro.
subst.
contradiction.
intro.
treat_equalities.
contradiction.
Qed.

Lemma axiom_pasch : forall A B C l, 
 ~ Col_H A B C -> ~ Incident C l ->
 cut l A B -> cut l A C \/ cut l B C.
Proof.
intros.
apply cut_two_sides in H1.
assert(~Col A B C).
intro.
apply H.
apply cols_coincide_2.
assumption.

assert(HH:=H1).
unfold two_sides in HH.
spliter.

unfold Incident in H0.

assert(HH:= one_or_two_sides (P1 l)(P2 l) A C H4 H0 ).

induction HH.
left.
apply <-cut_two_sides.
assumption.
right.
apply <-cut_two_sides.
apply l9_2.
eapply l9_8_2.
apply H1.
assumption.
Qed.

Lemma Incid_line : 
 forall P A B l, A<>B ->
 Incident A l -> Incident B l -> Col P A B -> Incident P l.
Proof.
intros.
unfold Incident in *.
destruct l as [C D HCD].
simpl in *.
assert (Col D A B) by eCol.
assert (Col C A B) by eCol.
assert (Col A D P) by eCol.
assert (Col A D C) by eCol.
cases_equality A D.
subst.
clear H3 H5 H6.
eCol.
eCol.
Qed.

(** * Group III Parallels *)

(** We use a definition of parallel which is valid only in 2D: *)

Definition Para l m := ~ exists X, Incident X l /\ Incident X m.

Lemma axiom_euclid_existence : 
 forall l P, ~ Incident P l -> exists m, Para l m.
Proof.
intros.
destruct l as [A B HC].

assert (T:=parallel_existence A B P HC).
decompose [ex and] T;clear T.
elim (axiom_line_existence x x0 H0);intros m Hm.
exists m.

unfold Par in H1.
destruct H1.
unfold Par_strict in *.
decompose [and] H1.
intro.
decompose [ex and] H6;clear H6.
apply H7.
exists x1.
split.
unfold Incident in H9.
simpl in *.
assumption.
apply cols_coincide_1.
exists m.
intuition.

unfold Incident in *.
simpl in *.
decompose [ex and] H1;clear H1.
decompose [and] Hm;clear Hm.

assert (Incident A m) by (eapply Incid_line;eauto).
assert (Incident B m) by (eapply Incid_line;eauto).
assert (Incident P m) by (eapply Incid_line;eauto).
cut False.
intuition.
apply H.
apply cols_coincide_1.
exists m;intuition.
Qed.

Lemma Para_Par : forall A B C D, forall HAB: A<>B, forall HCD: C<>D,
 Para (Lin A B HAB) (Lin C D HCD) -> Par A B C D.
Proof.
intros.
unfold Para in H.
unfold Incident in *;simpl in *.
unfold Par.
left.
unfold Par_strict.
repeat split;auto.
Qed.

Lemma axiom_euclid_unicity : 
  forall l P m1 m2,
  ~ Incident P l -> 
   Para l m1 -> Incident P m1 ->
   Para l m2 -> Incident P m2 -> 
   m1 =l= m2.
Proof.
intros.
destruct l as [A B HAB].
destruct m1 as [C D HCD].
destruct m2 as [C' D' HCD'].
unfold Incident in *;simpl in *.
apply Para_Par in H0.
apply Para_Par in H2.
elim (parallel_unicity A B C D C' D' P H0 H1 H2 H3);intros.
apply axiom_line_unicity with (A:=C') (B:=D');
unfold Incident;simpl;Col.
Qed.

(** * Goup IV Congruence *)

(** The cong predicate of Hilbert is the same as the one of Tarski: *)

Definition Hcong:=Cong.

Lemma axiom_hcong_1_existence : 
 forall A B l M, 
 A <> B -> Incident M l -> 
 exists A', exists B', 
    Incident A' l /\ Incident B' l /\
    Between_H A' M B' /\ Hcong M A' A B /\ Hcong M B' A B.
Proof.
intros.
unfold Hcong.
unfold Incident.

induction(eq_dec_points M (P1 l)).
subst M.

prolong (P2 l) (P1 l) A' A B.
prolong A' (P1 l) B' A B.

exists A'.
exists B'.

repeat split.
apply bet_col in H1.
apply bet_col in H3.
Col.
apply bet_col in H1.
apply bet_col in H3.
apply col_permutation_2.
eapply (col_transitivity_1 _ A').
intro.
treat_equalities.
tauto.
Col.
Col.
assumption.
intro.
subst A'.
apply cong_symmetry in H2.
apply cong_identity in H2.
contradiction.
intro.
treat_equalities.
tauto.
intro.
treat_equalities.
apply between_identity in H3.
subst A'.
apply cong_symmetry in H2.
apply cong_identity in H2.
contradiction.
assumption.
assumption.

prolong (P1 l) M A' A B.
prolong A' M B' A B.
exists A'.
exists B'.
repeat split.
apply bet_col in H2.
apply bet_col in H4.
eCol.
apply bet_col in H2.
apply bet_col in H4.

assert(Col (P1 l) M B').

apply col_permutation_2.
eapply (col_transitivity_1 _ A').
intro.
treat_equalities.
tauto.
Col.
Col.
eCol.
assumption.
intro.
treat_equalities.
tauto.
intro.
treat_equalities.
tauto.
intro.
treat_equalities.
tauto.
assumption.
assumption.
Qed.

Lemma axiom_hcong_1_unicity : 
 forall A B l M A' B' A'' B'', A <> B -> Incident M l ->
  Incident A' l -> Incident B' l ->
  Incident A'' l -> Incident B'' l ->
  Between_H A' M B' -> Hcong M A' A B ->
  Hcong M B' A B -> Between_H A'' M B'' ->
  Hcong M A'' A B -> Hcong M B'' A B ->
  (A' = A'' /\ B' = B'') \/ (A' = B'' /\ B' = A'').
Proof.
unfold Hcong.
unfold Between_H.
unfold Incident.
intros.
spliter.

assert(A' <> M /\ A'' <> M /\ B' <> M /\ B'' <> M /\ A' <> B' /\ A'' <> B'').
repeat split; intro; treat_equalities; tauto.
spliter.

induction(out_dec M A' A'').
left.
assert(A' = A'').
eapply (l6_11_unicity M A B A''); try assumption.
apply out_trivial.
assumption.

split.
assumption.
subst A''.

eapply (l6_11_unicity M A B B''); try assumption.

unfold out.
repeat split; try assumption.
eapply l5_2.
apply H18.
assumption.
assumption.
apply out_trivial.
assumption.

right.
apply not_out_bet in H23.

assert(A' = B'').
eapply (l6_11_unicity M A B A'); try assumption.
apply out_trivial.
assumption.

unfold out.
repeat split; try assumption.

eapply l5_2.
apply H18.
assumption.
apply between_symmetry.
assumption.

split.
assumption.

subst B''.
eapply (l6_11_unicity M A B B'); try assumption.
apply out_trivial.
assumption.
unfold out.
repeat split; try assumption.
eapply l5_2.
apply H20.
apply between_symmetry.
assumption.
assumption.
eapply col3.
apply (Cond l).
Col.
Col.
Col.
Qed.

(** As a remark we also prove another version of this axiom as formalized in Isabelle by
Phil Scott. *)

Definition same_side_scott E A B := E <> A /\ E <> B /\ Col_H E A B /\ ~ Between_H A E B.

Remark axiom_hcong_scott: 
 forall P Q A C, A <> C -> P <> Q ->
  exists B, same_side_scott A B C  /\ Hcong P Q A B.
Proof.
intros.
unfold same_side_scott.
assert (exists X : Tpoint, out A X C /\ Cong A X P Q).
apply l6_11_existence;auto.
decompose [ex and] H1;clear H1.
exists x.
repeat split.
unfold out in H3.
intuition.
unfold out in H3.
intuition.
apply cols_coincide_2.
apply out_col;assumption.


unfold out in H3.
unfold Between_H.
intro.
decompose [and] H3;clear H3.
decompose [and] H1;clear H1.
clear H8.
destruct H7.
assert (A = x).
eapply between_egality;eauto.
intuition.
assert (A = C).
eapply between_egality;eauto.
apply between_symmetry.
auto.
intuition.
unfold Hcong.
Cong.
Qed.

(** Transivity of congruence. *)

Lemma axiom_hcong_trans : forall A B C D E F, Hcong A B C D -> Hcong A B E F -> Hcong C D E F.
Proof.
unfold Hcong.
intros.
apply cong_symmetry.
apply cong_symmetry in H0.
eapply cong_transitivity;eauto.
Qed.

(** Reflexivity of congruence. *)

Lemma axiom_hcong_refl : forall A B , Hcong A B A B.
Proof.
unfold Hcong.
intros.
Cong.
Qed.

(** We define when two segments do not intersect. *)

Definition disjoint := fun A B C D => ~ exists P, Between_H A P B /\ Between_H C P D.

(** Note that two disjoint segments may share one of their extremities. *)

Lemma col_disjoint_bet : forall A B C, Col_H A B C -> disjoint A B B C -> Bet A B C.
Proof.
intros.
apply cols_coincide_1 in H.
unfold disjoint in H0.

induction (eq_dec_points A B).
subst  B.
apply between_trivial2.
induction (eq_dec_points B C).
subst  C.
apply between_trivial.

unfold Col in H.
induction H.
assumption.

induction H.
apply False_ind.
apply H0.
assert(exists M, is_midpoint M B C) by(apply midpoint_existence).
ex_and H3 M.
exists M.
unfold is_midpoint in H4.
spliter.
split.
unfold Between_H.
repeat split.
apply between_symmetry.
eapply between_exchange4.
apply H3.
assumption.
intro.
treat_equalities.

apply between_symmetry in H.
apply between_egality in H.
treat_equalities.
tauto.
apply between_symmetry.
assumption.
intro.
treat_equalities.
tauto.
assumption.
unfold Between_H.
repeat split.
assumption.
intro.
treat_equalities.
tauto.
intro.
treat_equalities.
tauto.
assumption.

apply False_ind.
apply H0.
assert(exists M, is_midpoint M A B) by(apply midpoint_existence).
ex_and H3 M.
exists M.
unfold is_midpoint in H4.
spliter.
split.
unfold Between_H.
repeat split.
assumption.
intro.
treat_equalities.
tauto.
intro.
treat_equalities.
tauto.
assumption.

unfold Between_H.
repeat split.

eapply between_exchange4.
apply between_symmetry.
apply H3.
apply between_symmetry.
assumption.
intro.
treat_equalities.
tauto.
intro.
treat_equalities.
intuition.
assumption.
Qed.


Lemma axiom_hcong_3 : forall A B C A' B' C',
   Col_H A B C -> Col_H A' B' C' ->
  disjoint A B B C -> disjoint A' B' B' C' -> 
  Hcong A B A' B' -> Hcong B C B' C' -> Hcong A C A' C'.
Proof.
unfold Hcong.
intros.
assert(Bet A B C).
eapply col_disjoint_bet.
assumption.
assumption.

assert(Bet A' B' C').
eapply col_disjoint_bet.
assumption.
assumption.
eapply l2_11;eauto.
Qed.

(** We define the notion of half ray. **)

Definition HLine := @Couple Tpoint.
Definition hlin := build_couple Tpoint.

(** We define incidence with an half ray **)

Definition IncidentH (A : Tpoint) (l : HLine) := 
 A = (P1 l) \/ A = (P2 l) \/ Between_H (P1 l) A (P2 l) \/  Between_H (P1 l) (P2 l) A.

(** Definition of half ray equality. **)

Definition hEq : relation HLine := fun h1 h2 => (P1 h1) = (P1 h2) /\ 
                          ((P2 h1) = (P2 h2) \/ Between_H (P1 h1) (P2 h2) (P2 h1) \/ 
                                                  Between_H (P1 h1) (P2 h1) (P2 h2)).

Infix "=h=" := hEq (at level 70):type_scope.

(** This is an equivalence relation. *)

Lemma hEq_refl : forall h, h =h= h.
Proof.
intros.
unfold hEq.
tauto.
Qed.

Lemma hEq_sym : forall h1 h2, h1 =h= h2 -> h2 =h= h1.
Proof.
intros.
unfold hEq in *.
spliter.
split.
auto.
rewrite H in H0.
induction H0.
left.
auto.
tauto.
Qed.

Lemma hEq_trans : forall h1 h2 h3, h1 =h= h2 -> h2 =h= h3 -> h1 =h= h3.
Proof.
intros.
unfold hEq in *.
spliter.
rewrite <-H in *.
rewrite <-H0 in *.

split.
reflexivity.

induction H2;
induction H1.
left.
rewrite H2.
assumption.

induction H1.
right; left.
rewrite H2.
assumption.
right; right.
rewrite H2.
assumption.

induction H2.
right; left.
rewrite <-H1.
assumption.
right; right.
rewrite <-H1.
assumption.


induction H2; induction H1; spliter.
right; left.
repeat split.
eapply between_exchange4.
apply H1.
unfold Between_H in *.
spliter.
assumption.
rewrite H0.
apply (Cond h3).
intro.

rewrite H3 in H1.
unfold Between_H in *.
spliter.
apply between_symmetry in H2.
apply between_symmetry in H1.
assert(P2 h2 = P2 h1).
eapply between_egality.
apply H1.
assumption.
auto.
intro.
assert(HH:= Cond h1).
contradiction.

induction(eq_dec_points (P2 h1) (P2 h3)).
left.
assumption.

assert((Bet (P1 h1) (P2 h3) (P2 h1) \/ Bet (P1 h1) (P2 h1) (P2 h3)) /\
  (P1 h1 <> P2 h3 /\ P2 h3 <> P2 h1 /\ P1 h1 <> P2 h1)).
split.
eapply l5_1.
2: apply H1.
unfold Between_H in *.
spliter.
assumption.
unfold Between_H in *.
spliter.
assumption.
repeat split.
unfold Between_H in *.
spliter.
assumption.
auto.
apply (Cond h1).

right.
unfold Between_H.
spliter.
induction H4.
left.
repeat split;
assumption.
right.
repeat split;
assumption.

induction(eq_dec_points (P2 h1) (P2 h3)).
left.
assumption.

assert((Bet (P1 h1) (P2 h3) (P2 h1) \/ Bet (P1 h1) (P2 h1) (P2 h3)) /\ 
 (P1 h1 <> P2 h3 /\ P2 h3 <> P2 h1 /\ P1 h1 <> P2 h1)).
split.
eapply l5_3.
apply H1.
unfold Between_H in *.
spliter.
assumption.
repeat split.
unfold Between_H in *.
spliter.
assumption.
auto.
apply (Cond h1).

right.
unfold Between_H.
spliter.
induction H4.
left.
repeat split;
assumption.
right.
repeat split;
assumption.

right; right.
unfold Between_H in *.
spliter.
repeat split.
eapply between_exchange4.
apply H2.
assumption.
apply (Cond h1).

intro.

rewrite <-H9 in H1.
apply between_symmetry in H2.
apply between_symmetry in H1.
assert(P2 h2 = P2 h1).
eapply between_egality.
apply H2.
assumption.
auto.
assumption.
Qed.

Instance hEq_Equiv : Equivalence hEq.
Proof.
split.
unfold Reflexive.
apply hEq_refl.
unfold Symmetric.
apply hEq_sym.
unfold Transitive.
apply hEq_trans.
Qed.

(** We define the concept of angle. *)

Definition Angle : Type := @Triple Tpoint.
Definition angle := build_triple Tpoint.

(**  The congruence of angles of Hilbert is the same as the congruence of angles of Tarski. *)

Definition Hconga : relation Angle := fun A1 A2 => Conga  (V1 A1) (V A1) (V2 A1)  (V1 A2) (V A2) (V2 A2).

(** This is an equivalence relation. *)

Lemma hconga_refl : forall a, Hconga a a.
Proof.
intros.
unfold Hconga.
assert(H:= Pred a).
spliter.
apply conga_refl.
assumption.
assumption.
Qed.

Lemma hconga_sym : forall a b, Hconga a b -> Hconga b a.
Proof.
intros.
unfold Hconga in *.
spliter.
apply conga_sym.
assumption.
Qed.

Lemma hconga_trans : forall a b c, Hconga a b -> Hconga b c -> Hconga a c.
Proof.
intros.
unfold Hconga in *.
eapply conga_trans.
apply H.
assumption.
Qed.

Instance hconga_Equiv :  Equivalence Hconga.
split.
unfold Reflexive.
apply hconga_refl.
unfold Symmetric.
apply hconga_sym.
unfold Transitive.
apply hconga_trans.
Qed.



Lemma exists_not_incident : forall A B : Tpoint, forall  HH : A <> B , exists C, ~ Incident C (Lin A B HH).
Proof.
intros.
unfold Incident.
assert(HC:=l6_25 A B HH).
ex_and HC C.
exists C.
intro.
apply H.
simpl in H0.
Col.
Qed.


Definition line_of_hline := fun hl => Lin (P1 hl) (P2 hl) (Cond hl).

Definition same_side := fun A B l => exists P, cut l A P /\ cut l B P.

(** Same side predicate corresponds to one_side of Tarski. *)

Lemma same_side_one_side : forall A B l, same_side A B l -> one_side (P1 l) (P2 l) A B.
Proof.
unfold same_side.
intros.
ex_and H P.
apply cut_two_sides in H.
apply cut_two_sides in H0.
eapply l9_8_1.
apply H.
apply H0.
Qed.

Lemma one_side_same_side : forall A B l, one_side (P1 l) (P2 l) A B -> same_side A B l.
Proof.
intros.
unfold same_side.
unfold one_side in H.
ex_and H P.
exists P.
unfold cut.
unfold Incident.
unfold two_sides in H.
unfold two_sides in H0.
spliter.
repeat split; auto.
ex_and H6 T.
exists T.
unfold Between_H.
repeat split; auto.
intro.
subst T.
contradiction.
intro.
subst T.
contradiction.
intro.
subst P.
apply between_identity in H7.
subst T.
contradiction.
ex_and H3 T.
exists T.
unfold Between_H.
repeat split; auto.
intro.
subst T.
contradiction.
intro.
subst T.
contradiction.
intro.
subst P.
apply between_identity in H7.
subst T.
contradiction.
Qed.


Definition outH := fun P A B => Between_H P A B \/ Between_H P B A \/ (P <> A /\ A = B).

(** This is equivalent to the out predicate of Tarski. *)

Lemma outH_out : forall P A B, outH P A B -> out P A B.
Proof.
unfold outH.
unfold out.
intros.
induction H.
unfold Between_H in H.
spliter.
repeat split; auto.
induction H.
unfold Between_H in H.
spliter.
repeat split; auto.
spliter.
repeat split.
auto.
subst B.
auto.
subst B.
left.
apply between_trivial.
Qed.

Lemma out_outH : forall P A B, out P A B -> outH P A B.
unfold out.
unfold outH.
intros.
spliter.
induction H1.

induction (eq_dec_points A B).
right; right.
split; auto.
left.
unfold Between_H.
repeat split; auto.


induction (eq_dec_points A B).
right; right.
split; auto.
right; left.
unfold Between_H.
repeat split; auto.
Qed.

(** Definition of a point inside an angle. *)

Definition InAngleH a P := 
 (exists M, Between_H (V1 a) M (V2 a) /\ ((outH (V a) M P) \/ M = (V a))) \/ 
                                   outH (V a) (V1 a) P \/ outH (V a) (V2 a) P.

(** This is (almost) equivalent to the same notion in Tarski's. *)

Lemma in_angle_equiv : forall a P, (P <> (V a) /\ InAngleH a P) <-> InAngle P (V1 a) (V a) (V2 a).
Proof.
unfold InAngle.
unfold InAngleH.

intros.
split.
intros.
assert(HH:= Pred a).
spliter.
repeat split; try auto.
induction H2.
ex_and H2 M.
exists M.
unfold Between_H in H2.
spliter.
split.
assumption.
induction H3.
right.
apply outH_out.
assumption.
left.
assumption.

induction H2.
exists (V1 a).
split.
apply between_symmetry.
apply between_trivial.
right.
apply outH_out.
assumption.
exists (V2 a).
split.
apply between_trivial.
right.
apply outH_out.
assumption.


intros.
spliter.
split.
assumption.
ex_and H2 M.
induction H3.
subst M.
left.
exists (V a).
unfold Between_H.
repeat split; try auto.
intro.
rewrite H3 in *.
apply between_identity in H2.
contradiction.

induction(eq_dec_points M (V1 a)).
subst M.
right.
left.
apply out_outH.
assumption.
induction(eq_dec_points M (V2 a)).
subst M.
right.
right.
apply out_outH.
assumption.

left.
exists M.
unfold Between_H.
repeat split; try auto.
intro.
rewrite H6 in *.
apply between_identity in H2.
rewrite H2 in *.
tauto.
left.
apply out_outH.
assumption.
Qed.

Lemma in_angleH_in_angle : forall a P, (P <> (V a) /\ InAngleH a P) -> InAngle P (V1 a) (V a) (V2 a).
Proof.
intros.
edestruct in_angle_equiv.
apply H0 in H.
assumption.
Qed.

(** The 2D version of the fourth congruence axiom **)

Lemma outH_in_angleH_colH : forall a P, outH (V a) (V1 a) (V2 a) -> InAngleH a P -> Col_H (V a) (V1 a) P.
Proof.
intros.
apply cols_coincide_2.
apply outH_out in H.
induction(eq_dec_points P (V a)).
subst P.
Col.
assert(HH:=in_angleH_in_angle a P (conj H1 H0)).
assert(out (V a) (V1 a) P).
apply (in_angle_out _ _ (V2 a)).
assumption.
assumption.
apply out_col in H2.
assumption.
Qed.

Lemma incident_col : forall M l, Incident M l -> Col M (P1 l)(P2 l).
Proof.
unfold Incident.
intros.
assumption.
Qed.

Lemma col_incident : forall M l, Col M (P1 l)(P2 l) -> Incident M l.
Proof.
unfold Incident.
intros.
assumption.
Qed.

Lemma Bet_Between_H : forall A B C, 
 Bet A B C -> A<>B -> B<>C -> Between_H A B C.
Proof.
intros.
unfold Between_H.
repeat split;try assumption.
intro.
subst.
treat_equalities.
intuition.
Qed.

Lemma aux : forall (h h1 : HLine), 
 P1 h = P1 h1 ->
 P2 h1 <> P1 h.
Proof.
intros.
intro.
rewrite H in H0.
assert (T:= Cond h1).
auto.
Qed.

Lemma axiom_hcong_4_existence : 
 forall a h P, 
 ~Incident P (line_of_hline h) -> ~Between_H (V1 a)(V a)(V2 a) ->
  exists h1, (P1 h) = (P1 h1) /\ 
 (forall CondAux : P1 h = P1 h1,  
       Hconga a (angle (P2 h) (P1 h) (P2 h1) (conj (sym_not_equal (Cond h)) (aux h h1 CondAux)))
        /\ (forall M, ~Incident M (line_of_hline h) /\ InAngleH (angle (P2 h) (P1 h) (P2 h1) (conj (sym_not_equal (Cond h)) (aux h h1 CondAux))) M
      -> same_side P M  (line_of_hline h))).
Proof.
intros.

assert (~Bet (V1 a) (V a) (V2 a)) by
 (intro;apply H0;
 assert (T:=Pred a);
 apply Bet_Between_H;intuition).

clear H0; rename H1 into H0.

assert(HP:=Pred a).
spliter.
assert(HC:=Cond h).
unfold Incident in H.
simpl in H.

induction (Col_dec (V1 a) (V a) (V2 a)).
induction H3.
contradiction.

induction H3.

exists h.
(* erreur ici *)
split.
reflexivity.
intros.
unfold Hconga.
simpl.
split.
eapply l11_21_b.
unfold out.
repeat split; auto.
unfold out.
repeat split; auto.
left.
apply between_trivial.
intros.
spliter.
unfold InAngleH in H5.
simpl in H5.
induction H5.
ex_and H5 M0.
induction H6.
apply outH_out in H6.
apply out_col in H6.
unfold Between_H in H5.
spliter.
apply between_identity in H5.
subst M0.
unfold Incident in H4.
simpl in H4.
apply False_ind.
apply H4.
Col.
subst M0.
unfold Between_H in H5.
spliter.
tauto.

induction H5.
apply outH_out in H5.
apply out_col in H5.
unfold Incident in H4.
simpl in H4.
apply False_ind.
apply H4.
Col.

apply outH_out in H5.
apply out_col in H5.
unfold Incident in H4.
simpl in H4.
apply False_ind.
apply H4.
Col.

exists h.
split.
reflexivity.
intros.
unfold Hconga.
simpl.
split.
eapply l11_21_b.
unfold out.
repeat split; auto.
left.
apply between_symmetry.
assumption.
apply out_trivial.
auto.
intros.
spliter.
unfold InAngleH in H5.
simpl in H5.
induction H5.
ex_and H5 M0.
unfold Between_H in H5.
spliter.
induction H6.
apply outH_out in H6.
apply between_identity in H5.
subst M0.
apply out_col in H6.
unfold Incident in H4.
simpl in H4.
apply False_ind.
apply H4.
Col.
subst M0.
apply between_identity in H5.
contradiction.
induction H5.
unfold Incident in H4.
simpl in H4.
apply outH_out in H5.
apply out_col in H5.
apply False_ind.
apply H4.
Col.
unfold Incident in H4.
simpl in H4.
apply outH_out in H5.
apply out_col in H5.
apply False_ind.
apply H4.
Col.

(** general case **)

assert(~Col (P2 h) (P1 h) P).
intro.
apply H.
Col.

assert(HH:=angle_construction_1 (V1 a)(V a)(V2 a) (P2 h) (P1 h) P H3 H4).
ex_and HH C.

assert((P1 h) <> C).
intro.
subst C.
unfold one_side in H6.
ex_and H6 X.
unfold two_sides in *.
spliter.
apply H11.
Col.

exists (hlin (P1 h) C H7).
simpl.
split.
reflexivity.
intros.
unfold Hconga.
simpl.
split.
assumption.
intros.

spliter.

assert(M <> V (angle (P2 h) (P1 h) C (conj (sym_not_equal (Cond h)) (sym_not_equal H7))) /\
     InAngleH (angle (P2 h) (P1 h) C (conj (sym_not_equal (Cond h)) (sym_not_equal H7))) M).
simpl.
split.
intro.
subst M.
apply H8.
unfold Incident.
simpl.
Col.
assumption.

assert(HH:= (in_angleH_in_angle (angle (P2 h) (P1 h) C (conj (sym_not_equal (Cond h)) (sym_not_equal H7))) M H10)).
simpl in *.


apply in_angle_one_side in HH.

assert(HS:=one_side_same_side P M (line_of_hline h)).
apply HS.
simpl.
eapply one_side_transitivity.
apply invert_one_side.
apply one_side_symmetry.
apply H6.
apply one_side_symmetry.
apply invert_one_side.
assumption.
unfold one_side in H6.
ex_and H6 T.
unfold two_sides in *.
spliter.
Col.
unfold Incident in H8.
simpl in H8.
intro.
apply H8.
Col.
Qed.

Definition hline_construction a h P hc H := 
 (P1 h) = (P1 hc) /\
 Hconga a (angle (P2 h) (P1 h) (P2 hc) (conj (sym_not_equal (Cond h)) H)) /\
  (forall M, InAngleH (angle (P2 h) (P1 h) (P2 hc) (conj (sym_not_equal (Cond h)) H)) M ->
   same_side P M  (line_of_hline h)).


Lemma same_side_trans :
 forall A B C l,
  same_side A B l -> same_side B C l -> same_side A C l.
Proof.
intros.
apply one_side_same_side.
apply same_side_one_side in H.
apply same_side_one_side in H0.
eapply one_side_transitivity.
apply H.
assumption.
Qed.

Lemma same_side_sym :
 forall A B l,
  same_side A B l -> same_side B A l.
Proof.
intros.
apply one_side_same_side.
apply same_side_one_side in H.
apply one_side_symmetry.
assumption.
Qed.

Lemma in_angleH_trivial :
 forall A B C H,
  InAngleH (angle A B C H) A /\ InAngleH (angle A B C H) C.
Proof.
intros.
elim H.
intros.
unfold InAngleH.
simpl.
split.
right; left.
apply out_outH.
apply out_trivial.
assumption.
right; right.
apply out_outH.
apply out_trivial.
assumption.
Qed.

Lemma axiom_hcong_4_unicity :
  forall a h P h1 h2 HH1 HH2,
  ~Incident P (line_of_hline h) -> ~Between_H (V1 a)(V a)(V2 a) ->
  hline_construction a h P h1 HH1 -> hline_construction a h P h2 HH2 ->
  h1 =h= h2.
Proof.
intros.

assert (~Bet (V1 a) (V a) (V2 a)) by
 (intro;apply H0;
 assert (T:=Pred a);
 apply Bet_Between_H;intuition).

clear H0.
rename H3 into H0.

unfold hEq.
unfold hline_construction in *.
spliter.
split.
rewrite H1 in H2.
assumption.

unfold Hconga in *.
simpl in *.

assert(Conga (P2 h)(P1 h)(P2 h1) (P2 h)(P1 h)(P2 h2)).
eapply conga_trans.
apply conga_sym.
apply H5.
assumption.

apply l11_22_aux in H7.
induction(eq_dec_points (P2 h1) (P2 h2)).
left.
assumption.

induction H7.
unfold out in H7.
spliter.
induction H10.
rewrite <-H1.
rewrite H2 in *.
right; right.
unfold Between_H.
repeat split; auto.
rewrite <-H1.
rewrite H2 in *.
right; left.
unfold Between_H.
repeat split; auto.

assert(Conga (P2 h)(P1 h)(P2 h2) (P2 h) (P1 h)(P2 h1)).
eapply conga_trans.
apply conga_sym.
apply H3.
assumption.


induction(Col_dec (V1 a) (V a) (V2 a)).
assert(HC0:=col_conga_col (V1 a)(V a)(V2 a)(P2 h)(P1 h)(P2 h1) H10 H5).
assert(HC1:=col_conga_col (V1 a)(V a)(V2 a)(P2 h)(P1 h)(P2 h2) H10 H3).
unfold two_sides in H7.
spliter.
apply False_ind.
apply H11.
Col.

assert(H11:=H10).

eapply ncol_conga_ncol in H10.
2: apply H5.
eapply ncol_conga_ncol in H11.
2: apply H3.

assert(HH4 := H4 (P2 h2)).
assert(HH6 := H6 (P2 h1)).

assert(same_side (P2 h1) (P2 h2) (line_of_hline h)).
eapply same_side_trans.
apply same_side_sym.
apply HH6.

assert(P2 h <> P1 h /\ P2 h1 <> P1 h).
split.
exact(sym_not_equal(Cond h)).
rewrite H1.
exact(sym_not_equal(Cond h1)).

assert(HH:= in_angleH_trivial (P2 h)(P1 h)(P2 h1) H12).
spliter.
apply H14.
apply HH4.
assert(P2 h <> P1 h /\ P2 h2 <> P1 h).
split.
exact(sym_not_equal(Cond h)).
rewrite H2.
exact(sym_not_equal(Cond h2)).

assert(HH:= in_angleH_trivial (P2 h)(P1 h)(P2 h2)H12).
spliter.
apply H14.

apply same_side_one_side in H12.
simpl in H12.
apply invert_one_side in H12.

apply l9_9 in H7.
contradiction.
Qed.


Lemma axiom_cong_5': 
 forall (A B C A' B' C' : Tpoint) (H1 : B <> A /\ C <> A)
          (H2 : B' <> A' /\ C' <> A') ,
 forall H3 : (A<>B /\ C<>B), forall H4: A' <> B' /\ C' <> B',
  Hcong A B A' B' ->
  Hcong A C A' C' ->
  Hconga {| V1 := B ; V := A ; V2:= C ; Pred := H1 |}
         {| V1 := B'; V := A'; V2:= C'; Pred := H2 |} ->
  Hconga {| V1 := A ; V := B ; V2:= C ; Pred := H3 |}
         {| V1 := A'; V := B'; V2:= C'; Pred := H4 |}.
Proof.
intros A B C A' B' C'.
intros.

unfold Hconga in *.
simpl in *.


assert (T:=l11_49 B A C B' A' C' ).
unfold Hcong.
intuition.
Qed.

End T.

Section Hilbert_to_Tarski.

Context `{T:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

Instance Hilbert_follow_from_Tarski : Hilbert.
Proof.
 exact (Build_Hilbert Tpoint Line Eq Eq_Equiv Incident 
       axiom_line_existence axiom_line_unicity axiom_two_points_on_line axiom_plan
       Between_H axiom_between_col axiom_between_comm axiom_between_out
       axiom_between_only_one axiom_between_one axiom_pasch
       axiom_euclid_existence axiom_euclid_unicity
       Hcong axiom_hcong_trans axiom_hcong_refl axiom_hcong_1_existence axiom_hcong_1_unicity
       axiom_hcong_3 Hconga axiom_cong_5' line_of_hline aux axiom_hcong_4_existence axiom_hcong_4_unicity).
Qed.

End Hilbert_to_Tarski.