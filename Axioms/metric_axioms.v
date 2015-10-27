(* Definition of a metric geometry following the book
by Millman and Parker.
 Geometry a metric approach with models.
It is a formalization of Birkhoff axioms.
 *)

Require Import Reals.
Require Export Setoid.

Open Scope R_scope.

Class incidence_geometry (Point:Type) (Line:Type) := {
 EqL : Line -> Line -> Prop;
 EqL_Equiv : Equivalence EqL;
 Incid : Point -> Line -> Prop;
 line_existence : forall A B, A<>B -> exists l, Incid A l /\ Incid B l;
 line_unicity :  forall A B l m, A <> B -> Incid A l -> Incid B l -> Incid A m -> Incid B m -> EqL l m;
 two_points_on_line : forall  l, exists A, exists B, Incid B l /\ Incid A l /\ A <> B;
 ColH := fun A B C => exists l, Incid A l /\ Incid B l /\ Incid C l;
 plan : exists A, exists B, exists C, ~ ColH A B C
}.

Class distance_function (Point:Type) := {
 d : Point -> Point -> R;
 d_pos : forall P Q, d P Q > 0;
 d_identity : forall P Q, d P Q = 0 <-> P=Q;
 d_sym : forall P Q, d P Q = d Q P
}.

Section bijections.

Variables A B : Type.
Definition injective (f : A -> B) := forall x y : A, f x = f y -> x = y.
Definition surjective (f : A -> B) := forall y : B,  exists x : A, f x = y.
Definition bijective (f : A -> B) : Prop := injective f /\ surjective f.

End bijections.

Section S1.

Context `{Mincid: incidence_geometry}.
Context `{Mdist: distance_function Point}.

Definition is_rule (f:Point -> R) l :=
 bijective Point  R f /\ 
 (forall P Q : Point, Incid P l -> Incid Q l ->  Rabs (f P - f Q) = d P Q).

Class metric_geometry := {
 ruler_postulate : forall l : Line, exists f, is_rule f l
}.

End S1.

Section MetricToTarski.

Context `{Mmetric: metric_geometry}.

Definition between A B C :=
 ColH A B C /\
 d A B  + d B C = d A C.

Lemma d_zero : forall A, d A A = 0.
Proof.
intros.
apply d_identity.
reflexivity.
Qed.

Lemma between_identity : forall A B, between A B A -> A = B.
Proof.
intros.
unfold between in *.
destruct H.
replace (d B A) with (d A B) in * by apply d_sym.
rewrite d_zero in *.
replace (d A B + d A B) with (2*d A B) in * by ring.
apply d_identity.

apply Rmult_integral in H0.
elim H0.
intro.
assert (2<>0).
discrR.
intuition.
auto.
Qed.

Definition cong A B C D :=
  d A B = d C D.

Lemma cong_identity : forall A B C, cong A B C C -> A = B.
Proof.
intros.
unfold cong in *.
rewrite d_zero in H.
apply d_identity.
assumption.
Qed.

Lemma cong_pseudo_reflexivity : forall A B, cong A B B A.
Proof.
apply d_sym.
Qed.

Lemma cong_inner_transitivity : forall A B C D E F,
 cong A B  C D -> cong A B E F -> cong C D  E F.
Proof.
unfold cong;intros.
rewrite <- H.
assumption.
Qed.

Lemma lower_dim : exists A, exists B, exists C, 
 ~ (between A B C \/ between B C A \/ between C A B).
Proof.
assert (T:= plan).
destruct T as [A [B [C HABC]]].
unfold ColH in HABC.
exists A.
exists B.
exists C.
intro.
decompose [or] H;clear H.
unfold between in H0.
decompose [and] H0.
unfold ColH in *.
decompose [ex and] H.
apply HABC.
exists x.
repeat split;assumption.

unfold between in H1.
decompose [and] H1.
unfold ColH in *.
decompose [ex and] H.
apply HABC.
exists x.
repeat split;assumption.

unfold between in H1.
decompose [and] H1.
unfold ColH in *.
decompose [ex and] H.
apply HABC.
exists x.
repeat split;assumption.
Qed.

(** To obtain Tarski's neutral geometry we need also to prove : 
 1-  inner_pasch,
 In the book by Millman and Parker this is an axiom stated as Hilbert's version of Pasch.
 The plane separation axiom is proved equivalent to Pasch's axiom. So there is not much to be proved.
 2-  five segments 
 To prove five segments axiom, Protractor geometry + SAS is needed.
*)

End MetricToTarski.