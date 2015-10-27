Require Export GeoCoq.Tarski_dev.Ch14_order.
Require Export GeoCoq.Tarski_dev.Annexes.quadrilaterals.

Section T15.

Context `{MT:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

(** Definition 15.1. *)
(** Length of a segment.*)

Definition length O E E' A B L :=
 O<>E /\ Col O E L /\ leP O E E' O L /\ Cong O L A B.

Definition is_length O E E' A B L :=
 length O E E' A B L \/ (O=E /\ O=L).

(** Lemma 15.2 *)
(** Cong corresponds to length equality.*)
(** Le corresponds to length inequality.*)

Lemma length_pos : 
 forall O E E' A B L,
 length O E E' A B L ->
 leP O E E' O L.
Proof.
intros.
unfold length in *.
tauto.
Qed.

Lemma length_id_1 : 
 forall O E E' A B,
 length O E E' A B O -> A=B.
Proof.
intros.
unfold length in *.
spliter.
treat_equalities.
reflexivity.
Qed.

Lemma length_id_2 : 
 forall O E E' A,
 O<>E ->
 length O E E' A A O.
Proof.
intros.
unfold length.
repeat split.
assumption.
Col.
unfold leP.
tauto.
Cong.
Qed.

Lemma length_id :
 forall O E E' A B,
 length O E E' A B O <-> (A=B /\ O<>E).
Proof.
intros.
split.
intros.
split.
eauto using length_id_1.
unfold length in *.
tauto.
intros.
spliter. subst.
apply length_id_2.
assumption.
Qed.

Lemma length_eq_cong_1 :
 forall O E E' A B C D AB,
 length O E E' A B AB ->
 length O E E' C D AB ->
 Cong A B C D.
Proof.
intros.
unfold length in *.
spliter.
apply cong_transitivity with O AB;Cong.
Qed.

Lemma length_eq_cong_2 :
 forall O E E' A B C D AB,
 length O E E' A B AB ->
 Cong A B C D ->
 length O E E' C D AB.
Proof.
intros.
unfold length in *.
spliter.
repeat split;try assumption.
apply cong_transitivity with A B;Cong.
Qed.



Lemma ltP_pos : forall O E E' A, ltP O E E' O A  -> Ps O E A.
Proof.
intros.
unfold ltP in H.
ex_and H A'.

assert(~Col O E E' /\ Col O E A).
unfold diff in H.
ex_and H X.
unfold sum in H1.
spliter.
unfold Ar2 in H1.
tauto.
spliter.

assert(HH:= diff_A_O O E E' A H1 H2).
assert(A = A').
apply(diff_unicity O E E' A O A A'); assumption.
subst A'.
assumption.
Qed.

Lemma bet_leP : forall O E E' AB CD, Bet O AB CD
                        -> leP O E E' O AB -> leP O E E' O CD -> leP O E E' AB CD.
Proof.
intros.
unfold leP in *.
induction H0; induction H1.

unfold ltP in H0.
unfold ltP in H1.
ex_and H0 P.
ex_and H1 Q.

assert(Ar2 O E E' AB CD P /\ Col O E Q).
unfold diff in H0.
ex_and H0 X.
unfold diff in H1.
ex_and H1 Y.
unfold sum in H4.
unfold sum in H5.
spliter.
unfold Ar2 in *.
spliter.
repeat split; Col.
unfold Ar2 in H4.
spliter.

assert(P = AB).
apply (diff_unicity O E E' AB O); auto.
apply diff_A_O; auto.
subst P.

assert(Q = CD).
apply (diff_unicity O E E' CD O); auto.
apply diff_A_O; auto.
subst Q.
clean_duplicated_hyps.

induction(eq_dec_points AB CD).
right.
assumption.
left.
clear H0 H1.


assert(HH:=opp_exists O E E' H4 AB H6).
ex_and HH AB'.

assert(exists P, sum O E E' CD AB' P).
apply(sum_exists O E E' H4 CD AB'); Col.
unfold opp in H0.
unfold sum in H0.
spliter.
unfold Ar2 in H0.
tauto.
ex_and H1 P.


unfold ltP.
exists P.
split.
unfold diff.
exists AB'.
split; auto.


assert(diff O E E' CD AB P).
unfold diff.
exists AB'.
split; auto.

apply diff_sum in H1.
induction (eq_dec_points AB O).
subst AB.
unfold Ps in H2.
unfold out in H2.
spliter.
tauto.

assert(Parallelogram_flat O AB CD P).
apply (sum_cong O E E' H4 AB P CD H1).
left.
assumption.
unfold Parallelogram_flat in H10.
spliter.

assert(Bet CD P O).
apply(l4_6 O AB CD CD P O).
assumption.
repeat split; Cong.
unfold Ps.
unfold out.
repeat split.
intro.
subst P.
assert(AB=CD).
apply cong_symmetry in H13.
apply (cong_identity _ _ O); Cong.
subst CD.
tauto.
intro.
subst E.
apply H4.
Col.
unfold Ps in H3.
unfold out in H3.
spliter.
induction H17.
left.
apply (between_exchange4 O P CD E); Between.
apply (l5_3 O P E CD); Between.
subst CD.
apply between_identity in H.
subst AB.
right; auto.
subst AB.
left; assumption.
subst AB.
subst CD.
right; auto.
Qed.



Lemma leP_bet : forall O E E' AB CD, leP O E E' AB CD 
                        -> leP O E E' O AB -> leP O E E' O CD -> Bet O AB CD.
Proof.
intros.
unfold leP in H.
induction H.
unfold ltP in H.
ex_and H X.
apply diff_sum in H.

assert(out O AB X \/ AB=O).
unfold leP in H0.
induction H0.
left.
apply ltP_pos in H0.
unfold Ps in *.
eapply (l6_7 _ _ E); auto.
apply l6_6.
assumption.
right.
auto.

induction H3.

apply (l14_36_a O E E' AB X CD); auto.
subst AB.
apply between_trivial2.
subst CD.
apply between_trivial.
Qed.


Lemma length_Ar2 : forall O E E' A B AB, length O E E' A B AB
                                 -> (Col O E AB /\ ~Col O E E') \/ AB = O.
Proof.
intros.
unfold length in H.
spliter.

unfold leP in H1.
induction H1.
left.
split.
assumption.
unfold ltP in H1.
ex_and H1 P.
unfold diff in H1.
ex_and H1 Q.
unfold sum in *.
spliter.
unfold Ar2 in *.
tauto.
right; auto.
Qed.

Lemma length_leP_le_1 :
 forall O E E' A B C D AB CD,
 length O E E' A B AB ->
 length O E E' C D CD ->
 leP O E E' AB CD ->
 le A B C D.
Proof.
intros.
unfold length in *.
spliter.
assert(Bet O AB CD).
apply (leP_bet O E E'); assumption.

prolong D C M' A B.
assert(HH:=symmetric_point_construction M' C).
ex_and HH M.
unfold is_midpoint in H11.
spliter.

assert(Cong A B C M).
apply (cong_transitivity _ _ C M'); Cong.

apply(le_transitivity _ _ C M).
unfold le.
exists M.
split; Between.

assert(le O AB O CD).
unfold le.
exists AB.
split; Cong.

apply(l5_6 O AB O CD C M C D).
repeat split; Cong.
apply (cong_transitivity _ _ A B); Cong.
Qed.


Lemma length_leP_le_2 :
 forall O E E' A B C D AB CD,
 length O E E' A B AB ->
 length O E E' C D CD ->
 le A B C D ->
 leP O E E' AB CD.
Proof.
intros.

assert(HH1:= length_Ar2 O E E' A B AB H).
assert(HH2:= length_Ar2 O E E' C D CD H0).
spliter.
unfold length in *.
spliter.
apply bet_leP; try assumption.

induction(eq_dec_points O CD).
subst CD.
apply cong_symmetry in H4.
apply cong_identity in H4.
subst D.
unfold le in H1.
ex_and H1 X.
apply between_identity in H1.
subst X.
apply cong_identity in H4.
subst B.
apply cong_identity in H7.
subst AB.
Between.
assert(le O AB O CD).

apply(l5_6 A B C D O AB O CD); Cong.
unfold le in H8.
ex_and H9 M.

induction HH1; induction HH2.
spliter.

unfold le in H1.
ex_and H1 P.

unfold leP in *.
induction H6; induction H3.
unfold ltP in *.
ex_and H6 X.
ex_and H3 Y.
apply diff_sum in H6.
apply diff_sum in H3.
apply sum_cong in H6; auto.
apply sum_cong in H3; auto.
unfold Parallelogram_flat in *.
spliter.
apply cong_symmetry in H19.
apply cong_identity in H19.
subst Y.
apply cong_symmetry in H23.
apply cong_identity in H23.
subst X.
clean_trivial_hyps.

assert(AB = M \/ is_midpoint O AB M).
apply(l7_20 O AB M); Cong.

unfold Ps in *.
assert(out O AB CD).
apply (l6_7 O AB E CD); auto.
apply l6_6.
assumption.
apply out_col in H3.
apply bet_col in H9.
apply col_permutation_2.

apply (col_transitivity_1 _ CD); Col.
induction H3.
subst M.
assumption.
unfold is_midpoint in H3.
spliter.

assert(out O AB CD).
unfold Ps in *.

apply (l6_7 O AB E CD); auto.
apply l6_6.
assumption.
assert(Bet AB O CD).

eapply (outer_transitivity_between _ _ M); Between.
intro.
subst M.
apply cong_identity in H6.
subst AB.
tauto.
unfold out in H18.
spliter.
induction H22.
assert(AB = O).
apply(between_egality _ _ CD); Between.
subst AB.
Between.
assert(Bet CD O CD).
apply (between_exchange3 AB); Between.
assert(O = CD).
apply between_egality in H23.
contradiction.
Between.
tauto.
right.
intro.
subst Y.
unfold Ps in H17.
unfold out in H17.
tauto.
right.
intro.
subst X.
unfold Ps in H16.
unfold out in H16.
tauto.
subst CD.
tauto.
subst AB.
Between.
subst CD.
tauto.
subst CD.
tauto.
subst AB.
Between.
subst CD.
tauto.
Qed.

Lemma l15_3 :
 forall O E E' A B C,
  sum O E E' A B C ->
  Cong O B A C.
Proof.
intros.
assert(Ar2 O E E' A B C).
unfold sum in H.
spliter.
assumption.
unfold Ar2 in H0.
spliter.
induction (eq_dec_points A O).
subst A.
assert(B = C).
apply (sum_unicity O E E' O B); auto.
apply sum_O_B; auto.
subst C.
Cong.
apply sum_cong in H; auto.
unfold Parallelogram_flat in H.
spliter.
Cong.
Qed.

(** Lemma 15.4. *)
(** Triangular equality. *)

Lemma length_unicity : forall O E E' A B AB AB', length O E E' A B AB -> length O E E' A B AB' -> AB = AB'.
Proof.
intros.
assert(Col O E AB /\ ~ Col O E E' \/ AB = O).
eapply (length_Ar2 O E E' A B AB); assumption.
assert(Col O E AB' /\ ~ Col O E E' \/ AB' = O).
eapply (length_Ar2 O E E' A B AB'); assumption.

unfold length in *.
spliter.
assert(Cong O AB O AB').
eCong.
assert(AB = AB' \/ is_midpoint O AB AB').
apply(l7_20 O AB AB').
ColR.
Cong.
induction H10.
assumption.
unfold is_midpoint in H10.
spliter.

induction H1; induction H2.
spliter.

unfold leP in *.
induction H4; induction H7.
unfold ltP in H4.
unfold ltP in H7.
ex_and H4 X.
ex_and H7 Y.
apply diff_sum in H4.
apply diff_sum in H7.
assert(X = AB').
apply(sum_O_B_eq O E E'); Col.
subst X.
assert(Y = AB).
apply(sum_O_B_eq O E E'); Col.
subst Y.
unfold Ps in *.
assert(out O AB AB').
eapply (l6_7 _ _ E).
assumption.
apply l6_6; assumption.
unfold out in H16.
spliter.
induction H18.
assert(AB = O).
eapply (between_egality _ _ AB'); Between.
subst AB.
apply cong_symmetry in H11.
apply cong_identity in H11.
auto.
assert(AB' = O).
eapply (between_egality _ _ AB); Between.
subst AB'.
apply cong_identity in H11.
auto.
subst AB.
apply cong_symmetry in H9.
apply cong_identity in H9.
auto.
subst AB'.
apply cong_identity in H9.
auto.
subst AB'.
apply cong_identity in H9.
auto.
subst AB'.
apply cong_identity in H9.
auto.
subst AB.
apply cong_symmetry in H9.
apply cong_identity in H9.
auto.
subst AB.
subst AB'.
reflexivity.
Qed.

Lemma length_cong : forall O E E' A B AB, length O E E' A B AB -> Cong A B O AB.
Proof.
intros.
unfold length in H.
spliter.
Cong.
Qed.

Lemma length_Ps : forall O E E' A B AB, AB <> O -> length O E E' A B AB -> Ps O E AB.
Proof.
intros.
unfold length in H0.
spliter.
unfold leP in H2.
induction H2.
unfold ltP in H2.
ex_and H2 X.
apply diff_sum in H2.
apply sum_cong in H2.
unfold Parallelogram_flat in H2.
spliter.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst X.
assumption.
unfold sum in H2.
spliter.
unfold Ar2 in H2.
tauto.
right.
intro.
subst X.
unfold Ps in H4.
unfold out in H4.
tauto.
subst AB.
tauto.
Qed.

Lemma length_not_col_null : forall O E E' A B AB, Col O E E' -> length O E E' A B AB -> AB=O.
Proof.
intros.
unfold length in H0.
spliter.
unfold leP in H2.
induction H2.
unfold ltP in H2.
ex_and H2 X.
apply diff_sum in H2.
unfold sum in H2.
spliter.
unfold Ar2 in H2.
spliter.
contradiction.
auto.
Qed.

Lemma triangular_equality_equiv : 

(forall O E A , O<>E -> (forall E' B C AB BC AC,
  Bet A B C ->
  length O E E' A B AB ->
  length O E E' B C BC ->
  length O E E' A C AC ->
  sum O E E' AB BC AC)) 
<->
(forall O E E' A B C AB BC AC,
  O<>E ->
  Bet A B C ->
  length O E E' A B AB ->
  length O E E' B C BC ->
  length O E E' A C AC ->
  sum O E E' AB BC AC).
Proof.
split.
intros.
assert(HH:= H O E A H0).
apply (HH E' B C); auto.
intros.
assert(HH:= H O E E' A B C AB BC AC H0 H1 H2 H3 H4).
assumption.
Qed.


Lemma not_triangular_equality1 :
 forall O E A , O<>E -> ~( forall E' B C AB BC AC,
  Bet A B C ->
  length O E E' A B AB ->
  length O E E' B C BC ->
  length O E E' A C AC ->
  sum O E E' AB BC AC).
Proof.
intros.
intro.
assert(HH:=(H0 E A A O O O)).
assert(Bet A A A); Between.
assert(length O E E A A O).
apply(length_id_2); auto.
assert(HHH:= (HH H1 H2 H2 H2)).
unfold sum in HHH.
spliter.
ex_and H4 X.
ex_and H5 Y.
unfold Ar2 in H3.
spliter.
apply H3.
Col.
Qed.

Definition sumg O E E' A B C := sum O E E' A B C \/ (~ (Ar2 O E E' A B B) /\ C = O).

Lemma triangular_equality :
 forall O E E' A B C AB BC AC,
  O<>E ->
  Bet A B C ->
  is_length O E E' A B AB ->
  is_length O E E' B C BC ->
  is_length O E E' A C AC ->
  sumg O E E' AB BC AC.
Proof.
intros O E E' A B C AB BC AC H H0 Hl1 Hl2 Hl3.

unfold is_length in *.

induction Hl1; induction Hl2; induction Hl3; try(spliter; contradiction).
unfold length in *.
spliter.
unfold leP in *.
induction H11; induction H8; induction H5.

(* General Case *)

unfold ltP in *.
ex_and H11 X.
ex_and H8 Y.
ex_and H5 Z.
apply diff_sum in H11.
apply diff_sum in H8.
apply diff_sum in H5.
assert(AB = X).
apply (sum_unicity O E E' O X).
assumption.
unfold sum in H11.
spliter.
unfold Ar2 in H11.
apply(sum_O_B); tauto.
subst X.

assert(BC = Y).
apply (sum_unicity O E E' O Y).
assumption.
unfold sum in H8.
spliter.
unfold Ar2 in H8.
apply(sum_O_B); tauto.
subst Y.

assert(AC = Z).
apply (sum_unicity O E E' O Z).
assumption.
unfold sum in H5.
spliter.
unfold Ar2 in H5.
apply(sum_O_B); tauto.
subst Z.

assert(forall A B : Tpoint,Col O E A -> Col O E B -> exists C : Tpoint, sum O E E' A B C).
apply(sum_exists O E E' ).
unfold sum in H11.
spliter.
unfold Ar2 in H11.
tauto.
assert(HS:= H16 AB BC H10 H7).
ex_and HS AC'.

assert(Bet O AB AC').
apply(l14_36_a O E E' AB BC AC' H17).
eapply (l6_7 _ _ E).
assumption.
apply l6_6.
assumption.

assert(HH:= l15_3 O E E' AB BC AC' H17).

assert(Cong O AC' A C).
apply(l2_11 O AB AC' A B C); Cong.
eCong.

assert(HP:= sum_pos_pos O E E' AB BC AC' H13 H14 H17).
assert(AC = AC').
apply(l6_11_unicity O A C E AC AC').
intro.
subst E.
tauto.
intro.
subst C.
apply between_identity in H0.
subst B.
apply cong_identity in H6.
subst AC.
unfold Ps in H15.
unfold out in H15.
tauto.
unfold Ps in H15.
assumption.
Cong.
unfold Ps in HP.
assumption.
Cong.
subst AC'.
left.
assumption.

(* Case AC = O *)

subst AC.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply between_identity in H0.
subst B.
apply cong_identity in H12.
subst AB.
apply cong_identity in H9.
subst BC.
unfold ltP in H8.
ex_and H8 X.
apply diff_sum in H0.
assert(X=O).
apply(sum_unicity O E E' O X).
apply sum_O_B.
unfold sum in H0.
spliter.
unfold Ar2 in H0.
tauto.
unfold Ps in H5.
apply out_col in H5.
Col.
assumption.
subst X.
unfold Ps in H5.
unfold out in H5.
tauto.

(* BC = O *)

subst BC.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
assert(Cong O AB O AC).
eCong.
unfold ltP in H11.
ex_and H11 X.
apply diff_sum in H9.
assert(X = AB).
apply (sum_unicity O E E' O X).
apply sum_O_B.
unfold sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold ltP in H5.
ex_and H5 Y.
apply diff_sum in H5.

assert(Y = AC).
apply (sum_unicity O E E' O Y).
apply sum_O_B.
unfold sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H13.
apply out_col in H13.
Col.
assumption.
subst Y.
assert(AB = AC).
apply(l6_11_unicity O A B E AB AC).
intro.
subst E.
unfold Ps in H13.
unfold out in H13.
tauto.
intro.
subst B.
apply cong_identity in H6.
subst AC.
unfold Ps in H13.
unfold out in H13.
tauto.
unfold Ps in H11.
assumption.
Cong.
unfold Ps in H13.
assumption.
Cong.
subst AB.
left.
apply sum_A_O.
unfold sum in H9.
unfold Ar2 in H9.
tauto.
unfold Ps in H11.
apply out_col in H11.
Col.

(* Case AC = O /\ BC = O *)

subst AC.
subst BC.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst B.
apply cong_identity in H12.
subst AB.
left.
apply sum_O_O.
unfold ltP in H11.
ex_and H11 X.
apply diff_sum in H5.
unfold sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O *)

subst AB.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.

assert(BC = AC).
apply(l6_11_unicity O A C E BC AC).
intro.
subst E.
tauto.
intro.
subst C.
apply cong_identity in H9.
subst BC.
unfold ltP in H8.
ex_and H8 X.
apply diff_sum in H8.
assert(X = O).
apply (sum_unicity O E E' O X).
apply sum_O_B.
unfold sum in H8.
unfold Ar2 in H8.
tauto;
unfold Ps in H13.
unfold Ps in H9.
apply out_col in H9.
Col.
assumption.
subst X.
unfold Ps in H9.
unfold out in H9.
tauto.
unfold ltP in H8.
ex_and H8 X.
apply diff_sum in H8.

assert(X = BC).
apply (sum_unicity O E E' O X).
apply sum_O_B.
unfold sum in H8.
unfold Ar2 in H8.
tauto;
unfold out in H13.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold Ps in H11.
assumption.
Cong.

unfold ltP in H5.
ex_and H5 X.
apply diff_sum in H5.
assert(X = AC).
apply (sum_unicity O E E' O X).
apply sum_O_B.
unfold sum in H5.
unfold Ar2 in H5.
tauto;
unfold out in H13.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold Ps in H11.
assumption.
Cong.
subst AC.
left.
apply sum_O_B.
unfold ltP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold sum in H5.
unfold Ar2 in H5.
tauto.
Col.

(* Case AB = O /\ AC = O *)

subst AC.
subst AB.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply cong_identity in H9.
subst BC.
left.
apply sum_O_O.
unfold ltP in H8.
ex_and H8 X.
apply diff_sum in H5.
unfold sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O /\ BC = O *)

subst AB.
subst BC.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.
apply cong_identity in H6.
subst AC.
left.
apply sum_O_O.
unfold ltP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O /\ BC = O /\ AC= O *)


treat_equalities.
assert(HH:=Col_dec O E E').
induction HH.
right.
split.
intro.
unfold Ar2 in H1.
spliter.
contradiction.
tauto.
left.
apply sum_O_O.
auto.
Qed.

Lemma length_O : forall O E E', O <> E -> length O E E' O O O.
Proof.
intros.
unfold length.
repeat split; Col.
unfold leP.
right;auto.
Cong.
Qed.


Lemma triangular_equality_bis :
 forall O E E' A B C AB BC AC,
  A <> B \/ A <> C \/ B <> C -> O<>E ->
  Bet A B C ->
  length O E E' A B AB ->
  length O E E' B C BC ->
  length O E E' A C AC ->
  sum O E E' AB BC AC.
Proof.
intros O E E' A B C AB BC AC.
intro HH0.
intros.

unfold length in *.
spliter.
unfold leP in *.
induction H11; induction H8; induction H5.

(* General Case *)

unfold ltP in *.
ex_and H11 X.
ex_and H8 Y.
ex_and H5 Z.
apply diff_sum in H11.
apply diff_sum in H8.
apply diff_sum in H5.
assert(AB = X).
apply (sum_unicity O E E' O X).
assumption.
unfold sum in H11.
spliter.
unfold Ar2 in H11.
apply(sum_O_B); tauto.
subst X.

assert(BC = Y).
apply (sum_unicity O E E' O Y).
assumption.
unfold sum in H8.
spliter.
unfold Ar2 in H8.
apply(sum_O_B); tauto.
subst Y.

assert(AC = Z).
apply (sum_unicity O E E' O Z).
assumption.
unfold sum in H5.
spliter.
unfold Ar2 in H5.
apply(sum_O_B); tauto.
subst Z.

assert(forall A B : Tpoint,Col O E A -> Col O E B -> exists C : Tpoint, sum O E E' A B C).
apply(sum_exists O E E' ).
unfold sum in H11.
spliter.
unfold Ar2 in H11.
tauto.
assert(HS:= H16 AB BC H10 H7).
ex_and HS AC'.

assert(Bet O AB AC').
apply(l14_36_a O E E' AB BC AC' H17).
eapply (l6_7 _ _ E).
assumption.
apply l6_6.
assumption.

assert(HH:= l15_3 O E E' AB BC AC' H17).

assert(Cong O AC' A C).
apply(l2_11 O AB AC' A B C); Cong.
eCong.

assert(HP:= sum_pos_pos O E E' AB BC AC' H13 H14 H17).
assert(AC = AC').
apply(l6_11_unicity O A C E AC AC').
intro.
subst E.
unfold Ps in H15.
unfold out in H15.
tauto.
intro.
subst C.
apply between_identity in H0.
subst B.
apply cong_identity in H6.
subst AC.
unfold Ps in H15.
unfold out in H15.
tauto.
unfold Ps in H15.
assumption.
Cong.
unfold Ps in HP.
assumption.
Cong.
subst AC'.
assumption.

(* Case AC = O *)

subst AC.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply between_identity in H0.
subst B.
apply cong_identity in H12.
subst AB.
apply cong_identity in H9.
subst BC.
unfold ltP in H8.
ex_and H8 X.
apply diff_sum in H0.
assert(X=O).
apply(sum_unicity O E E' O X).
apply sum_O_B.
unfold sum in H0.
spliter.
unfold Ar2 in H0.
tauto.
unfold Ps in H5.
apply out_col in H5.
Col.
assumption.
subst X.
unfold Ps in H5.
unfold out in H5.
tauto.

(* BC = O *)

subst BC.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
assert(Cong O AB O AC).
eCong.
unfold ltP in H11.
ex_and H11 X.
apply diff_sum in H9.
assert(X = AB).
apply (sum_unicity O E E' O X).
apply sum_O_B.
unfold sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold ltP in H5.
ex_and H5 Y.
apply diff_sum in H5.

assert(Y = AC).
apply (sum_unicity O E E' O Y).
apply sum_O_B.
unfold sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H13.
apply out_col in H13.
Col.
assumption.
subst Y.
assert(AB = AC).
apply(l6_11_unicity O A B E AB AC).
intro.
subst E.
unfold Ps in H13.
unfold out in H13.
tauto.
intro.
subst B.
apply cong_identity in H6.
subst AC.
unfold Ps in H13.
unfold out in H13.
tauto.
unfold Ps in H11.
assumption.
Cong.
unfold Ps in H13.
assumption.
Cong.
subst AB.
apply sum_A_O.
unfold sum in H9.
unfold Ar2 in H9.
tauto.
unfold Ps in H11.
apply out_col in H11.
Col.

(* Case AC = O /\ BC = O *)

subst AC.
subst BC.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst B.
apply cong_identity in H12.
subst AB.
apply sum_O_O.
unfold ltP in H11.
ex_and H11 X.
apply diff_sum in H5.
unfold sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O *)

subst AB.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.

assert(BC = AC).
apply(l6_11_unicity O A C E BC AC).
intro.
subst E.
tauto.
intro.
subst C.
apply cong_identity in H9.
subst BC.
unfold ltP in H8.
ex_and H8 X.
apply diff_sum in H8.
assert(X = O).
apply (sum_unicity O E E' O X).
apply sum_O_B.
unfold sum in H8.
unfold Ar2 in H8.
tauto;
unfold Ps in H13.
unfold Ps in H9.
apply out_col in H9.
Col.
assumption.
subst X.
unfold Ps in H9.
unfold out in H9.
tauto.
unfold ltP in H8.
ex_and H8 X.
apply diff_sum in H8.

assert(X = BC).
apply (sum_unicity O E E' O X).
apply sum_O_B.
unfold sum in H8.
unfold Ar2 in H8.
tauto;
unfold out in H13.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold Ps in H11.
assumption.
Cong.

unfold ltP in H5.
ex_and H5 X.
apply diff_sum in H5.
assert(X = AC).
apply (sum_unicity O E E' O X).
apply sum_O_B.
unfold sum in H5.
unfold Ar2 in H5.
tauto;
unfold out in H13.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold Ps in H11.
assumption.
Cong.
subst AC.
apply sum_O_B.
unfold ltP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold sum in H5.
unfold Ar2 in H5.
tauto.
Col.

(* Case AB = O /\ AC = O *)

subst AC.
subst AB.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst C.
apply cong_identity in H9.
subst BC.
apply sum_O_O.
unfold ltP in H8.
ex_and H8 X.
apply diff_sum in H5.
unfold sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O /\ BC = O *)

subst AB.
subst BC.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.
apply cong_identity in H6.
subst AC.
apply sum_O_O.
unfold ltP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O /\ BC = O /\ AC= O *)

subst AB.
subst AC.
subst BC.

apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
apply cong_identity in H6.
induction HH0; tauto.
Qed.

(** Lemma 15.5. *)
(** Known as Thales theorem or intercept theorem. *)

Lemma length_out : forall O E E' A B C D AB CD, A <> B -> C <> D -> length O E E' A B AB -> length O E E' C D CD
                               -> out O AB CD.
Proof.
intros.
unfold length in *.
spliter.
unfold leP in *.
induction H7; induction H4.
unfold ltP in *.
ex_and H7 X.
ex_and H4 Y.
apply diff_sum in H7.
apply diff_sum in H4.
assert(X = AB).
apply (sum_unicity O E E' O X).
apply sum_O_B.
unfold sum in H4.
spliter.
unfold Ar2 in H4.
tauto.
unfold Ps in H9.
apply out_col in H9.
Col.
assumption.
subst X.
assert(Y = CD).
apply (sum_unicity O E E' O Y).
apply sum_O_B.
unfold sum in H4.
spliter.
unfold Ar2 in H4.
tauto.
unfold Ps in H10.
apply out_col in H10.
Col.
assumption.
subst Y.
unfold Ps in *.
eapply (l6_7  _ _ E).
assumption.
apply l6_6.
assumption.
subst CD.
apply cong_symmetry in H5.
apply cong_identity in H5.
contradiction.
subst AB.
apply cong_symmetry in H8.
apply cong_identity in H8.
contradiction.
subst CD.
apply cong_symmetry in H5.
apply cong_identity in H5.
contradiction.
Qed.

Lemma image_preserves_bet1 : forall X Y A B C A' B' C', Bet A B C 
                                                       -> is_image A A' X Y 
                                                       -> is_image B B' X Y
                                                       -> is_image C C' X Y
                                                       -> Bet A' B' C'.
Proof.
intros.
induction(eq_dec_points X Y).
subst Y.
unfold is_image in *.
induction H0.
tauto.
induction H1.
tauto.
induction H2.
tauto.
spliter.
clean_duplicated_hyps.
apply(l7_15 A B C A' B' C' X).
apply l7_2.
auto.
apply l7_2; auto.
apply l7_2; auto.
assumption.
apply (image_preserves_bet A B C A' B' C' X Y).
unfold is_image in H0.
induction H0.
tauto.
spliter.
contradiction.
unfold is_image in *.
induction H0; induction H1; induction H2; try( spliter; contradiction).
spliter.
auto.
induction H0; induction H1; induction H2; try( spliter; contradiction).
spliter.
auto.
induction H0; induction H1; induction H2; try( spliter; contradiction).
spliter.
auto.
assumption.
Qed.


Lemma image_preserves_col : forall X Y A B C A' B' C', Col A B C 
                                                       -> is_image A A' X Y 
                                                       -> is_image B B' X Y
                                                       -> is_image C C' X Y
                                                       -> Col A' B' C'.
Proof.
intros.
induction H.
unfold Col.
left.
apply (image_preserves_bet1 X Y A B C A' B' C'); auto.
induction H.
unfold Col.
right; left.
apply (image_preserves_bet1 X Y B C A B' C' A'); auto.
unfold Col.
right; right.
apply (image_preserves_bet1 X Y C A B C' A' B'); auto.
Qed.




Lemma image_preserves_out : forall X Y A B C A' B' C', out A B C 
                                                       -> is_image A A' X Y 
                                                       -> is_image B B' X Y
                                                       -> is_image C C' X Y
                                                       -> out A' B' C'.
Proof.
intros.
unfold out in *.
spliter.
repeat split; auto.
intro.
subst B'.
assert(B = A).
apply (l10_2_unicity X Y A' B A H1 H0).
contradiction.

intro.
subst C'.
assert(C=A).
apply (l10_2_unicity X Y A' C A H2 H0).
contradiction.
induction H4.
left.
apply (image_preserves_bet1 X Y A B C); auto.
right.
apply (image_preserves_bet1 X Y A C B); auto.
Qed.


Lemma project_preserves_out : forall A B C A' B' C' P Q X Y, out A B C -> ~Par A B X Y
                                                     -> project A A' P Q X Y
                                                     -> project B B' P Q X Y
                                                     -> project C C' P Q X Y
                                                     -> out A' B' C'.
Proof.
intros.
repeat split.
intro.
subst B'.
unfold out in H.
spliter.
unfold project in H1.
unfold project in H2.
spliter.
induction H9; induction H13. 
assert(Par A A' B A').
apply (par_trans _ _ X Y); auto.
apply par_symmetry.
assumption.
induction H14.
apply H14.
exists A'.
split; Col.
spliter.
apply H0.
apply par_symmetry.
apply(par_col_par X Y A A' B).
intro.
subst B.
tauto.
apply par_symmetry.
assumption.
Col.
subst A'.
apply H0.
apply par_left_comm.
assumption.
subst A'.
contradiction.
subst A'.
contradiction.

assert(HC:Col A B C).
apply out_col in H.
assumption.
unfold out in H.
spliter.
intro.
subst C'.
unfold project in H1 ,H3.
spliter.
induction H9; induction H13.
assert(Par A A' C A').
apply (par_trans _ _ X Y).
assumption.
apply par_symmetry.
assumption.
induction H14.
apply H14.
exists A'.
split; Col.
spliter.

apply H0.
apply par_symmetry.
apply (par_col_par X Y A A' B).
intro.
subst B.
tauto.
apply par_symmetry.
assumption.
ColR.
subst A'.
apply H0.
apply par_symmetry.
apply(par_col_par X Y A C B).
intro.
subst B.
tauto.
apply par_symmetry.
apply par_left_comm.
assumption.
Col.
subst A'.
apply H0.
apply par_symmetry.
apply(par_col_par X Y A C B).
intro.
subst B.
tauto.
apply par_symmetry.
assumption.
Col.
subst A'.
contradiction.
unfold out in H.
spliter.
induction H5.
left.
apply (project_preserves_bet P Q X Y A B C A' B' C'); assumption.
right.
apply (project_preserves_bet P Q X Y A C B A' C' B'); assumption.
Qed.

Lemma conga_bet_conga : forall A B C D E F A' C' D' F',
                               Conga A B C D E F
                               -> A' <> B -> C' <> B -> D' <> E -> F' <> E
                               -> Bet A B A' -> Bet C B C' -> Bet D E D' -> Bet F E F'
                               -> Conga A' B C' D' E F'.
Proof.
intros.
assert(HH:= l11_13 A B C D E F A' D' H H4 H0 H6 H2).
apply conga_comm.
apply(l11_13 C B A' F E D' C' F'); auto.
apply conga_comm.
assumption.
Qed.


Definition prodg O E E' A B C := prod O E E' A B C \/ (~Ar2 O E E' A B B /\ C = O).

Lemma thales : 
 forall O E E' P A B C D A1 B1 C1 D1 AD,
  O<>E ->
  Col P A B ->
  Col P C D ->
  ~ Col P A C -> 
  Pj A C B D ->
  length O E E' P A A1 ->
  length O E E' P B B1 ->
  length O E E' P C C1 ->
  length O E E' P D D1 ->
  prodg O E E' A1 D1 AD ->
  prodg O E E' C1 B1 AD.
Proof.
intros.
induction(Col_dec O E E').
unfold prodg.
right.
split.
intro.
unfold Ar2 in H10.
spliter.
contradiction.
unfold prodg in H8.
induction H8.
unfold prod in H8.
spliter.
unfold Ar2 in H8.
spliter.
contradiction.
tauto.
induction H8.

induction(eq_dec_points P B).
subst B.
apply length_cong in H5.
apply cong_symmetry in H5.
apply cong_identity in H5.
subst B1.
unfold Pj in H3.
induction H3.
induction H3.
apply False_ind.
apply H3.
exists C.
split; Col.
spliter.
apply False_ind.
apply H2.
ColR.
subst D.
apply length_cong in H7.
apply cong_symmetry in H7.
apply cong_identity in H7.
subst D1.
assert (AD = O).
apply (prod_unicity O E E' A1 O).
assumption.
apply prod_0_r.
assumption.
unfold prod in H8.
spliter.
unfold Ar2 in H3.
tauto.
subst AD.
left.
apply prod_0_r.
assumption.

unfold length in H6.
spliter.
unfold leP in H6.
induction H6.
unfold ltP in H6.
ex_and H6 X.
apply diff_sum in H6.
unfold sum in H6.
spliter.
unfold Ar2 in H6.
tauto.
subst C1; Col.

induction(eq_dec_points A B).
subst B.
induction H3.
induction H3.
apply False_ind.
apply H3.
exists A.
split; Col.
spliter.
assert(C=D).
apply(inter_unicity P C A C); Col.
subst D.
assert(A1=B1).
apply (length_unicity O E E' P A);auto.
subst B1.
assert(C1 = D1).
apply (length_unicity O E E' P C);auto.
subst D1.
left.
apply prod_comm.
assumption.
subst D.
apply False_ind.
apply H2; Col.

rename H11 into HAB.

assert(Hl0:= H4).
assert(Hl1:= H5).
assert(Hl2:= H6).
assert(Hl3:= H7).

unfold length in H4.
unfold length in H5.
unfold length in H6.
unfold length in H7.
spliter.
clean_duplicated_hyps.


assert(exists C' : Tpoint, Cong_3 P A C O A1 C' /\ one_side O A1 E' C').
apply(l10_16 P A C O A1 E');
Cong.
apply length_Ar2 in Hl0.
induction Hl0.
spliter.
intro.
induction(eq_dec_points A1 O).
subst A1.
apply cong_symmetry in H22.
apply cong_identity in H22.
subst A.
apply H2.
Col.
apply H5.
ColR.
subst A1.
intro.
apply cong_symmetry in H22.
apply cong_identity in H22.
subst A.
apply H2.
Col.

ex_and H4 C1'.

assert(Conga P A C O A1 C1').
apply(cong3_conga).
intro.
subst A.
apply H2; Col.
intro.
subst C.
apply H2; Col.
assumption.

assert(HN:~Col O C1 C1').
intro.
unfold one_side in H5.
ex_and H5 K.
unfold two_sides in H23.
spliter.
apply H24.
apply col_permutation_2.
apply (col_transitivity_1 _ C1).
intro.
subst C1.
treat_equalities.
apply H2.
Col.
ColR.
Col.

assert(HH:= midpoint_existence C1 C1').
ex_and HH M.

assert(HH:= l10_2_existence O M D1).
ex_and HH D1'.
unfold is_image in H23.
induction H23.
spliter.
unfold is_image_spec in H24.
spliter.
ex_and H24 N.

assert(out O C1 D1).

apply (length_out O E E' P C P D).
intro.
subst C.
apply cong_identity in H16.
subst C1.
apply H2; Col.
intro.
subst D.
apply cong_identity in H13.
subst D1.
assert(AD=O).
apply (prod_unicity O E E' A1 O).
assumption.
apply prod_0_r.

unfold prod in H8.
spliter.
unfold Ar2 in H8.
tauto.
Col.
subst AD.
induction H3.
induction H3.
apply H3.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B; tauto.
assumption.
assumption.

(*********************)
assert(out O A1 C1).
apply (length_out O E E' P A P C).
intro.
subst A.
apply cong_identity in H22.
subst A1.
apply H2; Col.
intro.
subst C.
apply cong_identity in H16.
subst C1.
unfold out in H27.
tauto.
assumption.
assumption.
(*********************)

assert(M <> C1).
intro.
subst M.
eapply (symmetric_point_unicity _ _ C1) in H7.
subst C1'.
apply H2.
apply out_col.

apply(cong3_preserves_out O A1 C1 P A C H28).
unfold Cong_3 in *.
spliter.
repeat split; Cong.
apply l7_3_2.

assert(Per O M C1).
unfold Per.
exists C1'.
split.
assumption.
unfold Cong_3 in H4.
spliter.
apply (cong_transitivity _ _ P C); Cong.

apply per_perp_in in H30; auto.
apply perp_in_comm in H30.
apply perp_in_perp in H30.


assert(out O C1' D1').
apply(image_preserves_out O M O C1 D1).
assumption.
unfold is_image.
left.
split; auto.
unfold is_image_spec.
split.
exists O.
split; finish.
right.
auto.

unfold is_image.
left.
split; auto.
unfold is_image_spec.
split.
exists M.
split; finish.
left.
induction H30.
apply perp_sym.
apply perp_comm.
apply (perp_col _ M).
intro.
subst C1'.

apply l7_3 in H7.
contradiction.
finish.
unfold is_midpoint in H7.
spliter.
finish.
apply perp_distinct in H30.
tauto.
unfold is_image.
left.
split; auto.
unfold is_image_spec.
split.
exists N.
split; finish.
left.
induction H25.
apply perp_right_comm.
assumption.
subst D1'.
apply l7_3 in H24.
subst D1.
induction H30.
apply perp_not_col in H24.
apply False_ind.
apply H24.
apply out_col in H27.
apply col_permutation_2.
apply (col_transitivity_1 _ N).
intro.
subst N.
apply cong_symmetry in H13.
apply cong_identity in H13.
subst D.
unfold Pj in H3.
induction H3.
induction H3.
apply H3.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.
Col.
Col.
apply perp_distinct in H24.
tauto.

assert(Perp O N D1 N).
apply (perp_col O M D1 N).
intro.
subst N.
apply HN.
unfold is_midpoint in H24.
spliter.
apply bet_col in H24.
apply out_col in H31.
apply out_col in H27.
eapply (col_transitivity_1 _ D1').
intro.
subst D1'.
apply cong_identity in H32.
subst D1.
treat_equalities.
induction H3.
induction H1.
apply H1.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.
apply(col_transitivity_1 _ D1).
intro.
subst D1.
treat_equalities.
induction H3.
induction H1.
apply H1.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.
Col.
Col.
ColR.
apply perp_sym.
apply (perp_col _ D1').
intro.
subst N.
unfold is_midpoint in H24.
spliter.
treat_equalities.
apply HN.
apply out_col in H31.
apply out_col in H27.
apply (col_transitivity_1 _ D1).
intro.
subst D1.
treat_equalities.
induction H3.
induction H1.
apply H1.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.
Col.
Col.
induction H25.
finish.
subst D1'.
apply l7_3 in H24.
subst N.
apply False_ind.
apply out_col in H31.
apply out_col in H27.
apply HN.
apply (col_transitivity_1 _ D1).
intro.
subst D1.
treat_equalities.
treat_equalities.
induction H3.
induction H1.
apply H1.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.
Col.
Col.
unfold is_midpoint in H24.
spliter.
apply bet_col in H24.
Col.
Col.
apply perp_left_comm in H32.

assert(Cong O D1 O D1').
apply perp_perp_in in H32.
apply perp_in_comm in H32.
apply perp_in_per in H32.
unfold Per in H32.
ex_and H32 D2.
assert(D2 = D1').
eapply (l7_9 _ _ N D1);
finish.
subst D2.
assumption. 

assert(Pj C1 C1' D1 D1').
unfold Pj.
left.
induction H25; induction H30.


apply (l12_9 _ _ _ _ O M).
apply all_coplanar.
apply (perp_col _ M).
intro.
subst C1'.
apply HN.
Col.
finish.
unfold is_midpoint in H7.
spliter.
finish.
finish.
apply perp_distinct in H30.
tauto.
subst D1'.
apply l7_3 in H24.
subst N.
apply perp_distinct in H32.
tauto.
subst D1'.
apply l7_3 in H24.
subst N.
apply perp_distinct in H32.
tauto.



assert(Cong_3 P C A O C1' A1).
unfold Cong_3 in *.
spliter.
repeat split; Cong.

assert(Conga P C A O C1' A1).
apply cong3_conga.
intro.
subst C.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
assumption. 
unfold Cong_3 in H35.
spliter.
assert(Cong P A O A1 /\ (P <> A -> Conga C P A C1' O A1 /\ Conga C A P C1' A1 O)).
apply(l11_49 P C A O C1' A1); Cong.
spliter.
assert(P <> A).
intro.
subst A.
apply H2.
Col.
apply H40 in H41.
clear H40.
spliter.

assert(Conga C A P D B P).
induction(Bet_dec C P D).

assert(Bet A P B).
apply(project_preserves_bet A P A C C P D).
assumption.
unfold project.
repeat split.
intro.
subst A.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
intro.
induction H43.
apply H43.
exists A.
split; Col.
spliter.
apply H2.
Col.
Col.
left.
apply par_left_comm.
apply par_reflexivity.
intro.
subst A.
apply H2.
Col.
unfold project.
repeat split.
intro.
subst A.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
intro.
induction H43.
apply H43.
exists A.
split; Col.
spliter.
apply H2.
Col.
Col.
right.
reflexivity.
unfold project.
repeat split.
intro.
subst A.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
intro.
induction H43.
apply H43.
exists A.
split; Col.
spliter.
apply H2.
Col.
Col.
left.
unfold Pj in H3.
induction H3.
apply par_symmetry.
apply par_right_comm.
assumption.
subst D.
apply False_ind.
apply H2.
ColR.

assert(Conga C A B D B A <-> Par A C B D).
apply(l12_21 A C B D).
unfold two_sides.
split.
assumption.
repeat split.
intro.
apply H2.
ColR.
intro.
apply H2.

assert(P <> D).
intro.
subst D.
induction H3.
induction H3.
apply H3.
exists A.
split; Col.
spliter.
apply H3.
apply (inter_unicity P B A C); Col.
intro.
apply H2.
ColR.
subst B.
tauto.
ColR.

exists P.
split; Col.
destruct H44.
induction H3.
assert(HH3:=H3).
apply H45 in HH3.
apply(out_conga C A B D B A C P D P).
assumption.
apply out_trivial.
intro.
subst C.
apply H2.
Col.
repeat split.
intro.
subst B.
tauto.
intro.
subst A.
apply H2.
Col.
right.
assumption.
apply out_trivial.
intro.
subst D.
apply H2.
ColR.
repeat split.
assumption.
intro.
subst B.
apply H2.
tauto.
right; Between.
subst D.
apply False_ind.
apply H2.
ColR.

assert(out P C D).
unfold Col in H1.
unfold out.
repeat split.
intro.
subst C.
apply H42.
Between.
intro.
subst D.
apply H42.
Between.
induction H1.
left; assumption.
induction H1.
right; Between.
apply False_ind.
apply H42.
Between.

assert(out P A B).
apply (project_preserves_out P C D  P A B  P A A C).
assumption.
intro.
induction H44.
apply H44.
exists C.
split; Col.
spliter.
contradiction.
unfold project.
repeat split.
intro.
subst A.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
intro.
induction H44.
apply H44.
exists A.
split; Col.
spliter.
contradiction.
Col.
right.
reflexivity.

unfold project.
repeat split.
intro.
subst A.
apply H2.
Col.
intro.
subst C.
apply H2.
Col.
intro.
induction H44.
apply H44.
exists A.
split; Col.
spliter.
contradiction.
Col.
left.
apply par_left_comm.
apply par_reflexivity.
intro.
subst C.
apply H2.
Col.
unfold project.
repeat split.
intro.
subst A.
apply H2; Col.
intro.
subst C.
apply H2; Col.
intro.
induction H44.
apply H44.
exists A.
split; Col.
spliter.
contradiction.
Col.
left.
induction H3.
apply par_left_comm.
apply par_symmetry.
assumption.
subst D.
apply False_ind.
apply H2.
ColR.

apply (l12_22 A C B D P).
assumption.
apply out_one_side.
left.
assumption.
assumption.
induction H3.
assumption.
subst D.
apply False_ind.
apply H2.
ColR.

assert(C <> A).
intro.
subst C.
unfold Conga in H42.
tauto.

assert(P <> A).
intro.
subst A.
unfold Conga in H42.
tauto.

assert(~Par P A C A).
intro.
induction H45.
apply H45.
exists A.
split; Col.
spliter.
apply H2.
Col.

assert(Conga C P A D P B).
induction(Bet_dec C P D).

assert(Bet A P B).
apply (project_preserves_bet P A C A C P D A P B); auto.
repeat split; Col.
left.
right.
repeat split; Col.
repeat split; Col.
repeat split; Col.
unfold Pj in H3.
induction H3.
left.
finish.
right.
auto.
apply(l11_14 C P A D B); auto.
intro.
subst C.
unfold Conga in H36.
tauto.
intro.
subst D.
induction H3.
induction H3.
apply H3.
exists A.
split; Col.
spliter.
apply H2.
ColR.
subst B.
tauto.

assert(out P C D).
apply(not_bet_out).
intro.
subst C.
apply H46.
Between.
intro.
subst D.
apply H46.
Between.
Col.
assumption.
assert(out P A B).
apply(project_preserves_out P C D P A B P A C A).
repeat split.
intro.
subst C.
apply H46.
Between.
intro.
subst D.
apply H46.
Between.
unfold out in H47.
spliter.
tauto.
intro.
induction H48.
apply H48.
exists C.
split; Col.
spliter.
apply H2.
Col.
repeat split; Col.
repeat split; Col.
left.
right.
repeat split; Col.
repeat split; Col.
left.
unfold Pj in H3.
induction H3.
finish.
subst D.
apply False_ind.
unfold Conga in H42.
tauto.

apply conga_sym.
apply(out_conga C P A C P A D B C A); finish.
apply conga_refl.
apply out_trivial.
unfold out in H47.
tauto.
unfold out in H48.
tauto.
apply out_trivial.
unfold out in H47.
tauto.
apply out_trivial.
auto.

assert(C1 <> C1').
intro.
subst C1'.
apply HN.
Col.

assert(O <> C1').
intro.
subst C1'.
unfold Conga in H36.
tauto.

assert(~Col O C1 C1').
intro.
induction H30.
apply perp_not_col in H30.
apply H30.
unfold is_midpoint in H7.
spliter.
apply bet_col in H7.
ColR.
apply perp_distinct in H30.
tauto.

assert(~Par O C1' C1 C1').
intro.
induction H50.
apply H50.
exists C1'.
split; Col.
spliter.
contradiction.

assert(~Par O C1 C1 C1').
intro.
induction H51.
apply H51.
exists C1.
split; Col.
spliter.
contradiction.

assert(out O C1' D1').
apply(project_preserves_out O C1 D1 O C1' D1' O C1' C1 C1'); auto.
repeat split; Col.
repeat split; Col.
left.
finish.
repeat split; Col.
apply out_col in H31.
assumption.
left.
apply(l12_9 D1 D1' C1 C1' O M).
apply all_coplanar.
assert(Perp D1 D1' N O).
apply(perp_col D1 N N O D1').
intro.
subst D1'.
apply l7_3 in H24.
subst N.
apply perp_distinct in H32.
tauto.
finish.
unfold is_midpoint in H24.
spliter.
apply bet_col in H24.
Col.
apply perp_sym.
apply(perp_col O N D1 D1' M).
assumption.
finish.
Col.
induction H30.
apply (perp_col C1 M O M C1'); finish.
unfold is_midpoint in H7.
spliter.
apply bet_col in H7.
Col.
apply perp_distinct in H30.
tauto.

assert(Conga C1' O A1 D1' O B1).
apply(out_conga C1' O A1 C1' O A1 C1' A1 D1' B1); auto.
apply conga_refl.
auto.
intro.
subst A1.
unfold out in H28.
tauto.
apply out_trivial.
auto.
apply out_trivial.
intro.
subst A1.
unfold out in H28.
tauto.
apply(length_out O E E' P A  P B A1 B1); auto.

assert(Conga D1' O B1 D P B).
apply (conga_trans _ _ _ C P A).
apply (conga_trans _ _ _ C1' O A1).
apply conga_sym.
assumption.
apply conga_sym.
assumption.
assumption.

assert((D1' <> B1 -> Conga O D1' B1 P D B /\ Conga O B1 D1' P B D)).
apply (l11_49 D1' O B1 D P B).
assumption.
apply (cong_transitivity _ _ O D1); Cong.
assumption.

assert(D1' <> B1).
intro.
subst D1'.
induction H34.
induction H34.
apply H34.
exists C1.
split; Col.
ColR.
spliter.
apply H49.
ColR.
subst D1.
apply l7_3 in H24.
subst N.
apply perp_distinct in H32.
tauto.
apply H55 in H56.
spliter.
clear H55.
apply conga_comm in H57.

assert(Conga C1' A1 O D1' B1 O <-> Par A1 C1' B1 D1').
apply(l12_22 A1 C1' B1 D1' O).
apply (length_out O E E' P A P B); auto.
apply out_one_side.
left.
intro.
apply H49.
assert(A1 <> O).
intro.
subst A1.
unfold Conga in H53.
tauto.
ColR.
assumption.
destruct H55.
assert(Par A1 C1' B1 D1').
apply H55.
apply (conga_trans _ _ _ D B P).
apply (conga_trans _ _ _ C A P).
apply conga_sym.
assumption.
assumption.
apply conga_sym.
assumption.
clear H55 H58.

assert(prod O C1 C1' A1 D1 B1).
unfold prod.
repeat split.
assumption.
ColR.
ColR.
ColR.
exists D1'.
repeat split.
assumption.

apply out_col in H31.
ColR.
left.
finish.

assert(exists Y : Tpoint, prod O E C1' A1 D1 Y /\ prod O E C1' C1 B1 Y).
apply(prod_x_axis_unit_change O C1 C1' A1 D1 C1 B1 E).
repeat split; Col.
ColR.
ColR.
ColR.
Col.
intro.
subst E.
apply H9.
Col.
exists B1.
split; auto.
apply prod_1_l; Col.
ColR.
ex_and H58 Y.


assert(HH:=prod_y_axis_change O E C1' E' A1 D1 Y H58 H9).
assert(Y = AD).
apply(prod_unicity O E E' A1 D1); auto.
subst Y.
assert(HP:=prod_y_axis_change O E C1' E' C1 B1 AD H60 H9).
left.
assumption.

spliter.
subst M.
apply False_ind.
unfold is_midpoint in H7.
spliter.
apply bet_col in H7.
Col.

right.
spliter.
split.
intro.
apply H8.
unfold Ar2 in H11.
spliter.
repeat split; Col.
unfold length in H4.
tauto.
unfold length in H7.
tauto.
unfold length in H7.
tauto.
assumption.
Qed.

Lemma length_existence : forall O E E' A B, ~Col O E E' -> exists AB, length O E E' A B AB.
Proof.
intros.
assert(NEO : E <> O).
intro.
subst E.
apply H.
Col.
assert(HH:= segment_construction_2 E O A B NEO).
ex_and HH AB.
exists AB.
unfold length.
assert(AB = O \/ out O E AB).
induction(eq_dec_points AB O).
left; assumption.
right.
repeat split; auto.
assert(Col O E AB).
induction H2.
subst AB.
Col.
apply out_col.
assumption.
repeat split; Col.
unfold leP.
induction H2.
right; auto.
left.
unfold ltP.
exists AB.
repeat split.
apply diff_A_O; Col.
unfold out in H2.
tauto.
auto.
induction H0.
right; assumption.
left; assumption.
Qed.



(** Lemma 15.7 *)
(** Known as Euklid *)
(*
Lemma l15_7 :
 forall O E E' A B C H AB AC AH AC2,
  O<>E ->
  Per A C B ->
  Perp_in H C H A B ->
  length O E E' A B AB ->
  length O E E' A C AC ->
  length O E E' A H AH ->
  prod O E E' AB AH AC2 ->
  prod O E E' AC AC AC2.

intros.
induction(eq_dec_points AB O).
subst AB.
assert(A = B).
apply (length_id_1 O E E'); assumption.
subst B.
apply perp_in_distinct in H2.
tauto.

assert(~Col O E E' /\ Col O E AB).
unfold length in H3.
spliter.
unfold leP in H9.
induction H9.
unfold ltP in H9.
ex_and H9 X.
apply diff_sum in H9.
apply sum_ar2 in H9.
unfold Ar2 in H9.
tauto.
subst AB.
tauto.
spliter.

induction(eq_dec_points H A).
subst H.
assert(AH=O).
apply (length_unicity O E E' A A); auto.
apply length_id_2.
assumption.
subst AH.
apply perp_in_per in H2.
assert(A = C).
apply (l8_7 B);
finish.
subst C.
assert(AC = O).
apply (length_unicity O E E' A A); auto.
subst AC.
assert(AC2=O).
apply (prod_unicity O E E' AB O); auto.
apply prod_0_r; auto.
subst AC2.
apply prod_0_l; Col.

assert(C <> A).
intro.
subst C.
apply perp_in_right_comm in H2.
apply perp_in_id in H2.
contradiction.

assert(HH:= segment_construction_2 H A A C H10).
ex_and HH C'.
assert(out A H C').
unfold out.
repeat split; auto.
intro.
subst C'.
apply cong_symmetry in H13.
apply cong_identity in H13.
subst C.
tauto.

assert(HH:= segment_construction_2 C A A H H11).
ex_and HH H'.
assert(out A C H').
repeat split;auto.
intro.
subst H'.
apply cong_symmetry in H16.
apply cong_identity in H16.
subst H.
tauto.

assert(H <> C).
intro.
subst H.
apply perp_in_distinct in H2.
tauto.

assert(Cong H C H' C' /\ (H <> C -> Conga A H C A H' C' /\ Conga A C H A C' H')).
apply(l11_49 H A C H' A C').
apply (l11_10 H A C C A H).
apply conga_right_comm.
apply conga_refl; auto.
apply out_trivial; auto.
apply out_trivial; auto.
apply l6_6.
assumption.
apply l6_6.
assumption.
Cong.
Cong.
spliter.
assert(HH:= H20 H18).
clear H20.
spliter.

assert(Per A H C).
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_comm.
apply (perp_col  _ B).
auto.
apply perp_in_perp in H2.
induction H2.
apply perp_distinct in H2.
tauto.
apply perp_sym.
apply perp_left_comm.
assumption.
apply perp_in_col in H2.
tauto.

assert(HH:= l11_17 A H C A H' C' H22 H20).
assert(Par C B H' C').
apply(l12_9 C B H' C' A C).
unfold coplanar; auto.
apply per_perp_in in H1.
apply perp_in_comm in H1.
apply perp_in_perp in H1.
induction H1.
finish.
apply perp_distinct in H1.
tauto.
auto.
intro.
subst C.
apply perp_in_id in H2.
contradiction.
apply per_perp_in in HH.
apply perp_in_comm in HH.
apply perp_in_perp in HH.
apply perp_sym.
apply perp_right_comm.
apply(perp_col A H' C' H' C).
auto.
induction HH.
finish.
apply perp_distinct in H23.
tauto.
apply out_col in H17.
Col.
intro.
subst H'.
apply conga_distinct in H20.
tauto.
intro.
subst H'.
apply conga_distinct in H20.
tauto.

assert(HL1:=length_existence O E E' A H' H8).
ex_and HL1 AH'.
assert(HL1:=length_existence O E E' A C' H8).
ex_and HL1 AC'.
assert(exists P : Tpoint, prod O E E' AC' AC P).

apply(prod_exists O E E' H8 AC' AC).
unfold length in H25.
tauto.
unfold length in H4.
tauto.
ex_and H26 P.

assert(Perp C H A B).
apply perp_in_perp in H2.
induction H2.
apply perp_distinct in H2.
tauto.
assumption.

assert(prodg O E E' AH' AB P).
apply(thales O E E' A C' B H' C  AC' AB AH' AC   P); Col.
apply perp_in_col in H2.
spliter.

apply out_col in H14.
ColR.
apply out_col in H17.
Col.
intro.
assert(Perp H A C H).
apply perp_comm.
apply(perp_col A B H C H).
intro.
subst H.
apply conga_distinct in H20.
tauto.
finish.
apply perp_in_col in H2.
tauto.
apply perp_not_col in H29.
apply H29.
apply out_col in H14.
apply out_col in H17.
assert(A <> C').
intro.
subst C'.
unfold Conga in H21.
tauto.
assert(Col A H H').
ColR.
assert(A <> H').
intro.
subst H'.
unfold Conga in H20.
tauto.
ColR.

left.
finish.
left.
assumption.
assert(length O E E' A H' AH).
apply(length_eq_cong_2 O E E' A H A H' AH H5).
Cong.
assert(AH = AH').
apply (length_unicity O E E' A H'); auto.
subst AH'.
assert(P = AC2).
apply (prod_unicity O E E' AB AH).
apply prod_comm.
induction H28.
assumption.
spliter.
subst P.

apply prod_null in H27.
induction H27.
subst AC'.
assert(A = C').
apply (length_id_1 O E E'); auto.
subst C'.
unfold Conga in H21.
tauto.
subst AC.
assert(A = C).
apply (length_id_1 O E E'); auto.
subst C.
unfold Conga in H21.
tauto.
assumption.
subst AC2.

assert(length O E E' A C' AC).
apply(length_eq_cong_2 O E E' A C A C' ).
assumption.
Cong.
assert(AC = AC').
apply (length_unicity O E E' A C'); auto.
subst AC'.
assumption.
Qed.


Lemma l15_7_bis :
 forall O E E' A B C H AB AC AH AC2,
  O<>E ->
  Per A C B ->
  Perp_in H C H A B ->
  length O E E' A B AB ->
  length O E E' A C AC ->
  length O E E' A H AH ->
  prod O E E' AC AC AC2 ->
  prod O E E' AB AH AC2.
intros.

intros.
induction(eq_dec_points AB O).
subst AB.
assert(A = B).
apply (length_id_1 O E E'); assumption.
subst B.
apply perp_in_distinct in H2.
tauto.

assert(~Col O E E' /\ Col O E AB).
unfold length in H3.
spliter.
unfold leP in H9.
induction H9.
unfold ltP in H9.
ex_and H9 X.
apply diff_sum in H9.
apply sum_ar2 in H9.
unfold Ar2 in H9.
tauto.
subst AB.
tauto.
spliter.

induction(eq_dec_points H A).
subst H.
assert(AH=O).
apply (length_unicity O E E' A A); auto.
apply length_id_2.
assumption.
subst AH.
apply perp_in_per in H2.
assert(A = C).
apply (l8_7 B);
finish.
subst C.
assert(AC = O).
apply (length_unicity O E E' A A); auto.
subst AC.
assert(AC2=O).
apply (prod_unicity O E E' O O); auto.
apply prod_0_r; Col.
subst AC2.
apply prod_0_r; Col.

assert(C <> A).
intro.
subst C.
apply perp_in_right_comm in H2.
apply perp_in_id in H2.
contradiction.

assert(HH:= segment_construction_2 H A A C H10).
ex_and HH C'.
assert(out A H C').
unfold out.
repeat split; auto.
intro.
subst C'.
apply cong_symmetry in H13.
apply cong_identity in H13.
subst C.
tauto.

assert(HH:= segment_construction_2 C A A H H11).
ex_and HH H'.
assert(out A C H').
repeat split;auto.
intro.
subst H'.
apply cong_symmetry in H16.
apply cong_identity in H16.
subst H.
tauto.

assert(H <> C).
intro.
subst H.
apply perp_in_distinct in H2.
tauto.

assert(Cong H C H' C' /\ (H <> C -> Conga A H C A H' C' /\ Conga A C H A C' H')).
apply(l11_49 H A C H' A C').
apply (l11_10 H A C C A H).
apply conga_right_comm.
apply conga_refl; auto.
apply out_trivial; auto.
apply out_trivial; auto.
apply l6_6.
assumption.
apply l6_6.
assumption.
Cong.
Cong.
spliter.
assert(HH:= H20 H18).
clear H20.
spliter.

assert(Per A H C).
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_comm.
apply (perp_col  _ B).
auto.
apply perp_in_perp in H2.
induction H2.
apply perp_distinct in H2.
tauto.
apply perp_sym.
apply perp_left_comm.
assumption.
apply perp_in_col in H2.
tauto.

assert(HH:= l11_17 A H C A H' C' H22 H20).
assert(Par C B H' C').
apply(l12_9 C B H' C' A C).
unfold coplanar; auto.
apply per_perp_in in H1.
apply perp_in_comm in H1.
apply perp_in_perp in H1.
induction H1.
finish.
apply perp_distinct in H1.
tauto.
auto.
intro.
subst C.
apply perp_in_id in H2.
contradiction.
apply per_perp_in in HH.
apply perp_in_comm in HH.
apply perp_in_perp in HH.
apply perp_sym.
apply perp_right_comm.
apply(perp_col A H' C' H' C).
auto.
induction HH.
finish.
apply perp_distinct in H23.
tauto.
apply out_col in H17.
Col.
intro.
subst H'.
apply conga_distinct in H20.
tauto.
intro.
subst H'.
apply conga_distinct in H20.
tauto.

assert(HL1:=length_existence O E E' A H' H8).
ex_and HL1 AH'.
assert(HL1:=length_existence O E E' A C' H8).
ex_and HL1 AC'.
assert(exists P : Tpoint, prod O E E' AC' AC P).

apply(prod_exists O E E' H8 AC' AC).
unfold length in H25.
tauto.
unfold length in H4.
tauto.
ex_and H26 P.

assert(Perp C H A B).
apply perp_in_perp in H2.
induction H2.
apply perp_distinct in H2.
tauto.
assumption.

assert(prodg O E E' AH' AB P).
apply(thales O E E' A C' B H' C  AC' AB AH' AC   P); Col.
apply perp_in_col in H2.
spliter.

apply out_col in H14.
ColR.
apply out_col in H17.
Col.
intro.
assert(Perp H A C H).
apply perp_comm.
apply(perp_col A B H C H).
intro.
subst H.
apply conga_distinct in H20.
tauto.
finish.
apply perp_in_col in H2.
tauto.
apply perp_not_col in H29.
apply H29.
apply out_col in H14.
apply out_col in H17.
assert(A <> C').
intro.
subst C'.
unfold Conga in H21.
tauto.
assert(Col A H H').
ColR.
assert(A <> H').
intro.
subst H'.
unfold Conga in H20.
tauto.
ColR.

left.
finish.
left.
assumption.

assert(prod O E E' AH' AB P).
induction H28.
assumption.
spliter.
apply False_ind.
apply H28.
repeat split; Col.
unfold length in H24.
tauto.


assert(length O E E' A H' AH).
apply(length_eq_cong_2 O E E' A H A H' AH H5).
Cong.
assert(AH = AH').
apply (length_unicity O E E' A H'); auto.
subst AH'.

assert(length O E E' A C' AC).
apply(length_eq_cong_2 O E E' A C A C' AC H4).
Cong.
assert(AC = AC').
apply (length_unicity O E E' A C'); auto.
subst AC'.

assert(P = AC2).
apply (prod_unicity O E E' AC AC); auto.
subst P.
apply prod_comm.
assumption.
Qed.
*)

Lemma l15_7 :
 forall O E E' A B C H AB AC AH AC2,
  O<>E ->
  Per A C B ->
  Perp_in H C H A B ->
  length O E E' A B AB ->
  length O E E' A C AC ->
  length O E E' A H AH ->
  (prod O E E' AC AC AC2 <-> prod O E E' AB AH AC2).
Proof.
intros.

induction(eq_dec_points AB O).
subst AB.
assert(A = B).
apply (length_id_1 O E E'); assumption.
subst B.
apply perp_in_distinct in H2.
tauto.

assert(~Col O E E' /\ Col O E AB).
unfold length in H3.
spliter.
unfold leP in H8.
induction H8.
unfold ltP in H8.
ex_and H8 X.
apply diff_sum in H8.
apply sum_ar2 in H8.
unfold Ar2 in H8.
tauto.
subst AB.
tauto.
spliter.

induction(eq_dec_points H A).
subst H.
assert(AH=O).
apply (length_unicity O E E' A A); auto.
apply length_id_2.
assumption.
subst AH.
apply perp_in_per in H2.
assert(A = C).
apply (l8_7 B);
finish.
subst C.
assert(AC = O).
apply (length_unicity O E E' A A); auto.
subst AC.
split;intros;
assert(AC2=O).
apply (prod_unicity O E E' O O); auto.
apply prod_0_r; Col.
subst AC2.
apply prod_0_r; Col.
apply (prod_unicity O E E' AB O); auto.
apply prod_0_r; Col.
subst AC2.
apply prod_0_r; Col.



assert(C <> A).
intro.
subst C.
apply perp_in_right_comm in H2.
apply perp_in_id in H2.
contradiction.

assert(HH:= segment_construction_2 H A A C H9).
ex_and HH C'.
assert(out A H C').
unfold out.
repeat split; auto.
intro.
subst C'.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst C.
tauto.

assert(HH:= segment_construction_2 C A A H H10).
ex_and HH H'.
assert(out A C H').
repeat split;auto.
intro.
subst H'.
apply cong_symmetry in H15.
apply cong_identity in H15.
subst H.
tauto.

assert(H <> C).
intro.
subst H.
apply perp_in_distinct in H2.
tauto.

assert(Cong H C H' C' /\ (H <> C -> Conga A H C A H' C' /\ Conga A C H A C' H')).
apply(l11_49 H A C H' A C').
apply (l11_10 H A C C A H).
apply conga_right_comm.
apply conga_refl; auto.
apply out_trivial; auto.
apply out_trivial; auto.
apply l6_6.
assumption.
apply l6_6.
assumption.
Cong.
Cong.
spliter.
assert(HH:= H19 H17).
clear H19.
spliter.

assert(Per A H C).
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_comm.
apply (perp_col  _ B).
auto.
apply perp_in_perp in H2.
induction H2.
apply perp_distinct in H2.
tauto.
apply perp_sym.
apply perp_left_comm.
assumption.
apply perp_in_col in H2.
tauto.

assert(HH:= l11_17 A H C A H' C' H21 H19).
assert(Par C B H' C').
apply(l12_9 C B H' C' A C).
apply all_coplanar.
apply per_perp_in in H1.
apply perp_in_comm in H1.
apply perp_in_perp in H1.
induction H1.
finish.
apply perp_distinct in H1.
tauto.
auto.
intro.
subst C.
apply perp_in_id in H2.
contradiction.
apply per_perp_in in HH.
apply perp_in_comm in HH.
apply perp_in_perp in HH.
apply perp_sym.
apply perp_right_comm.
apply(perp_col A H' C' H' C).
auto.
induction HH.
finish.
apply perp_distinct in H22.
tauto.
apply out_col in H16.
Col.
intro.
subst H'.
apply conga_distinct in H19.
tauto.
intro.
subst H'.
apply conga_distinct in H19.
tauto.

assert(HL1:=length_existence O E E' A H' H7).
ex_and HL1 AH'.
assert(HL1:=length_existence O E E' A C' H7).
ex_and HL1 AC'.
assert(exists P : Tpoint, prod O E E' AC' AC P).

apply(prod_exists O E E' H7 AC' AC).
unfold length in H24.
tauto.
unfold length in H4.
tauto.
ex_and H25 P.

assert(Perp C H A B).
apply perp_in_perp in H2.
induction H2.
apply perp_distinct in H2.
tauto.
assumption.

assert(prodg O E E' AH' AB P).
apply(thales O E E' A C' B H' C  AC' AB AH' AC   P); Col.
apply perp_in_col in H2.
spliter.

apply out_col in H13.
ColR.
apply out_col in H16.
Col.
intro.
assert(Perp H A C H).
apply perp_comm.
apply(perp_col A B H C H).
intro.
subst H.
apply conga_distinct in H19.
tauto.
finish.
apply perp_in_col in H2.
tauto.
apply perp_not_col in H28.
apply H28.
apply out_col in H13.
apply out_col in H16.
assert(A <> C').
intro.
subst C'.
unfold Conga in H20.
tauto.
assert(Col A H H').
ColR.
assert(A <> H').
intro.
subst H'.
unfold Conga in H19.
tauto.
ColR.

left.
finish.
left.
assumption.

assert(prod O E E' AH' AB P).
induction H27.
assumption.
spliter.
apply False_ind.
apply H27.
repeat split; Col.
unfold length in H23.
tauto.


assert(length O E E' A H' AH).
apply(length_eq_cong_2 O E E' A H A H' AH H5).
Cong.
assert(AH = AH').
apply (length_unicity O E E' A H'); auto.
subst AH'.

assert(length O E E' A C' AC).
apply(length_eq_cong_2 O E E' A C A C' AC H4).
Cong.
assert(AC = AC').
apply (length_unicity O E E' A C'); auto.
subst AC'.

split.
intro.
assert(P = AC2).
apply (prod_unicity O E E' AC AC); auto.
subst P.
apply prod_comm.
assumption.

intro.
assert(P = AC2).
apply (prod_unicity O E E' AB AH); auto.
apply prod_sym.
assumption.
subst P.
assumption.
Qed.

Lemma l15_7_1 : forall O E E' A B C H AB AC AH AC2,
  O<>E ->
  Per A C B ->
  Perp_in H C H A B ->
  length O E E' A B AB ->
  length O E E' A C AC ->
  length O E E' A H AH ->
  prod O E E' AC AC AC2 -> prod O E E' AB AH AC2.
Proof.
intros.
destruct(l15_7 O E E' A B C H AB AC AH AC2 H0 H1 H2 H3 H4 H5).
apply H7.
assumption.
Qed.

Lemma l15_7_2 : forall O E E' A B C H AB AC AH AC2,
  O<>E ->
  Per A C B ->
  Perp_in H C H A B ->
  length O E E' A B AB ->
  length O E E' A C AC ->
  length O E E' A H AH ->
  prod O E E' AB AH AC2 -> prod O E E' AC AC AC2.
Proof.
intros.
destruct(l15_7 O E E' A B C H AB AC AH AC2 H0 H1 H2 H3 H4 H5).
apply H8.
assumption.
Qed.


Lemma length_sym : forall O E E' A B AB, length O E E' A B AB -> length O E E' B A AB.
Proof.
intros.
unfold length in *.
spliter.
repeat split; auto.
Cong.
Qed.

Lemma pythagoras : forall O E E' A B C AC BC AB AC2 BC2 AB2, 
  O<>E ->
  Per A C B ->
  length O E E' A B AB ->
  length O E E' A C AC ->
  length O E E' B C BC ->
  prod O E E' AC AC AC2 ->
  prod O E E' BC BC BC2 ->
  prod O E E' AB AB AB2 ->
  sum  O E E' AC2 BC2 AB2.
Proof.
intros.
assert(~Col O E E' /\ Col O E AB2 /\ Col O E AC2 /\ Col O E BC).
unfold prod in *.
spliter.
unfold Ar2 in H4 ,H5 ,H6.
repeat split; tauto.
spliter.

induction(Col_dec A C B).
assert(HH:=l8_9 A C B H0 H11).
induction HH.
subst C.
assert(AB = BC).
apply(length_unicity O E E' A B).
assumption.
apply length_sym.
assumption.
subst BC.
assert(AB2 = BC2).
apply(prod_unicity O E E' AB AB); auto.
subst BC2.

assert(AC = O).
apply(length_unicity O E E' A A).
assumption.
apply length_id_2; assumption.
subst AC.
assert(AC2=O).
apply(prod_unicity O E E' O O).
assumption.
apply prod_0_l; Col.
subst AC2.
apply sum_O_B; Col.

subst C.
assert(AB = AC).
apply(length_unicity O E E' A B).
assumption.
assumption.
subst AC.
assert(AB2 = AC2).
apply(prod_unicity O E E' AB AB); auto.
subst AC2.

assert(BC = O).
apply(length_unicity O E E' B B).
assumption.
apply length_id_2; assumption.
subst BC.
assert(BC2=O).
apply(prod_unicity O E E' O O).
assumption.
apply prod_0_l; Col.
subst BC2.
apply sum_A_O; Col.
assert(exists X : Tpoint, Col A B X /\ Perp A B C X).
apply(l8_18_existence A B C); Col.
ex_and H12 P.
assert(Perp_in P A B C P).
apply(l8_14_2_1b_bis A B C P P H13); Col.
assert(Bet A P B /\ A <> P /\ B <> P).
apply(l11_47 A B C P H0).
finish.
spliter.

assert(HL1:= length_existence O E E' A P H7).
assert(HL2:= length_existence O E E' B P H7).
ex_and HL1 AP.
ex_and HL2 BP.

assert(sum O E E' AP BP AB).
apply(triangular_equality_bis O E E' A P B AP BP AB); auto.
apply length_sym.
assumption.

assert(prod O E E' AB AP AC2).
apply(l15_7_1 O E E' A B C P AB AC AP AC2 H H0); finish.

assert(prod O E E' AB BP BC2).
eapply(l15_7_1 O E E' B A C P AB BC); finish.
apply length_sym;auto.

assert(HD:=distr_l O E E' AB AP BP AB AC2 BC2 AB2 H20 H21 H22 H6).
assumption.
Qed.

Lemma is_length_exists : forall O E E' X Y,
  ~ Col O E E' -> exists XY, is_length O E E' X Y XY.
Proof.
intros O E E' X Y HNC.
elim (eq_dec_points X Y); intro HXY;
[treat_equalities; exists O; left; apply length_id_2; assert_diffs; auto|
destruct (length_existence O E E' X Y) as [XY HLength]; Col; exists XY; left; auto].
Qed.

End T15.