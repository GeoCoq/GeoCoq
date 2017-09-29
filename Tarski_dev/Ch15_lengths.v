Require Export GeoCoq.Tarski_dev.Ch14_order.

Section T15.

Context `{TE:Tarski_2D_euclidean}.

(** Lemma 15.2 *)
(** Cong corresponds to length equality.*)
(** Le corresponds to length inequality.*)

Lemma length_pos : forall O E E' A B L,
  Length O E E' A B L -> LeP O E E' O L.
Proof.
intros.
unfold Length in *.
tauto.
Qed.

Lemma length_id_1 : forall O E E' A B,
  Length O E E' A B O -> A=B.
Proof.
intros.
unfold Length in *.
spliter.
treat_equalities.
reflexivity.
Qed.

Lemma length_id_2 : forall O E E' A,
  O<>E -> Length O E E' A A O.
Proof.
intros.
unfold Length.
repeat split.
assumption.
Col.
unfold LeP.
tauto.
Cong.
Qed.

Lemma length_id : forall O E E' A B,
 Length O E E' A B O <-> (A=B /\ O<>E).
Proof.
intros.
split.
intros.
split.
eauto using length_id_1.
unfold Length in *.
tauto.
intros.
spliter. subst.
apply length_id_2.
assumption.
Qed.

Lemma length_eq_cong_1 : forall O E E' A B C D AB,
 Length O E E' A B AB -> Length O E E' C D AB -> Cong A B C D.
Proof.
intros.
unfold Length in *.
spliter.
apply cong_transitivity with O AB;Cong.
Qed.

Lemma length_eq_cong_2 : forall O E E' A B C D AB,
 Length O E E' A B AB -> Cong A B C D -> Length O E E' C D AB.
Proof.
intros.
unfold Length in *.
spliter.
repeat split;try assumption.
apply cong_transitivity with A B;Cong.
Qed.

Lemma ltP_pos : forall O E E' A, LtP O E E' O A  -> Ps O E A.
Proof.
intros.
unfold LtP in H.
ex_and H A'.

assert(~Col O E E' /\ Col O E A).
unfold Diff in H.
ex_and H X.
unfold Sum in H1.
spliter.
unfold Ar2 in H1.
tauto.
spliter.

assert(HH:= diff_A_O O E E' A H1 H2).
assert(A = A').
apply(diff_uniqueness O E E' A O A A'); assumption.
subst A'.
assumption.
Qed.

Lemma bet_leP : forall O E E' AB CD,
  Bet O AB CD -> LeP O E E' O AB -> LeP O E E' O CD -> LeP O E E' AB CD.
Proof.
intros.
unfold LeP in *.
induction H0; induction H1.

unfold LtP in H0.
unfold LtP in H1.
ex_and H0 P.
ex_and H1 Q.

assert(Ar2 O E E' AB CD P /\ Col O E Q).
unfold Diff in H0.
ex_and H0 X.
unfold Diff in H1.
ex_and H1 Y.
unfold Sum in H4.
unfold Sum in H5.
spliter.
unfold Ar2 in *.
spliter.
repeat split; Col.
unfold Ar2 in H4.
spliter.

assert(P = AB).
apply (diff_uniqueness O E E' AB O); auto.
apply diff_A_O; auto.
subst P.

assert(Q = CD).
apply (diff_uniqueness O E E' CD O); auto.
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

assert(exists P, Sum O E E' CD AB' P).
apply(sum_exists O E E' H4 CD AB'); Col.
unfold Opp in H0.
unfold Sum in H0.
spliter.
unfold Ar2 in H0.
tauto.
ex_and H1 P.


unfold LtP.
exists P.
split.
unfold Diff.
exists AB'.
split; auto.


assert(Diff O E E' CD AB P).
unfold Diff.
exists AB'.
split; auto.

apply diff_sum in H1.
induction (eq_dec_points AB O).
subst AB.
unfold Ps in H2.
unfold Out in H2.
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
unfold Out.
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
unfold Out in H3.
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

Lemma leP_bet : forall O E E' AB CD,
  LeP O E E' AB CD -> LeP O E E' O AB -> LeP O E E' O CD -> Bet O AB CD.
Proof.
intros.
unfold LeP in H.
induction H.
unfold LtP in H.
ex_and H X.
apply diff_sum in H.

assert(Out O AB X \/ AB=O).
unfold LeP in H0.
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

Lemma length_Ar2 : forall O E E' A B AB,
  Length O E E' A B AB -> (Col O E AB /\ ~Col O E E') \/ AB = O.
Proof.
intros.
unfold Length in H.
spliter.

unfold LeP in H1.
induction H1.
left.
split.
assumption.
unfold LtP in H1.
ex_and H1 P.
unfold Diff in H1.
ex_and H1 Q.
unfold Sum in *.
spliter.
unfold Ar2 in *.
tauto.
right; auto.
Qed.

Lemma length_leP_le_1 : forall O E E' A B C D AB CD,
 Length O E E' A B AB -> Length O E E' C D CD -> LeP O E E' AB CD -> Le A B C D.
Proof.
intros.
unfold Length in *.
spliter.
assert(Bet O AB CD).
apply (leP_bet O E E'); assumption.

prolong D C M' A B.
assert(HH:=symmetric_point_construction M' C).
ex_and HH M.
unfold Midpoint in H11.
spliter.

assert(Cong A B C M).
apply (cong_transitivity _ _ C M'); Cong.

apply(le_transitivity _ _ C M).
unfold Le.
exists M.
split; Between.

assert(Le O AB O CD).
unfold Le.
exists AB.
split; Cong.

apply(l5_6 O AB O CD C M C D); Cong.
apply (cong_transitivity _ _ A B); Cong.
Qed.

Lemma length_leP_le_2 : forall O E E' A B C D AB CD,
 Length O E E' A B AB -> Length O E E' C D CD -> Le A B C D -> LeP O E E' AB CD.
Proof.
intros.

assert(HH1:= length_Ar2 O E E' A B AB H).
assert(HH2:= length_Ar2 O E E' C D CD H0).
spliter.
unfold Length in *.
spliter.
apply bet_leP; try assumption.

induction(eq_dec_points O CD).
subst CD.
apply cong_symmetry in H4.
apply cong_identity in H4.
subst D.
unfold Le in H1.
ex_and H1 X.
apply between_identity in H1.
subst X.
apply cong_identity in H4.
subst B.
apply cong_identity in H7.
subst AB.
Between.
assert(Le O AB O CD).

apply(l5_6 A B C D O AB O CD); Cong.
unfold Le in H8.
ex_and H9 M.

induction HH1; induction HH2.
spliter.

unfold Le in H1.
ex_and H1 P.

unfold LeP in *.
induction H6; induction H3.
unfold LtP in *.
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

assert(AB = M \/ Midpoint O AB M).
apply(l7_20 O AB M); Cong.

unfold Ps in *.
assert(Out O AB CD).
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
unfold Midpoint in H3.
spliter.

assert(Out O AB CD).
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
unfold Out in H18.
spliter.
induction H22.
assert(AB = O).
apply(between_equality _ _ CD); Between.
subst AB.
Between.
assert(Bet CD O CD).
apply (between_exchange3 AB); Between.
assert(O = CD).
apply between_equality in H23.
contradiction.
Between.
tauto.
right.
intro.
subst Y.
unfold Ps in H17.
unfold Out in H17.
tauto.
right.
intro.
subst X.
unfold Ps in H16.
unfold Out in H16.
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

Lemma l15_3 : forall O E E' A B C, Sum O E E' A B C -> Cong O B A C.
Proof.
intros.
assert(Ar2 O E E' A B C).
unfold Sum in H.
spliter.
assumption.
unfold Ar2 in H0.
spliter.
induction (eq_dec_points A O).
subst A.
assert(B = C).
apply (sum_uniqueness O E E' O B); auto.
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
Lemma length_uniqueness : forall O E E' A B AB AB',
  Length O E E' A B AB -> Length O E E' A B AB' -> AB = AB'.
Proof.
intros.
assert(Col O E AB /\ ~ Col O E E' \/ AB = O).
eapply (length_Ar2 O E E' A B AB); assumption.
assert(Col O E AB' /\ ~ Col O E E' \/ AB' = O).
eapply (length_Ar2 O E E' A B AB'); assumption.

unfold Length in *.
spliter.
assert(Cong O AB O AB').
apply cong_transitivity with A B; Cong.
assert(AB = AB' \/ Midpoint O AB AB').
apply(l7_20 O AB AB').
ColR.
Cong.
induction H10.
assumption.
unfold Midpoint in H10.
spliter.

induction H1; induction H2.
spliter.

unfold LeP in *.
induction H4; induction H7.
unfold LtP in H4.
unfold LtP in H7.
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
assert(Out O AB AB').
eapply (l6_7 _ _ E).
assumption.
apply l6_6; assumption.
unfold Out in H16.
spliter.
induction H18.
assert(AB = O).
eapply (between_equality _ _ AB'); Between.
subst AB.
apply cong_symmetry in H11.
apply cong_identity in H11.
auto.
assert(AB' = O).
eapply (between_equality _ _ AB); Between.
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

Lemma length_cong : forall O E E' A B AB, Length O E E' A B AB -> Cong A B O AB.
Proof.
intros.
unfold Length in H.
spliter.
Cong.
Qed.

Lemma length_Ps : forall O E E' A B AB,
  AB <> O -> Length O E E' A B AB -> Ps O E AB.
Proof.
intros.
unfold Length in H0.
spliter.
unfold LeP in H2.
induction H2.
unfold LtP in H2.
ex_and H2 X.
apply diff_sum in H2.
apply sum_cong in H2.
unfold Parallelogram_flat in H2.
spliter.
apply cong_symmetry in H6.
apply cong_identity in H6.
subst X.
assumption.
unfold Sum in H2.
spliter.
unfold Ar2 in H2.
tauto.
right.
intro.
subst X.
unfold Ps in H4.
unfold Out in H4.
tauto.
subst AB.
tauto.
Qed.

Lemma length_not_col_null : forall O E E' A B AB,
  Col O E E' -> Length O E E' A B AB -> AB=O.
Proof.
intros.
unfold Length in H0.
spliter.
unfold LeP in H2.
induction H2.
unfold LtP in H2.
ex_and H2 X.
apply diff_sum in H2.
unfold Sum in H2.
spliter.
unfold Ar2 in H2.
spliter.
contradiction.
auto.
Qed.

Lemma triangular_equality_equiv :
  (forall O E A , O<>E -> (forall E' B C AB BC AC,
   Bet A B C ->
   Length O E E' A B AB -> Length O E E' B C BC -> Length O E E' A C AC ->
   Sum O E E' AB BC AC)) <->
  (forall O E E' A B C AB BC AC,
   O<>E -> Bet A B C ->
   Length O E E' A B AB -> Length O E E' B C BC -> Length O E E' A C AC ->
   Sum O E E' AB BC AC).
Proof.
split.
intros.
assert(HH:= H O E A H0).
apply (HH E' B C); auto.
intros.
assert(HH:= H O E E' A B C AB BC AC H0 H1 H2 H3 H4).
assumption.
Qed.

Lemma not_triangular_equality1 : forall O E A ,
  O<>E ->
  ~ (forall E' B C AB BC AC,
  Bet A B C ->
  Length O E E' A B AB -> Length O E E' B C BC -> Length O E E' A C AC ->
  Sum O E E' AB BC AC).
Proof.
intros.
intro.
assert(HH:=(H0 E A A O O O)).
assert(Bet A A A); Between.
assert(Length O E E A A O).
apply(length_id_2); auto.
assert(HHH:= (HH H1 H2 H2 H2)).
unfold Sum in HHH.
spliter.
ex_and H4 X.
ex_and H5 Y.
unfold Ar2 in H3.
spliter.
apply H3.
Col.
Qed.

Lemma triangular_equality : forall O E E' A B C AB BC AC,
  O<>E -> Bet A B C ->
  Is_length O E E' A B AB -> Is_length O E E' B C BC ->
  Is_length O E E' A C AC ->
  Sumg O E E' AB BC AC.
Proof.
intros O E E' A B C AB BC AC H H0 Hl1 Hl2 Hl3.

unfold Is_length in *.

induction Hl1; induction Hl2; induction Hl3; try(spliter; contradiction).
unfold Length in *.
spliter.
unfold LeP in *.
induction H11; induction H8; induction H5.

(* General Case *)

unfold LtP in *.
ex_and H11 X.
ex_and H8 Y.
ex_and H5 Z.
apply diff_sum in H11.
apply diff_sum in H8.
apply diff_sum in H5.
assert(AB = X).
apply (sum_uniqueness O E E' O X).
assumption.
unfold Sum in H11.
spliter.
unfold Ar2 in H11.
apply(sum_O_B); tauto.
subst X.

assert(BC = Y).
apply (sum_uniqueness O E E' O Y).
assumption.
unfold Sum in H8.
spliter.
unfold Ar2 in H8.
apply(sum_O_B); tauto.
subst Y.

assert(AC = Z).
apply (sum_uniqueness O E E' O Z).
assumption.
unfold Sum in H5.
spliter.
unfold Ar2 in H5.
apply(sum_O_B); tauto.
subst Z.

assert(forall A B : Tpoint,Col O E A -> Col O E B -> exists C : Tpoint, Sum O E E' A B C).
apply(sum_exists O E E' ).
unfold Sum in H11.
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
apply cong_transitivity with O BC; Cong.

assert(HP:= sum_pos_pos O E E' AB BC AC' H13 H14 H17).
assert(AC = AC').
apply(l6_11_uniqueness O A C E AC AC').
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
unfold Out in H15.
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
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H0.
assert(X=O).
apply(sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H0.
spliter.
unfold Ar2 in H0.
tauto.
unfold Ps in H5.
apply out_col in H5.
Col.
assumption.
subst X.
unfold Ps in H5.
unfold Out in H5.
tauto.

(* BC = O *)

subst BC.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
assert(Cong O AB O AC).
apply cong_transitivity with A B; Cong.
unfold LtP in H11.
ex_and H11 X.
apply diff_sum in H9.
assert(X = AB).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold LtP in H5.
ex_and H5 Y.
apply diff_sum in H5.

assert(Y = AC).
apply (sum_uniqueness O E E' O Y).
apply sum_O_B.
unfold Sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H13.
apply out_col in H13.
Col.
assumption.
subst Y.
assert(AB = AC).
apply(l6_11_uniqueness O A B E AB AC).
intro.
subst E.
unfold Ps in H13.
unfold Out in H13.
tauto.
intro.
subst B.
apply cong_identity in H6.
subst AC.
unfold Ps in H13.
unfold Out in H13.
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
unfold Sum in H9.
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
unfold LtP in H11.
ex_and H11 X.
apply diff_sum in H5.
unfold Sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O *)

subst AB.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.

assert(BC = AC).
apply(l6_11_uniqueness O A C E BC AC).
intro.
subst E.
tauto.
intro.
subst C.
apply cong_identity in H9.
subst BC.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H8.
assert(X = O).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H8.
unfold Ar2 in H8.
tauto;
unfold Ps in H13.
unfold Ps in H9.
apply out_col in H9.
Col.
assumption.
subst X.
unfold Ps in H9.
unfold Out in H9.
tauto.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H8.

assert(X = BC).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H8.
unfold Ar2 in H8.
tauto;
unfold Out in H13.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold Ps in H11.
assumption.
Cong.

unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
assert(X = AC).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H5.
unfold Ar2 in H5.
tauto;
unfold Out in H13.
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
unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold Sum in H5.
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
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H5.
unfold Sum in H5.
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
unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold Sum in H5.
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

Lemma length_O : forall O E E', O <> E -> Length O E E' O O O.
Proof.
intros.
unfold Length.
repeat split; Col.
unfold LeP.
right;auto.
Cong.
Qed.


Lemma triangular_equality_bis : forall O E E' A B C AB BC AC,
  A <> B \/ A <> C \/ B <> C -> O<>E -> Bet A B C ->
  Length O E E' A B AB -> Length O E E' B C BC -> Length O E E' A C AC ->
  Sum O E E' AB BC AC.
Proof.
intros O E E' A B C AB BC AC.
intro HH0.
intros.

unfold Length in *.
spliter.
unfold LeP in *.
induction H11; induction H8; induction H5.

(* General Case *)

unfold LtP in *.
ex_and H11 X.
ex_and H8 Y.
ex_and H5 Z.
apply diff_sum in H11.
apply diff_sum in H8.
apply diff_sum in H5.
assert(AB = X).
apply (sum_uniqueness O E E' O X).
assumption.
unfold Sum in H11.
spliter.
unfold Ar2 in H11.
apply(sum_O_B); tauto.
subst X.

assert(BC = Y).
apply (sum_uniqueness O E E' O Y).
assumption.
unfold Sum in H8.
spliter.
unfold Ar2 in H8.
apply(sum_O_B); tauto.
subst Y.

assert(AC = Z).
apply (sum_uniqueness O E E' O Z).
assumption.
unfold Sum in H5.
spliter.
unfold Ar2 in H5.
apply(sum_O_B); tauto.
subst Z.

assert(forall A B : Tpoint,Col O E A -> Col O E B -> exists C : Tpoint, Sum O E E' A B C).
apply(sum_exists O E E' ).
unfold Sum in H11.
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
apply cong_transitivity with O BC; Cong.

assert(HP:= sum_pos_pos O E E' AB BC AC' H13 H14 H17).
assert(AC = AC').
apply(l6_11_uniqueness O A C E AC AC').
intro.
subst E.
unfold Ps in H15.
unfold Out in H15.
tauto.
intro.
subst C.
apply between_identity in H0.
subst B.
apply cong_identity in H6.
subst AC.
unfold Ps in H15.
unfold Out in H15.
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
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H0.
assert(X=O).
apply(sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H0.
spliter.
unfold Ar2 in H0.
tauto.
unfold Ps in H5.
apply out_col in H5.
Col.
assumption.
subst X.
unfold Ps in H5.
unfold Out in H5.
tauto.

(* BC = O *)

subst BC.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst C.
assert(Cong O AB O AC).
apply cong_transitivity with A B; Cong.
unfold LtP in H11.
ex_and H11 X.
apply diff_sum in H9.
assert(X = AB).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold LtP in H5.
ex_and H5 Y.
apply diff_sum in H5.

assert(Y = AC).
apply (sum_uniqueness O E E' O Y).
apply sum_O_B.
unfold Sum in H9.
spliter.
unfold Ar2 in H9.
tauto.
unfold Ps in H13.
apply out_col in H13.
Col.
assumption.
subst Y.
assert(AB = AC).
apply(l6_11_uniqueness O A B E AB AC).
intro.
subst E.
unfold Ps in H13.
unfold Out in H13.
tauto.
intro.
subst B.
apply cong_identity in H6.
subst AC.
unfold Ps in H13.
unfold Out in H13.
tauto.
unfold Ps in H11.
assumption.
Cong.
unfold Ps in H13.
assumption.
Cong.
subst AB.
apply sum_A_O.
unfold Sum in H9.
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
unfold LtP in H11.
ex_and H11 X.
apply diff_sum in H5.
unfold Sum in H5.
unfold Ar2 in H5.
tauto.

(* Case AB = O *)

subst AB.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst B.

assert(BC = AC).
apply(l6_11_uniqueness O A C E BC AC).
intro.
subst E.
tauto.
intro.
subst C.
apply cong_identity in H9.
subst BC.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H8.
assert(X = O).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H8.
unfold Ar2 in H8.
tauto;
unfold Ps in H13.
unfold Ps in H9.
apply out_col in H9.
Col.
assumption.
subst X.
unfold Ps in H9.
unfold Out in H9.
tauto.
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H8.

assert(X = BC).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H8.
unfold Ar2 in H8.
tauto;
unfold Out in H13.
unfold Ps in H11.
apply out_col in H11.
Col.
assumption.
subst X.
unfold Ps in H11.
assumption.
Cong.

unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
assert(X = AC).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H5.
unfold Ar2 in H5.
tauto;
unfold Out in H13.
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
unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold Sum in H5.
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
unfold LtP in H8.
ex_and H8 X.
apply diff_sum in H5.
unfold Sum in H5.
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
unfold LtP in H5.
ex_and H5 X.
apply diff_sum in H5.
unfold Sum in H5.
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
Lemma length_out : forall O E E' A B C D AB CD,
  A <> B -> C <> D -> Length O E E' A B AB -> Length O E E' C D CD ->
  Out O AB CD.
Proof.
intros.
unfold Length in *.
spliter.
unfold LeP in *.
induction H7; induction H4.
unfold LtP in *.
ex_and H7 X.
ex_and H4 Y.
apply diff_sum in H7.
apply diff_sum in H4.
assert(X = AB).
apply (sum_uniqueness O E E' O X).
apply sum_O_B.
unfold Sum in H4.
spliter.
unfold Ar2 in H4.
tauto.
unfold Ps in H9.
apply out_col in H9.
Col.
assumption.
subst X.
assert(Y = CD).
apply (sum_uniqueness O E E' O Y).
apply sum_O_B.
unfold Sum in H4.
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

Lemma image_preserves_bet1 : forall X Y A B C A' B' C',
  Bet A B C -> Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y ->
  Bet A' B' C'.
Proof.
intros.
induction(eq_dec_points X Y).
subst Y.
unfold Reflect in *.
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
unfold Reflect in H0.
induction H0.
tauto.
spliter.
contradiction.
unfold Reflect in *.
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

Lemma image_preserves_col : forall X Y A B C A' B' C',
  Col A B C -> Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y ->
  Col A' B' C'.
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

Lemma image_preserves_out : forall X Y A B C A' B' C',
  Out A B C -> Reflect A A' X Y -> Reflect B B' X Y -> Reflect C C' X Y ->
  Out A' B' C'.
Proof.
intros.
unfold Out in *.
spliter.
repeat split; auto.
intro.
subst B'.
assert(B = A).
apply (l10_2_uniqueness X Y A' B A H1 H0).
contradiction.

intro.
subst C'.
assert(C=A).
apply (l10_2_uniqueness X Y A' C A H2 H0).
contradiction.
induction H4.
left.
apply (image_preserves_bet1 X Y A B C); auto.
right.
apply (image_preserves_bet1 X Y A C B); auto.
Qed.


Lemma project_preserves_out : forall A B C A' B' C' P Q X Y,
  Out A B C -> ~Par A B X Y ->
  Proj A A' P Q X Y -> Proj B B' P Q X Y -> Proj C C' P Q X Y ->
  Out A' B' C'.
Proof.
intros.
repeat split.
intro.
subst B'.
unfold Out in H.
spliter.
unfold Proj in H1.
unfold Proj in H2.
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
unfold Out in H.
spliter.
intro.
subst C'.
unfold Proj in H1 ,H3.
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
unfold Out in H.
spliter.
induction H5.
left.
apply (project_preserves_bet P Q X Y A B C A' B' C'); assumption.
right.
apply (project_preserves_bet P Q X Y A C B A' C' B'); assumption.
Qed.

Lemma conga_bet_conga : forall A B C D E F A' C' D' F',
  CongA A B C D E F -> A' <> B -> C' <> B -> D' <> E -> F' <> E ->
  Bet A B A' -> Bet C B C' -> Bet D E D' -> Bet F E F' ->
  CongA A' B C' D' E F'.
Proof.
intros.
assert(HH:= l11_13 A B C D E F A' D' H H4 H0 H6 H2).
apply conga_comm.
apply(l11_13 C B A' F E D' C' F'); auto.
apply conga_comm.
assumption.
Qed.

Lemma thales : forall O E E' P A B C D A1 B1 C1 D1 AD,
  O<>E -> Col P A B -> Col P C D -> ~ Col P A C -> Pj A C B D ->
  Length O E E' P A A1 -> Length O E E' P B B1 ->
  Length O E E' P C C1 -> Length O E E' P D D1 ->
  Prodg O E E' A1 D1 AD ->
  Prodg O E E' C1 B1 AD.
Proof.
intros.
induction(Col_dec O E E').
unfold Prodg.
right.
split.
intro.
unfold Ar2 in H10.
spliter.
contradiction.
unfold Prodg in H8.
induction H8.
unfold Prod in H8.
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
apply (prod_uniqueness O E E' A1 O).
assumption.
apply prod_0_r.
assumption.
unfold Prod in H8.
spliter.
unfold Ar2 in H3.
tauto.
subst AD.
left.
apply prod_0_r.
assumption.

unfold Length in H6.
spliter.
unfold LeP in H6.
induction H6.
unfold LtP in H6.
ex_and H6 X.
apply diff_sum in H6.
unfold Sum in H6.
spliter.
unfold Ar2 in H6.
tauto.
subst C1; Col.

induction(eq_dec_points A B).
{
subst B.
induction H3.
induction H3.
apply False_ind.
apply H3.
exists A.
split; Col.
spliter.
assert(C=D).
apply(l6_21 P C A C); Col.
subst D.
assert(A1=B1).
apply (length_uniqueness O E E' P A);auto.
subst B1.
assert(C1 = D1).
apply (length_uniqueness O E E' P C);auto.
subst D1.
left.
apply prod_comm.
assumption.
subst D.
apply False_ind.
apply H2; Col.
}

rename H11 into HAB.

assert(Hl0:= H4).
assert(Hl1:= H5).
assert(Hl2:= H6).
assert(Hl3:= H7).

unfold Length in H4.
unfold Length in H5.
unfold Length in H6.
unfold Length in H7.
spliter.
clean_duplicated_hyps.


assert(exists C' : Tpoint, Cong_3 P A C O A1 C' /\ OS O A1 E' C').
{
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
}

ex_and H4 C1'.

assert(CongA P A C O A1 C1').
{
apply(cong3_conga).
intro.
subst A.
apply H2; Col.
intro.
subst C.
apply H2; Col.
assumption.
}

assert(HN:~Col O C1 C1').
{
intro.
unfold OS in H5.
ex_and H5 K.
unfold TS in H23.
spliter.
apply H23.
apply col_permutation_2.
apply (col_transitivity_1 _ C1).
intro.
subst C1.
treat_equalities.
apply H2.
Col.
ColR.
Col.
}

assert(HH:= midpoint_existence C1 C1').
ex_and HH M.

assert(HH:= l10_2_existence O M D1).
ex_and HH D1'.
unfold Reflect in H23.
induction H23.
spliter.
unfold ReflectL in H24.
spliter.
ex_and H24 N.

assert(Out O C1 D1).
{
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
{
apply (prod_uniqueness O E E' A1 O).
assumption.
apply prod_0_r.
unfold Prod in H8.
spliter.
unfold Ar2 in H8.
tauto.
Col.
}
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
}

(*********************)
assert(Out O A1 C1).
{
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
unfold Out in H27.
tauto.
assumption.
assumption.
}
(*********************)

assert(M <> C1).
{
intro.
subst M.
eapply (symmetric_point_uniqueness _ _ C1) in H7.
subst C1'.
apply H2.
apply out_col.

apply(cong3_preserves_out O A1 C1 P A C H28).
unfold Cong_3 in *.
spliter.
repeat split; Cong.
apply l7_3_2.
}

assert(Per O M C1).
{
unfold Per.
exists C1'.
split.
assumption.
unfold Cong_3 in H4.
spliter.
apply (cong_transitivity _ _ P C); Cong.
}

apply per_perp_in in H30; auto.
apply perp_in_comm in H30.
apply perp_in_perp_bis in H30.


assert(Out O C1' D1').
{
apply(image_preserves_out O M O C1 D1).
assumption.
unfold Reflect.
left.
split; auto.
unfold ReflectL.
split.
exists O.
split; finish.
right.
auto.

unfold Reflect.
left.
split; auto.
unfold ReflectL.
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
unfold Midpoint in H7.
spliter.
finish.
apply perp_distinct in H30.
tauto.
unfold Reflect.
left.
split; auto.
unfold ReflectL.
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
}

assert(Perp O N D1 N).
{
apply (perp_col O M D1 N).
intro.
subst N.
apply HN.
unfold Midpoint in H24.
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
unfold Midpoint in H24.
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
unfold Midpoint in H24.
spliter.
apply bet_col in H24.
Col.
Col.
}
apply perp_left_comm in H32.

assert(Cong O D1 O D1').
{
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
}

assert(Pj C1 C1' D1 D1').
{
unfold Pj.
left.
induction H25; induction H30.
apply (l12_9 _ _ _ _ O M).
apply (perp_col _ M).
intro.
subst C1'.
apply HN.
Col.
finish.
unfold Midpoint in H7.
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
}
assert(Cong_3 P C A O C1' A1).
{
unfold Cong_3 in *.
spliter.
repeat split; Cong.
}
assert(CongA P C A O C1' A1).
{
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
}
unfold Cong_3 in H35.
spliter.
assert(Cong P A O A1 /\ (P <> A -> CongA C P A C1' O A1 /\ CongA C A P C1' A1 O)).
{
apply(l11_49 P C A O C1' A1); Cong.
}
spliter.
assert(P <> A).
{
intro.
subst A.
apply H2.
Col.
}
apply H40 in H41.
clear H40.
spliter.

assert(CongA C A P D B P).
{
induction(bet_dec C P D).
assert(Bet A P B).
apply(project_preserves_bet A P A C C P D).
assumption.
unfold Proj.
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
unfold Proj.
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
unfold Proj.
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

assert(CongA C A B D B A <-> Par A C B D).
apply(l12_21 A C B D).
unfold TS.
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
apply (l6_21 P B A C); Col.
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

assert(Out P C D).
unfold Col in H1.
unfold Out.
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

assert(Out P A B).
apply (project_preserves_out P C D  P A B  P A A C).
assumption.
intro.
induction H44.
apply H44.
exists C.
split; Col.
spliter.
contradiction.
unfold Proj.
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

unfold Proj.
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
unfold Proj.
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
}
assert(C <> A).
{
intro.
subst C.
unfold CongA in H42.
tauto.
}

assert(P <> A).
{
intro.
subst A.
unfold CongA in H42.
tauto.
}

assert(~Par P A C A).
{
intro.
induction H45.
apply H45.
exists A.
split; Col.
spliter.
apply H2.
Col.
}

assert(CongA C P A D P B).
{
induction(bet_dec C P D).

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
unfold CongA in H36.
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


assert(Out P C D).
apply(not_bet_out).
Col.
assumption.
assert(Out P A B).
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
unfold Out in H47.
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
unfold CongA in H42.
tauto.

apply conga_sym.
apply(out_conga C P A C P A D B C A); finish.
apply conga_refl.
apply out_trivial.
unfold Out in H47.
tauto.
unfold Out in H48.
tauto.
apply out_trivial.
unfold Out in H47.
tauto.
}

assert(C1 <> C1').
{
intro.
subst C1'.
apply HN.
Col.
}

assert(O <> C1').
{
intro.
subst C1'.
unfold CongA in H36.
tauto.
}

assert(~Col O C1 C1').
{
intro.
induction H30.
apply perp_not_col in H30.
apply H30.
unfold Midpoint in H7.
spliter.
apply bet_col in H7.
ColR.
apply perp_distinct in H30.
tauto.
}
assert(~Par O C1' C1 C1').
{
intro.
induction H50.
apply H50.
exists C1'.
split; Col.
spliter.
contradiction.
}

assert(~Par O C1 C1 C1').
{
intro.
induction H51.
apply H51.
exists C1.
split; Col.
spliter.
contradiction.
}
assert(Out O C1' D1').
{
apply(project_preserves_out O C1 D1 O C1' D1' O C1' C1 C1'); auto.
repeat split; Col.
repeat split; Col.
left.
finish.
repeat split; Col.
left.
apply(l12_9 D1 D1' C1 C1' O M).
assert(Perp D1 D1' N O).
apply(perp_col D1 N N O D1').
intro.
subst D1'.
apply l7_3 in H24.
subst N.
apply perp_distinct in H32.
tauto.
finish.
unfold Midpoint in H24.
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
unfold Midpoint in H7.
spliter.
apply bet_col in H7.
Col.
apply perp_distinct in H30.
tauto.
}
assert(CongA C1' O A1 D1' O B1).
{
apply(out_conga C1' O A1 C1' O A1 C1' A1 D1' B1); auto.
apply conga_refl.
auto.
intro.
subst A1.
unfold Out in H28.
tauto.
apply out_trivial.
auto.
apply out_trivial.
intro.
subst A1.
unfold Out in H28.
tauto.
apply(length_out O E E' P A  P B A1 B1); auto.
}
assert(CongA D1' O B1 D P B).
{
apply (conga_trans _ _ _ C P A).
apply (conga_trans _ _ _ C1' O A1).
apply conga_sym.
assumption.
apply conga_sym.
assumption.
assumption.
}
assert((D1' <> B1 -> CongA O D1' B1 P D B /\ CongA O B1 D1' P B D)).
{
apply (l11_49 D1' O B1 D P B).
assumption.
apply (cong_transitivity _ _ O D1); Cong.
assumption.
}

assert(D1' <> B1).
{
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
}
apply H55 in H56.
spliter.
clear H55.
apply conga_comm in H57.

assert(CongA C1' A1 O D1' B1 O <-> Par A1 C1' B1 D1').
{
apply(l12_22 A1 C1' B1 D1' O).
apply (length_out O E E' P A P B); auto.
apply out_one_side.
left.
intro.
apply H49.
assert(A1 <> O).
intro.
subst A1.
unfold CongA in H53.
tauto.
ColR.
assumption.
}
destruct H55.
assert(Par A1 C1' B1 D1').
{
apply H55.
apply (conga_trans _ _ _ D B P).
apply (conga_trans _ _ _ C A P).
apply conga_sym.
assumption.
assumption.
apply conga_sym.
assumption.
}
clear H55 H58.
assert(Prod O C1 C1' A1 D1 B1).
{
unfold Prod.
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
}

assert(exists Y : Tpoint, Prod O E C1' A1 D1 Y /\ Prod O E C1' C1 B1 Y).
{
apply(prod_x_axis_unit_change O C1 C1' A1 D1 C1 B1 E).
repeat split; Col.
ColR.
ColR.
Col.
exists B1.
split; auto.
apply prod_1_l; Col.
ColR.
}
ex_and H58 Y.
assert(HH:=prod_y_axis_change O E C1' E' A1 D1 Y H58 H9).
{
assert(Y = AD).
apply(prod_uniqueness O E E' A1 D1); auto.
subst Y.
assert(HP:=prod_y_axis_change O E C1' E' C1 B1 AD H60 H9).
left.
assumption.
}
spliter.
subst M.
apply False_ind.
unfold Midpoint in H7.
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
unfold Length in H4.
tauto.
unfold Length in H7.
tauto.
unfold Length in H7.
tauto.
assumption.
Qed.

Lemma length_existence : forall O E E' A B,
  ~ Col O E E' -> exists AB, Length O E E' A B AB.
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
unfold Length.
assert(AB = O \/ Out O E AB).
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
unfold LeP.
induction H2.
right; auto.
left.
unfold LtP.
exists AB.
repeat split.
apply diff_A_O; Col.
unfold Out in H2.
tauto.
auto.
induction H0.
right; assumption.
left; assumption.
Qed.

(** Known as Euklid *)
Lemma l15_7 : forall O E E' A B C H AB AC AH AC2,
  O<>E -> Per A C B -> Perp_at H C H A B ->
  Length O E E' A B AB -> Length O E E' A C AC -> Length O E E' A H AH ->
  (Prod O E E' AC AC AC2 <-> Prod O E E' AB AH AC2).
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
unfold Length in H3.
spliter.
unfold LeP in H8.
induction H8.
unfold LtP in H8.
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
apply (length_uniqueness O E E' A A); auto.
apply length_id_2.
assumption.
subst AH.
apply perp_in_per in H2.
assert(A = C).
apply (l8_7 B);
finish.
subst C.
assert(AC = O).
apply (length_uniqueness O E E' A A); auto.
subst AC.
split;intros;
assert(AC2=O).
apply (prod_uniqueness O E E' O O); auto.
apply prod_0_r; Col.
subst AC2.
apply prod_0_r; Col.
apply (prod_uniqueness O E E' AB O); auto.
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
assert(Out A H C').
unfold Out.
repeat split; auto.
intro.
subst C'.
apply cong_symmetry in H12.
apply cong_identity in H12.
subst C.
tauto.

assert(HH:= segment_construction_2 C A A H H10).
ex_and HH H'.
assert(Out A C H').
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

assert(Cong H C H' C' /\ (H <> C -> CongA A H C A H' C' /\ CongA A C H A C' H')).
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
apply perp_in_perp_bis in H2.
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
apply per_perp_in in H1.
apply perp_in_comm in H1.
apply perp_in_perp_bis in H1.
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
apply perp_in_perp_bis in HH.
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
assert(exists P : Tpoint, Prod O E E' AC' AC P).

apply(prod_exists O E E' H7 AC' AC).
unfold Length in H24.
tauto.
unfold Length in H4.
tauto.
ex_and H25 P.

assert(Perp C H A B).
apply perp_in_perp_bis in H2.
induction H2.
apply perp_distinct in H2.
tauto.
assumption.

assert(Prodg O E E' AH' AB P).
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
assert(A <> C').
intro.
subst C'.
unfold CongA in H20.
tauto.
assert(Col A H H').
ColR.
assert(A <> H').
intro.
subst H'.
unfold CongA in H19.
tauto.
ColR.

left.
finish.
left.
assumption.

assert(Prod O E E' AH' AB P).
induction H27.
assumption.
spliter.
apply False_ind.
apply H27.
repeat split; Col.
unfold Length in H23.
tauto.


assert(Length O E E' A H' AH).
apply(length_eq_cong_2 O E E' A H A H' AH H5).
Cong.
assert(AH = AH').
apply (length_uniqueness O E E' A H'); auto.
subst AH'.

assert(Length O E E' A C' AC).
apply(length_eq_cong_2 O E E' A C A C' AC H4).
Cong.
assert(AC = AC').
apply (length_uniqueness O E E' A C'); auto.
subst AC'.

split.
intro.
assert(P = AC2).
apply (prod_uniqueness O E E' AC AC); auto.
subst P.
apply prod_comm.
assumption.

intro.
assert(P = AC2).
apply (prod_uniqueness O E E' AB AH); auto.
apply prod_sym.
assumption.
subst P.
assumption.
Qed.

Lemma l15_7_1 : forall O E E' A B C H AB AC AH AC2,
  O<>E -> Per A C B -> Perp_at H C H A B ->
  Length O E E' A B AB -> Length O E E' A C AC -> Length O E E' A H AH ->
  Prod O E E' AC AC AC2 ->
  Prod O E E' AB AH AC2.
Proof.
intros.
destruct(l15_7 O E E' A B C H AB AC AH AC2 H0 H1 H2 H3 H4 H5).
apply H7.
assumption.
Qed.

Lemma l15_7_2 : forall O E E' A B C H AB AC AH AC2,
  O<>E -> Per A C B -> Perp_at H C H A B ->
  Length O E E' A B AB -> Length O E E' A C AC -> Length O E E' A H AH ->
  Prod O E E' AB AH AC2 ->
  Prod O E E' AC AC AC2.
Proof.
intros.
destruct(l15_7 O E E' A B C H AB AC AH AC2 H0 H1 H2 H3 H4 H5).
apply H8.
assumption.
Qed.


Lemma length_sym : forall O E E' A B AB,
  Length O E E' A B AB -> Length O E E' B A AB.
Proof.
intros.
unfold Length in *.
spliter.
repeat split; auto.
Cong.
Qed.

Lemma pythagoras : forall O E E' A B C AC BC AB AC2 BC2 AB2,
  O<>E -> Per A C B ->
  Length O E E' A B AB -> Length O E E' A C AC -> Length O E E' B C BC ->
  Prod O E E' AC AC AC2 -> Prod O E E' BC BC BC2 -> Prod O E E' AB AB AB2 ->
  Sum  O E E' AC2 BC2 AB2.
Proof.
intros.
assert(~Col O E E' /\ Col O E AB2 /\ Col O E AC2 /\ Col O E BC).
unfold Prod in *.
spliter.
unfold Ar2 in H4 ,H5 ,H6.
repeat split; tauto.
spliter.

induction(Col_dec A C B).
assert(HH:=l8_9 A C B H0 H11).
induction HH.
subst C.
assert(AB = BC).
apply(length_uniqueness O E E' A B).
assumption.
apply length_sym.
assumption.
subst BC.
assert(AB2 = BC2).
apply(prod_uniqueness O E E' AB AB); auto.
subst BC2.

assert(AC = O).
apply(length_uniqueness O E E' A A).
assumption.
apply length_id_2; assumption.
subst AC.
assert(AC2=O).
apply(prod_uniqueness O E E' O O).
assumption.
apply prod_0_l; Col.
subst AC2.
apply sum_O_B; Col.

subst C.
assert(AB = AC).
apply(length_uniqueness O E E' A B).
assumption.
assumption.
subst AC.
assert(AB2 = AC2).
apply(prod_uniqueness O E E' AB AB); auto.
subst AC2.

assert(BC = O).
apply(length_uniqueness O E E' B B).
assumption.
apply length_id_2; assumption.
subst BC.
assert(BC2=O).
apply(prod_uniqueness O E E' O O).
assumption.
apply prod_0_l; Col.
subst BC2.
apply sum_A_O; Col.



assert(exists X : Tpoint, Col A B X /\ Perp A B C X).
apply(l8_18_existence A B C); Col.
ex_and H12 P.
assert(Perp_at P A B C P).
apply(l8_14_2_1b_bis A B C P P H13); Col.
assert(Bet A P B /\ A <> P /\ B <> P).
apply(l11_47 A B C P H0).
finish.
spliter.

assert(HL1:= length_existence O E E' A P H7).
assert(HL2:= length_existence O E E' B P H7).
ex_and HL1 AP.
ex_and HL2 BP.

assert(Sum O E E' AP BP AB).
apply(triangular_equality_bis O E E' A P B AP BP AB); auto.
apply length_sym.
assumption.

assert(Prod O E E' AB AP AC2).
apply(l15_7_1 O E E' A B C P AB AC AP AC2 H H0); finish.

assert(Prod O E E' AB BP BC2).
eapply(l15_7_1 O E E' B A C P AB BC); finish.
apply length_sym;auto.

assert(HD:=distr_l O E E' AB AP BP AB AC2 BC2 AB2 H20 H21 H22 H6).
assumption.
Qed.

Lemma is_length_exists : forall O E E' X Y,
  ~ Col O E E' -> exists XY, Is_length O E E' X Y XY.
Proof.
intros O E E' X Y HNC.
elim (eq_dec_points X Y); intro HXY;
[treat_equalities; exists O; left; apply length_id_2; assert_diffs; auto|
destruct (length_existence O E E' X Y) as [XY HLength]; Col; exists XY; left; auto].
Qed.

End T15.