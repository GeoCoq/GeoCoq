  (* Gabriel Braun April 2013 *)

Require Export GeoCoq.Tarski_dev.Ch12_parallel.
(*Require Export Ch12_parallel_inter_dec.*)

Section L13_1.

  Context `{MT:Tarski_2D}.
  Context `{EqDec:EqDecidability Tpoint}.

(** Pappus Desargues *)

Lemma per2_col_eq : forall A P P' B, A <> P -> A <> P' -> Per A P B -> Per A P' B -> Col P A P' -> P = P'.
Proof.
intros.
induction(eq_dec_points P B).
subst B.
assert( A = P' \/ P = P').
apply(l8_9 A P' P H2); Col.
induction H4.
contradiction.
assumption.
induction(eq_dec_points P' B).
subst B.
assert(A = P \/ P' = P).
apply(l8_9 A P P' H1); Col.
induction H5; auto.
contradiction.

apply per_perp_in in H1; auto.
apply per_perp_in in H2; auto.

apply perp_in_comm in H1.
apply perp_in_comm in H2.
apply perp_in_perp in H1.
apply perp_in_perp in H2.
induction H1; induction H2.
apply(l8_18_unicity P A B P P'); Col.
apply perp_not_col; auto.
apply perp_left_comm.
apply(perp_col A P' B P' P); Perp.
Col.
apply perp_distinct in H2.
tauto.
apply perp_distinct in H1.
tauto.
apply perp_distinct in H1.
tauto.
Qed.

Lemma per_distinct : forall A B C, Per A B C -> A <> B -> A <> C.
Proof.
intros.
intro.
subst C.
apply H0.
apply (l8_8).
assumption.
Qed.

Lemma per2_preserves_diff : forall O A B A' B', O <> A' -> O <> B' -> Col O A' B' -> Per O A' A -> Per O B' B -> A' <> B' -> A <> B.

Proof.
intros.
intro.
subst B.
apply H4.
apply(per2_col_eq O A' B' A);Col.
Qed.

Lemma per23_preserves_bet : forall A B C B' C', Bet A B C -> A <> B' -> A <> C' -> Col A B' C' -> Per A B' B -> Per A C' C -> Bet A B' C'.
Proof.
intros.
assert(HC:Col A B C).
apply bet_col in H; Col.

induction(eq_dec_points B B').
subst B'.

assert(Col A C' C).
ColR.

assert(A = C' \/ C = C').
apply l8_9; auto.
induction H6.
contradiction.
subst C'.
assumption.

assert(A <> C).
intro.
subst C.
apply l8_8 in H4.
contradiction.

assert(C <> C').
intro.
subst C'.

assert(Col A B' B).
ColR.

assert(A = B' \/ B = B').
apply l8_9; auto.
induction H8; contradiction.

assert(Perp A B' B' B).
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp in H3.
induction H3; Perp.
apply perp_distinct in H3.
tauto.

assert(Perp A C' C' C).
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp in H4.
induction H4; Perp.
apply perp_distinct in H4.
tauto.

assert(Par B B' C C').
apply(l12_9 B B' C C' A B');Perp.
apply perp_sym.
apply(perp_col _ C'); Perp.
ColR.

induction(eq_dec_points B C).
subst C.
assert(B' = C').
apply(per2_col_eq A B' C' B); Perp.
Col.
subst C'.
Between.

assert(~Col A B' B).
apply per_not_col in H3; auto.

assert(~Col A C' C).
apply per_not_col in H4; auto.

assert(B' <> C').
intro.
subst C'.
clean_trivial_hyps.

assert(Col B C B').
apply(per_per_col B C A B'); Perp.
apply H13; ColR.

induction H10.
apply l12_6 in H10.

assert(two_sides B B' A C).
repeat split;auto.
intro.
assert(A = B' \/ B = B').
apply l8_9; Col.
induction H12; tauto.
intro.
apply H13; ColR.
exists B.
split; Col.

assert(two_sides B B' A C').
apply l9_2.
apply(l9_8_2 B B' C C' A); auto.
apply l9_2.
assumption.
unfold two_sides in H16.
spliter.
ex_and H19 T.
assert(T = B').
apply bet_col in H20.
apply (l6_21 B B' A B'); Col.
ColR.
subst T.
assumption.
spliter.
apply False_ind.
apply H12.
ColR.
Qed.

Lemma per23_preserves_bet_inv : forall A B C B' C', Bet A B' C' -> A <> B' -> Col A B C -> Per A B' B -> Per A C' C -> Bet A B C.
Proof.
intros.

induction(eq_dec_points B B').
subst B'.
assert(Col A C' C).
apply bet_col in H.
ColR.
assert(A = C' \/ C = C').
apply(l8_9 A C' C); auto.
induction H5.
subst C'.
apply between_identity in H.
contradiction.
subst C'.
assumption.

assert(Perp A B' B' B).
apply per_perp_in in H2.
apply perp_in_comm in H2.
apply perp_in_perp in H2.
induction H2.
Perp.
apply perp_distinct in H2.
tauto.
auto.
auto.


assert(Perp A C' C' C).
apply per_perp_in in H3.
apply perp_in_comm in H3.
apply perp_in_perp in H3.
induction H3.
Perp.
apply perp_distinct in H3.
tauto.
intro.
subst C'.
apply between_identity in H.
contradiction.
intro.
subst C'.
induction(eq_dec_points A C).
subst C.
apply between_identity in H.
contradiction.
assert(Col A B' B).
apply bet_col in H.
ColR.
assert(A = B' \/ B = B').
apply(l8_9 A B' B); auto.
induction H8;contradiction.

assert(Perp A B' C' C).
apply bet_col in H.
apply(perp_col _ C'); Col.

assert( Par B' B C' C).
apply(l12_9 B' B C' C A B').
Perp.
Perp.

induction(eq_dec_points B C).
subst C.
Between.

induction H8.
assert(B' <> C').
intro.
subst C'.
apply H8.
exists B'.
split; Col.


assert(HH:=l12_6 B' B C' C H8).

assert(two_sides B' B A C').
repeat split; auto.
intro.
assert(A = B' \/ B = B').
apply(l8_9 A B' B); auto.
induction H12;contradiction.
intro.
assert(Col A B' B).
assert_cols.
ColR.
assert(A = B' \/ B = B').
apply(l8_9 A B' B); auto.
induction H13;contradiction.
exists B'.
split; Col.

assert(two_sides B' B C A).
apply(l9_8_2 B' B C' C A); auto.
apply l9_2.
assumption.
unfold two_sides in H12.
spliter.
ex_and H15 T.

assert(A <> C).
intro.
subst C.
apply between_identity in H16.
subst T.
contradiction.

assert (T = B).
assert_cols.
apply (l6_21 A C B' B); Col.
intro.
assert(Col A B' B).
ColR.
assert(A = B' \/ B = B').
apply(l8_9 A B' B); auto.
induction H22;contradiction.
subst T.
Between.


spliter.
assert_cols.
assert(Col A B' B).
ColR.
assert(A = B' \/ B = B').
apply(l8_9 A B' B); auto.
induction H15;contradiction.
Qed.



Lemma per13_preserves_bet : forall A B C A' C', Bet A B C -> B <> A' -> B <> C' -> Col A' B C' -> Per B A' A -> Per B C' C -> Bet A' B C'.
Proof.
intros.
assert(Col A B C).
apply bet_col in H.
Col.

induction(eq_dec_points A A').
subst A'.
assert(Col B C' C).
ColR.

assert(B = C' \/ C = C').
apply l8_9; auto.
induction H7.
contradiction.
subst C'.
assumption.

assert(C <> C').
intro.
subst C'.
assert(Col A A' B).
ColR.
assert(B = A' \/ A = A').
apply l8_9; Col.
induction H8; tauto.

assert(Perp B A' A' A).
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp in H3.
induction H3.
Perp.
apply perp_distinct in H3.
tauto.

assert(Perp B C' C' C).
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp in H4.
induction H4.
Perp.
apply perp_distinct in H4.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' B A');Perp.
apply perp_sym.
apply(perp_col _ C'); Perp.
ColR.

induction H10.
assert(HH:=par_strict_symmetry A A' C C' H10).
apply l12_6 in H10.
apply l12_6 in HH.

assert(~Col A A' B).
apply per_not_col in H3; auto.
intro.
apply H3.
Col.

assert(~Col C C' B).
apply per_not_col in H4; auto.
intro.
apply H4.
Col.

assert(one_side A A' B C).
apply out_one_side.
left; auto.
repeat split.
intro.
subst A.
unfold one_side in H10.
ex_and H10 X.
unfold two_sides in H13.
spliter.
apply H14.
Col.
intro.
subst C.
unfold one_side in H10.
ex_and H10 X.
unfold two_sides in H10.
spliter.
apply H14.
Col.
left.
assumption.

assert(one_side C C' B A).
apply out_one_side.
left; auto.
repeat split.
intro.
subst C.
apply H12.
Col.
intro.
subst C.
unfold one_side in H10.
ex_and H10 X.
unfold two_sides in H10.
spliter.
apply H15.
Col.
left.
Between.

assert(one_side A A' B C').
apply(one_side_transitivity _ _ _ C); auto.
assert(one_side C C' B A').
apply(one_side_transitivity _ _ _ A); auto.

apply invert_one_side in H15.
apply invert_one_side in H16.
assert(HP:= col_one_side_out A' A B C' H2 H15).
assert(out C' B A').
apply(col_one_side_out C' C B A'); Col.

unfold out in *.
spliter.

induction H19.
Between.
induction H22.
Between.
apply False_ind.
apply H18.
apply (between_equality _ _ B); Between.
spliter.

induction(eq_dec_points A C).
subst C.
apply between_identity in H.
subst B.
clean_duplicated_hyps.
clean_trivial_hyps.
apply l8_8 in H4.
contradiction.
assert(Col B C' C).
ColR.
apply per_not_col in H4; auto.
contradiction.
Qed.

Lemma per13_preserves_bet_inv : forall A B C A' C', Bet A' B C' -> B <> A' -> B <> C' ->  Col A B C  -> Per B A' A -> Per B C' C -> Bet A B C.
Proof.
intros.
assert(Col A' B C').
apply bet_col in H.
Col.

induction(eq_dec_points A A').
subst A'.
assert(Col B C' C).
ColR.
assert(HH:=l8_9 B C' C H4 H6 ).
induction HH.
contradiction.
subst C'.
assumption.

assert(C <> C').
intro.
subst C'.
assert(Col B A' A).
ColR.
assert(HH:=l8_9 B A' A H3 H7).
induction HH;
contradiction.

assert(Perp B A' A' A).
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp in H3.
induction H3.
Perp.
apply perp_distinct in H3.
tauto.

assert(Perp B C' C' C).
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp in H4.
induction H4.
Perp.
apply perp_distinct in H4.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' B A');Perp.
apply perp_sym.
apply(perp_col _ C'); Perp.
ColR.

induction H10.
assert(HH:=par_strict_symmetry A A' C C' H10).
apply l12_6 in H10.
apply l12_6 in HH.

assert(~Col A' A B).
apply per_not_col in H3; auto.
intro.
apply H3.
Col.

assert(~Col C' C B).
apply per_not_col in H4; auto.
intro.
apply H4.
Col.

assert(one_side A' A B C').
apply out_one_side.
left; auto.
repeat split.
intro.
subst A'.
apply H11.
Col.
intro.
subst C'.
apply one_side_symmetry in H10.
unfold one_side in H10.
ex_and H10 X.
unfold two_sides in H10.
spliter.
apply H14.
Col.
left.
assumption.

assert(one_side C' C B A').
apply out_one_side.
left; auto.
repeat split.
intro.
subst C'.
apply H12.
Col.
intro.
subst C'.
apply one_side_symmetry in H10.
unfold one_side in H10.
ex_and H10 X.
unfold two_sides in H10.
spliter.
apply H15.
Col.
left.
Between.

assert(one_side A' A B C).
apply(one_side_transitivity _ _ _ C'); auto.
apply invert_one_side.
apply one_side_symmetry.
assumption.

assert(one_side C C' B A).
apply(one_side_transitivity _ _ _ A'); auto.
apply invert_one_side.
assumption.
apply one_side_symmetry.
assumption.

apply invert_one_side in H15.

assert(HP:= col_one_side_out A A' B C H2 H15).

assert(out C B A).
apply(col_one_side_out C C' B A); Col.

unfold out in *.
spliter.

induction H19.
Between.
induction H22.
Between.
apply False_ind.
apply H18.
apply (between_equality _ _ B); Between.

(****************************)

spliter.
assert(Perp A' C' A A').
apply (perp_col _ B); Perp.
intro.
subst C'.
apply between_identity in H.
subst A'.
apply perp_distinct in H9.
tauto.
apply perp_not_col in H14.

apply False_ind.
apply H14.
ColR.
Qed.

Lemma per3_preserves_bet1 : forall O A B C A' B' C', Col O A B -> Bet A B C -> O <> A' -> O <> B' -> O <> C'
                                                    -> Per O A' A -> Per O B' B -> Per O C' C
                                                    -> Col A' B' C' -> Col O A' B' -> Bet A' B' C'.

Proof.
intros O A B C A' B' C'.
intro HC.
intros.

induction(eq_dec_points A B).
subst B.
assert(A' = B').
apply(per2_col_eq O A' B' A H0 H1 H3 H4); Col.
subst B'.
Between.

induction (eq_dec_points A A').
subst A'.
induction(eq_dec_points B B').
subst B'.
assert(Col O C C').
apply bet_col in H.
ColR.

assert(C = C').
apply bet_col in H.
assert(O = C' \/ C = C').
apply(l8_9 O C' C H5); Col.
induction H10.
contradiction.
assumption.
subst C'.
assumption.

induction(eq_dec_points A B').
subst B'.
Between.

assert(A <> C).
intro.
subst C.
apply between_identity in H.
contradiction.

assert( ~ Col O B' B).
apply(per_not_col O B' B H1); auto.

assert(C <> C').
intro.
subst C'.
clean_trivial_hyps.
apply H12.
apply bet_col in H.
ColR.

assert(Perp B B' O A).

apply per_perp_in in H4; auto.
apply perp_in_perp in H4.
induction H4.
apply perp_distinct in H4.
tauto.
apply perp_sym.
apply perp_right_comm.
apply(perp_col O B' B' B A); auto.
Col.

assert(Perp C C' O A).

apply per_perp_in in H5; auto.
apply perp_in_perp in H5.
induction H5.
apply perp_distinct in H5.
tauto.
apply perp_sym.
apply perp_right_comm.
apply(perp_col O C' C' C A); auto.
apply bet_col in H.
ColR.

assert(Par B B' C C').
apply(l12_9 B B' C C' O A);auto.
induction H16.

assert(HH:=l12_6 B B' C C' H16).

assert(two_sides B B' A C).
unfold two_sides.
repeat split; Col.
assert(~Col B' A B).
apply(perp_not_col).
apply perp_left_comm.
apply(perp_col A O B B' B'); Col.
finish.
intro.
apply H17.
Col.
intro.
apply H16.
exists C.
split; Col.
exists B.
split; Col.
assert(two_sides B B' C' A).
apply(l9_8_2 B B' C C' A).

apply l9_2.
assumption.
assumption.
unfold two_sides in H18.
spliter.
ex_and H21 T.
assert(B'=T).
apply (l6_21 B B' A C'); Col.
intro.
subst C'.
apply between_identity in H22.
subst T.
contradiction.
subst T.
apply between_symmetry.
assumption.
spliter.

assert(Per O C' B).
apply(per_col O C' C B); Col.
assert(B'=C').
apply(per2_col_eq O B' C' B); Col.
ColR.
subst C'.
Between.

(*-------------------------------*)

induction(eq_dec_points A' B').
subst B'.
Between.

induction(eq_dec_points B C).
subst C.
assert(B' = C').
apply(per2_col_eq O B' C' B); auto.
ColR.
subst C'.
Between.

induction(eq_dec_points B B').
subst B'.
induction(eq_dec_points A' B).
subst B.
Between.

assert(C <> C').
intro.
subst C'.

assert( ~ Col O A' A).
apply(per_not_col O A' A ); auto.
apply H13.
apply bet_col in H.
ColR.

assert(Perp A A' O A').
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp in H3.
induction H3.
finish.
apply perp_distinct in H3.
tauto.

assert(Perp C C' O A').
apply per_perp_in in H5; auto.
apply perp_in_comm in H5.
apply perp_in_perp in H5.
induction H5.
apply perp_sym.
apply (perp_col _ C'); auto.
finish.
ColR.
apply perp_distinct in H5.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' O A');auto.
induction H16.


assert(HH:=l12_6 A A' C C' H16).

(*--------------------------------*)
assert(one_side C C' A A').
apply(l12_6 C C' A A').
finish.
assert(one_side C C' A B).
apply(out_one_side C C' A B).
left.
intro.
apply H16.
exists A.
split; Col.
unfold out.
repeat split; auto.
intro.
subst C.
apply between_identity in H.
contradiction.
right.
Between.

assert(one_side C C' A' B).
apply(one_side_transitivity C C' A' A); auto.
apply one_side_symmetry.
assumption.

assert(out C' B A').
induction H6.
unfold out.
repeat split.
intro.
subst C'.
clean_trivial_hyps.
unfold one_side in H17.
ex_and H17 T.
unfold two_sides in H4.
spliter.
apply H17.
Col.
intro.
subst C'.
apply H16.
exists A'.
split; Col.
left.
Between.

induction H6.

assert(two_sides C C' B A').
unfold two_sides.
repeat split.
intro.
subst C'.
unfold Par_strict in H16.
tauto.
intro.
unfold one_side in H18.
ex_and H18 T.
unfold two_sides in H21.
spliter.
contradiction.
intro.
apply H16.
exists A'.
split; Col.
exists C'.
split; Col.
apply one_side_symmetry in H19.
apply l9_9_bis in H19.
contradiction.

unfold out.
repeat split.
intro.
subst C'.
apply H16.
exists A.
apply bet_col in H.
split; Col.
intro.
subst C'.
apply H16.
exists A'.
split; Col.
right; auto.

(*****************************)

assert(out A' B C').
induction H6.
unfold out.
repeat split.
intro.
subst A'.
clean_trivial_hyps.
apply H16.
exists C.
apply bet_col in H.
split; Col.
intro.
subst C'.
unfold out in H20.
tauto.
left.
auto.

induction H6.
unfold out in H20.
spliter.
unfold out.
repeat split.
intro.
subst A'.
apply H16.
exists C.
apply bet_col in H.
split; Col.
auto.
induction H22.
left.
Between.

apply False_ind.
apply H21.
apply (between_equality _ _ B); Between.

(***************************)

assert(one_side A A' B C).
apply(out_one_side A A' B C).
right.
intro.
apply H16.
exists C.
split; Col.
unfold out.
repeat split; auto.
intro.
subst C.
apply between_identity in H.
contradiction.

assert(one_side A A' C' B).
apply(one_side_transitivity A A' C' C);
apply one_side_symmetry; auto.


(***********************)
assert(two_sides A A' B C').
unfold two_sides.
repeat split.
intro.
subst A'.
unfold Par_strict in H16.
tauto.
intro.
unfold one_side in H21.
ex_and H21 T.
unfold two_sides in H21.
spliter.
contradiction.
intro.
apply H16.
exists C'.
split; Col.
exists A'.
split; Col.
Between.
apply one_side_symmetry in H22.
apply l9_9_bis in H22.
contradiction.

unfold out in *.
spliter.
clean_duplicated_hyps.

induction H25; induction H23.
assumption.
apply False_ind.
apply H20.
apply(between_equality _ _ A'); Between.
apply False_ind.
apply H10.
apply(between_equality _ _ C'); Between.
apply False_ind.
apply H24.
apply(between_equality _ _ B); Between.
spliter.


assert(~Col O C' C).
apply(per_not_col); auto.
apply False_ind.
apply H20.

assert(A<>C).
intro.
subst C.
apply between_identity in H.
subst B.
tauto.
apply bet_col in H.
ColR.

(********************************)

assert(Perp A A' O A').
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp in H3.
induction H3.
finish.
apply perp_distinct in H3.
tauto.

assert(Perp B B' O A').
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp in H4.
induction H4.
apply perp_sym.
apply (perp_col _ B'); Col.
finish.
apply perp_distinct in H4.
tauto.

assert(Par A A' B B').
apply(l12_9 A A' B B' O A');auto.

induction H15.
assert(HH:=l12_6 A A' B B' H15).



assert(two_sides B B' A C).
unfold two_sides.
repeat split; Col.
intro.
apply H15.
exists A.
split; Col.
intro.
apply H11.
apply (l6_21 B B' A C); Col.
intro.
apply H15.
exists A.
split; Col.
intro.
subst C.
apply between_identity in H.
subst B.
tauto.
exists B.
split; Col.

assert(one_side B B' A A').
apply(l12_6 B B' A A').
finish.

assert(HP:= l9_8_2 B B' A A' C H16 H17).


induction(eq_dec_points C C').
subst C'.
unfold two_sides in HP.
spliter.
ex_and H21 T.

assert(T = B').
apply (l6_21 B B' A' C); Col.
intro.
subst A'.
apply between_identity in H22.
subst T.
contradiction.
subst T.
assumption.

assert(Perp C C' O A').
apply per_perp_in in H5; auto.
apply perp_in_comm in H5.
apply perp_in_perp in H5.
induction H5.
apply perp_sym.
apply (perp_col _ C'); finish.
ColR.
apply perp_distinct in H5.
tauto.

assert(Par B B' C C').
apply(l12_9 B B' C C' O A');auto.
induction H20.

assert(HQ:=l12_6 B B' C C' H20).

assert(two_sides B B' C' A').
apply(l9_8_2 B B' C C' A'); auto.
apply l9_2.
assumption.
unfold two_sides in H21.
spliter.
ex_and H24 T.
assert(T = B').
apply (l6_21 B B' A' C'); Col.
intro.
subst C'.
apply between_identity in H25.
subst T.
contradiction.
subst T.
Between.
spliter.
unfold two_sides in HP.
spliter.
apply False_ind.
apply H26.
ColR.
spliter.

apply perp_left_comm in H13.
apply perp_not_col in H13.
apply False_ind.
apply H13.
ColR.
Qed.


Lemma per3_preserves_bet2_aux : forall O A B C B' C', Col O A C -> A <> C' ->
                               Bet A B' C' -> O <> A -> O <> B' -> O <> C'
                               -> Per O B' B -> Per O C' C
                               -> Col A B C -> Col O A C' -> Bet A B C.
Proof.
intros O A B C B' C'.
intro HX.
intros.
induction(eq_dec_points A B).
subst B.
Between.
induction(eq_dec_points B C).
subst C.
Between.

assert(Col O A B').
apply bet_col in H0.
ColR.
assert(Col O B' C').
apply bet_col in H0.
ColR.

induction(eq_dec_points B B').
subst B'.
assert(Col O C C').
apply bet_col in H0.
ColR.
assert(C = C').
apply(per_col_eq C C' O); finish.
subst C'.
assumption.
assert(C <> C').
intro.
subst C'.
apply per_not_col in H4; auto.
apply H4.
ColR.

assert(Perp O A C C').
apply per_perp_in in H5; auto.
apply perp_in_comm in H5.
apply perp_in_perp in H5.
induction H5.
apply (perp_col _ C'); finish.
apply perp_distinct in H5.
tauto.

assert(Perp O A B B').
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp in H4.
induction H4.
apply (perp_col _ B'); finish.
apply perp_distinct in H4.
tauto.

assert(Par B B' C C').
apply(l12_9 B B' C C' O A);finish.

induction H16.
assert(HH:=l12_6 B B' C C' H16).
assert(two_sides B B' A C').
repeat split; finish.
intro.
assert(Per B B' A).
apply(per_col B B' O A); finish.
apply per_not_col in H18; auto.
apply H18.
Col.
intro.
subst B'.
clean_trivial_hyps.
apply H16.
exists C.
split; Col.
intro.
apply H16.
exists C'.
split; Col.
exists B'.
split; finish.

assert(two_sides B B' C A).
apply(l9_8_2 B B' C' C A).
apply l9_2; auto.
apply one_side_symmetry; auto.
unfold two_sides in H18.
spliter.
ex_and H21 T.
assert(B = T).
apply (l6_21 A C B' B); Col.
assert(A <> C).
intro.
subst C.
apply between_identity in H22.
subst T.
contradiction.
intro.
apply bet_col in H0.
apply H20.
ColR.
subst T.
Between.

spliter.

assert(B' <> C').
intro.
subst C'.
clean_trivial_hyps.
assert(Perp O B' C B').
apply(perp_col O A C B' B'); Col.
apply perp_left_comm in H0.
apply perp_not_col in H0.
apply H0.
ColR.

assert(Per C C' B').
apply(per_col C C' O B'); finish.
apply per_not_col in H21; auto.
apply False_ind.
apply H21.
Col.
Qed.

Lemma per3_preserves_bet2 : forall O A B C A' B' C', Col O A C -> A' <> C' ->
                               Bet A' B' C' -> O <> A' -> O <> B' -> O <> C'
                               -> Per O A' A -> Per O B' B -> Per O C' C
                               -> Col A B C -> Col O A' C' -> Bet A B C.

Proof.
intros O A B C A' B' C'.
intro HX.
intros.
induction(eq_dec_points A A').
subst A'.
apply (per3_preserves_bet2_aux O A B C B' C');auto.
induction(eq_dec_points C C').
subst C'.
apply between_symmetry.
apply(per3_preserves_bet2_aux O C B A B' A'); finish.

assert(Perp O A' C C').
apply per_perp_in in H6; auto.
apply perp_in_comm in H6.
apply perp_in_perp in H6.
induction H6.
apply (perp_col _ C'); finish.
apply perp_distinct in H6.
tauto.

assert(Perp O A' A A').
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp in H4.
induction H4.
finish.
apply perp_distinct in H4.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' O A');finish.

induction H13.
assert(HH:=l12_6 A A' C C' H13).
apply par_strict_symmetry in H13.
assert(HP:=l12_6 C C' A A' H13).

induction(eq_dec_points B B').
subst B'.

assert(one_side A' A B C').
apply out_one_side.
right.
intro.
apply H13.
exists C'.
split; Col.
repeat split.
intro.
subst A'.
apply H13.
exists C.
split; Col.
auto.
left; auto.
apply invert_one_side in H14.
assert(one_side A A' B C).
apply (one_side_transitivity _ _ _ C').
assumption.
apply one_side_symmetry.
assumption.

assert(out A B C).
apply (col_one_side_out A A');auto.

assert(one_side C' C B A').
apply out_one_side.
right.
intro.
apply H13.
exists A'.
split; Col.
repeat split.
intro.
subst C'.
apply H13.
exists A.
split; Col.
auto.
left; Between.
apply invert_one_side in H17.
assert(one_side C C' B A).
apply (one_side_transitivity _ _ _ A').
assumption.
apply one_side_symmetry.
assumption.
apply one_side_symmetry in H18.

assert(out C A B).
apply (col_one_side_out C C');Col.
unfold out in *.
spliter.


induction H23; induction H21.
assumption.
assumption.
assert(A = C).
apply (between_equality A C B); auto.
subst C.
apply False_ind.
apply H13.
exists A.
split; Col.
assert(B = C).
apply (between_equality B C A); Between.
subst C.
Between.

(****************************************************************************************)

assert(Perp O A' B B').
apply per_perp_in in H5; auto.
apply perp_in_comm in H5.
apply perp_in_perp in H5.
induction H5.
apply (perp_col _ B'); finish.
apply bet_col in H0.
ColR.
apply perp_distinct in H5.
tauto.

assert(Par B B' A A').
apply(l12_9 B B' A A' O A');finish.

induction H16.
assert(HQ:=l12_6 B B' A A' H16).

assert(Par B B' C C').
apply(l12_9 B B' C C' O A');finish.
induction H17.
assert(HR:=l12_6 B B' C C' H17).

assert(two_sides B B' A' C').
repeat split; auto.
intro.
apply H16.
exists A'.
split; Col.
intro.
apply H17.
exists C'.
split; Col.
exists B'.
split; finish.
apply one_side_symmetry in HQ.
assert(HH1:= l9_8_2 B B' A' A C' H18 HQ).
apply l9_2 in HH1.
apply one_side_symmetry in HR.
assert(HH2:= l9_8_2 B B' C' C A HH1 HR).
unfold two_sides in HH2.
spliter.
ex_and H22 T.
assert(B = T).
apply (l6_21 B B' A C); Col.
intro.
subst C.
apply H13.
exists A.
split; Col.
subst T.
Between.
spliter.

induction(eq_dec_points B C).
subst C.
Between.
assert(Col A C C').
ColR.
apply False_ind.
apply H13.
exists A.
split; Col.
spliter.

induction(eq_dec_points A B).
subst B.
Between.
assert(Col C A A').
ColR.
apply False_ind.
apply H13.
exists C.
split; Col.
spliter.

assert(A <> C).
intro.
subst C.
apply H.
apply(per2_col_eq O A' C' A); Col.

assert(Col O C C').
ColR.
apply False_ind.
apply per_not_col in H6; auto.
apply H6.
Col.
Qed.


Lemma symmetry_preserves_per : forall A P B A' P', Per B P A -> is_midpoint B A A' -> is_midpoint B P P'
                                                   -> Per B P' A'.
Proof.
intros.
assert(HS:=symmetric_point_construction A P).
ex_and HS C.
assert(HS:=symmetric_point_construction C B).
ex_and HS C'.

assert(HH:= symmetry_preserves_midpoint A P C A' P' C' B H0 H1 H3 H2).
unfold Per.
exists C'.
split.
assumption.
unfold Per in H.
ex_and H X.
assert(X = C).
apply(symmetric_point_unicity A P X C); auto.
subst X.
unfold is_midpoint in *.
spliter.
apply (cong_transitivity _ _ B A).
Cong.
apply(cong_transitivity _ _ B C).
assumption.
Cong.
Qed.



Lemma l13_1 : forall A B C P Q R,
   ~ Col A B C -> is_midpoint P B C -> is_midpoint Q A C -> is_midpoint R A B ->
   exists X, exists Y, Perp_in R X Y A B /\ Perp X Y P Q.
Proof.
intros A B C P Q R HC MBC MAC MAB.
assert(Q <> C).
intro.
subst Q.
unfold is_midpoint in MAC.
spliter.
apply cong_identity in H0.
subst C.
apply HC.
Col.
assert(P <> C).
intro.
subst P.
unfold is_midpoint in MBC.
spliter.
apply cong_identity in H1.
subst C.
apply HC.
Col.

assert(D1:Q<>R).
intro.
subst R.
assert(B=C).
apply(symmetric_point_unicity A Q); auto.
subst C.
apply l7_3 in MBC.
contradiction.

assert(D2:R <> B).
intro.
subst R.
unfold is_midpoint in MAB.
spliter.
apply cong_identity in H2.
subst B.
apply HC.
Col.

assert(~Col P Q C).
intro.
apply HC.
unfold is_midpoint in *.
spliter.
apply bet_col in H2.
apply bet_col in H4.
apply bet_col in H6.
ColR.

assert(HH:= l8_18_existence P Q C H1).
ex_and HH C'.

assert(HS1:=symmetric_point_construction C' Q).
ex_and HS1 A'.
assert(HS1:=symmetric_point_construction C' P).
ex_and HS1 B'.

assert(Cong C C' B B').
apply(l7_13 P C C' B B' MBC); finish.
assert(Cong C C' A A').
apply(l7_13 Q C C' A A'); finish.

assert(Per P B' B).
induction(eq_dec_points P C').
subst C'.
unfold is_midpoint in H5.
spliter.
apply cong_symmetry in H8.
apply cong_identity in H8.
subst B'.
apply l8_2.
apply l8_5.

apply(symmetry_preserves_per C C' P B B'); finish.
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_left_comm.
apply (perp_col _ Q); Col.

assert(Per Q A' A).
induction(eq_dec_points Q C').
subst C'.
unfold is_midpoint in H4.
spliter.
apply cong_symmetry in H9.
apply cong_identity in H9.
subst A'.
apply l8_2.
apply l8_5.
apply(symmetry_preserves_per C C' Q A A'); finish.
apply perp_in_per.
apply perp_in_comm.
apply perp_perp_in.
apply perp_left_comm.
apply (perp_col _ P); Col.
finish.

assert(Cl1: Col A' C' Q).
unfold is_midpoint in H4.
spliter.
apply bet_col in H4.
Col.

assert(Cl2: Col B' C' P).
unfold is_midpoint in H5.
spliter.
apply bet_col in H5.
Col.

assert(NE0: P <> Q).
apply perp_distinct in H3; tauto.

assert(NE1 : A' <> B').
intro.
subst B'.
apply NE0.
apply (l7_17 C' A'); auto.

assert(Cl3: Col A' B' P).
induction(eq_dec_points P C').
subst P.
unfold is_midpoint in  H5.
spliter.
apply cong_symmetry in H10.
apply cong_identity in H10.
subst C'.
Col.
induction(eq_dec_points Q C').
subst Q.
unfold is_midpoint in  H4.
spliter.
apply cong_symmetry in H11.
apply cong_identity in H11.
subst C'.
Col.
ColR.

assert(Cl4: Col A' B' Q).
induction(eq_dec_points P C').
subst P.
unfold is_midpoint in  H5.
spliter.
apply cong_symmetry in H10.
apply cong_identity in H10.
subst C'.
Col.
induction(eq_dec_points Q C').
subst Q.
unfold is_midpoint in  H4.
spliter.
apply cong_symmetry in H11.
apply cong_identity in H11.
subst C'.
Col.
ColR.

assert(Cl5:Col A' B' C').
ColR.

assert(NE2 : C <> C').
apply perp_distinct in H3.
tauto.

assert(NE3: A <> A').
intro.
subst A'.
apply cong_identity in H7.
contradiction.

assert(NE4: B <> B').
intro.
subst B'.
apply cong_identity in H6.
contradiction.

assert(Per P A' A).
induction(eq_dec_points A' Q).
subst Q.
unfold is_midpoint in H4.
spliter.
apply cong_identity in H10.
subst C'.
clean_trivial_hyps.
apply perp_left_comm in H3.
apply perp_perp_in in H3.
apply perp_in_comm in H3.
apply perp_in_per in H3.
unfold is_midpoint in MAC.
spliter.
apply bet_col in H2.
apply (per_col P A' C A); Col.
apply l8_2.
apply (per_col A A' Q P); finish.
ColR.

assert(Per Q B' B).
induction(eq_dec_points B' P).
subst P.
unfold is_midpoint in H5.
spliter.
apply cong_identity in H11.
subst C'.
clean_trivial_hyps.
apply perp_perp_in in H3.
apply perp_in_comm in H3.
apply perp_in_per in H3.
unfold is_midpoint in MBC.
spliter.
apply bet_col in H2.
apply (per_col Q B' C B); Col.
apply l8_2.
apply (per_col B B' P Q); finish.
ColR.

assert(Per A' B' B).
apply l8_2.
induction(eq_dec_points B' P).
subst P.
unfold is_midpoint in H5.
spliter.
apply cong_identity in H12.
subst C'.
clean_trivial_hyps.
apply(per_col B B' Q A'); finish.
apply(per_col B B' P A'); finish.

assert(Per B' A' A).
apply l8_2.
induction(eq_dec_points A' Q).
subst Q.
unfold is_midpoint in H4.
spliter.
apply cong_identity in H13.
subst C'.
clean_trivial_hyps.
apply(per_col A A' P B'); finish.
apply(per_col A A' Q B'); finish.


assert(NC1 : ~Col A' B' A).
apply per_not_col in H13; auto.
intro.
apply H13.
Col.

assert(NC2 : ~Col A' B' B).
apply per_not_col in H12; auto.

(****************************************)

assert(HM:=midpoint_existence A' B').
ex_and HM X.

assert(HP:=perp_exists X A' B' NE1).
ex_and HP y.

assert(HH:=ex_sym X y A).
ex_and HH B''.

assert( X <> y).
apply perp_distinct in H15.
tauto.


assert(is_image B'' A X y).
unfold is_image.
left.
repeat split;auto.
ex_and H17 M.
exists M.
split; finish.

assert(is_image A' B' X y).
unfold is_image.
left.
split; auto.
repeat split.
exists X.
split; finish.
left.
finish.
apply l10_4 in H19.

assert(HH:= l10_10 X y B''  B' A A' H19 H20).

assert(Per A' B' B'').
unfold is_image in *.
induction H19; induction H20.
spliter.

apply(image_preserves_per B' A' A A' B' B'' X y); auto.
apply l10_4_spec.
assumption.
spliter.
contradiction.
spliter.
contradiction.
spliter.
contradiction.

unfold is_image in H20.
induction H20.
spliter.
unfold is_image_spec in H22.


assert(one_side A' B' A B'').
induction H16.
assert(Par A' B' A B'').
apply(l12_9 A' B' A B'' X y); finish.

induction H23.
apply( l12_6 A' B' A B'' H23).
spliter.

apply per_not_col in H21; auto.
apply False_ind.
apply H21.
ColR.
intro.
subst B''.
apply cong_symmetry in HH.
apply cong_identity in HH.
subst A'.
apply cong_identity in H7.
subst C'.
tauto.
subst B''.
apply one_side_reflexivity.
intro.
apply NC1.
Col.

assert(one_side A' B' A B).
unfold one_side.
exists C.
split.
unfold two_sides.
repeat split; Col.
intro.
apply H1.
ColR.
exists Q.
split; Col.
unfold is_midpoint in MAC.
tauto.
unfold two_sides.
repeat split; Col.
intro.
apply H1.
ColR.
exists P.
split; Col.
unfold is_midpoint in MBC.
tauto.

(*********************************)


assert( Col B B'' B').
apply(per_per_col B B'' A' B'); finish.

assert(Cong B B' A A').
eCong.

assert(B = B'' \/ is_midpoint B' B B'').
apply( l7_20); Col.

eCong.
induction H27.
subst B''.

exists R.
exists X.

ex_and H17 M.
assert(R = M).
apply (l7_17 A B); auto.
subst M.

assert(A <> B).
intro.
subst B.
apply HC; Col.

assert(Col R A B).
unfold is_midpoint in MAB.
spliter.
apply bet_col in H30.
Col.

assert(X <> R).
intro.
subst X.
assert(Par A B A' B').
apply(l12_9 A B A' B' R y);finish.
induction H16.
Perp.
contradiction.
induction H31.
apply H31.
exists R.

unfold is_midpoint in H14.
spliter.
apply bet_col in H14.
split; Col.
spliter.
apply NC1.
Col.

split.

apply(l8_14_2_1b_bis R X A B R); Col.
induction H16.
apply perp_left_comm.
apply(perp_col _ y); auto.
contradiction.

apply perp_left_comm.
apply(perp_col _ y);auto.
apply perp_sym.
induction(eq_dec_points B' P).
subst P.
apply(perp_col _ A');auto.
Perp.
Col.
apply(perp_col _ B');auto.
apply perp_left_comm.

apply(perp_col _ A');auto.
Perp.
Col.
ColR.

assert(two_sides A' B' B B'').
unfold two_sides.
repeat split; auto.
intro.
apply NC2; Col.
intro.
apply per_not_col in H21; auto.
apply H21.
Col.
intro.
subst B''.
unfold is_midpoint in H27.
spliter.
apply cong_identity in H29.
subst B'.
unfold one_side in H23.
ex_and H23 T.
unfold two_sides in H29.
spliter.
apply H31.
Col.
exists B'.
split; Col.
unfold is_midpoint in H27.
tauto.
assert(one_side A' B' B B'').
apply (one_side_transitivity A' B' B A ).
apply one_side_symmetry.
assumption.
assumption.
apply l9_9 in H28.
contradiction.
spliter.
contradiction.
Qed.



Lemma per_lt : forall A B C, A <> B ->  C <> B -> Per A B C -> lt A B A C /\ lt C B A C.
  Proof.
    intros.
    assert(lt B A A C /\ lt B C A C).
      apply( l11_46 A B C).
        apply per_not_col; auto.
      left.
      assumption.
    spliter.
    split; apply lt_left_comm; assumption.
  Qed.

Lemma cong_perp_conga : forall A B C P,  Cong A B C B -> Perp A C B P -> Conga A B P C B P /\ two_sides B P A C.
Proof.
    intros.
    assert(A <> C /\ B <> P).
      split.
        apply perp_not_eq_1 in H0.
        assumption.
      apply perp_not_eq_2 in H0.
      assumption.
    spliter.
    assert(A <> B).
      intro.
      subst B.
      apply cong_symmetry in H.
      apply cong_identity in H.
      apply H1.
      auto.
    assert(C <> B).
      intro.
      subst B.
      apply cong_identity in H.
      contradiction.
    induction(Col_dec A B C).
      assert(~ Col B A P).
        apply perp_not_col.
        apply perp_comm.
        apply (perp_col _ C); Col.
      assert(Per P B A).
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_perp_in.
        apply perp_sym.
        eapply (perp_col _ C); Col.
      assert(Per P B C).
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_perp_in.
        apply perp_sym.
        eapply (perp_col _ A); Col.
        Perp.
      apply l8_2 in H7.
      apply l8_2 in H8.
      split.
        apply l11_16; auto.
      assert( A = C \/ is_midpoint B A C).
        eapply l7_20; Cong.
      induction H9.
        contradiction.
      unfold two_sides.
      repeat split.
        auto.
        intro.
        apply H6.
        Col.
        intro.
        apply H6.
        ColR.
      exists B.
      unfold is_midpoint in H9.
      spliter.
      split; Between.
    assert(HH:= H0).
    unfold Perp in HH.
    ex_and HH T.
    apply perp_in_col in H6.
    spliter.
    assert(B <> T).
      intro.
      subst T.
      apply H5.
      Col.
    assert(Perp B T A C).
      apply (perp_col _ P); Perp.
    assert(A <> T).
      intro.
      subst T.
      apply perp_comm in H9.
      apply perp_perp_in in H9.
      apply perp_in_comm in H9.
      apply perp_in_per in H9.
      assert(lt B A B C /\ lt C A B C).
        apply( per_lt B A C); auto.
      spliter.
      unfold lt in H10.
      spliter.
      apply H12.
      Cong.
    assert(C <> T).
      intro.
      subst T.
      apply perp_left_comm in H9.
      apply perp_perp_in in H9.
      apply perp_in_comm in H9.
      apply perp_in_per in H9.
      assert(lt B C B A /\ lt A C B A).
        apply( per_lt B C A); auto.
      spliter.
      unfold lt in H11.
      spliter.
      apply H13.
      Cong.
    assert(Perp_in T B T T A).
      apply perp_in_comm.
      apply perp_perp_in.
      apply perp_sym.
      apply (perp_col _ C).
        assumption.
        apply perp_sym.
        apply perp_left_comm.
        apply (perp_col _ P); Perp.
      Col.
    assert(Perp_in T B T T C).
      apply perp_in_comm.
      apply perp_perp_in.
      apply perp_sym.
      apply (perp_col _ A).
        assumption.
        apply perp_sym.
        apply perp_left_comm.
        apply (perp_col _ P); Perp.
      Col.
    assert(Cong T A T C /\ Conga T A B T C B /\ Conga T B A T B C).
      apply( l11_52 A T B C T B); Cong.
        eapply l11_16; auto.
          apply perp_in_per.
          apply perp_in_comm.
          apply perp_in_sym.
          assumption.
        apply perp_in_per.
        apply perp_in_comm.
        apply perp_in_sym.
        assumption.
      assert(lt B T B A /\ lt A T B A).
        apply( per_lt B T A); auto.
        apply perp_in_per.
        assumption.
      spliter.
      apply le_comm.
      unfold lt in H14.
      spliter.
      assumption.
    spliter.
    split.
      induction(Bet_dec P B T).
        apply conga_comm.
        eapply l11_13; auto.
          apply H16.
          Between.
        Between.
      apply conga_comm.
      assert(out B T P).
        unfold out.
        repeat split; auto.
        induction H7.
          right.
          assumption.
        induction H7.
          left.
          Between.
        apply between_symmetry in H7.
        contradiction.
      eapply out_conga.
        apply H16.
        assumption.
        apply out_trivial.
        auto.
        assumption.
      apply out_trivial.
      auto.
    assert(A = C \/ is_midpoint T A C).
      apply l7_20; Col.
    induction H17.
      contradiction.
    unfold two_sides.
    repeat split; Col.
      assert(~ Col T A B).
        apply perp_not_col.
        apply perp_in_perp in H12.
        induction H12.
          apply perp_not_eq_1 in H12.
          tauto.
        Perp.
      intro.
      apply H18.
      ColR.
      assert(~ Col T C B).
        apply perp_not_col.
        apply perp_in_perp in H13.
        induction H13.
          apply perp_not_eq_1 in H13.
          tauto.
        Perp.
      intro.
      apply H18.
      ColR.
    exists T.
    apply midpoint_bet in H17.
    split; Col.
Qed.




Lemma perp_per_bet : forall A B C P, ~Col A B C -> Col A P C -> Per A B C -> Perp_in P P B A C -> Bet A P C.
Proof.
intros.
assert( A <> C).
intro.
subst C.
apply H.
Col.
assert(Bet A P C /\ A <> P /\ C <> P).
apply(l11_47 A C B P); auto.
Perp.
tauto.
Qed.





Lemma ts_per_per_ts : forall A B C D, two_sides A B C D -> Per B C A -> Per B D A -> two_sides C D A B.
Proof.
intros.
assert(HTS:= H).
    unfold two_sides in H.
    spliter.
    ex_and H4 P.
    assert_diffs.
    show_distinct C D.
contradiction.

unfold two_sides.
repeat split; auto.
intro.
assert(A = P).
apply bet_col in H5.
apply (l6_21 A B C D); Col.
subst P.
apply H6.
apply(per2_col_eq A C D B); finish.
intro.
assert(B = P).
apply bet_col in H5.
apply (l6_21 A B C D); Col.
subst P.
apply H6.
apply(per2_col_eq B C D A); finish.
exists P.
split.
finish.

assert(exists X : Tpoint, Col A B X /\ Perp A B C X).
apply(l8_18_existence A B C); Col.
ex_and H7 C'.

assert(exists X : Tpoint, Col A B X /\ Perp A B D X).
apply(l8_18_existence A B D); Col.
ex_and H12 D'.

assert( A <> C').
intro.
subst C'.
apply perp_perp_in in H8.
apply perp_in_comm in H8.
apply perp_in_per in H8.
assert(A = C).
apply (l8_7 B); Perp.
subst C.
tauto.

assert( A <> D').
intro.
subst D'.
apply perp_perp_in in H14.
apply perp_in_comm in H14.
apply perp_in_per in H14.
assert(A = D).
apply (l8_7 B); Perp.
subst D.
tauto.


assert(Bet A C' B).
apply(perp_per_bet A C B C'); Col.
Perp.
assert(Perp A C' C' C).
apply(perp_col _ B); Col; Perp.
apply perp_in_sym.
apply perp_in_right_comm.
apply(l8_15_1 A B C C'); auto.

assert(Bet A D' B).
apply(perp_per_bet A D B D'); Col.
Perp.
assert(Perp A D' D' D).
apply(perp_col _ B); Col; Perp.
apply perp_in_sym.
apply perp_in_right_comm.
apply(l8_15_1 A B D D'); auto.

induction(eq_dec_points C' P).
subst C'.
assumption.

induction(eq_dec_points D' P).
subst D'.
assumption.

induction(eq_dec_points A P).
subst P.
Between.
induction(eq_dec_points B P).
subst P.
Between.

assert(Bet C' P D').
apply(per13_preserves_bet C P D C' D'); Col.
ColR.
assert(Perp P C' C' C).
apply(perp_col _ A);auto.
apply perp_left_comm.
apply(perp_col _ B);Perp.
Col.
ColR.
apply perp_comm in H23.
apply perp_perp_in in H23.
apply perp_in_comm in H23.
apply perp_in_per in H23.
assumption.

assert(Perp P D' D' D).
apply(perp_col _ A);auto.
apply perp_left_comm.
apply(perp_col _ B);Perp.
Col.
ColR.
apply perp_comm in H23.
apply perp_perp_in in H23.
apply perp_in_comm in H23.
apply perp_in_per in H23.
assumption.

assert(HH:= l5_3 A C' D' B H17 H18).
induction HH.
eBetween.
apply between_symmetry in H23.
eBetween.
Qed.


Lemma l13_2_1 : forall A B C D E, two_sides A B C D -> Per B C A -> Per B D A -> Col C D E
    -> Perp A E C D -> Conga C A B D A B
    -> Conga B A C D A E /\ Conga B A D C A E /\ Bet C E D.
Proof.
    intros.
    intros.
    assert(HH:= H).
    unfold two_sides in HH.
    spliter.
    assert(A <> C /\ A <> B /\ A <> D).
      unfold Conga in H4.
      spliter.
      repeat split; auto.
    spliter.
    assert(Cong B C B D /\ Cong A C A D /\ Conga C B A D B A).
      apply(l11_50_2 B A C B A D).
        intro.
        apply H6.
        Col.
        eapply l11_16; auto.
          apply l8_2.
          auto.
          intro.
          subst C.
          apply H6.
          Col.
          apply l8_2.
          auto.
        intro.
        subst D.
        apply H7.
        Col.
        apply conga_comm.
        auto.
      Cong.
    spliter.
    assert(Perp C D A B).
      apply( cong_conga_perp C A D B); Cong.
    assert(Col A B E).
      eapply perp_perp_col.
        apply perp_sym.
        apply H15.
      auto.
    assert(two_sides C D A B).
      apply ts_per_per_ts; auto.
    unfold two_sides in H17.
    spliter.
    ex_and H20 T1.
    ex_and H8 T.
    assert(T = T1).
      apply bet_col in H21.
      apply bet_col in H22.
      apply (l6_21 A B C D); Col.
    subst T1.
    assert(T = E).
      apply (l6_21 A B C D); Col.
    subst T.
    split.
      apply conga_left_comm.
      eapply out_conga.
        apply H4.
        apply out_trivial; auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
      unfold out.
      repeat split; auto.
      intro.
      subst E.
      contradiction.
    split.
      apply conga_sym.
      apply conga_right_comm.
      eapply out_conga.
        apply H4.
        apply out_trivial; auto.
        unfold out.
        repeat split; auto.
        intro.
        subst E.
        contradiction.
        apply out_trivial; auto.
      apply out_trivial; auto.
    assumption.
Qed.

Lemma inangle_one_side : forall A B C P Q , ~ Col A B C -> ~ Col A B P -> ~ Col A B Q
    -> InAngle P A B C -> InAngle Q A B C
    -> one_side A B P Q.
Proof.
    intros.
    unfold InAngle in *.
    spliter.
    ex_and H9 P'.
    ex_and H6 Q'.
    induction H10.
      subst P'.
      apply bet_col in H9.
      contradiction.
    induction H11.
      subst Q'.
      apply bet_col in H6.
      contradiction.
    assert(one_side A B P' Q').
      prolong P' A T A C.
      unfold one_side.
      exists T.
      unfold two_sides.
      assert(A <> P').
        intro.
        subst P'.
        apply out_col in H10.
        apply H0.
        Col.
      repeat split; auto.
        intro.
        apply H0.
        assert(P' <> B).
          unfold out in H10.
          spliter.
          assumption.
        apply out_col in H10.
        ColR.
        intro.
        induction(eq_dec_points A T).
          subst T.
          apply cong_symmetry in H13.
          apply cong_identity in H13.
          subst C.
          apply H.
          Col.
        apply H.
        apply bet_col in H9.
        apply bet_col in H12.
        assert(Col T A C).
          ColR.
        eapply (col_transitivity_1 _ T); Col.
        exists A.
        split; Col.
        intro.
        apply H1.
        assert(Q' <> B).
          unfold out in H11.
          spliter.
          assumption.
        apply out_col in H11.
        ColR.
        intro.
        induction(eq_dec_points A T).
          subst T.
          apply cong_symmetry in H13.
          apply cong_identity in H13.
          subst C.
          apply H.
          Col.
        apply H.
        apply bet_col in H9.
        apply bet_col in H12.
        assert(Col T A C).
          ColR.
        eapply (col_transitivity_1 _ T); Col.
      exists A.
      split; Col.
      assert(Bet A P' Q' \/ Bet A Q' P').
        eapply l5_3.
          apply H9.
        assumption.
      induction H15.
        eapply (outer_transitivity_between2 _ P'); Between.
      eapply (between_exchange3 P'); Between.
    assert(one_side A B P P').
      eapply (out_one_side_1  _ _ _ _  B); Col.
      apply l6_6.
      auto.
    assert(one_side A B Q Q').
      eapply (out_one_side_1  _ _ _ _ B); Col.
      apply l6_6.
      auto.
    eapply one_side_transitivity.
      apply H13.
    apply one_side_symmetry.
    eapply one_side_transitivity.
      apply H14.
    apply one_side_symmetry.
    assumption.
Qed.

Lemma inangle_one_side2 : forall A B C P Q , ~ Col A B C -> ~ Col A B P -> ~ Col A B Q
    -> ~ Col C B P -> ~ Col C B Q
    -> InAngle P A B C -> InAngle Q A B C
    -> one_side A B P Q /\ one_side C B P Q.
Proof.
    intros.
    split.
      apply (inangle_one_side _ _ C); Col.
    apply (inangle_one_side _ _ A); Col.
      apply l11_24.
      auto.
    apply l11_24.
    auto.
Qed.


  Lemma triangle_mid_par : forall A B C P Q, ~Col A B C -> is_midpoint P B C -> is_midpoint Q A C -> Par_strict A B Q P.
  Proof.
  intros.
   assert(HM:= midpoint_existence A B).
   ex_and HM R.
   assert(HH:= l13_1 A B C P Q R H H0 H1 H2).
   ex_and HH X.
   ex_and H3 Y.
assert(HH:= perp_in_col X Y A B R H3).
spliter.
   apply perp_in_perp in H3.
unfold is_midpoint in H2.
spliter.
apply bet_col in H2.
assert(X <> Y).
apply perp_distinct in H4.
tauto.

   induction H3.
   assert(Perp Y X A B).
apply (perp_col _ R); Perp.
Col.
apply perp_left_comm in H9.
assert(Par A B P Q).
   apply(l12_9 A B P Q X Y);Perp.
induction H10.
finish.
spliter.
assert(Col A B P).
ColR.
assert(P = B).
apply (l6_21 A B C P); Col.
unfold is_midpoint in H0.
spliter.
apply bet_col in H0.
Col.
intro.
subst P.
contradiction.
subst P.
unfold is_midpoint in H0.
spliter.
apply cong_symmetry in H15.
apply cong_identity in H15.
subst C.
contradiction.

assert(Perp X Y A B).
apply (perp_col _ R); Perp.
Col.
assert(Par A B P Q).
   apply(l12_9 A B P Q X Y);Perp.
induction H10.
finish.
spliter.
assert(Col A B P).
ColR.
assert(P = B).
apply (l6_21 A B C P); Col.
unfold is_midpoint in H0.
spliter.
apply bet_col in H0.
Col.
intro.
subst P.
contradiction.
subst P.
unfold is_midpoint in H0.
spliter.
apply cong_symmetry in H15.
apply cong_identity in H15.
subst C.
contradiction.
Qed.

Lemma perp_in_perp_in_col : forall A B A' B' X Y P, Perp_in P A B X Y -> Perp_in P A' B' X Y  -> Col A B A'.
Proof.
intros.
assert(HP1:= H).
assert(HP2:=H0).
assert(Col A B P /\ Col X Y P).
apply perp_in_col in H.
spliter.
split; Col.
spliter.
unfold Perp_in in H.
unfold Perp_in in H0.
spliter.
induction(eq_dec_points A P);
induction(eq_dec_points P X).
subst A.
subst X.
assert(Per B P Y).
apply(H10 B Y); Col.
assert(Per A' P Y).
apply(H6 A' Y); Col.
apply col_permutation_2.
apply(per_per_col B A' Y P); auto.
subst A.
assert(Per B P X).
apply(H10 B X); Col.
assert(Per A' P X).
apply(H6 A' X); Col.
apply col_permutation_2.
apply(per_per_col B A' X P); auto.
subst X.
assert(Per A P Y).
apply(H10 A Y); Col.
induction(eq_dec_points P A').
subst A'.
assert(Per B' P Y).
apply(H6 B' Y); Col.
assert(Col A B' P).
apply(per_per_col A B' Y P); auto.
ColR.

assert(Per A' P Y).
apply(H6 A' Y); Col.
assert(Col A A' P).
apply(per_per_col A A' Y P); auto.
ColR.

assert(Per A P X).
apply(H10 A X); Col.
induction(eq_dec_points P A').
subst A'.
assert(Per B' P X).
apply(H6 B' X); Col.
assert(Col A B' P).
apply(per_per_col A B' X P); auto.
ColR.

assert(Per A' P X).
apply(H6 A' X); Col.
assert(Col A A' P).
apply(per_per_col A A' X P); auto.
ColR.
Qed.


Lemma l13_2 : forall A B C D E, two_sides A B C D -> Per B C A -> Per B D A -> Col C D E -> Perp A E C D
    -> Conga B A C D A E /\ Conga B A D C A E /\ Bet C E D.
Proof.
    intros.
    assert(HH:= H).
    unfold two_sides in HH.
    spliter.
    assert(C <> D).
      intro.
      subst D.
      assert(one_side A B C C).
        apply one_side_reflexivity.
        assumption.
      apply l9_9 in H.
      contradiction.
    assert(exists C', Conga B A C D A C' /\ one_side D A C' B).
      apply(angle_construction_1 B A C D A B).
        intro.
        apply H5.
        Col.
      intro.
      apply H6.
      Col.
    ex_and H9 E'.
    assert(A <> B /\ A <> C /\ A <> D).
      unfold Conga in H9.
      spliter; auto.
    spliter.
    assert(HH:=l11_22 C A E' B D A B E').
    assert(HH1:=ts_per_per_ts A B C D H H0 H1).
    unfold two_sides in HH1.
    spliter.
    ex_and H7 T.
    ex_and H17 T2.
    assert(T = T2).
      apply (l6_21 A B C D); Col.
    subst T2.
    assert(InAngle B D A C).
      unfold InAngle.
      repeat split; auto.
      exists T.
      split.
        Between.
      right.
      unfold out.
      repeat split.
        intro.
        subst T.
        assert(~ Col C D A /\ Per A E D).
          apply(l8_16_1 C D A D E H8 H2).
            Col.
            intro.
            subst E.
            apply H15.
            auto.
          apply perp_sym.
          assumption.
        spliter.
        apply H20.
        Col.
        auto.
      left.
      assumption.
    assert(lea C A B C A D).
      unfold lea.
      exists B.
      split.
        apply l11_24.
        assumption.
      apply conga_refl; auto.
    assert(InAngle E' D A C).
      eapply lea_in_angle.
        apply lea_comm.
        eapply l11_30.
        apply H21.
        apply conga_comm.
        assumption.
        apply conga_refl; auto.
      assert(HH1:=ts_per_per_ts A B C D H H0 H1).
      assert(one_side D A C B).
        apply ts_ts_os.
          apply invert_two_sides.
          assumption.
        apply l9_2.
        assumption.
      eapply one_side_transitivity.
        apply H22.
      apply one_side_symmetry.
      assumption.
    unfold InAngle in H22.
    spliter.
    ex_and H25 E''.
    induction H26.
      subst E''.
      apply False_ind.
      apply H15.
      apply bet_col in H25.
      Col.
    assert(Conga B A C D A E'').
      eapply (out_conga B A C D A E').
        auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
      apply l6_6.
      auto.
    assert(A <> T).
      intro.
      subst T.
      apply H15.
      Col.
    induction(eq_dec_points E'' T).
      subst E''.
      apply l13_2_1; auto.
      eapply out_conga.
        apply conga_left_comm.
        apply H27.
        apply out_trivial; auto.
        apply out_trivial; auto.
        apply out_trivial; auto.
      unfold out.
      repeat split; auto.
    assert(D <> E'').
      intro.
      subst E''.
      apply conga_sym in H27.
      apply eq_conga_out in H27.
      apply out_col in H27.
      apply H5.
      Col.
    assert(C <> E'').
      intro.
      subst E''.
      assert(out A B D \/ two_sides C A B D).
        apply(l11_22_aux C A B D).
        apply conga_comm.
        assumption.
      induction H31.
        apply out_col in H31.
        apply H6.
        Col.
      assert(one_side A C B D).
        apply ts_ts_os.
          assumption.
        apply ts_per_per_ts; auto.
      apply invert_one_side in H32.
      apply l9_9 in H31.
      contradiction.
    assert(A <> E'').
      intro.
      subst E''.
      unfold out in H26.
      tauto.
    assert(~ Col E'' A B).
      intro.
      apply H29.
      apply bet_col in H25.
      apply (l6_21 A B C D); Col.
    assert(Conga C A E'' D A B).
      apply (l11_22 C A E'' B D A B E'').
      split.
        induction(one_side_dec A B C E'').
          right.
          split.
            auto.
          unfold one_side.
          exists C.
          split.
            unfold two_sides.
            repeat split.
              auto.
              intro.
              apply H15.
              apply bet_col in H25.
              apply col_permutation_1.
              eapply (col_transitivity_1 _ E''); Col.
              intro.
              apply bet_col in H25.
              apply H15.
              apply col_permutation_2.
              eapply (col_transitivity_1 _ E''); Col.
            exists E''.
            split; Col.
          assert(two_sides A E'' T C).
            unfold two_sides.
            repeat split.
              auto.
              intro.
              apply H29.
              apply (l6_21 A B C D);Col.
              eapply (col_transitivity_1 _ T); Col.
              apply bet_col in H25.
              Col.
              intro.
              apply H15.
              ColR.
            exists E''.
            split.
              Col.
            assert(Bet C T E'' \/ Bet C E'' T).
              eapply l5_3.
                apply H18.
              Between.
            induction H35.
              assert(two_sides A B C E'').
                unfold two_sides.
                repeat split; auto.
                exists T.
                split.
                  Col.
                auto.
              apply l9_9 in H36.
              contradiction.
            Between.
          eapply (l9_5 _ _ T _ A); Col.
          unfold out.
          repeat split; auto.
        left.
        apply not_one_side_two_sides in H34; auto.
        split.
          auto.
        assert(one_side A B D E'').
          eapply l9_8_1.
            apply l9_2.
            apply H.
          apply l9_2.
          assumption.
        assert(two_sides A E'' T D).
          unfold two_sides.
          repeat split.
            auto.
            intro.
            apply H33.
            apply col_permutation_2.
            apply(col_transitivity_1 _ T); Col.
            intro.
            apply bet_col in H25.
            apply H15.
            apply col_permutation_1.
            eapply (col_transitivity_1 _ E''); Col.
          exists E''.
          split.
            Col.
          assert(Bet D T E'' \/ Bet D E'' T).
            eapply l5_3.
              apply between_symmetry.
              apply H18.
            assumption.
          induction H36.
            assert(two_sides A B D E'').
              unfold two_sides.
              repeat split; auto.
              exists T.
              split; Col.
            apply l9_9 in H37.
            contradiction.
          Between.
        apply l9_2.
        eapply (l9_5 _ _ T _ A).
          auto.
          Col.
        unfold out.
        repeat split; auto.

      split.
        apply conga_left_comm.
        auto.
      apply conga_right_comm.
      apply conga_refl; auto.
    (***********************)
    prolong B C C' B C.
    prolong B D D' B D.
    assert(Cong_3 B A D D' A D).
      apply l8_2 in H1.
      unfold Per in H1.
      ex_and H1 D''.
      assert(is_midpoint D B D').
        unfold is_midpoint.
        split; Cong.
      assert(D' = D'').
        eapply symmetric_point_unicity.
          apply H40.
        auto.
      subst D''.
      repeat split; Cong.
    assert(Conga B A D D' A D).
      apply cong3_conga; auto.
    assert(Cong_3 B A C C' A C).
      apply l8_2 in H0.
      unfold Per in H0.
      ex_and H0 C''.
      assert(is_midpoint C B C').
        unfold is_midpoint.
        split; Cong.
      assert(C' = C'').
        eapply symmetric_point_unicity.
          apply H42.
        auto.
      subst C''.
      repeat split; Cong.
    assert(Conga B A C C' A C).
      apply cong3_conga; auto.
    assert(Conga E'' A C' D' A E'').
      apply l11_22 with C D.
      split.
        clear HH.
        (***************************************************)
        left.
        assert(one_side C A D E'').
          eapply out_out_one_side.
            apply one_side_reflexivity.
            intro.
            apply H15.
            Col.
          unfold out.
          repeat split; auto.
          right.
          Between.
        assert(one_side C A B D).
          apply in_angle_one_side.
            intro.
            apply H15.
            Col.
            intro.
            apply H5.
            Col.
          apply l11_24.
          auto.
        assert(two_sides C A B C').
          unfold two_sides.
          repeat split.
            auto.
            intro.
            apply H5.
            Col.
            intro.
            apply H5.
            apply bet_col in H35.
            assert(C <> C').
              intro.
              subst C'.
              apply cong_symmetry in H36.
              apply cong_identity in H36.
              subst C.
              apply H16.
              Col.
            eapply (col_transitivity_1 _ C'); Col.
          exists C.
          split; Col.
        assert(one_side C A B E'').
          eapply one_side_transitivity.
            apply H44.
          auto.
        assert(one_side D A C E'').
          eapply out_out_one_side.
            apply one_side_reflexivity.
            intro.
            apply H15.
            Col.
          unfold out.
          repeat split; auto.
        assert(one_side D A B C).
          apply in_angle_one_side.
            intro.
            apply H15.
            Col.
            intro.
            apply H6.
            Col.
          auto.
        assert(two_sides D A B D').
          unfold two_sides.
          repeat split.
            auto.
            intro.
            apply H6.
            Col.
            intro.
            apply H6.
            apply bet_col in H37.
            assert(D <> D').
              intro.
              subst D'.
              apply cong_symmetry in H38.
              apply cong_identity in H38.
              subst D.
              apply H16.
              Col.
            eapply (col_transitivity_1 _ D'); Col.
          exists D.
          split; Col.
        assert(one_side D A B E'').
          eapply one_side_transitivity.
            apply H48.
          auto.
        split.
          apply invert_two_sides.
          eapply l9_8_2.
            apply H45.
          auto.
        apply invert_two_sides.
        apply l9_2.
        eapply l9_8_2.
          apply H49.
        auto.
      split.
        eapply conga_trans.
          apply conga_comm.
          apply H34.
        apply H40.
      apply conga_sym.
      eapply conga_trans.
        apply conga_sym.
        apply H27.
      apply conga_right_comm.
      auto.
    assert(D' <> B).
      intro.
      subst D'.
      apply between_identity in H37.
      subst D.
      apply H16.
      Col.
    assert(C' <> B).
      intro.
      subst C'.
      apply between_identity in H35.
      subst C.
      apply H16.
      Col.
    assert(~ Col C' D' B).
      intro.
      apply H16.
      apply bet_col in H35.
      apply  bet_col in H37.
      assert(Col C' B D).
        ColR.
      ColR.
    assert(Par_strict C' D' C D).
      apply(triangle_mid_par C' D' B D C).
        auto.
        unfold is_midpoint.
        split.
          Between.
        Cong.
      unfold is_midpoint.
      split.
        Between.
      Cong.
    assert(two_sides A E'' C D).
      unfold two_sides.
      repeat split.
        auto.
        intro.
        apply H15.
        apply bet_col in H25.
        apply col_permutation_2.
        eapply (col_transitivity_1 _ E''); Col.
        intro.
        apply H15.
        apply bet_col in H25.
        apply col_permutation_1.
        eapply (col_transitivity_1 _ E''); Col.
      exists E''.
      split; Col.
      Between.
    assert(two_sides B A C D).
      apply in_angle_two_sides.
        intro.
        apply H5.
        Col.
        intro.
        apply H6.
        Col.
      apply l11_24.
      assumption.
    assert (one_side A B C C').
      apply (out_one_side_1 _ _ _ _ B); Col.
      unfold out.
      repeat split; auto.
      intro.
      subst C.
      apply H5.
      Col.
    assert (one_side A B D D').
      apply (out_one_side_1 _ _ _ _ B); Col.
      unfold out.
      repeat split; auto.
      intro.
      subst D.
      apply H6.
      Col.
    apply invert_two_sides in H49.
    assert(two_sides A B C' D).
      eapply l9_8_2.
        apply H49.
      auto.
    assert(two_sides A B C' D').
      apply l9_2.
      eapply l9_8_2.
        apply l9_2.
        apply H52.
      auto.
    assert(Perp  C' D' A E'').
      eapply cong_conga_perp.
        apply conga_right_comm in H43.
        apply l11_22_aux in H43.
        induction H43.
          assert(one_side A B C' D').
            eapply (out_one_side_1 _ _ _ _ A); Col.
            intro.
            assert(B <> C').
              intro.
              subst C'.
              apply H46.
              Col.
            apply H5.
            apply col_permutation_1.
            eapply col_transitivity_1.
              apply H55.
              apply bet_col in H35.
              Col.
            Col.
          apply l9_9 in H53.
          contradiction.
        apply invert_two_sides.
        assumption.
        unfold Cong_3 in *.
        spliter.
        eCong.
      apply conga_left_comm.
      assumption.


assert(Cong A C' A B).
apply l8_2 in H0.
unfold Per in H0.
ex_and H0 C''.
assert(C' = C'').
apply(symmetric_point_unicity B C C' C''); finish.
split; finish.
subst C''.
Cong.

assert(Cong A D' A B).
apply l8_2 in H1.
unfold Per in H1.
ex_and H1 D''.
assert(D' = D'').
apply(symmetric_point_unicity B D D' D''); finish.
split; finish.
subst D''.
Cong.

assert(Cong A C' A D').
eCong.

assert(HM:=midpoint_existence C' D').
ex_and HM R.
assert(exists X Y : Tpoint, Perp_in R X Y C' D' /\ Perp X Y D C).
apply(l13_1 C' D' B D C R);
finish.
split; Between; Cong.
split; Between; Cong.
ex_and H59 X.
ex_and H60 Y.

assert(HXY:X <> Y).
apply perp_distinct in H60.
tauto.

assert(Perp C D A E'').

induction(eq_dec_points A R).
subst R.

assert(Perp_in A C' D' A E'').
assert_cols.
apply(l8_14_2_1b_bis C' D' A E'' A); Col.

assert(Col X Y A).
apply(perp_in_perp_in_col X Y A E'' C' D' A); finish.
assert(Col X Y E'').
apply(perp_in_perp_in_col X Y E'' A C' D' A); finish.
apply perp_sym.
induction(eq_dec_points Y A).
subst Y.
apply(perp_col _ X).
auto.
Perp.
Col.
apply(perp_col _ Y).
auto.
apply perp_left_comm.
apply (perp_col _ X); Col.
Perp.
ColR.

assert(R <> C').
intro.
subst R.
unfold is_midpoint in H58.
spliter.
apply cong_symmetry in H62.
apply cong_identity in H62.
subst D'.
apply perp_distinct in H54.
tauto.

assert(Per A R C').
unfold Per.
exists D'.
split; finish.
apply per_perp_in in H63; auto.
apply perp_in_sym in H63.
apply perp_in_perp in H63.
induction H63.
apply perp_comm in H63.
assert(Perp C' D' R A).
apply(perp_col _ R).
intro.
subst D'.
apply perp_distinct in H54.
tauto.
assumption.
assert_cols.
Col.

assert(Perp_in R C' D' R A).
apply(l8_14_2_1b_bis C' D' R A R); Col.
assert_cols.
Col.

assert( Col X Y A).
apply(perp_in_perp_in_col X Y A R C' D' R); Perp.
assert( Col X Y R).
apply(perp_in_perp_in_col X Y R A C' D' R); Perp.

assert(Col A E'' R).
apply(perp_perp_col A E'' R C' D'); Perp.

assert(Col A R X).
ColR.
assert(Col A R Y).
ColR.


apply perp_sym.
induction(eq_dec_points X A).
subst X.
apply (perp_col _ Y); finish.
ColR.
apply (perp_col _ X); finish.
apply perp_left_comm.
apply(perp_col _ Y); finish.
ColR.
apply perp_distinct in H63.
tauto.

    assert(Col A E E'').
      eapply perp_perp_col.

        apply H3.
Perp.

    assert(E'' = E).
      apply (l6_21 C D A E); Col.
      apply perp_not_eq_1 in H3.
      assumption.
    subst E''.
    split.
      auto.
    split.
      apply conga_sym.
      apply conga_right_comm.
      auto.
    Between.
Qed.

Definition Perp2 := fun A B C D P => exists X, exists Y, Col P X Y /\ Perp X Y A B /\ Perp X Y C D.

Lemma perp2_refl : forall A B P, A <> B -> Perp2 A B A B P.
Proof.
    intros.
    induction(Col_dec A B P).
      assert(HH:=not_col_exists A B H).
      ex_and HH X.
      assert(HH:=l10_15 A B P X  H0 H1).
      ex_and HH Q.
      unfold Perp2.
      exists Q.
      exists P.
      split; Perp.
      Col.
    assert(HH:=l8_18_existence A B P H0).
    ex_and HH Q.
    unfold Perp2.
    exists P.
    exists Q.
    split; Perp.
    Col.
Qed.


Lemma perp2_sym : forall A B C D P, Perp2 A B C D P -> Perp2 C D A B P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_left_comm : forall A B C D P, Perp2 A B C D P -> Perp2 B A C D P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_right_comm : forall A B C D P, Perp2 A B C D P -> Perp2 A B D C P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_comm : forall A B C D P, Perp2 A B C D P -> Perp2 B A D C P.
Proof.
    unfold Perp2.
    intros.
    ex_and H X.
    ex_and H0 Y.
    exists X.
    exists Y.
    repeat split; Perp.
Qed.


Lemma perp2_trans : forall A B C D E F P, Perp2 A B C D P -> Perp2 C D E F P -> Perp2 A B E F P.
Proof.
    intros.
    unfold Perp2 in *.
    ex_and H X.
    ex_and H1 Y.
    ex_and H0 X'.
    ex_and H3 Y'.
    assert(Par X Y X' Y').
      eapply (l12_9 _ _ _ _ C D); Perp.
    exists X.
    exists Y.
    assert(Col X X' Y').
      induction H5.
        unfold Par_strict in H5.
        spliter.
        apply False_ind.
        apply H8.
        exists P.
        split; Col.
      spliter.
      auto.
    assert(Col Y X' Y').
      induction H5.
        unfold Par_strict in H5.
        spliter.
        apply False_ind.
        apply H9.
        exists P.
        split; Col.
      spliter.
      auto.
    repeat split; auto.
    assert(X <> Y).
      apply perp_not_eq_1 in H1.
      assert(X' <> Y').
        apply perp_not_eq_1 in H3.
        auto.
      auto.
    induction(eq_dec_points X Y').
      subst Y'.
      apply (perp_col _ X').
        auto.
        Perp.
      ColR.
    apply (perp_col _ Y').
      auto.
      apply perp_left_comm.
      apply(perp_col _ X').
        auto.
        Perp.
      ColR.
    apply par_symmetry in H5.
    induction H5.
      unfold Par_strict in H5.
      spliter.
      apply False_ind.
      apply H12.
      exists P.
      split; Col.
    spliter.
    Col.
Qed.




Lemma perp2_par : forall A B C D O, Perp2 A B C D O -> Par A B C D.
Proof.
    intros.
    unfold Perp2 in H.
    ex_and H X.
    ex_and H0 Y.
    eapply (l12_9 _ _ _ _ X Y).
      Perp.
    Perp.
Qed.


Lemma perp2_preserves_bet23 : forall O A B A' B', Bet O A B -> Col O A' B' -> ~Col O A A' ->
    Perp2 A A' B B' O -> Bet O A' B'.

Proof.
intros.

assert(HD1: A <> A').
intro.
subst A'.
apply H1.
Col.

induction(eq_dec_points A' B').
subst B'.
Between.

assert(A <> B).
intro.
subst B.
unfold Perp2 in H2.
ex_and H2 X.
ex_and H4 Y.
assert(Col A A' B').
apply(perp_perp_col A A' B' X Y); Perp.
apply H1.
ColR.

assert(Par A A' B B').
apply(perp2_par A A' B B' O H2).
induction H5.
assert(one_side A A' B B').
apply l12_6; Par.
assert(two_sides A A' O B).
repeat split; Col.
intro.
apply H5.
exists B.
split; Col.
exists A.
split; Col.

assert(two_sides A A' B' O).
apply( l9_8_2 A A' B B' O); auto.
apply l9_2.
auto.

unfold two_sides in H8.
spliter.
ex_and H11 T.
assert(T = A').
apply (l6_21 A A' O B'); Col.
intro.
subst B'.
apply between_identity in H12.
subst T.
contradiction.
subst T.
Between.

spliter.
apply False_ind.
apply H1.
ColR.
Qed.

Lemma perp2_preserves_bet13 : forall O B C B' C', Bet B O C -> Col O B' C' -> ~Col O B B' ->
    Perp2 B C' C B' O -> Bet B' O C'.

Proof.
intros.

induction(eq_dec_points C' O).
subst C'.
Between.
induction(eq_dec_points B' O).
Between.

assert(B <> O).
intro.
subst B.
apply H1.
Col.

assert(B' <> O).
intro.
subst B'.
apply H1.
Col.

assert(Col B O C).
apply bet_col.
Between.

induction(eq_dec_points B C).
subst C.
apply between_identity in H.
contradiction.

assert(Par B C' C B').
apply (perp2_par _ _ _ _ O); auto.
assert(Par_strict B C' C B').
induction H9.
assumption.
spliter.
apply False_ind.
apply H1.
ColR.

assert(C<> O).
intro.
subst C.
assert(Par_strict B C' O C').
apply(par_strict_col_par_strict _ _ _ B'); auto.
apply H11.
exists C'.
Col.

assert(B' <> O).
intro.
subst B'.
assert(Par_strict B C' O B).
apply(par_strict_col_par_strict _ _ _ C); auto.
apply par_strict_right_comm.
assumption.
Col.
apply H12.
exists B.
split; Col.

unfold Perp2 in H2.
ex_and H2 X.
ex_and H13 Y.

assert(X <> Y).
apply perp_distinct in H13.
tauto.

induction(Col_dec X Y B).
assert(Col X Y C).
ColR.

apply(per13_preserves_bet_inv  B' O C' C B); Between.
Col.

apply perp_in_per.
induction(eq_dec_points X C).
subst X.
assert(Perp C O B' C).
apply(perp_col _ Y); Perp.
ColR.
apply perp_perp_in in H18.
Perp.
assert(Perp X C C B').
apply(perp_col _ Y); Perp.
assert(Perp C O B' C).
apply(perp_col _ X); Perp.
ColR.
apply perp_perp_in in H20.
Perp.

apply perp_in_per.
induction(eq_dec_points X B).
subst X.
assert(Perp B O C' B).
apply(perp_col _ Y); Perp.
ColR.
apply perp_perp_in in H18.
Perp.
assert(Perp X B C' B).
apply(perp_col _ Y); Perp.
assert(Perp B O C' B).
apply(perp_col _ X); Perp.
ColR.
apply perp_perp_in in H20.
Perp.

assert(HP1:=l8_18_existence X Y B H16).
ex_and HP1 B0.
assert(~Col X Y C).
intro.
apply H16.
ColR.
assert(HP1:=l8_18_existence X Y C H19).
ex_and HP1 C0.

assert(B0 <> O).
intro.
subst B0.
assert(Par B O B C').
apply(l12_9 B O B C' X Y); Perp.
induction H22.
apply H22.
exists B.
split; Col.
spliter.
apply H1.
ColR.

assert(C0 <> O).
intro.
subst C0.
assert(Par C O C B').
apply(l12_9 C O C B' X Y); Perp.
induction H23.
apply H23.
exists C.
split; Col.
spliter.
apply H1.
ColR.

assert(Bet B0 O C0).

apply(per13_preserves_bet B O C B0 C0); auto.
Between.
ColR.
apply perp_in_per.
induction(eq_dec_points X B0).
subst X.
assert(Perp B0 O B B0).
apply(perp_col _ Y); Perp.
Col.
apply perp_perp_in in H24.
Perp.
assert(Perp X B0 B B0).
apply(perp_col _ Y); Perp.
assert(Perp B0 O B B0).
apply (perp_col _ X); Perp.
ColR.
apply perp_perp_in in H26.
Perp.

apply perp_in_per.
induction(eq_dec_points X C0).
subst X.
assert(Perp C0 O C C0).
apply(perp_col _ Y); Perp.
Col.
apply perp_perp_in in H24.
Perp.
assert(Perp X C0 C C0).
apply(perp_col _ Y); Perp.
assert(Perp C0 O C C0).
apply (perp_col _ X); Perp.
ColR.
apply perp_perp_in in H26.
Perp.

induction(eq_dec_points C' B0).
subst B0.
assert(B' = C0).
apply bet_col in H24.
apply (l6_21 C' O C C0); Col.
assert(Par C B' C C0).
apply(l12_9 C B' C C0 X Y); Perp.

induction H25.
apply False_ind.
apply H25.
exists C.
split; Col.
spliter.
Col.
intro.
apply H1.
ColR.
intro.
subst C0.
apply H1.
ColR.
apply(perp_perp_col C C0 B' X Y); Perp.
subst C0.
Between.

assert(B' <> C0).
intro.
subst C0.
apply H25.
apply (l6_21 B' O B B0); Col.
intro.
subst B0.
Col.
assert(Par B C' B B0).
apply(l12_9 B C' B B0 X Y); Perp.

induction H26.
apply False_ind.
apply H26.
exists B.
split; Col.
spliter.
Col.

assert(Col C C0 B').
apply(perp_perp_col C C0 B' X Y); Perp.
assert(Col B B0 C').
apply(perp_perp_col B B0 C' X Y); Perp.

apply(per13_preserves_bet_inv B' O C' C0 B0); Between.
Col.

apply perp_in_per.
induction(eq_dec_points X C0).
subst X.
assert(Perp C0 O C B').
apply (perp_col _ Y); Perp.
Col.
assert(Perp B' C0 C0 O).
apply(perp_col _ C); Perp.
Col.
apply perp_comm in H30.
apply perp_perp_in in H30.
Perp.

assert(Perp X C0 C B').
apply(perp_col _ Y); Perp.
assert(Perp C0 O C B').
apply (perp_col _ X); Perp.
ColR.
assert(Perp B' C0 C0 O).
apply(perp_col _ C); Perp.
Col.
apply perp_comm in H32.
apply perp_perp_in in H32.
Perp.


apply perp_in_per.

assert(Perp C' B0 X Y).
apply (perp_col _ B); Perp.
Col.
induction (eq_dec_points X O).
subst X.
assert(Perp O B0 B0 C').
apply(perp_col _ Y);Perp.
apply perp_comm in H30.
apply perp_perp_in in H30.
Perp.
 
assert(Perp X O C' B0).
apply(perp_col _ Y); Perp.
Col.
assert(Perp O B0 B0 C').
apply(perp_col _ X); Perp.
ColR.
apply perp_comm in H32.
apply perp_perp_in in H32.
Perp.

Qed.


Lemma is_image_perp_in : forall A A' X Y, A <> A' -> X <> Y -> is_image A A' X Y -> exists P, Perp_in P A A' X Y.
Proof.
intros.
unfold is_image in H.
induction H1.
spliter.
unfold is_image_spec in H2.
spliter.
ex_and H2 P.
induction H3.
exists P.

apply perp_in_sym.
apply perp_in_right_comm.
apply(l8_14_2_1b_bis X Y A' A P); Col.
assert_cols.
Col.
subst A'.
tauto.
spliter.
contradiction.
Qed.

Lemma perp_inter_perp_in_n
     : forall A B C D : Tpoint,
       Perp A B C D ->
       exists P : Tpoint, Col A B P /\ Col C D P /\ Perp_in P A B C D.
Proof.
intros.
assert(A <> B /\ C <> D).
apply perp_distinct in H.
tauto.
spliter.
induction(Col_dec A B C).
exists C.
split; Col.
split; Col.
apply(l8_14_2_1b_bis A B C D C); Col.

assert(HH:=l8_18_existence A B C H2).
ex_and HH P.
exists P.
assert(Col C D P).
apply(perp_perp_col C D P A B); Perp.
split; Col.
split; Col.
apply(l8_14_2_1b_bis A B C D P); Col.
Qed.

Lemma perp2_perp_in : forall A B C D O, Perp2 A B C D O -> ~Col O A B /\ ~Col O C D ->
    exists P, exists Q, Col A B P /\ Col C D Q /\ Col O P Q /\ Perp_in P O P A B /\ Perp_in Q O Q C D.
  Proof.
    intros.
    unfold Perp2 in H.
    ex_and H X.
    ex_and H1 Y.
    assert(X <> Y).
      apply perp_not_eq_1 in H2.
      auto.
    assert(HH:= perp_inter_perp_in_n X Y A B H2).
    ex_and HH P.
    assert(HH:= perp_inter_perp_in_n X Y C D H3).
    ex_and HH Q.
    exists P.
    exists Q.
    split; auto.
    split; auto.
    split.
      apply (col3 X Y); Col.
    split.
      induction(eq_dec_points X O).
        subst X.
        apply perp_in_sym.
        apply(perp_in_col_perp_in A B O Y P P).
          intro.
          subst P.
          apply H.
          Col.
          Col.
        apply perp_in_sym.
        auto.
      assert(Perp_in P A B X O).
        apply(perp_in_col_perp_in A B X Y O P H11).
          Col.
        apply perp_in_sym.
        auto.
      apply perp_in_right_comm in H12.
      eapply (perp_in_col_perp_in _ _ _ _ P) in H12 .
        apply perp_in_sym.
        auto.
        intro.
        subst P.
        apply H.
        Col.
      ColR.
    induction(eq_dec_points X O).
      subst X.
      apply perp_in_sym.
      apply(perp_in_col_perp_in C D O Y Q Q).
        intro.
        subst Q.
        apply H0.
        Col.
        Col.
      apply perp_in_sym.
      auto.
    assert(Perp_in Q C D X O).
      apply(perp_in_col_perp_in C D X Y O Q H11).
        Col.
      apply perp_in_sym.
      auto.
    apply perp_in_right_comm in H12.
    eapply (perp_in_col_perp_in _ _ _ _ Q) in H12 .
      apply perp_in_sym.
      auto.
      intro.
      subst Q.
      apply H0.
      Col.
    ColR.
Qed.


Lemma l13_8 : forall O P Q U V, U <> O -> V <> O ->Col O P Q -> Col O U V
    -> Per P U O -> Per Q V O -> (out O P Q <-> out O U V).
Proof.
    intros.
    induction(eq_dec_points P U).
      subst P.
      assert(Col Q V O).
        ColR.
      assert(HH:= l8_9 Q V O H4 H5).
      induction HH.
        subst Q.
        tauto.
      subst V.
      tauto.
    assert(Q <> V).
      intro.
      subst Q.
      assert(HH:= per_not_col P U O H5 H H3).
      apply HH.
      ColR.
split.
intro.
unfold out in H7.
spliter.
induction H9.

assert(HH:= per23_preserves_bet O P Q U V).
repeat split; auto.
left.
apply(per23_preserves_bet O P Q U V); auto.
Perp.
Perp.
repeat split; auto.
right.
apply(per23_preserves_bet O Q P V U); Col.
Perp.
Perp.

intro.
unfold out in H7.
spliter.

repeat split.
intro.
subst P.
apply l8_8 in H3.
contradiction.
intro.
subst Q.
apply l8_8 in H4.
contradiction.
induction H9.
left.
apply(per23_preserves_bet_inv O P Q U V); Perp.
right.
apply(per23_preserves_bet_inv O Q P V U); Perp.
Col.
Qed.

Lemma perp_in_rewrite : forall A B C D P, Perp_in P A B C D ->
                                          Perp_in P A P P C \/
                                          Perp_in P A P P D \/
                                          Perp_in P B P P C \/
                                          Perp_in P B P P D.
Proof.
intros.
assert(HH:= perp_in_col A B C D P H).
spliter.
induction(eq_dec_points A P);
induction(eq_dec_points C P).
subst A .
subst C.
right;right;right.
Perp.
subst A.
right; right; left.
apply perp_in_right_comm.
assert(HP:=perp_in_col_perp_in P B C D P P H3 H1 H).
Perp.
subst C.
right; left.
apply perp_in_sym.
apply(perp_in_col_perp_in P D A B P P H2 H0).
Perp.
left.
assert(HP:= perp_in_col_perp_in A B C D P P H3 H1 H).
apply perp_in_sym.
apply perp_in_left_comm.
apply(perp_in_col_perp_in C P A B P P H2 H0).
Perp.
Qed.

Lemma conga_preserves_acute : forall A B C A' B' C', acute A B C -> Conga A B C A' B' C' -> acute A' B' C'.
Proof.
intros.
unfold acute in *.
ex_and H A1.
ex_and H1 B1.
ex_and H C1.

exists A1.
exists B1.
exists C1.
split; auto.

assert(A1 <> B1 /\ C1 <> B1).
unfold lta in H1.
spliter.
unfold lea in H1.
ex_and H1 P.
unfold InAngle in H1.
spliter.
split; auto.
spliter.

apply(conga_preserves_lta A B C A1 B1 C1 A' B' C' A1 B1 C1); auto.
apply conga_refl; auto.
Qed.

Lemma gta_to_lta : forall A B C D E F, gta A B C D E F -> lta D E F A B C.
Proof.
intros.
unfold gta in H.
assumption.
Qed.

Lemma lta_to_gta : forall A B C D E F, lta A B C D E F -> gta D E F A B C.
Proof.
intros.
unfold gta.
assumption.
Qed.

Lemma conga_preserves_obtuse : forall A B C A' B' C', obtuse A B C -> Conga A B C A' B' C' -> obtuse A' B' C'.
Proof.
intros.
unfold obtuse in *.
ex_and H A1.
ex_and H1 B1.
ex_and H C1.

exists A1.
exists B1.
exists C1.
split; auto.

assert(A1 <> B1 /\ C1 <> B1).
unfold gta in H1.
unfold lta in H1.
spliter.
unfold lea in H1.
ex_and H1 P.
unfold Conga in H3.
spliter.
split; auto.

unfold gta in *.
spliter.
apply(conga_preserves_lta A1 B1 C1 A B C A1 B1 C1 A' B' C'); auto.
apply conga_refl; auto.
Qed.


Lemma perp_out_acute : forall A B C C', out B A C' -> Perp A B C C' -> acute A B C.
Proof.
intros.
assert(A <> B /\ C' <> B).
apply out_distinct.
assumption.
spliter.

assert(Perp B C' C C').
apply(perp_col _ A); Perp.
apply out_col in H.
Col.
assert(Per C C' B).
apply perp_in_per.
apply perp_sym in H3.
apply perp_left_comm in H3.
apply perp_perp_in in H3.
apply perp_in_comm.
assumption.
assert(acute C' C B /\ acute C' B C).
apply( l11_43 C' C B).

apply perp_left_comm in H3.
apply perp_not_col in H3.
intro.
apply H3.
assert_cols.
ColR.
left.
assumption.
spliter.

assert(C <> B).
intro.
subst C.
apply l8_8 in H4.
subst C'.
apply perp_distinct in H0.
tauto.

assert(Conga C' B C A B C ).
apply(out_conga A B C A B C C' C A C); auto.
apply conga_refl; auto.
apply out_trivial; auto.
apply out_trivial; auto.
apply out_trivial; auto.
apply (conga_preserves_acute C' B C); auto.
Qed.

Lemma flat_all_lea : forall A B C, A <> B -> C <> B -> Bet A B C -> forall P, P <> B -> lea A B P A B C.
Proof.
intros.
unfold lea.
exists P.
spliter.
split.
unfold InAngle.
repeat split; auto.
exists B.
split; auto.
apply conga_refl; auto.
Qed.

Lemma acute_bet_obtuse : forall A B C P, B <> C -> Bet A B C -> acute A B P -> obtuse C B P.
Proof.
intros.

assert(A <> C).
intro.
subst C.
apply between_identity in H0.
subst B.
tauto.

assert(A <> B).
unfold acute in H1.
ex_and H1 A'.
ex_and H3 B'.
ex_and H1 P'.
unfold lta in H3.
spliter.
unfold lea in H3.
ex_and H3 X.
apply conga_distinct in H5.
tauto.

assert(D : P <> B).
unfold acute in H1.
ex_and H1 A'.
ex_and H4 B'.
ex_and H1 Q'.
unfold lta in H4.
spliter.
unfold lea in H4.
ex_and H4 X.
apply conga_distinct in H6.
tauto.

induction(Col_dec A B P).
assert(HH:= perp_exists B A B H3).
ex_and HH Q.

assert(HD: Q <> B).
apply perp_distinct in H5.
intro.
subst Q.
tauto.

assert(Per A B Q).
apply perp_in_per.
apply perp_perp_in in H5.
Perp.

unfold obtuse.
exists A.
exists B.
exists Q.
split; auto.

assert(out B A P).
apply(col_in_angle_out A B Q); Col.
intro.
apply perp_not_col in H5.
apply H5.
apply bet_col in H7.
Col.

unfold acute in H1.
ex_and H1 A'.
ex_and H7 B'.
ex_and H1 Q'.

assert(Conga A B Q A' B' Q').
apply l11_16; auto.

intro.
subst B'.
unfold lta in H7.
spliter.
unfold lea in H7.
ex_and H7 X.
apply conga_distinct in H9.
tauto.
intro.
subst Q'.
unfold lta in H7.
spliter.
unfold lea in H7.
ex_and H7 X.
unfold InAngle in H7.
tauto.

assert(lta A B P A B Q).

apply(conga_preserves_lta A B P A' B' Q' A B P A B Q).
apply conga_refl;auto.
apply conga_sym.
assumption.
assumption.
unfold InAngle.
repeat split; auto.
unfold lta in H9.
spliter.
exists A.
split.
Between.
right.

induction H4.

assert(HH:= flat_all_lea A B P H3 D H4).
assert(HP:=HH Q HD).
assert(HQ:=lea_asym A B P A B Q H9 HP).
contradiction.

induction H4.
unfold out.
repeat split; auto.
unfold out.
repeat split; auto.
left.
Between.

unfold gta.
unfold lta.
split.
unfold lea.
exists Q.
split.
unfold InAngle.
repeat split; auto.
exists B.
split.

induction H7.
spliter.
induction H9.

apply (outer_transitivity_between _ _ A); Between.
apply (between_inner_transitivity _ _ _ A); Between.
left.
auto.
apply l11_16; Perp.

assert(Perp B C B Q).
apply (perp_col _ A);Perp.
apply bet_col in H0.
Col.
apply perp_in_per.
apply perp_right_comm in H8.
apply perp_perp_in in H8.
Perp.
intro.

assert(HH:= l11_17 A B Q C B P H6 H8).
apply per_not_col in HH; auto.
apply HH.
apply bet_col in  H0.
ColR.

assert(HC:Col A B C).
apply bet_col in H0.
Col.

assert(exists Q : Tpoint, Perp A C Q B /\ one_side A C P Q).
apply(l10_15 A C B P); Col.
intro.
apply H4.
ColR.

ex_and H5 Q.
assert(Perp A B Q B).
apply (perp_col _ C); Perp.
Col.
apply perp_left_comm in H7.

assert(~Col B A Q).
apply perp_not_col in H7.
assumption.

assert(Per A B Q).
apply perp_in_per.
apply perp_perp_in in H7.
Perp.

assert(B <> Q).
intro.
subst Q.
apply H8.
Col.


assert(one_side B Q A P).
unfold acute in H1.
ex_and H1 A'.
ex_and H11 B'.
ex_and H1 Q'.
assert(Conga A B Q A' B' Q').
apply l11_16; auto.
unfold lta in H11.
spliter.
unfold lea in H11.
ex_and H11 X.
apply conga_distinct in H13.
tauto.
unfold lta in H11.
spliter.
unfold lea in H11.
ex_and H11 X.
unfold InAngle in H11.
tauto.

assert(lta A B P A B Q).
apply(conga_preserves_lta A B P A' B' Q' A B P A B Q ); auto.
apply conga_refl; auto.
apply conga_sym.
assumption.
unfold lta in H13.
spliter.
unfold lea in H13.
ex_and H13 P0.

assert(InAngle P A B Q).

apply(conga_preserves_in_angle A B Q P0 A B Q P).
apply conga_refl; auto.
apply conga_sym.
assumption.
assumption.
apply (col_one_side _ C); Col.

unfold InAngle in H16.
spliter.

ex_and H19 X.

induction H20.
subst X.
apply False_ind.
apply H8.
apply bet_col in H19.
Col.

assert(one_side Q B A X).
apply out_one_side.
left.
intro.
apply H8.
Col.
repeat split.
intro.
subst Q.
apply l8_8 in H9.
contradiction.
intro.
subst X.
apply H14.
apply conga_sym.
apply(out_conga A B P A B P A Q A P).
apply conga_refl; auto.
apply out_trivial; auto.
apply l6_6.
assumption.
apply out_trivial; auto.
apply out_trivial; auto.
right.
Between.

assert(one_side B Q X P).

apply( out_one_side B Q X P).
right.
intro.
apply H14.

apply conga_sym.
apply(out_conga A B P A B P A Q A P).
apply conga_refl; auto.
apply out_trivial; auto.

apply(col_one_side_out _ C).
Col.
apply invert_one_side.

apply(col_one_side _ A); Col.
apply invert_one_side.
assumption.
apply out_trivial; auto.
apply out_trivial; auto.
assumption.
apply invert_one_side in H21.
eapply(one_side_transitivity _ _ _ X); auto.

assert(two_sides B Q A C).
unfold two_sides.
repeat split; auto.
intro.
apply H8.
Col.
intro.
apply H8.
ColR.
exists B.
split; Col.

assert(two_sides B Q P C).
apply(l9_8_2 B Q A P C); auto.

unfold obtuse.
exists A.
exists B.
exists Q.
split; auto.
unfold gta.
unfold lta.

assert(HP:Per C B Q).
assert(Perp B C Q B).
apply(perp_col _ A); Perp.
Col.
apply perp_in_per.
apply perp_perp_in in H14.
Perp.

split.
unfold lea.
exists Q.
split.
unfold InAngle.
repeat split; auto.
unfold two_sides in H13.
spliter.
ex_and H16 X.
exists X.
split; Between.
right.

assert(one_side C A X P).
apply out_one_side.
right.
intro.
apply H4.
ColR.
repeat split.
intro.
subst X.
contradiction.
intro.
subst P.
apply between_identity in  H17.
subst X.
contradiction.
left.
Between.
apply invert_one_side in H18.
assert(one_side A C X Q).
apply (one_side_transitivity _ _ _ P); auto.
apply(col_one_side_out B C X Q).
Col.
apply invert_one_side.
apply(col_one_side _ A); Col.
apply invert_one_side.
assumption.
apply l11_16; Perp.

assert(Conga A B Q C B Q).
apply l11_16; Perp.
intro.
assert(Conga C B Q C B P).
apply(conga_trans _ _ _ A B Q); auto.
apply conga_sym.
auto.

unfold acute in H1.
ex_and H1 A'.
ex_and H17 B'.
ex_and H1 Q'.
assert(Conga A B Q A' B' Q').
apply l11_16; Perp.
intro.
subst B'.
unfold lta in H17.
spliter.
unfold lea in H17.
ex_and H17 X.
apply conga_distinct in H19.
tauto.
intro.
subst Q'.
unfold lta in H17.
spliter.
unfold lea in H17.
ex_and H17 X.
unfold InAngle in H17.
tauto.
assert(lta A B P A B Q).
apply(conga_preserves_lta A B P A' B' Q' A B P A B Q); auto.
apply conga_refl; auto.
apply conga_sym; auto.
unfold lta in H19.
spliter.
apply H20.
apply conga_sym.
apply(l11_13 C B Q C B P A A H16); Between.
Qed.

Lemma perp_bet_obtuse : forall A B C C', B <> C' -> Perp A B C C' -> Bet A B C' -> obtuse A B C.
Proof.
intros.
assert(HPO:=perp_out_acute).
assert(HBO:=acute_bet_obtuse).
assert(Col A B C').
apply bet_col in H1.
Col.
assert(acute C' B C).
apply (HPO _ _ _ C').
apply out_trivial; auto.
apply perp_left_comm.
apply(perp_col _ A); Perp.
Col.
apply (HBO C').
intro.
subst B.
apply perp_distinct in H0.
tauto.
Between.
assumption.
Qed.

End L13_1.