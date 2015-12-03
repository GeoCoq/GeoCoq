Require Import GeoCoq.Tarski_dev.Annexes.midpoint_theorems.

Section Varignon.

Context `{MT:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

(** This is the usual proof using midpoints theorem but this proof needs the fact that IJK are not collinear. *)

Lemma varignon :
 forall A B C D I J K L,
  A<>C -> B<>D -> ~ Col I J K ->
  is_midpoint I A B ->
  is_midpoint J B C ->
  is_midpoint K C D ->
  is_midpoint L A D ->
  Parallelogram I J K L.
Proof.
intros.
assert_diffs.
assert (Par I L B D)
  by perm_apply (triangle_mid_par B D A L I).
assert (Par J K B D)
  by perm_apply (triangle_mid_par B D C K J).
assert (Par I L J K)
  by (apply par_trans with B D;finish).
assert (Par I J A C)
  by perm_apply (triangle_mid_par A C B J I).
assert (Par L K A C)
  by perm_apply (triangle_mid_par A C D K L).
assert (Par I J K L)
  by (apply par_trans with A C;finish).
apply par_2_plg;finish.
Qed.

(** We propose here a more complex proof to simplify the ndg. If we know that a quadrilateral has its pairs of opposite side congruent and parallel
 then it is a parallelogram. *)

Lemma varignon_aux :
 forall A B C D I J K L,
  (A<>C \/ B<>D) ->
  J<>L ->
  is_midpoint I A B ->
  is_midpoint J B C ->
  is_midpoint K C D ->
  is_midpoint L A D ->
  Parallelogram I J K L.
Proof.
intros.
induction H.
induction (eq_dec_points B D).
treat_equalities.
apply plg_trivial.
intro;treat_equalities;intuition.
Name X the midpoint of B and D.
assert_diffs.

assert (Par B D L I /\ Cong B X L I)
  by (apply (triangle_mid_par_cong_1 A B D X L I);finish).
assert (Par B D K J /\ Cong B X K J)
  by (apply (triangle_mid_par_cong_1 C B D X K J);finish).
spliter.
assert (Par I L J K)
  by (eapply par_trans with B D;finish).
assert (Cong I L J K)
  by (eapply cong_transitivity with B X;finish).

Name X' the midpoint of A and C.
assert (Par A C J I /\ Cong A X' J I)
  by (apply (triangle_mid_par_cong_1 B A C X' J  I);finish).
assert (Par A C K L /\ Cong A X' K L)
  by (apply (triangle_mid_par_cong_1 D A C X' K L);finish).
spliter.
assert (Par I J K L)
  by (eapply par_trans with A C;finish).
assert (Cong I J K L)
   by (eapply cong_transitivity with A X';finish).
apply par_par_cong_cong_parallelogram;finish.

induction (eq_dec_points A C).
treat_equalities.
apply plg_trivial1.
intro;treat_equalities;intuition.

Name X the midpoint of B and D.
assert_diffs.

assert (Par B D L I /\ Cong B X L I)
  by (apply (triangle_mid_par_cong_1 A B D X L I);finish).
assert (Par B D K J /\ Cong B X K J)
  by (apply (triangle_mid_par_cong_1 C B D X K J);finish).
spliter.
assert (Par I L J K)
  by (eapply par_trans with B D;finish).
assert (Cong I L J K)
  by (eapply cong_transitivity with B X;finish).

Name X' the midpoint of A and C.
assert (Par A C J I /\ Cong A X' J I)
  by (apply (triangle_mid_par_cong_1 B A C X' J  I);finish).
assert (Par A C K L /\ Cong A X' K L)
  by (apply (triangle_mid_par_cong_1 D A C X' K L);finish).
spliter.
assert (Par I J K L)
  by (eapply par_trans with A C;finish).
assert (Cong I J K L)
   by (eapply cong_transitivity with A X';finish).
apply par_par_cong_cong_parallelogram;finish.
Qed.

Lemma varignon' :
 forall A B C D I J K L,
  (A<>C \/ B<>D) ->
  is_midpoint I A B ->
  is_midpoint J B C ->
  is_midpoint K C D ->
  is_midpoint L A D ->
  Parallelogram I J K L.
Proof.
intros.
induction (eq_dec_points J L).
subst.
unfold Parallelogram.
right.
unfold Parallelogram_flat.
assert_congs_perm.
Name X the midpoint of B and D.
induction (eq_dec_points A B).
 treat_equalities.
 assert_cols.
 repeat split;Cong;Col; intuition.
induction (eq_dec_points A D).
 treat_equalities.
 induction (eq_dec_points X K).
  treat_equalities.
  intuition.
 assert_cols.
 assert (Cong X L K L).
 assert (Par B L L K /\
       Par B C K X /\
       Par L C L X /\
       Cong B X K L /\
       Cong L X K L /\
       Cong B L K X /\ Cong C L K X /\ Cong L K L X /\ Cong C K L X).
  apply (triangle_mid_par_flat_cong B L C K L X);Col;Midpoint.
   intro;treat_equalities. intuition.
   intro;treat_equalities. intuition.
   spliter.
   Cong.
 repeat split.
 show_distinct L X . intuition.
 assert_diffs.
 ColR.
 Col.
 auto.
 auto.
 left;auto.
induction (eq_dec_points B D).
 treat_equalities. intuition.
assert (is_midpoint L I K).
assert (Par A B L X /\
       Par A D X I /\
       Par B D L I /\
       Cong A I X L /\
       Cong B I X L /\
       Cong A L X I /\ Cong D L X I /\ Cong B X L I /\ Cong D X L I).
apply (triangle_mid_par_cong A B D X L I);auto.
spliter.
induction (eq_dec_points C D).
 treat_equalities.
 intuition.
assert_diffs.
induction (eq_dec_points B C).
 treat_equalities.
 assert_cols.
 apply cong_col_mid.
  auto.
  ColR.
 Cong.
assert (Par B C X K /\
       Par B D K L /\
       Par C D X L /\
       Cong B L K X /\
       Cong C L K X /\
       Cong B X K L /\ Cong D X K L /\ Cong C K X L /\ Cong D K X L).
apply (triangle_mid_par_cong B C D K X L);auto.
spliter.
induction (eq_dec_points I K).
  treat_equalities.
  assert (Parallelogram A D B C) by (apply mid_plg with I;Midpoint).
  assert (Parallelogram A B D C) by (apply mid_plg with L;Midpoint).
  exfalso.
  apply Plg_perm in H39.
  apply Plg_perm in H40.
  spliter.
  apply (plg_not_comm_1 B D A C);auto.

apply cong_col_mid.
 auto.
 assert (Par I L K L).
  apply par_trans with B D;Par.
 apply par_id_5;Par.
 eCong.
assert_congs_perm.
assert_cols.
repeat split;Col;Cong.
left.
intro.
subst.
treat_equalities.
intuition.
eapply varignon_aux;eauto.
Qed.



End Varignon.