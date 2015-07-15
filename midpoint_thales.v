(* Exercise done by David Braun under the supervision of Nicolas Magaud, cleaned up by Julien Narboux. *)

Require Export triangle_midpoints_theorems.
Section T_42.

Context `{MT:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma midpoint_thales : forall o a b c : Tpoint, 
   ~ Col a b c ->
   is_midpoint o a b -> 
   Cong o a o c ->
   Per a c b.
Proof.
intros.
Name x the midpoint of c and a.
assert (Par_strict o x b c)
 by perm_apply (triangle_mid_par_strict_cong_simp c b a o x).
assert(Per o x a)
 by (exists c;split;finish).
assert_diffs.
assert_cols.
assert(Hid2 : Perp o x c a)
 by perm_apply (col_per_perp o x a c).
assert (Perp b c c a).
 apply (par_perp_perp o x b c c a);finish.
 apply par_strict_par;finish. (* TODO sous typage *)
apply perp_per_1;Perp.
Qed.

(* TODO cleanup *)

Lemma midpoint_thales_reci :
  forall a b c o: Tpoint,
   Per a c b ->
   is_midpoint o a b ->
   Cong o a o b /\ Cong o b o c.
Proof.
intros.

induction (Col_dec a b c).

induction (l8_9 a c b H);
treat_equalities;assert_congs_perm;try split;finish.
assert_diffs.
(* Demonstration Cong o a o b *)
assert_congs_perm.
split.
Cong.
(* Demonstration Cong o b o c *)
assert(Hmid := midpoint_existence a c).
(* Soit x le milieu de a c *)
destruct Hmid.
(* Demonstration o x parallele à b c *)
assert(Hpar : Par c b x o).
apply (triangle_mid_par c b a o x);finish.
(* On doit effectuer le changement d'angle perpendiculaire en appliquant par_perp_perp*)
(* Demonstration du sous but Perp pour appliquer par_perp_perp *)
assert(Hper : Perp c b c a).
apply perp_left_comm.
apply per_perp.
auto.
auto.
Perp.
(* Application de par_perp_perp *)
assert(HH := par_perp_perp c b x o c a Hpar Hper).
assert(Hper2 : Perp c x o x).
apply (perp_col c a o x x).
assert_diffs.
finish.
Perp.
assert_cols.
Col.
(*Transformation de Perp c x o x en Per *)
apply perp_left_comm in Hper2.
apply perp_perp_in in Hper2.
apply perp_in_comm in Hper2.
apply perp_in_per in Hper2.
apply l8_2 in Hper2.
(* Depliage de Per pour obtenir Cong o b o c *)
unfold Per in Hper2.
destruct Hper2.
spliter.
apply l7_2 in H8.
assert(HmidU := l7_9 a x0 x c H2 H8).
rewrite <- HmidU in *.
unfold is_midpoint in H2.
spliter.
apply cong_left_commutativity in H9.
apply cong_transitivity with (C:=o)(D:=a).
Cong.
Cong.
Qed.

End T_42.