From mathcomp Require Import ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq order.
From mathcomp
Require Import fintype finset finfun bigop.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra vector.
From mathcomp
Require Import zmodp.
From mathcomp Require Import tuple fintype bigop.
From mathcomp Require Import ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.
Require Import GeoCoq.Algebraic.POF_to_Tarski.
Require Import GeoCoq.Algebraic.Counter_models.nD.dimensional_axioms.

Section Tarskinp3D.

Variable n : nat.
Variable R : realFieldType.

Definition o := @to_nD R n.+1 (row2   0  0).

Definition i := @to_nD R n.+1 (row2 (-1) 0).

Definition basis : n.+2.-tuple 'rV_(n.+3) :=
  map_tuple (fun i => @delta_mx R _ _ 0 (inord i)) (iota_tuple n.+2 0).

Lemma nth_basis i : (i < n.+2)%N -> tnth basis (inord i) = delta_mx 0 (inord i).
Proof.
move => iP; rewrite /basis /tnth (@nth_map nat 0%N) ?size_iota //.
by rewrite inordK // nth_iota.
Qed.

Lemma oP : o = const_mx 0.
Proof. exact: dimensional_axioms.oP. Qed.

Lemma iP : i = - (delta_mx 0 0).
Proof. exact: dimensional_axioms.iP. Qed.

Lemma e_dist (j : 'I_n.+3) : cong o i o (delta_mx 0 j).
Proof. by rewrite oP iP /cong !subr0 dot2N !dot_delta !mxE !eqxx. Qed.

Lemma cong_deltas (j k l : 'I_n.+3) : j != k -> l != 0 ->
  cong (delta_mx 0 j) (delta_mx 0 k) i (delta_mx 0 l).
Proof.
move=> jk l0; rewrite iP /cong opprK.
rewrite (dot2B (delta_mx 0 k)) (dot2D (delta_mx 0 l)).
rewrite !dot_delta !mxE !eqxx (negPf jk) (eq_sym 0 l) (negPf l0) /=.
by rewrite !mulr1n !mulr0n; apply/eqP; lra.
Qed.

Lemma lower_dim : lower_dimP _ (@bet R (n.+3)) (@cong R (n.+3)) n.+2 o i basis.
Proof.
rewrite /lower_dimP /orthonormal_basis /= !nth_basis //.
split; first by apply i_neq_basis_nth0.
split; first by rewrite bet_o_i_basis_nth0.
split; [apply big_andb_and|apply big_pairs_andb_and]; rewrite big_all.
- apply/allP => j; rewrite mem_index_iota => /andP[_ jn].
  by rewrite nth_basis // e_dist.
apply/allP => j; rewrite mem_index_iota => /andP[_ jn]; rewrite big_all.
apply/allP => k; rewrite mem_index_iota => /andP[jk kn].
have jn3 : (j < n.+3)%N := ltnW jn; have kn3 : (k < n.+3)%N := ltnW kn.
rewrite !nth_basis // cong_deltas // -val_eqE /= !inordK //.
by rewrite neq_ltn jk.
Qed.

Lemma nth_new_basis i p :
  (i < n.+1)%N -> tnth (@rot_tuple n.+2 1 _ (belast_tuple p basis))
                       (inord i) = delta_mx 0 (inord i).
Proof.
move => iP; rewrite /basis /tnth; set f := fun j => delta_mx 0 (inord j).
rewrite /rot /= belast_map /rot /=; move: iP.
case: i => /= [|m i]; first rewrite inordK //=.
rewrite inordK ?(ltn_trans i) //= nth_cat size_map size_belast size_iota.
have m_lt_n : (m < n)%N by move: i; rewrite -ltn_predRL.
rewrite m_lt_n (@nth_map nat 0%N) ?size_belast ?size_iota //.
suff -> : nth O (belast (S O) (iota 2 n)) m = m.+1 by rewrite /f.
suff: forall l, (m < l)%N -> nth O (belast (S O) (iota 2 l)) m = m.+1.
- by move => lP; rewrite (lP n).
move => {p f i m_lt_n} l; elim l => // {}l IHl m_lt_lp1.
rewrite -(addn1 l) iotaD belast_cat nth_cat size_belast size_iota.
case: (m =P l) => [-> {IHl m_lt_lp1 m}|/eqP lm_neq]; last first.
- suff m_lt_l : (m < l)%N by rewrite m_lt_l IHl.
  by move: (ltnSE m_lt_lp1) lm_neq; rewrite leq_eqVlt => /orP[/eqP ->/eqP|->].
rewrite ltnn subnn /= -nth_last size_iota.
case: (l =P O) => [-> //|/eqP l_nz]; rewrite nth_iota ?ltn_predL ?lt0n //.
by move: l_nz; case: l.
Qed.

Lemma last_new_basis p :
  tnth (@rot_tuple n.+2 1 _ (belast_tuple p basis)) (inord n.+1) = p.
Proof.
rewrite /basis /tnth /=.
have -> : nat_of_ord (@inord n.+1 n.+1) =
          (size (@rot_tuple n.+2 1 _ (belast_tuple p basis))).-1.
- by rewrite inordK // size_rot size_belast size_map size_iota.
by rewrite nth_last last_cat.
Qed.

Lemma upper_dim :
  ~ upper_dimP _ (@bet R (n.+3)) (@cong R (n.+3)) n.+2 o i basis.
Proof.
pose p : 'rV[R]_(n.+3) := delta_mx 0 (inord n.+2).
pose new_basis := rot_tuple 1 (belast_tuple p basis).
have nbE x : (x < n.+2)%N -> tnth new_basis (inord x) =
                            delta_mx 0 (inord (if x == n.+1 then n.+2 else x)).
  move=> xn; case: eqP => [->|/eqP xn1]; first exact: last_new_basis.
  by apply: nth_new_basis; move: xn; rewrite ltnS leq_eqVlt (negPf xn1).
have HNE : tnth basis (inord n.+1) <> p.
  rewrite nth_basis // /p => /rowP/(_ (inord n.+2)).
  rewrite !mxE !eqxx -val_eqE /= !inordK // gtn_eqF // ?mulr0n ?mulr1n.
  by move=> /eqP; rewrite eq_sym oner_eq0.
have bP : lower_dimP _ (@bet R (n.+3)) (@cong R (n.+3)) n.+2 o i new_basis.
  rewrite /lower_dimP /orthonormal_basis /= (nbE 0%N) //=.
  split; first by apply i_neq_basis_nth0.
  split; first by rewrite bet_o_i_basis_nth0.
  split; [apply big_andb_and|apply big_pairs_andb_and]; rewrite big_all.
  - apply/allP => j; rewrite mem_index_iota => /andP[_ jn].
    by rewrite nbE // e_dist.
  apply/allP => j; rewrite mem_index_iota => /andP[_ jn]; rewrite big_all.
  apply/allP => k; rewrite mem_index_iota => /andP[jk kn].
  have jn1 : (j == n.+1) = false by rewrite ltn_eqF // (leq_trans jk kn).
  have jn3 : (j < n.+3)%N := ltnW jn; have kn3 : (k < n.+3)%N := ltnW kn.
  rewrite !nbE // jn1 cong_deltas //.
  + by case: ifP => _; rewrite -val_eqE /= !inordK // neq_ltn ?jn ?jk.
  + by case: ifP => _; rewrite -val_eqE /= inordK.
move=> /(_ p lower_dim bP HNE); rewrite nth_basis // oP /p.
move=> /bet_scale [r /rowP E]; move: (E (inord n.+1)) (E (inord n.+2)).
rewrite !mxE !eqxx -!val_eqE /= !inordK // ltn_eqF // gtn_eqF //.
by rewrite ?mulr0n ?mulr1n; lra.
Qed.

End Tarskinp3D.