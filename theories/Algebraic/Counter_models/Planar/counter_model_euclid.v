Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq order.
From mathcomp
Require Import fintype finset finfun bigop.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra algC.
From mathcomp
Require Import zmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.Counter_models.nD.counter_model_euclid.
Require Import GeoCoq.Algebraic.POF_to_Tarski.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Main.Meta_theory.Models.tarski_to_gupta_inspired.
Require Import GeoCoq.Main.Tarski_dev.Ch06_out_lines.
Require Import GeoCoq.Main.Tarski_dev.Ch11_angles.
Require Export GeoCoq.Main.Meta_theory.Parallel_postulates.parallel_postulates.
Require Import GeoCoq.Algebraic.Counter_models.Planar.independence.


Section rcfTarski2D.

Variable R : rcfType.
Notation "#" := proj1_sig.

Definition Point := counter_model_euclid.Point' R 2.

Definition bet' := @counter_model_euclid.bet' R 2.

Definition cong' := @counter_model_euclid.cong' R 2.

Lemma point_equality_decidability : point_equality_decidabilityP Point.
Proof. by move => a b; case: (a =P b); tauto. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof. by apply counter_model_euclid.bet_inner_transitivity. Qed.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point cong'.
Proof. by apply counter_model_euclid.cong_pseudo_reflexivity. Qed.

Lemma cong_identity : cong_identityP Point cong'.
Proof. by apply counter_model_euclid.cong_identity. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP Point cong'.
Proof. by apply counter_model_euclid.cong_inner_transitivity. Qed.

Lemma inner_paschP : inner_paschP Point bet'.
Proof. by move => a b c p q; apply counter_model_euclid.pasch. Qed.

Lemma bet_symmetry : bet_symmetryP Point bet'.
Proof. by apply counter_model_euclid.bet_symmetry. Qed.

Lemma five_segment : five_segmentP Point bet' cong'.
Proof. by apply counter_model_euclid.five_segment. Qed.

Lemma segment_construction : segment_constructionP Point bet' cong'.
Proof.
by move => a b c d; apply counter_model_euclid.segment_construction_holds.
Qed.

Definition a' : 'rV[R]_(2) := row2 0 0.
Definition b' : 'rV[R]_(2) := row2 0 (1/(1+1)).
Definition c' : 'rV[R]_(2) := row2 (1/(1+1)) 0.

Lemma a'_in_unit_disk : (a' *m a'^T) 0 0 < 1.
Proof.
by rewrite /a' !mxE !big_ord_recr /= big_ord0 !mxE /= mulr0 !addr0 ltr01.
Qed.

Lemma b'_in_unit_disk : (b' *m b'^T) 0 0 < 1.
Proof.
rewrite /b' !mxE !big_ord_recr /= big_ord0 !mxE /= mulr0 addr0 add0r.
apply mulr_ilt1 ; rewrite ?one_half_ge0 ?one_half_lt1 //.
Qed.

Lemma c'_in_unit_disk : (c' *m c'^T) 0 0 < 1.
Proof.
rewrite /c' !mxE !big_ord_recr /= big_ord0 !mxE /= mulr0 addr0 add0r.
apply mulr_ilt1 ; rewrite ?one_half_ge0 ?one_half_lt1 //.
Qed.

Lemma c'_norm : (c' *m c'^T) 0 0 = 1/(1+1+1+1).
Proof.
rewrite /c' !mxE !big_ord_recr /= big_ord0 !mxE /= mulr0 addr0 add0r.
by rewrite quarter.
Qed.

Definition a : Point :=
  exist (fun p => (p *m p^T) 0 0 < 1) a' a'_in_unit_disk.
Definition b : Point :=
  exist (fun p => (p *m p^T) 0 0 < 1) b' b'_in_unit_disk.
Definition c : Point :=
  exist (fun p => (p *m p^T) 0 0 < 1) c' c'_in_unit_disk.

Lemma a'_eq0 : a' = 0.
Proof. by rewrite /a'; apply /eqP; rewrite vector2_eq0 !mxE /= eqxx. Qed.

Lemma betR_abc : betR a' b' c' = 0.
Proof.
rewrite /betR /ratio; case: pickP => /= [x|all_v_neq0 //].
rewrite /a' /b' /c' !mxE /=; case: x => [] [|[| //]] //= p;
by rewrite !subr0 ?mul0r ?eqxx.
Qed.

Lemma betR_bca : betR b' c' a' = 1.
Proof.
rewrite /betR /ratio a'_eq0 sub0r.
case: pickP => /= [x|/all_v_neq0 H]; last first.
- exfalso; apply H; rewrite oppr_eq0 -a'_eq0 /a' /b'.
  by rewrite row2_eq one_half_neq0 eqxx.
rewrite /b' /c' !mxE /=; case: x => [] [|[| //]] //= p.
- by rewrite oppr_eq0 eqxx.
by rewrite sub0r divff // oppr_eq0 one_half_neq0.
Qed.

Lemma betR_cab : betR c' a' b' = 0 \/ betR c' a' b' = 1.
Proof.
rewrite /betR /ratio a'_eq0 sub0r; case: pickP => /= [x|] ; [|tauto].
rewrite /b' /c' !mxE /=; case: x => [] [|[| //]] //= p.
- rewrite sub0r divff; [tauto|by rewrite oppr_eq0 one_half_neq0].
by rewrite subr0 oppr0 mul0r; tauto.
Qed.

Lemma nbet_abc : bet' a b c = false.
Proof.
rewrite /bet' /counter_model_euclid.bet' /a /b /c /= /bet /betE /betS.
rewrite betR_abc /a' /b' /c' ltxx !row2_eq eqxx.
by rewrite one_half_neq0 eq_sym one_half_neq0 !andbF.
Qed.

Lemma nbet_bca : bet' b c a = false.
Proof.
rewrite /bet' /counter_model_euclid.bet' /a /b /c /= /bet /betE /betS.
rewrite betR_bca /a' /b' /c' ltxx !row2_eq eqxx.
by rewrite one_half_neq0 eq_sym one_half_neq0 !andbF.
Qed.

Lemma nbet_cab : bet' c a b = false.
Proof.
rewrite /bet' /counter_model_euclid.bet' /a /b /c /= /bet /betE /betS.
elim betR_cab => ->; rewrite /a' /b' /c' ltxx !row2_eq eqxx;
by rewrite one_half_neq0 eq_sym one_half_neq0 !andbF.
Qed.

Lemma lower_dim : lower_dimP Point bet' a b c.
Proof.
rewrite /lower_dimP /Col nbet_abc nbet_cab nbet_bca => H.
by repeat (elim H; clear H; intro H).
Qed.

Lemma upper_dim_aux_2 (a p q : Point)  (k := Num.sqrt(omd p p/ omd q q)) :
  cong' a p a q -> (omd a p /omd a q == k).
Proof.
rewrite /cong'/counter_model_euclid.cong'/cong_v=> cong_apaq .
have: omd a p ^+ 2 / (omd a a * omd p p) * (omd a a * omd p p)/omd a q ^+ 2 ==
omd a q ^+ 2 / (omd a a * omd q q) * (omd a a * omd p p)/omd a q ^+ 2.
- rewrite -subr_eq0 -mulrBl -mulrBl !mulf_eq0 !omd_eq0 invr_eq0 sqrf_eq0.
  by rewrite omd_eq0 !orbF subr_eq0 cong_apaq.
set t_ap := omd a p. set t_aq := omd a q. set t_aa := omd a a.
set t_pp := omd p p. set t_qq := omd q q.
rewrite -[ (_ *_) *(_* _)]mulrA [((t_aa * t_pp)^-1*(t_aa*t_pp))]mulrC.
rewrite divff ?mulf_neq0 ?omd_eq0//.
rewrite eq_sym mulrC !mulrA expr2.
rewrite -[(t_aq * t_aq)^-1 * t_aq * t_aq ]mulrC mulrA.
rewrite -[t_aq/(t_aq*t_aq)*t_aq]mulrC mulrA divff ?mulf_neq0 ?omd_eq0 //.
rewrite mul1r invfM mulrC !mulrA mulrAC [t_pp / t_aa * t_aa / t_qq ]mulrC !mulrA mulrAC.
rewrite -!mulrA divff ?omd_eq0 //.
rewrite mulr1 eq_sym !mulrA mulr1 -!expr2 /k.
rewrite -eqr_sqrt ?mulr_ge0 ?invr_ge0 ?expr2 ?mulr_ge0 ?omd_ge0 //.
rewrite [X in _ == Num.sqrt(X)]mulrC => /eqP <-.
rewrite sqrtrM ?mulr_ge0 ?omd_ge0 //.
rewrite -!expr2 -exprVn !sqrtr_sqr !ger0_norm ?omd_ge0 //.
by rewrite invr_ge0 omd_ge0.
Qed.

Lemma upper_dim_aux (a p q : Point) (k := Num.sqrt(omd p p/ omd q q))
                    (e := #p-k*:#q) :
  cong' a p a q -> #a 0 0 * e 0 0  + #a 0 1 * e 0 1 = (1-k).
Proof.
move=> cong_apaq.
apply upper_dim_aux_2 in cong_apaq.
suffices: omd a p == k * omd a q ; [move => H1|].
suffices: (#a *m e^T) 0 0 == 1 - k ; [move => /eqP <-|].
rewrite !mxE !big_ord_recr /= big_ord0 add0r !mxE.
congr (# a 0 _ * (# p 0 _ - k * # q 0 _) + # a 0 _ * (# p 0 _ - k * # q 0 _)) ;
by apply: val_inj.
rewrite /e dotC mulmxBl mxE eq_sym subr_eq addrC addrA addrC addrA -subr_eq.
move/eqP: H1.
rewrite /omd/omd_v dotC => ->.
rewrite mulrBr mulr1 -subr_eq0 opprD addrA addrC.
rewrite !addrA [- k + k]addrC subrr add0r -scalemxAl.
by rewrite dotC !mxE /= subrr eqxx.
move/eqP: cong_apaq.
rewrite /e /k=> <-.
by rewrite mulrAC -mulrA divff ?mulr1 ?eqxx ?omd_eq0.
Qed.

Lemma upper_dim : upper_dimP Point bet' cong'.
Proof.
move => a b c p q /eqP neq_pq _ _ _ H1 H2 H3.
suffices: (((#a 0 0) - (#b 0 0)) * ((#b 0 1) - (#c 0 1))) ==
         (((#a 0 1) - (#b 0 1)) * ((#b 0 0) - (#c 0 0))).
rewrite /bet';  apply col_2D.
set (k := Num.sqrt(omd p p/ omd q q)).
set (e := #p-k*:#q).
suffices: ( ((#a 0 0 * e 0 0 + #a 0 1 * e 0 1) == (#b 0 0 * e 0 0 + #b 0 1 * e 0 1)) &&
            ((#b 0 0 * e 0 0 + #b 0 1 * e 0 1) == (#c 0 0 * e 0 0 + #c 0 1 * e 0 1))).
case: (e 0 1 =P 0) ; case: (e 0 0 =P 0).
move => E00 E01 _.
suffices: (#p == #q).
  rewrite -point_vector_eq=> pq_eq //.
  exfalso.
  move/negP:  neq_pq.
  by rewrite pq_eq.
have: (e == 0) by rewrite vector2_eq E00 E01 !mxE /= eqxx.
rewrite /e subr_eq0 => /eqP p_eqkq.
suffices: k = 1.
  by rewrite p_eqkq=>->; rewrite scale1r eqxx.
have:(k = Num.sqrt ((1 - ((k*k) *: (# q *m (# q)^T)) 0 0) / (1 - (# q *m (# q)^T) 0 0))).
  by rewrite {1}/k /omd/omd_v p_eqkq -scalemxAl dotC -scalemxAl scalerA.
move=>H.
have: ( 0 < k) by rewrite sqrtr_gt0 mulr_gt0 ?invr_gt0 ?omd_gt0.
move=> k_gt0.
have: k^+2 == 1.
  move: (eqf_sqr k  (Num.sqrt
      ((1 - ((k * k) *: (# q *m (# q)^T)) 0 0) / (1 - (# q *m (# q)^T) 0 0)))).
  rewrite {4}H eqxx /= [X in _ == X]sqr_sqrtr.
  move => /eqP P1.
  have: k ^+ 2 * (1 - (# q *m (# q)^T) 0 0) == (1 - ((k * k) *: (# q *m (# q)^T)) 0 0).
    rewrite P1 mulrAC -mulrA divff ?lt0r_neq0 ?subr_gt0 // ; last by destruct q.
    by rewrite mulr1 eqxx.
  rewrite mulrBr mulr1 subr_eq expr2 addrAC -addrA.
  by rewrite !mxE /= subrr addr0.
  by rewrite le0r -sqrtr_gt0 -H k_gt0 orbT.
by rewrite sqrp_eq1 ?le0r ?k_gt0 ?orbT // => /eqP ->.

move=> /eqP /negPf NX0 ->.
rewrite !mulr0 !addr0 -subr_eq0 -[X in _ && X]subr_eq0 -!mulrBl.
rewrite !mulf_eq0 NX0 !Bool.orb_false_r !subr_eq0=> /andP[/eqP -> /eqP ->].
by rewrite !subrr mulr0 mul0r eqxx.

move=> -> /eqP /negPf NX0.
rewrite !mulr0 !add0r -subr_eq0 -[X in _ && X]subr_eq0 -!mulrBl.
rewrite !mulf_eq0 NX0 !Bool.orb_false_r !subr_eq0 => /andP[/eqP -> /eqP ->].
by rewrite !subrr mulr0 mul0r eqxx.

move=> /eqP /negPf NX0 /eqP /negPf NX1.
rewrite -subr_eq0 opprD addrCA -[_-_]addrA -mulrBl addrCA addrA -mulrBl -[X in _ + X]opprK subr_eq0.
rewrite Bool.andb_comm.
rewrite -[(# b 0 0 * e 0 0 + # b 0 1 * e 0 1 == # c 0 0 * e 0 0 + # c 0 1 * e 0 1) ]subr_eq0 opprD addrCA -[_-_]addrA -mulrBl addrCA addrA -mulrBl -[X in _ + X]opprK subr_eq0.
move=> /andP[/eqP H4 /eqP H5].
suffices: (# a 0 0 - # b 0 0) * e 0 0 * -(# b 0 1 - # c 0 1) * e 0 1 ==
          (# b 0 0 - # c 0 0) * e 0 0 * -(# a 0 1 - # b 0 1) * e 0 1.
rewrite -subr_eq0 -mulrBl mulf_eq0.
rewrite mulrC [X in _ - X]mulrC !mulrA -mulrBl mulf_eq0.
move: NX0 NX1 => -> ->.
rewrite subr_eq0 mulrC [X in _ == X]mulrC !mulrN eqr_opp [X in _ == X]mulrC.
rewrite !Bool.orb_false_r.
exact.

move: H4 H5 => -> ->.
rewrite -mulrA mulrC !mulrN !mulNr mulrA.
by rewrite eqxx.

move: (upper_dim_aux H1) (upper_dim_aux H2) (upper_dim_aux H3).
move => -> -> ->.
by rewrite eqxx.
Qed.

Global Instance Rcf_to_GI_PED' :
  Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality.
Proof.
exact
(Build_Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality
  Point bet' cong' point_equality_decidability
  cong_pseudo_reflexivity cong_inner_transitivity
  cong_identity
  segment_construction five_segment
  bet_symmetry bet_inner_transitivity
  (@counter_model_euclid.pasch R 0)
  a b c
  lower_dim).
Defined.

Lemma euclid : ~ euclidP Point bet'.
Proof.
move=> HP; apply (@counter_model_euclid.euclid_fails R 0).
cut (tarski_s_parallel_postulate).
- rewrite /tarski_s_parallel_postulate; move=> HT A B C D T H1 H2 HBD HDC HNCol.
  apply HT with D; auto; intro; subst; apply HNCol; right; right.
  apply bet_symmetry, H2.
cut (proclus_postulate); [|rewrite /proclus_postulate].
- apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
  simpl; try tauto.
intros A B C D P Q HPar HC HNC HCop; apply HP with A B;
[clear HC HNC HCop|intuition..].
destruct HPar as [[HCop HNI]|HParC]; [left|right; intuition].
split; [intro; treat_equalities; apply HNI; exists C; Col|].
split; [intro; treat_equalities; apply HNI; exists A; Col|].
split; [intuition|intros [X [? ?]]; apply HNI; exists X; Col].
Qed.

End rcfTarski2D.
