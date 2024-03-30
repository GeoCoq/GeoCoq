Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq order.
From mathcomp
Require Import fintype finset finfun bigop.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra algC.
From mathcomp
Require Import zmodp.
From mathcomp Require Import tuple fintype bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.
Require Import GeoCoq.Algebraic.tcp_ndc.
Require Import GeoCoq.Algebraic.coplanarity.
Require Import GeoCoq.Algebraic.Counter_models.nD.dimensional_axioms.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Main.Meta_theory.Models.tarski_to_gupta_inspired.
Require Import GeoCoq.Main.Tarski_dev.Ch06_out_lines.
Require Import GeoCoq.Main.Tarski_dev.Ch11_angles.
Require Export GeoCoq.Main.Meta_theory.Parallel_postulates.parallel_postulates.
Require Import GeoCoq.Algebraic.POF_to_Tarski.

Section rcfTarski.

Variable R : rcfType.
Variable n : nat.

Lemma quarter: (1/(1+1)) * (1/(1+1)) = (1/(1+1+1+1)) :> R.
Proof. by rewrite mulf_div mulr1 mulrDl mulrDr !mulr1 !addrA. Qed.

Lemma one_half_gt0 : 0 < 1 / (1+1) :> R.
Proof. by rewrite divr_gt0 ?addr_gt0 ?ltr01. Qed.

Lemma one_half_ge0 : 0 <= 1 / (1 + 1) :> R.
Proof. by rewrite ltW ?one_half_gt0. Qed.

Lemma one_half_lt1 : 1 / (1 + 1) < 1 :>R.
Proof.
by rewrite ltr_pdivr_mulr ?mul1r ?cpr_add ?addr_gt0 ?ltr01.
Qed.

Lemma one_half_neq0 :  (1 / (1 + 1) == 0 :> R) = false.
Proof.
by rewrite mulf_eq0 invr_eq0 paddr_eq0 ?oner_eq0 ?lter01.
Qed.

Lemma one_quarter_lt_one_half: (1/(1+1)) * (1/(1+1)) < 1/(1+1) :> R.
Proof.
rewrite quarter ltr_pdivl_mulr ?addr_gt0 ?ltr01 //.
rewrite mulrC mulrA ltr_pdivr_mulr ?addr_gt0 ?ltr01 //.
rewrite mul1r mulr1 -subr_lt0 !opprD !addrA -[_+1-1]addrA subrr addr0.
rewrite subrr add0r subr_lt0.
by apply lt_trans with 0; first rewrite ltr_oppl; rewrite ?oppr0 ?ltr01.
Qed.

Lemma one_eighth_lt_one_quarter: (1/(1+1+1+1))*(1/(1+1+1+1))<(1/(1+1))*(1/(1+1)):> R.
Proof.
apply ltr_pmul.
rewrite mul1r ltW // ?invr_gt0 ?addr_gt0 ?ltr01 //.
rewrite mul1r ltW // ?invr_gt0 ?addr_gt0 ?ltr01 //.
rewrite -quarter.
exact: one_quarter_lt_one_half.
rewrite -quarter.
exact: one_quarter_lt_one_half.
Qed.

Definition Point' n : Type := {p : 'rV[R]_n | (p *m p^T) 0 0 < 1}.
Definition Point := Point' n.
Notation "#" := proj1_sig.
Implicit Types (a b c d: Point).
Implicit Types (v w x y z : 'rV[R]_n).

Definition omd_v v w := (1 - (v *m (w)^T) 0 0).
Definition dist_v v w := (omd_v v v * omd_v w w)/(omd_v v w)^+2.
Definition cong_v v w x y :=
  (omd_v v w)^+2/(omd_v v v * omd_v w w) ==
  (omd_v x y)^+2/(omd_v x x * omd_v y y).
Definition bet_dist_v x y z :=
  dist_v x z == (dist_v x y) * (dist_v y z) /
  (1+Num.sqrt(1-(dist_v x y))*Num.sqrt(1-(dist_v y z)))^+2.
Definition norm v := Num.sqrt((v *m (v)^T) 0 0).

Definition omd a b := omd_v (#a) (#b).
Definition dist a b := dist_v (#a) (#b).
Definition cong' a b c d := cong_v (#a) (#b) (#c) (#d).

Definition bet' a b c := bet (#a) (#b) (#c).
Definition bet_dist a b c := bet_dist_v (#a) (#b) (#c).

Lemma point_vector_eq a b : a == b = (#a == #b).
Proof.
apply /eqP /eqP.
by move->.
induction a, b.
rewrite /=.
move=> eq_x_x0.
move: eq_x_x0 p i=>-> p p0.
have: (p=p0) by apply eq_irrelevance.
by move->.
Qed.

Lemma point_vector_neq a b : a != b = (#a != #b).
Proof. by rewrite point_vector_eq. Qed.

Lemma cauchy_schwartz v w :
  ((v *m w^T) 0 0)^+2 <= (v*m v^T) 0 0 * (w*m w^T) 0 0.
Proof.
case: ((w *m w^T) =P 0).
  move=>/eqP. rewrite quad_eq0=>/eqP ->.
  by rewrite linear0 !mulmx0 !mxE expr2 !mulr0 lexx.
move=> /eqP; rewrite quad_eq0 => w_neq0.
set r := (v *m (w)^T) 0 0/(w*m(w)^T) 0 0.
suffices: 0 <= ((v - r *: w)*m(v - r *: w)^T) 0 0.
rewrite mulmxBl ![_ *m (v - r *: w)^T]dotC !mulmxBl.
rewrite [v*m (r *: w)^T]dotC -!scalemxAl [_*m(r*:w)^T]dotC -scalemxAl.
rewrite scalerA mxE /= mxE /= opprB.
  have: ((r * r) *: (w *m w^T) - r *: (w *m v^T)) 0 0 == 0.
  rewrite mxE /= mxE /= [X in _ + X]mxE /= subr_eq0.
  rewrite {2}/r mulrA mulrAC -!mulrA divff ?quad_neq0 //.
  by rewrite [w *m v ^T]dotC /r !mxE /= !mulrA mulr1 eqxx.
move=> /eqP ->.
rewrite addr0 [X in _ +X]mxE subr_ge0 /r mxE.
rewrite [w*m v^T]dotC mulrC mulrA -expr2 ler_pdivr_mulr //.
by rewrite lt0r quad_ge0 quad_neq0 w_neq0.
by rewrite quad_ge0.
Qed.

Lemma cauchy_schwartz' v w :
  - norm v * norm w <= (v *m w^T) 0 0 <= norm v * norm w.
Proof.
case: (v*m v^T =P 0).
  move=> /eqP ;rewrite quad_eq0 => /eqP->.
  by rewrite /norm !mul0mx !mxE /= !sqrtr0 oppr0 mul0r lexx.
move=> /eqP; rewrite quad_eq0 => v_neq0.
case: (w*m w^T =P 0).
  move=> /eqP ;rewrite quad_eq0 => /eqP->.
  by rewrite /norm linear0 !mulmx0 !mxE /= !sqrtr0 !mulr0 lexx.
move=> /eqP; rewrite quad_eq0 => w_neq0.
move: (cauchy_schwartz v w).
rewrite -[_^+2 <= _]ler_sqrt.
- by rewrite sqrtr_sqr ler_norml  !sqrtrM !/norm -?mulNr ?quad_ge0.
- by rewrite ?mulr_ge0 ?mulr_gt0 ?lt0r ?quad_ge0 ?quad_neq0 ?w_neq0 ?v_neq0.
Qed.

Lemma cauchy_schwartz_eq v w (r := ((v *m w^T) 0 0)/((w *m w^T) 0 0)):
  w != 0 -> (((v *m w^T) 0 0)^+2 == ((v*m v^T) 0 0 * (w*m w^T)0 0)) = (v ==  r *: w).
Proof.
move=> w_neq0.
apply /eqP /eqP.
move=> H.
suffices: (((v - r *: w) *m (v - r *: w)^T) == 0).
 by rewrite quad_eq0 subr_eq0 => /eqP.
rewrite [X in X == 0]mx11_scalar.
rewrite mulmxBl ![_ *m (v-r*:w)^T]dotC !mulmxBl.
rewrite -!scalemxAl ![_*m(r*:w)^T]dotC -!scalemxAl scalerA.
rewrite opprB mxE /=.
  have: ((r * r) *: (w *m w^T) - r *: (w *m v^T)) 0 0 == 0.
  rewrite mxE /= mxE /= [X in _ + X]mxE /= subr_eq0.
  rewrite {2}/r mulrA mulrAC -!mulrA divff ?quad_neq0 //.
  by rewrite [w *m v ^T]dotC /r !mxE /= !mulrA mulr1 eqxx.
move=> /eqP->.
rewrite addr0 mxE /= [X in _ + X]mxE /=.
rewrite /r [ X in _ - X]mxE /= [w*m(v)^T]dotC.
rewrite mulrAC -expr2 H -mulrA divff ?quad_neq0 //.
rewrite mulr1 subrr.
by rewrite [X in _ == X]mx11_scalar !mxE /=.
move->.
rewrite -scalemxAl mxE /= expr2.
rewrite -scalemxAl [_*m(r*:w)^T]dotC -scalemxAl scalerA.
rewrite [((r * r) *: (w *m w^T)) 0 0]mxE /=.
by rewrite mulrAC !mulrA.
Qed.

Lemma cauchy_schwartz_eq'  v w (r := ((v *m w^T) 0 0)/((w *m w^T) 0 0)):
  w != 0 -> `|(v *m w^T) 0 0| == norm v * norm w = (v ==  r *: w).
Proof.
move => w_neq0.
suffices: (`|(v *m w^T) 0 0| == norm v * norm w) =
 (((v *m w^T) 0 0)^+2 == ((v*m v^T) 0 0 * (w*m w^T)0 0)).
  move->.
  by apply cauchy_schwartz_eq.
rewrite -[X in _ = X]eqr_sqrt ?sqr_ge0 ?mulr_ge0 ?quad_ge0 //.
by rewrite sqrtr_sqr sqrtrM -!/(norm _) ?quad_ge0.
Qed.

Lemma p_scalar_lt1 v w :
  (v *m v^T) 0 0 < 1 -> (w *m w^T) 0 0 < 1 -> v != w ->
 ( v *m w^T) 0 0 < 1.
Proof.
move => v_in_disk w_in_disk ?.
apply lt_trans with ( ((v *m v^T) 0 0 + (w *m w^T) 0 0)/(1+1)).
rewrite ltr_pdivl_mulr ?addr_gt0 ?ltr01 //.
rewrite mulrDr mulr1.
assert (0 < ((v - w) *m (v - w)^T) 0 0).
by rewrite lt_def quad_ge0 quad_neq0 subr_eq0 andbT.
move: H.
rewrite mulmxBl [X in X - _]dotC [X in _ - X]dotC !mulmxBl 2!mxE /=.
rewrite addrC mxE /= !addrA [X in _+X]mxE subr_gt0 [X in -X+_]mxE.
rewrite addrC opprD [X in _ - X]mxE opprK -addrCA addrC.
by rewrite ltr_subr_addr dotC.
rewrite ltr_pdivr_mulr ?addr_gt0 ?ltr01 //.
by rewrite mulrDr mulr1 ltr_add.
Qed.

Lemma p_scalar_point_lt1 a b:
  ((#a) *m (#b)^T) 0 0 < 1.
Proof.
case: ((#a)=P(#b)).
  by move->; destruct b.
move=> /eqP ab_neq.
apply p_scalar_lt1.
by destruct a.
by destruct b.
by [].
Qed.

Lemma invf_eq (a b : R) : b!=0 -> a==b = (a^-1 == b^-1).
Proof.
move=> /negPf b_neq0.
have: (a==b = (a/b == b/b)).
by rewrite -[X in _ = X]subr_eq0 -mulrBl
 mulf_eq0 invr_eq0 b_neq0 orbF subr_eq0.
move->.
rewrite divff ?b_neq0// -invr_eq1 invf_div.
have: (b/a == 1 = (b/a * b^-1 == b^-1)).
by rewrite -[X in _ = X]subr_eq0 -{2}[b^-1]mul1r -mulrBl
 mulf_eq0 invr_eq0 b_neq0 orbF subr_eq0.
move->.
by rewrite mulrAC divff ?b_neq0// mul1r.
Qed.

Lemma divf_lt1 (a b: R): 0 < b -> a / b < 1 = (a < b).
Proof.
move=> b_gt0.
suffices: (a/b < b/b) = (a < b).
  by move<- ; rewrite divff ?lt0r_neq0.
by rewrite -subr_lt0 -mulrBl pmulr_llt0 ?invr_gt0 ?subr_lt0.
Qed.

Lemma divf_le1 (a b: R): 0 < b -> a / b <= 1 = (a <= b).
Proof.
move=> b_g0.
suffices: (a/b <= b/b) = (a <= b).
  by move<- ; rewrite divff ?lt0r_neq0.
by rewrite -subr_le0 -mulrBl pmulr_lle0 ?invr_gt0 ?subr_le0.
Qed.

Lemma divf_eq1 (a b : R): b!=0 -> a/b == 1 = (a == b).
Proof.
move=> /negPf b_neq0.
suffices: (a/b == b/b) = (a == b).
  by move<-; rewrite divff ?b_neq0.
by rewrite -subr_eq0 -mulrBl mulf_eq0 invr_eq0 b_neq0 subr_eq0 orbF.
Qed.

Lemma invf_lt_invf (a b : R) : 0 < a -> 0 < b ->
  a^-1 < b^-1 = (b < a).
Proof. by move=> a_gt0 b_gt0; rewrite ltf_pinv. Qed.

Lemma scaler_eq v w k: k!=0 ->
  v == w = (k*:v == k*: w).
Proof.
move=> /negPf k_neq0.
apply Logic.eq_sym.
by rewrite -subr_eq0 -scalerBr scaler_eq0 k_neq0 orFb subr_eq0.
Qed.

Lemma omd_gt0 a b : 0 < omd a b.
Proof.
by rewrite /omd subr_gt0 p_scalar_point_lt1.
Qed.

Lemma norm_ge0 v : 0 <= norm v.
Proof. by rewrite /norm sqrtr_ge0. Qed.

Lemma norm_sqr v : (norm v)^+2 = (v *m v^T) 0 0.
Proof. by rewrite /norm sqr_sqrtr ?quad_ge0. Qed.

Lemma norm_point_lt1 a : norm(#a) < 1.
Proof.
rewrite /norm -[X in _ < X]sqrtr1 ltr_sqrt ?ltr01 //.
by destruct a.
Qed.

Lemma norm_point_le1 a : norm(#a) <= 1.
Proof. by rewrite ltW ?norm_point_lt1. Qed.

Lemma omd_ge0 a b : 0 <= omd a b.
Proof. by rewrite ltW ?omd_gt0. Qed.

Lemma omd_eq0 a b : omd a b == 0 = false.
Proof. by rewrite gt_eqF ?omd_gt0. Qed.

Lemma omd_v_reflexivity v w : omd_v v w = omd_v w v.
Proof. by rewrite /omd_v dotC. Qed.

Lemma omd_reflexivity a b : omd a b = omd b a.
Proof. by rewrite /omd omd_v_reflexivity. Qed.

Lemma dist_v_reflexivity v w : dist_v v w = dist_v w v.
Proof.
by rewrite /dist_v omd_v_reflexivity [X in X/_]mulrC.
Qed.

Lemma dist_reflexivity a b : dist a b =  dist b a.
Proof. by rewrite /dist dist_v_reflexivity. Qed.

Lemma dist_aa_eq1 a : dist a a = 1.
Proof.
by rewrite /dist/dist_v expr2 divff //mulf_neq0//;
rewrite -/(omd a a) omd_eq0.
Qed.

Lemma cong_identity_holds_aux v w:
  (1-norm(v) * norm w)^+2 - (1-(norm(v))^+2) * (1-(norm(w))^+2) =
  (norm(v) - norm(w))^+2 .
Proof.
apply /eqP.
rewrite -subr_eq0 ![(_-_)^+2]expr2.
rewrite !mulrBl !mulrBr !mul1r !mulr1 !opprD !opprK !addrA.
rewrite mulrA -mulrAC [_*_*_*_]mulrC !mulrA ![norm w * norm v]mulrC.
rewrite -expr2 -mulrA -expr2.
set n_v2 := norm v^+2.
set n_w2 := norm w^+2.
set n_vw := norm v * norm w.
rewrite [1 - n_vw - n_vw + n_v2 * n_w2 - 1]addrC.
rewrite !addrA [-1+1]addrC subrr add0r.
rewrite [- n_vw - n_vw + n_v2 * n_w2 + n_w2 + n_v2 - n_v2 * n_w2 - n_v2 + n_vw]addrC.
rewrite !addrA subrr add0r.
rewrite [- n_vw + n_v2 * n_w2 + n_w2 + n_v2 - n_v2 * n_w2 - n_v2 + n_vw ]addrC.
rewrite !addrA subrr add0r.
rewrite [n_v2 * n_w2 + n_w2 + n_v2 - n_v2 * n_w2]addrC.
rewrite !addrA [- (n_v2 * n_w2) + n_v2 * n_w2 ]addrC subrr add0r.
by rewrite -addrC !addrA -addrA subrr addr0 addrC subrr.
Qed.

Lemma addr_ge_gt0 (x y : R): 0 < x -> 0 <= y -> 0 < x + y.
Proof.
move=> x_gt0 y_ge0.
apply lt_le_trans with x.
by [].
by rewrite -subr_ge0 addrAC subrr add0r.
Qed.

Lemma triangle_ineq v w :
  norm (v + w) <= norm (v) + norm (w).
Proof.
case: (w =P 0).
  move ->.
  by rewrite {3}/norm mul0mx mxE sqrtr0 !addr0 lexx.
move=>/eqP w_neq0.
suffices : (norm (v + w))^+2 <= (norm v + norm w)^+2.
- rewrite -ler_sqrt ?le0r.
  + by rewrite !sqrtr_sqr !ger0_norm ?addr_ge0 ?norm_ge0.
  rewrite addrC expr2 ?mulr_gt0 ?addr_ge_gt0 ?orbT ?norm_ge0 // lt_def;
  rewrite norm_ge0 /norm lt0r_neq0 //;
  by rewrite sqrtr_gt0 lt_def quad_ge0 quad_neq0 w_neq0.
rewrite norm_sqr mulmxDl ![_*m(v+w)^T]dotC !mulmxDl mxE.
rewrite ![(_*m_^T+_*m_^T) 0 0]mxE expr2 mulrDr !mulrDl -!norm_sqr -!expr2.
rewrite ?ler_add ?lexx //.
by move: (cauchy_schwartz' w v) => /andP[_ ].
by move: (cauchy_schwartz' v w) => /andP[_ ].
Qed.

Lemma sqrt_invf (a :R) : (Num.sqrt(a))^-1 = Num.sqrt(a^-1).
Proof.
apply /eqP.
case: (Num.sqrt a =P 0).
  move=> sqrt_a_eq0.
  by rewrite sqrt_a_eq0 eq_sym invr0 sqrtr_eq0 invr_le0
   -sqrtr_eq0 sqrt_a_eq0.
move=>/eqP sqrt_a_neq0.
have: 0 < a by
  move: sqrt_a_neq0; rewrite sqrtr_eq0 -ltNge.
move=> a_gt0.
rewrite eq_sym -divf_eq1 ?invr_eq0 // invrK -sqrtrM ?invr_ge0 ?ltW //.
rewrite mulrC divff ?sqrtr1 ?lt0r_neq0  //.
Qed.

Lemma dist'_ge0 a b : 0 <= omd a b ^+ 2 - omd a a * omd b b.
Proof.
apply le_trans with
((1-norm(#a) * norm(#b))^+2 - (1-(norm(#a))^+2) * (1-(norm(#b))^+2)).
by rewrite cong_identity_holds_aux sqr_ge0.
rewrite !norm_sqr -!/(omd_v _ _) -!/(omd _ _).
rewrite ler_sub ?lexx //.
move: (cauchy_schwartz' (#a) (#b)) => /andP [_ ?].
by rewrite expr2 ler_pmul ?subr_ge0 ?mulr_ile1 ?norm_ge0 ?norm_point_le1 //;
rewrite /omd/omd_v ler_sub ?lexx.
Qed.

Lemma dist_le1 a b : dist a b <= 1.
Proof.
rewrite /dist/dist_v -!/(omd _ _).
rewrite divf_le1 ; last by rewrite expr2 mulr_gt0 ?omd_gt0.
by rewrite -subr_ge0 dist'_ge0.
Qed.

Lemma dist_gt0 a b: 0 < dist a b.
Proof.
by rewrite /dist /dist_v -!/(omd _ _) expr2 invfM
  ?mulr_gt0 ?invr_gt0 ?omd_gt0.
Qed.

Lemma dist_cong' a b c d :
  dist a b == dist c d = cong' a b c d.
Proof. rewrite /dist/dist_v /cong'/cong_v invf_eq.
by rewrite !invf_div.
by rewrite expr2 ?mulf_neq0 ?invr_neq0 ?mulf_neq0 -?/(omd _ _) ?omd_eq0.
Qed.

Lemma omd_cb a b l:
  (1 - (((1 - l) *: # a + l *: # b) *m (# b)^T) 0 0) =
     (1-l) * omd a b + l * omd b b.
Proof.
apply /eqP.
rewrite mulmxDl mxE -!scalemxAl ![(_ *: (_ *m (_)^T)) 0 0]mxE  opprD.
rewrite eq_sym.
rewrite /omd/omd_v !mulrBr !mulr1.
rewrite !addrA addrAC addrC !addrA [l + 1]addrC.
by rewrite -!addrA addrC addrA subrr add0r addrC  !addrA eqxx.
Qed.

Lemma omd_ca  a b l:
  (1 - (((1 - l) *: # a + l *: # b) *m (# a)^T) 0 0) =
    (1-l) * omd a a + l * omd a b.
Proof.
apply /eqP.
rewrite mulmxDl mxE -!scalemxAl ![(_ *: (_ *m (_)^T)) 0 0]mxE  opprD.
rewrite [# b *m (# a)^T]dotC eq_sym.
rewrite /omd/omd_v !mulrBr !mulr1.
rewrite !addrA addrAC addrC !addrA [l + 1]addrC.
by rewrite -!addrA addrC addrA subrr add0r addrC  !addrA eqxx.
Qed.

Lemma omd_cc a b l:
  1 - (((1 - l) *: # a + l *: # b) *m ((1 - l) *: # a + l *: # b)^T)  0 0 =
    (1-l)^+2 * omd a a + l^+2 * omd b b + l * (1-l) * omd a b *+2.
Proof.
apply /eqP.
rewrite mulmxDl mxE -!scalemxAl ![(_ *: (_ *m (_)^T)) 0 0]mxE  opprD.
rewrite ![#_*m_^T]dotC addrA.
have: 1 == (l*1+(1-l)*1) by
  rewrite !mulr1 addrCA subrr addr0.
move=> /eqP l_eq.
rewrite {1}l_eq -[l*1 + _ + _]addrA -mulrBr addrAC -mulrBr.
rewrite omd_ca omd_cb mulrDr mulrDr.
rewrite addrACA [X in X + _]addrC mulrA -expr2.
rewrite addrA addrAC [(1 - l) * (l * omd a b)]mulrCA.
rewrite -[X in X +_ == _]addrA addrAC mulrA -expr2.
by rewrite !addrA !mulrA eqxx.
Qed.

Lemma bet_dist_bet' a b c :
  bet' a b c -> bet_dist a b c.
Proof.
rewrite /bet_dist /bet_dist_v.
move=>/orP[|betS_abc]. (* We first do the betE case *)
  by move=>/betEP[[-> <-]|->|->] ; rewrite -!/(dist _ _);
  rewrite dist_aa_eq1 subrr sqrtr0 ?mulr0 ?mul0r
  addr0 expr1n invr1 ?mulr1 ?mul1r.
rewrite /dist_v -!/(omd _ _) -subr_eq0.
rewrite -!mulrA -mulrBr mulf_eq0 omd_eq0 orFb.
rewrite [X in _ - X]mulrC -!mulrA.
rewrite [X in _ - X]mulrC -!mulrA.
rewrite [X in _ - X]mulrC -!mulrA.
rewrite -mulrBr mulf_eq0 omd_eq0 orFb.
rewrite subr_eq0 !mulrA mulrAC mulrC -!mulrA -expr2.
rewrite -!exprVn -!exprMn eqf_sqr.
suffices: ((omd a c)^-1 == (* We now this is the right equality *)
  ((omd a b)^-1 *
   ((omd b c)^-1 *
    ((1 +
      Num.sqrt (1 - omd a a * (omd b b * (omd a b)^-1 ^+ 2)) *
      Num.sqrt (1 - omd b b * (omd c c * (omd b c)^-1 ^+ 2)))^-1 *
     omd b b)))) = true.
  by move->.
apply /eqP /eqP.
rewrite !exprVn.
rewrite invf_eq ;
  last by rewrite ?mulf_neq0 ?invr_eq0 ?omd_eq0
  ?lt0r_neq0 ?addr_ge_gt0 ?ltr01 ?mulr_ge0 ?sqrtr_ge0.
rewrite !invfM !invrK.
rewrite !mulrA mulrDr mulr1.
rewrite eq_sym -divf_eq1 ?omd_eq0 //.
rewrite -!mulrA -!invfM divf_eq1 ?mulf_neq0 ?omd_eq0 //.
rewrite -subr_eq0 addrAC addr_eq0.
move: betS_abc=> /betSP[bet_eq betR_gt0 betR_lt1].
move/eqP: bet_eq.
rewrite eq_sym scalerBr -subr_eq0.
rewrite  -addrA addr_eq0 opprD !opprK.
have: (betR (#a) (#b) (#c))^-1 != 0
  by rewrite lt0r_neq0 ?invr_gt0.
move=> l_neq0.
rewrite (scaler_eq _ _ l_neq0).
rewrite scalerDr !scalerA mulrC divff ?lt0r_neq0 // !scale1r.
rewrite scalerBr [_ - _]addrC addrA -{1}[#a]scale1r -scalerBl.
move: l_neq0 ;
set l := (betR (#a) (#b) (#c))^-1 => l_neq0 /eqP c_eq.
have: (omd a b * omd b c - omd b b * omd a c ==
  (1 - l) * (omd a b ^+ 2 - omd a a * omd b b)).
  rewrite ![omd _ c]omd_reflexivity.
  rewrite ![omd c _]/omd/omd_v c_eq.
  rewrite omd_cb omd_ca.
  rewrite [omd _ _ * (_ + _)]mulrDr [omd _ _ * (_ + _)]mulrDr.
  rewrite opprD addrAC !addrA -addrA addrC.
  rewrite [- (omd b b * (l * omd a b)) + omd a b * (l * omd b b)]addrC.
  rewrite mulrCA [X in _- X]mulrC mulrA subrr add0r.
  rewrite mulrCA -expr2 [X in _ -X]mulrCA -mulrBr.
  by rewrite [omd b b * _]mulrC eqxx.
move /eqP ->.
rewrite eq_sym mulrA mulrACA.
rewrite -{1}[omd a b]ger0_norm ?omd_ge0 //.
rewrite -{1}[omd b c]ger0_norm ?omd_ge0 //.
rewrite -!sqrtr_sqr.
rewrite -sqrtrM; last by rewrite expr2 mulr_ge0 ?omd_ge0.
rewrite -sqrtrM; last by rewrite expr2 mulr_ge0 ?omd_ge0.
rewrite ![_^+2 * (_ - _)]mulrBr !mulr1.
rewrite [_^+2 * (_)]mulrC.
rewrite [_^+2 * (_)]mulrC.
rewrite -!expr2 !mulrA -!mulrA -!expr2.
rewrite ![_^-2 * _^+2]mulrC ?divff ?expr2 ?mulf_neq0 ?omd_eq0 //.
rewrite !mulr1 -sqrtrM -!expr2 ?dist'_ge0 //.
have: (omd b c ^+ 2 - omd b b * omd c c) ==
  ((1-l)^+2 * (omd a b ^+ 2 - omd a a * omd b b)).
  rewrite [omd b c]omd_reflexivity.
  have: omd c c == (
    (1-l)^+2 * (omd a a)
    + l^+2 * omd b b
    + (1-l) * l * omd a b
    + (1-l) * l * omd a b).
    rewrite [omd c c]/omd/omd_v c_eq.
    rewrite mulmxDl mxE -!scalemxAl mxE [X in 1 - (_  + X)]mxE ![(#_)*m(_)^T]dotC.
    have:  1 == (1-l)*1 +(l*1)
      by rewrite !mulr1  addrAC -addrA subrr addr0.
    move=> /eqP one_eq ; rewrite{1}one_eq.
    rewrite !opprD !addrA addrAC addrC !addrA -!addrA -mulrBr.
    rewrite !addrA [ X in X + _]addrC -mulrBr.
    rewrite omd_cb omd_ca mulrDr mulrDr.
    rewrite mulrA -expr2 [l * ((1 - l) * omd a b)]mulrCA.
    rewrite [l * (l * omd b b)]mulrA -expr2.
    rewrite [(1 - l) * (l * omd a b)]mulrA.
    by rewrite addrA addrAC -addrA addrAC addrA eqxx.
  move/eqP ->.
  rewrite [omd c b]/omd/omd_v c_eq omd_cb.
  rewrite sqrrD !exprMn.
  rewrite [omd b b * _]mulrDr [omd b b * _]mulrDr [omd b b * _]mulrDr.
  rewrite !opprD.
  rewrite [-(omd b b * ((1 - l) ^+ 2 * omd a a)) - omd b b * (l ^+ 2 * omd b b)]addrC.
  rewrite !addrA -!addrA addrC !addrA -!addrA addrC.
  rewrite !addrA -!addrA addrC !addrA.
  rewrite [omd b b * (l ^+ 2 * omd b b)]mulrC expr2 expr2 mulrA.
  rewrite subrr sub0r addrC !addrA -!addrA.
  rewrite addrCA !addrA -!addrA addrC !addrA.
  rewrite mulrAC [ omd b b * ((1 - l) * l * omd a b)]mulrC.
  rewrite -mulrA -[(1 - l) * l * omd a b * omd b b]mulrA.
  rewrite [omd a b * omd b b]mulrC mulrA mulrA mulrA.
  rewrite subrr sub0r addrAC addrC !addrA subrr add0r.
  rewrite [X in _ - X]mulrC.
  by rewrite -[X in _ - X]mulrA -mulrBr eqxx.
move /eqP ->.
rewrite mulrCA -expr2 -exprMn sqrtr_sqr.
rewrite ler0_norm ;
last rewrite nmulr_rle0 ?subr_lt0 ?invf_gt1 ?dist'_ge0 //.
by rewrite opprK eqxx.
Qed.

Lemma dist_eq1' a b:
  dist a b == 1 -> (a=b).
Proof.
move=>  dist_ab.
apply /eqP.
move: dist_ab.
rewrite /dist /dist_v -!/(omd _ _).
rewrite divf_eq1 ?expr2 ?mulf_neq0 ?omd_eq0 //.
rewrite -expr2.
case: (((#a)*m(#b)^T) 0 0 =P norm(#a) * norm(#b)).
  rewrite /omd/omd_v point_vector_eq => pab_eq.
  case: (#b =P 0).
    move ->.
    rewrite [#a*m 0^T]dotC !mul0mx [X in _*(1 - X)]mxE [X in (1-X)^+2]mxE /=.
    rewrite subr0 expr2 !mulr1 subr_eq -subr_eq0 opprD.
    rewrite addrA subrr sub0r oppr_eq0.
    by rewrite quad_eq0'.
  move=> /eqP b_neq0 H.
  suffices: (norm(#a) - norm(#b))^+2 == 0.
    rewrite sqrf_eq0 subr_eq0 /norm eqr_sqrt ?quad_ge0 // => /eqP na_nb_eq.
    have: (# a *m (# b)^T) 0 0 == `|(# a *m (# b)^T) 0 0|.
      rewrite eq_sym -ger0_def.
      by rewrite pab_eq mulr_ge0 ?norm_ge0.
    move=> /eqP pab_abs.
    assert (pab_eq2 := pab_eq).
    move/eqP: pab_eq.
    rewrite pab_abs cauchy_schwartz_eq' //.
    move => /eqP ->.
    rewrite pab_eq2.
    have: norm(#a) == norm(#b)
      by rewrite /norm eqr_sqrt ?quad_ge0 ?na_nb_eq.
    move => /eqP ->.
    rewrite /norm -sqrtrM -?expr2 ?quad_ge0 //.
    rewrite sqrtr_sqr.
    have: `|(# b *m (# b)^T) 0 0| == (# b *m (# b)^T) 0 0.
      by rewrite -ger0_def quad_ge0.
    move=> /eqP ->.
    by rewrite divff ?scale1r ?quad_neq0.
  rewrite -cong_identity_holds_aux.
  by rewrite subr_eq0 eq_sym !norm_sqr -pab_eq H.
rewrite -divf_eq1 ; last by rewrite expr2 mulf_eq0 omd_eq0.
move=> /eqP pab_neq /eqP dist_eq1.
exfalso.
suffices: 1 < (1-(norm(#a))^+2) * (1-(norm(#b))^+2)/(1-norm(#a) * norm(#b))^+2.
  rewrite -invf_lt1;
    last by rewrite ?mulr_gt0 -?exprVn ?exprn_gt0 ?invr_gt0 ?subr_gt0
    ?expr2 ?mulr_ilt1 ?norm_ge0 ?norm_point_lt1.
  rewrite invf_div divf_lt1;
    last by rewrite mulr_gt0 ?subr_gt0 ?expr2 ?mulr_ilt1 ?norm_ge0 ?norm_point_lt1.
  rewrite -subr_lt0 cong_identity_holds_aux.
  move=> H_lt0.
  suffices: (norm(#a) - norm(#b))^+2 < 0 <= (norm(#a) - norm(#b))^+2.
    by rewrite lt_le_asym.
  by rewrite H_lt0 sqr_ge0.
rewrite -[X in X < _]dist_eq1.
rewrite !norm_sqr -!/(omd_v _ _) -!/(omd _ _).
have : (omd a b)^-1 < (1 - norm (# a) * norm (# b))^-1.
rewrite invf_lt_invf ?subr_gt0 ?mulr_ilt1 ?norm_ge0 ?norm_point_lt1 ?p_scalar_point_lt1 //.
rewrite /omd /omd_v -subr_gt0 opprB !addrA addrC !addrA [-1+1]addrC.
rewrite subrr sub0r addrC subr_gt0 lt_def.
rewrite eq_sym pab_neq.
by move:(cauchy_schwartz' (#a) (#b))=> /andP[_ ->].
move=> ?.
rewrite -subr_gt0 -mulrBr ?mulr_gt0 ?omd_gt0 //.
by rewrite subr_gt0 -!exprVn !expr2 ltr_pmul ?invr_ge0 ?omd_ge0.
Qed.

Lemma cong_identity_holds a b c : cong' a b c c -> a = b.
Proof.
rewrite -dist_cong' dist_aa_eq1.
exact: dist_eq1'.
Qed.

Lemma dist_eq1 a b :
  dist a b == 1 = (a==b).
Proof.
apply /eqP /eqP.
move=> /eqP.
exact: dist_eq1'.
move->.
rewrite dist_aa_eq1 //.
Qed.

Lemma dist_neq1 a b:
  dist a b != 1  = (a!=b).
Proof. by rewrite dist_eq1. Qed.

Lemma dist_lt1 a b:
  dist a b < 1 = (a!=b).
Proof.
by rewrite -dist_neq1 lt_def dist_le1 andbT eq_sym.
Qed.

Lemma cong_inner_transitivity_vector (a b c d e f : 'rV[R]_n) :
  cong_v a b e f -> cong_v c d e f -> cong_v a b c d.
Proof. by rewrite /cong_v => /eqP -> /eqP ->. Qed.

Lemma bet_in_disk (a b c : 'rV[R]_n) :
  (a *m a^T) 0 0 < 1 -> (c *m c^T) 0 0 < 1 -> bet a b c
  -> (b *m b^T) 0 0 < 1.
Proof.
move=> a_in_disk c_in_disk.
rewrite /bet => /orP[/betEP [ [H _] | H | H ] |H ] ;
rewrite -?H ?a_in_disk ?H ?c_in_disk //.
move: H.
rewrite betS_neq13=> /andP [/betSP [H1 H2 H3] H4].
have: (c *m a^T) 0 0 < 1 by rewrite dotC p_scalar_lt1 //.
move=> ca_lt1.
move/eqP:  H1;rewrite subr_eq => /eqP ->.
set r := betR a b c.
rewrite -[X in _ + X]scale1r scalerBr addrAC -addrA -scalerBl.
rewrite mulmxDl -!scalemxAl dotC [X in _ + (_ *: X)]dotC.
rewrite !mulmxDl -!scalemxAl [a *m c^T]dotC !scalerDr !scalerA.
rewrite addrA.
apply lt_le_trans with
 (r * r * 1 + r * (1 - r) * 1 + (1 - r) * r * 1 + (1 - r) * (1 - r) * 1).
rewrite !mxE ?ltr_add //;
rewrite -subr_gt0 -mulrBr ?pmulr_rgt0 ?subr_gt0 //.
move: c_in_disk ; rewrite !mxE //.
move: ca_lt1 ; rewrite !mxE //.
move: ca_lt1 ; rewrite !mxE //.
move: a_in_disk ; rewrite !mxE //.
rewrite !mulr1 !mulrBl !mulrBr !mul1r !mulr1.
rewrite [r * r + (r -r * r)]addrCA subrr addr0.
rewrite [(1 - r) - (r - r * r)]addrC addrA addrC.
rewrite -[r + (r - r * r) - (r - r * r)]addrA subrr addr0.
by rewrite addrAC -addrA subrr addr0 lexx.
Qed.

Lemma X_in_disk (a b p q : Point) :
  (exists X' : 'rV[R]_n, bet (# p) X' (# b) /\ bet (# q) X' (# a))->
  (exists X : Point, bet (# p) (# X) (# b) /\ bet (# q) (# X) (# a)).
Proof.
move => H.
destruct H.
assert ((x *m x^T) 0 0 < 1).
apply bet_in_disk with (#p) (#b).
by destruct p.
by destruct b.
destruct H as [H _] ; assumption.
exists (exist (fun p => (p *m p^T) 0 0 < 1) x H0).
exact: H.
Qed.

Lemma segment_addition' (a b c a' b' c' : Point):
  cong' a b a' b' -> cong' b c b' c' -> bet' a b c -> bet' a' b' c' ->
  cong' a c a' c'.
Proof.
rewrite -!dist_cong'.
move=> /eqP cong'_aba'b' /eqP cong'_bcb'c' bet'_abc bet'_a'b'c'.
apply bet_dist_bet' in bet'_abc.
apply bet_dist_bet' in bet'_a'b'c'.
move: bet'_abc bet'_a'b'c'.
rewrite /bet_dist /bet_dist_v -!/(dist _ _) => /eqP -> /eqP ->.
by rewrite cong'_aba'b' cong'_bcb'c' eqxx.
Qed.

Lemma cong_v_aabc a b c : cong_v (#a) (#a) (#b) (#c) = ((#b) == (#c)).
Proof.
apply /eqP /eqP.
move=>/eqP.
rewrite eq_sym -/(cong_v _ _ _ _) -/(cong' _ _ _ _) => H.
rewrite (@cong_identity_holds b c a) //.
move->.
rewrite -!expr2 -!/(omd _ _) !divff ?mulf_eq0 ?omd_eq0 //.
Qed.

Lemma cong_v_bcaa a b c : cong_v (#b) (#c) (#a) (#a) = ((#b) == (#c)).
Proof.
apply /eqP /eqP.
move=>/eqP.
rewrite -/(cong_v _ _ _ _) -/(cong' _ _ _ _) => H.
rewrite (@cong_identity_holds b c a) //.
move->.
rewrite -!expr2 -!/(omd _ _) !divff ?mulf_eq0 ?omd_eq0 //.
Qed.

Lemma five_segment_holds_aux a c d :
  dist c d = dist a d * (omd c c / omd a a) * (omd a d/ omd c d)^+2.
Proof.
apply /eqP.
rewrite eq_sym /dist /dist_v -!/(omd _ _) exprMn exprVn.
rewrite mulrACA mulrC -[omd a a * omd d d / omd a d ^+ 2 * omd a d ^+ 2]mulrA.
rewrite [omd a d ^- 2 * omd a d ^+ 2]mulrC divff;
  last by rewrite expr2 mulf_eq0 omd_eq0.
rewrite mulr1 mulrACA mulrC -[omd c c / omd a a * omd a a]mulrA.
rewrite [(omd a a)^-1 * omd a a]mulrC divff ?omd_eq0 //.
by rewrite mulr1 mulrAC -mulrA mulrC eqxx.
Qed.

Lemma five_segment_holds_aux2 a b c l mu:
(#c) == (1-l) *: #a + l*: #b ->
mu == l * Num.sqrt(omd b b/ omd a a) ->
mu != 0 ->
omd c c /omd a a =
  mu^+2 *(((1-l)/mu)^+2 + (1-l) / mu * 2%:R/Num.sqrt(dist a b) + 1).
Proof.
move=> /eqP c_eq /eqP mu_eq mu_neq0.
have: omd c c == (
  (1 - l)^+2 * (omd a a)
  + l^+2 * omd b b
  + (1 - l) * l * omd a b
  + (1 - l) * l * omd a b).
  rewrite [omd c c]/omd/omd_v c_eq.
  rewrite mulmxDl mxE -!scalemxAl mxE [X in 1 - (_  + X)]mxE ![(#_)*m(_)^T]dotC.
  have:  1 == (1-l)*1 +(l*1)
    by rewrite !mulr1  addrAC -addrA subrr addr0.
  move=> /eqP one_eq ; rewrite{1}one_eq.
  rewrite !opprD !addrA addrAC addrC !addrA -!addrA -mulrBr.
  rewrite !addrA [ X in X + _]addrC -mulrBr.
  rewrite omd_cb omd_ca mulrDr mulrDr.
  rewrite mulrA -expr2 [l * ((1 - l) * omd a b)]mulrCA.
  rewrite [l * (l * omd b b)]mulrA -expr2.
  rewrite [(1 - l) * (l * omd a b)]mulrA.
  by rewrite addrA addrAC -addrA addrAC addrA eqxx.
move=> /eqP ->.
apply /eqP.
rewrite mulrDl mulrDl mulrDl -mulrA divff ?omd_eq0 //.
rewrite mulr1 eq_sym.
rewrite mulrDr mulrDr exprMn exprVn mulrCA divff; last by rewrite expr2 mulf_neq0.
rewrite !mulr1 mulrA mulrA mulrCA {1}[mu^+2]expr2.
rewrite -[mu * mu/mu]mulrA divff //.
rewrite mulr1 mulrAC mu_eq exprMn sqr_sqrtr ?mulr_ge0 ?invr_ge0 ?omd_ge0 //.
rewrite mulrA -[ _ * _ * Num.sqrt _ / Num.sqrt _]mulrA.
rewrite sqrt_invf -sqrtrM /dist/dist_v -!/(omd _ _) ?mulr_ge0 ?invr_ge0 ?omd_ge0 //.
rewrite !invfM !invrK -expr2.
rewrite [X in Num.sqrt X]mulrCA ![X in Num.sqrt X]mulrA.
rewrite [(omd a a)^-1 / omd b b * (omd b b / omd a a)]mulrA.
rewrite -[_ /omd b b * omd b b]mulrA [(omd b b)^-1 * omd b b]mulrC.
rewrite divff ?omd_eq0 // mulr1 -expr2 -[ _ *omd a b * omd a b]mulrA.
rewrite -expr2 -exprMn sqrtr_sqr ger0_norm ?mulr_ge0 ?invr_ge0 ?omd_ge0 //.
rewrite [_^-1 * _]mulrC /GRing.natmul /= mulrDr !mulr1.
by rewrite addrAC !mulrA !addrA eqxx.
Qed.

Lemma five_segment_holds_aux3 a b c d l mu:
(#c) == (1-l) *: #a + l *: (#b) ->
mu == l * Num.sqrt(omd b b/ omd a a) ->
mu != 0 ->
(omd a d/ omd c d) ^+2 =
  (mu^+2 * (((1-l)/mu)^+2
  + (1-l) / mu * 2%:R * Num.sqrt(dist a d/ dist b d)
  + dist a d/dist b d))^-1.
Proof.
move=> /eqP c_eq /eqP mu_eq mu_neq0; apply /eqP.
rewrite eq_sym invf_eq ?expr2 ?mulf_eq0 ?invr_eq0 ?omd_eq0 //.
rewrite -!expr2 invrK eq_sym -exprVn invf_div.
have: omd c d == (1-l) * omd a d + l * (omd b d).
  rewrite /omd c_eq /omd_v mulmxDl dotC mxE dotC -scalemxAl.
  rewrite -scalemxAl opprD [(l *: (_*m (_)^T)) 0 0]mxE.
  rewrite addrA eq_sym mulrBr mulrBr !mulr1.
  by rewrite addrCA !addrA [l + 1 - l]addrAC subrr add0r !mxE eqxx.
move=> /eqP ->.
rewrite [(_ + _)/omd a d]mulrDl -[X in (X+_)^+2]mulrA.
rewrite divff ?omd_eq0 // mulr1 expr2 mulrDl mulrDr -expr2.
rewrite mulrDr -expr2 -[l* omd _ _ / omd _ _]mulrA exprMn.
rewrite [X in _ + _ + (X + _)]mulrC eq_sym.
rewrite ![mu^+2 * (_ +_)]mulrDr exprMn exprVn mulrCA.
rewrite divff; last by rewrite expr2 mulf_neq0.
rewrite mulrA mulrA mulrCA {1}[mu^+2]expr2 -[mu*(mu)/mu]mulrA.
rewrite divff // !mulr1 mulrAC mu_eq mulrA mulrA mulrA.
rewrite -[_ * _* Num.sqrt _ *Num.sqrt _]mulrA -sqrtrM
  ?mulr_ge0 ?invr_ge0 ?omd_ge0 //.
rewrite exprMn sqr_sqrtr ?mulr_ge0 ?invr_ge0 ?omd_ge0 //.
rewrite -[X in _+ _+X]mulrA -[X in _+ _+X]mulrA.
have: omd b b / omd a a * (dist a d / dist b d) ==
  (omd b d / omd a d)^+2.
  rewrite /dist/dist_v -!/(omd _ _).
  rewrite invf_div !mulrA [omd b b / omd a a * omd a a]mulrAC.
  rewrite -[omd b b * omd a a / omd a a]mulrA divff ?omd_eq0 //.
  rewrite !invfM !mulrA -mulrAC mulrC !mulrA [(omd b b)^-1 * omd b b]mulrC.
  rewrite divff ?omd_eq0 // !mul1r mulrC !mulrA [_^-1 *_]mulrC.
  rewrite divff ?omd_eq0 // mul1r -invfM -expr2.
  by rewrite -mulrA -expr2 mulrC exprMn exprVn.
move=> /eqP ->.
rewrite sqrtr_sqr ger0_norm ?mulr_ge0 ?invr_ge0 ?omd_ge0 //.
by rewrite /GRing.natmul /= mulrDr !mulr1 !mulrA !addrA eqxx.
Qed.

Lemma five_segment_holds_aux4 a b :
  omd a a / omd a b = Num.sqrt(omd a a * dist a b/ omd b b).
Proof.
apply /eqP.
rewrite /dist/dist_v -!/(omd _ _) eq_sym !mulrA mulrAC.
rewrite mulrC !mulrA -mulrA divff ?omd_eq0 //.
rewrite mulr1 mulrC mulrCA -expr2 mulrC -exprVn -exprMn.
by rewrite sqrtr_sqr ger0_norm ?mulr_ge0 ?invr_ge0 ?omd_ge0.
Qed.

Lemma five_segment_holds_aux5 a b c l:
  (#c) == (1-l) *: #a + l *: (#b) ->
  l != 0 ->
  a!=b->
  a!=c->
  (omd a c/l/omd a b)^+2 = (1 - dist a b)/(1- dist a c).
Proof.
move=> /eqP c_eq l_neq0 ab_neq bc_neq.
apply /eqP.
rewrite -divf_eq1;
last by rewrite mulf_neq0 ?invr_eq0 ?subr_eq0 1?eq_sym ?dist_neq1.
rewrite invf_div mulrA divf_eq1 ;
last by rewrite subr_eq0 eq_sym dist_neq1.
rewrite mulrDr mulr1 mulrN /(dist a c)/dist_v -!/(omd _ _).
rewrite -{2}mulrA [(omd a c * _)^+2]exprMn mulrA.
rewrite [X in _ -X]mulrAC [X in _ -X*_]mulrAC divff;
  last by rewrite expr2 mulf_eq0 omd_eq0.
rewrite omd_reflexivity {1}/omd/omd_v c_eq omd_ca.
rewrite mulrDl [l * omd a b / l]mulrAC divff //.
rewrite mulrDl mul1r divff ?omd_eq0 //.
rewrite sqrrD [1^+2]expr2 !mul1r !mulr1.
rewrite addrC !addrA mulrC -[(1 - l) * omd a a / l / omd a b]mulrA.
rewrite [(_*(l^-1 / omd a b))^+2]exprMn -mulNr.
rewrite -mulrDl /(omd c c)/omd_v c_eq omd_cc.
rewrite mulrDr mulrDr [omd a a * ((1 - l) ^+ 2 * omd a a)]mulrCA.
rewrite -expr2 -exprMn !opprD [_ + _^+2] addrC addrA.
rewrite addrA subrr sub0r -opprD mulNr.
rewrite [(_)*(l^-1/omd a b)^+2]mulrDl exprMn !exprVn.
rewrite mulrA mulrAC mulrA -[omd a a * l ^+ 2 / l ^+ 2]mulrA.
rewrite divff; last by rewrite expr2 mulf_neq0 ?l_neq0.
rewrite mulr1 mulrAC {1}/omd {1}/omd {1}/omd.
rewrite -/(dist_v _ _) -/(dist _ _).
rewrite [X in dist a b + X]mulrA [l * (1 - l) * omd a b *+ 2]addrC.
rewrite mulrDr [X in dist a b + X/_]mulrDl [X in dist a b + X]mulrDl.
rewrite mulrA mulrAC mulrC [omd a b ^+2]expr2.
rewrite invfM invfM mulrA mulrA mulrA mulrA mulrC mulrA.
rewrite mulrA mulrA -mulrA divff ?omd_eq0 // mulr1.
rewrite mulrACA mulrA mulrC mulrA mulrA mulrA mulrC.
rewrite mulrA mulrA mulrA mulrA -mulrA divff ?l_neq0 //.
rewrite mulr1 mulrC mulrA mulrA mulrAC mulrC mulrA mulrA.
rewrite !opprD addrA -[-_-_-_+_]addrA [X in -_-_+X]addrC.
rewrite subrr addr0 addrC addrA addrA -addrA [X in 1 -_+X]addrC.
by rewrite subrr addr0 eqxx.
Qed.

Lemma betR_neq0 a b c :
  betS (#a) (#b) (#c) -> betR (#a) (#b) (#c) != 0.
Proof.
move => /betSP[_ ? _].
by rewrite lt0r_neq0.
Qed.

Lemma five_segment_holds a a' b b' c c' d d' :
  cong' a b a' b' -> cong' b c b' c' -> cong' a d a' d' -> cong' b d b' d' ->
  bet' a b c -> bet' a' b' c' -> a <> b ->
  cong' c d c' d'.
Proof.
move=> cong1 cong2 cong3 cong4 bet1 bet2  /eqP /negPf ab_neq.
move: bet1 cong1 cong2 cong3 cong4.
rewrite point_vector_eq in ab_neq.
rewrite /bet /cong' => /orP[/betEP[[/eqP]|/eqP|->]|];
rewrite ?ab_neq //.
rewrite cong_v_aabc=> _ /eqP -> //.
move=> betS_abc.
move:bet2.
rewrite /bet => /orP[/betEP[[-> _]|->|->]|];
rewrite ?cong_v_bcaa ?ab_neq //.
move=> _ /eqP -> //.
move=> betS_a'b'c'.
rewrite -!/(cong' _ _ _ _)-!dist_cong'.
move=> /eqP dist_ab /eqP dist_bc /eqP dist_ad /eqP dist_bd.
have: (#c) = extension (#a) (#b) (betR (#a) (#b) (#c))
  by apply betS_extension.
have: (#c') = extension (#a') (#b') (betR (#a') (#b') (#c'))
  by apply betS_extension.
rewrite /extension.
set l := (betR (#a) (#b) (#c))^-1.
set l' := (betR (#a') (#b') (#c'))^-1.
rewrite scalerBr addrAC -[X in _ + X -_]scale1r -addrA.
rewrite -scalerBl addrC.
move => c'_eq.
rewrite scalerBr addrAC -[X in _ + X -_]scale1r -addrA.
rewrite -scalerBl addrC.
move => c_eq.
rewrite (five_segment_holds_aux a c d) (five_segment_holds_aux a' c' d').
set mu := l * Num.sqrt(omd b b/ omd a a).
set mu' := l' * Num.sqrt(omd b' b'/ omd a' a').
have: mu != 0 by
  rewrite /mu /l mulf_neq0 ?invr_neq0 ?betR_neq0 ?lt0r_neq0 ?sqrtr_gt0
   ?mulr_gt0 ?invr_gt0 ?omd_gt0.
have: mu' != 0 by
  rewrite /mu /l mulf_neq0 ?invr_neq0 ?betR_neq0 ?lt0r_neq0 ?sqrtr_gt0
   ?mulr_gt0 ?invr_gt0 ?omd_gt0.
move=> mu'_neq0 mu_neq0.
rewrite (@five_segment_holds_aux2 a b c l mu) ?c_eq //.
rewrite (@five_segment_holds_aux2 a' b' c' l' mu') ?c'_eq //.
rewrite (@five_segment_holds_aux3 a b c d l mu) ?c_eq //.
rewrite (@five_segment_holds_aux3 a' b' c' d' l' mu') ?c'_eq //.
have : (1-l)/mu == (1-l')/mu'.
  suffices: (1-l)/l * (omd a a/ omd a b) ==
    (1-l')/l' * (omd a' a'/ omd a' b').
    rewrite (@five_segment_holds_aux4 a b).
    rewrite (@five_segment_holds_aux4 a' b').
    rewrite [omd a a * dist a b / omd b b]mulrAC.
    rewrite [omd a' a' * dist a' b' / omd b' b']mulrAC.
    rewrite sqrtrM ?mulr_ge0 ?invr_ge0 ?omd_ge0 //.
    rewrite [Num.sqrt (omd a' a' / omd b' b' * dist a' b')]sqrtrM
    ?mulr_ge0 ?invr_ge0 ?omd_ge0 //.
    rewrite -subr_eq0 dist_ab mulrA mulrA -mulrBl mulf_eq0.
    rewrite sqrtr_eq0 /dist/dist_v -!/(omd _ _) -{2}(mul1r (omd a' a')).
    rewrite expr2 invfM mulrA.
    rewrite !pmulr_lle0 ?invr_gt0 ?omd_gt0 //.
    rewrite ler10 orbF subr_eq0 /mu/mu' !invfM.
    by rewrite !sqrt_invf !invf_div !mulrA.
  suffices: (omd a c/l/omd a b)^+2 ==
           (omd a' c'/l'/omd a' b')^+2.
    rewrite eqf_sqr =>/orP[|].
    rewrite [omd a c]omd_reflexivity  [omd c a]/omd/omd_v c_eq.
    rewrite omd_ca.
    rewrite [omd a' c']omd_reflexivity  [omd c' a']/omd/omd_v c'_eq.
    rewrite omd_ca mulrDl mulrDl.
    rewrite [X in _ == X/_]mulrDl [X in _ == X]mulrDl.
    rewrite addrC mulrAC mulrC mulrA mulrA -mulrA divff ?omd_eq0 //.
    rewrite mulr1 mulrC divff; last by rewrite invr_eq0 betR_neq0.
    rewrite eq_sym.
    rewrite addrC mulrAC mulrC mulrA mulrA -mulrA divff ?omd_eq0 //.
    rewrite mulr1 mulrC divff ; last by rewrite invr_eq0 betR_neq0.
    rewrite add2r_eq.
    rewrite mulrAC mulrC mulrA mulrA [_^-1*_]mulrC.
    rewrite eq_sym.
    by rewrite [X in X == _]mulrAC mulrC !mulrA [_^-1*_]mulrC.
    rewrite -subr_eq0 opprK => /negPn /negPf H1.
    move: H1.
    rewrite lt0r_neq0 //.
    rewrite addr_gt0 ?mulr_gt0 ?invr_gt0 ?omd_gt0 //.
    move: betS_abc => /betSP[] //.
    move: betS_a'b'c' => /betSP[] //.
  have : dist a c == dist a' c'
    by rewrite dist_cong' (@segment_addition' a b c a' b' c') -?dist_cong'
    /bet'/bet ?betS_abc ?betS_a'b'c' ?orbT ?dist_ab ?dist_bc.
  move=> /eqP dist_ac.
  rewrite (@five_segment_holds_aux5 a b c l)
    ; rewrite ?c_eq ?invr_eq0 ?betR_neq0 //.
  rewrite (@five_segment_holds_aux5 a' b' c' l')
    ; rewrite ?c'_eq ?invr_eq0 ?betR_neq0 //.
  by rewrite dist_ab dist_ac eqxx.
  move:betS_a'b'c'.
  by rewrite betS_neq12 -point_vector_neq=> /andP [_ ].
  move:betS_a'b'c'.
  by rewrite betS_neq13 -point_vector_neq=> /andP [_ ].
  move:betS_abc.
  by rewrite betS_neq12 -point_vector_neq=> /andP [_ ].
  move:betS_abc.
  by rewrite betS_neq13 -point_vector_neq=> /andP [_ ].
move=> /eqP ->.
rewrite [(_^+2 * _)^-1]invfM mulrA mulrA.
rewrite mulrACA -[dist a d * mu ^+ 2 / mu ^+ 2]mulrA divff;
  last by rewrite expr2 mulf_neq0.
rewrite eq_sym.
rewrite [(_^+2 * _)^-1]invfM mulrA mulrA.
rewrite [X in X == _]mulrAC mulrC.
rewrite mulrA mulrA mulrCA [_^-2 * _^+2]mulrC divff;
  last by rewrite expr2 mulf_neq0.
by rewrite dist_ad dist_bd dist_ab eqxx.
Qed.

Lemma E_in_disk_aux b c d  (E': 'rV[R]_n) :
  cong_v (#b) E' (#c) (#d) ->
  (E' *m (E')^T) 0 0 < 1.
Proof.
move=> cong_v_bE'cd.
rewrite -subr_gt0.
move:cong_v_bE'cd.
rewrite /cong_v -!/(omd _ _) eq_sym.
have: 0 < omd c d ^+ 2 / (omd c c * omd d d)
  by rewrite mulr_gt0 ?invr_gt0 ?expr2 ?mulr_gt0 ?omd_gt0.
move => H1 /eqP H2.
move: H1 ; rewrite H2 lt0r.
rewrite lt0r invfM mulrA.
move => /andP[neq0 ge0].
apply /andP.
split.
  move: neq0.
  by rewrite mulf_eq0 negb_or invr_eq0 => /andP[_ ->].
move: ge0.
rewrite pmulr_rge0 ?invr_ge0 //.
rewrite lt0r mulr_ge0 ?invr_ge0 ?omd_ge0 ?sqr_ge0 // andbT.
move: neq0.
by rewrite mulf_eq0 negb_or=> /andP[-> _].
Qed.

Lemma E_in_disk (a b c d : Point) :
  (exists E' : 'rV[R]_n, bet (#a) (#b) E' /\ cong_v (#b) E' (#c) (#d))->
  exists E : Point, bet' a b E /\ cong' b E c d.
Proof.
move=> H.
destruct H as [E' [bet cong_v]].
assert (E'_in_disk := cong_v).
apply E_in_disk_aux in E'_in_disk.
set E := (exist (fun p => (p *m p^T) 0 0 < 1) E' E'_in_disk).
exists E.
by rewrite /bet' bet /cong' cong_v.
Qed.

Lemma roots_poly2 (a b c: R) (d := b^+2 - 4%:R * a * c):
  a != 0 -> d >= 0 ->
  let r1 := (- b - Num.sqrt d) / 2%:R / a in
  let r2 := (- b + Num.sqrt d) / 2%:R / a in
  a * r1^+2 + b * r1 + c == 0 /\
  a * r2^+2 + b * r2 + c == 0.
Proof.
move=> a_neq0 d_ge0 r1 r2.
have: 4%:R * a * c * (2%:R^-1 / a) ^+ 2 == c / a.
  rewrite exprMn !exprVn mulrCA !mulrA [2%:R ^- 2 * 4%:R]mulrC.
  rewrite /GRing.natmul /= expr2 mulrDl mul1r !addrA.
  rewrite divff ?lt0r_neq0 ?addr_gt0 ?ltr01 //.
  rewrite mul1r expr2 mulrAC invfM mulrA divff //.
  by rewrite mul1r mulrC.
move => /eqP H1.
have: (2%:R^-1 + 2%:R^-1) == 1 :> R.
  by rewrite /GRing.natmul /= -[(1 + 1)^-1]mul1r -mulrDl divff
  ?lt0r_neq0 ?addr_gt0 ?ltr01.
move=> /eqP H2.
have: a * ((r1+b/2%:R/a)^+2-d* (2%:R^-1 / a) ^+ 2 ) == 0.
  rewrite /r1 -!mulrDl [(- b - Num.sqrt d + b)]addrC addrA subrr.
  by rewrite add0r -mulrA exprMn sqrrN sqr_sqrtr ?subrr ?mulr0.
rewrite sqrrD /d mulrBl H1 -exprMn mulrA mulrA mulrA opprD opprK !addrA.
rewrite mulrDr [a * (c / a)]mulrCA divff // mulr1.
rewrite -!addrA subrr addr0 -mulrDl -mulrDr H2 mulr1.
rewrite mulrDr [a * (r1 * b / a)]mulrCA divff // mulr1.
rewrite !addrA [r1*b]mulrC => ->.

have: a * ((r2+b/2%:R/a)^+2-d* (2%:R^-1 / a) ^+ 2 ) == 0.
  rewrite /r2 -!mulrDl [(- b + Num.sqrt d + b)]addrC addrA subrr.
  by rewrite add0r -mulrA exprMn sqr_sqrtr ?subrr ?mulr0.
rewrite sqrrD /d mulrBl H1 -exprMn mulrA mulrA mulrA opprD opprK !addrA.
rewrite mulrDr [a * (c / a)]mulrCA divff // mulr1.
rewrite -!addrA subrr addr0 -mulrDl -mulrDr H2 mulr1.
rewrite mulrDr [a * (r2 * b / a)]mulrCA divff // mulr1.
by rewrite !addrA [r2*b]mulrC => ->.
Qed.

Lemma cong_aaxx (a x : 'rV[R]_n) : cong a a x x.
Proof. by rewrite /cong !subrr eqxx. Qed.

Lemma cong_cdab (a b c d : 'rV[R]_n) :
  cong c d a b = cong a b c d.
Proof. by rewrite /cong eq_sym. Qed.

Lemma cong_id (a b c d: 'rV[R]_n) :  cong a b c d ->
  a == b = (c==d).
Proof.
move=> cong_abcd.
apply /eqP/eqP.
  move=> ab_eq.
  move: cong_abcd.
  rewrite ab_eq cong_cdab.
  exact: cong_identity.
move=> cd_eq.
move: cong_abcd.
rewrite cd_eq.
exact: cong_identity.
Qed.

Lemma cong_inner_transitivity' (a b c d e f : 'rV[R]_n):
  cong a b c d -> cong a b e f ->
  cong c d e f.
Proof.
move => ? ?.
by apply cong_inner_transitivity with a b;
rewrite cong_cdab.
Qed.

Lemma cong_abab (a b : 'rV[R]_n) : cong a b a b.
Proof. by rewrite /cong. Qed.

Lemma cong_bacd (a b c d : 'rV[R]_n) :
  cong b a c d = cong a b c d.
Proof. by rewrite /cong -opprB mulNmx dotC mulNmx opprK. Qed.

Lemma cong_abdc (a b c d : 'rV[R]_n) :
  cong a b d c = cong a b c d.
Proof. by rewrite cong_cdab cong_bacd cong_cdab. Qed.

Lemma segment_addition (a b c a' b' c' : 'rV[R]_n) :
  cong a b a' b' -> cong b c b' c' -> bet a b c -> bet a' b' c' ->
  cong a c a' c'.
Proof.
case: (a =P b).
  move ->.
  rewrite cong_cdab=> H.
  by rewrite (cong_identity H).
move=> /eqP ab_neq cong_aba'b' cong_bcb'c' bet_abc bet_a'b'c'.
rewrite cong_bacd cong_abdc.
apply five_segment with a a' b b'=> //.
by rewrite cong_aaxx.
by rewrite cong_bacd cong_abdc.
by apply /eqP.
Qed.

Lemma one_side_cong_eq (a b c d : 'rV[R]_n) :
  bet a b c -> bet a b d -> cong b c b d -> a != b ->
  c == d.
Proof.
move=> bet_abc bet_abd cong_bcbd ab_neq.
apply /eqP ; apply cong_identity with c.
apply five_segment with a a b b;
rewrite ?cong_abab 1?cong_cdab //;
last by apply /eqP.
by apply segment_addition with b b;
rewrite ?cong_abab.
Qed.

Lemma bet_outer_transitivity (a b c d: 'rV[R]_n) :
  b!=c -> bet a b c -> bet b c d -> bet a c d.
Proof.
move=> bc_neq bet_abc bet_bcd.
destruct (segment_construction a c c d) as [e [? ?]].
suffices: (e == d) => [/eqP <- //|].
apply one_side_cong_eq with b c=> //.
rewrite bet_sym.
by apply bet_inner_transitivity with a;
rewrite bet_sym.
Qed.

Lemma bet_outer_transitivity' (a b c d: 'rV[R]_n) :
  b!=c -> bet a b c -> bet b c d -> bet a b d.
Proof.
move=> ? ? ?.
rewrite bet_sym.
by apply bet_outer_transitivity with c;
rewrite 1?eq_sym 1?bet_sym.
Qed.

Lemma cong'_cdab (a b c d : Point) :
  cong' c d a b = cong' a b c d.
Proof. by rewrite /cong'/cong_v eq_sym. Qed.

Lemma cong'_abab (a b : Point) : cong' a b a b.
Proof. by rewrite /cong'/cong_v. Qed.

Lemma one_side_cong'_eq (a b c d : Point):
  bet' a b c -> bet' a b d -> cong' b c b d -> a != b ->
  c == d.
Proof.
move=> bet_abc bet_abd cong_bcbd ab_neq.
apply /eqP ; apply cong_identity_holds with c.
apply five_segment_holds with a a b b;
rewrite ?cong'_abab 1?cong'_cdab //;
last by apply /eqP.
by apply segment_addition' with b b;
rewrite ?cong'_abab.
Qed.

Lemma one_sub_half : 1 - 2%:R^-1 = 2%:R^-1 :> R.
Proof.
apply /eqP.
rewrite /GRing.natmul /= -subr_eq0 -[(1+1)^-1]mul1r -addrA -opprD.
by rewrite -mulrDl divff ?subrr // lt0r_neq0 // addr_gt0 ?ltr01.
Qed.

Lemma norm_point_subr_gt0 a b : (a!=b) ->
   0 < norm(#b - #a).
Proof.
by rewrite sqrtr_gt0 lt_def quad_ge0 quad_neq0 subr_eq0
 eq_sym point_vector_neq => ->.
Qed.

Lemma poly_cong a b c d r (K :=  omd b b / dist c d):
  ((norm (# b) ^+ 2 - ((#a)*m(#b)^T) 0 0) ^+ 2 +K * norm (# a - # b) ^+ 2) * r ^+ 2 +
    2%:R * (K * (((#a)*m(#b)^T) 0 0 - norm (# a) ^+ 2)
    + omd a b * (((#a)*m(#b)^T) 0 0 - norm (# b) ^+ 2)) *r
  + (omd a b ^+ 2 - K * omd a a) == 0
-> cong_v (#b) (extension (#a) (#b) r^-1) (#c) (#d).
Proof.
set E := (extension (#a) (#b) r^-1).
have : 2%:R == (1+1 ) :> R.
  by rewrite /GRing.natmul /=.
move=> /eqP rew2.
have :
((norm (# b) ^+ 2 - (# a *m (# b)^T) 0 0) ^+ 2 + K * norm (# a - # b) ^+ 2) *
r ^+ 2 +
2%:R *
(K * ((# a *m (# b)^T) 0 0 - norm (# a) ^+ 2) +
 omd a b * ((# a *m (# b)^T) 0 0 - norm (# b) ^+ 2)) * r +
(omd a b ^+ 2 - K * omd a a)
==
(omd_v (#b) E)^+2 - K * (1-norm(E)^+2).
  rewrite eq_sym /omd_v.
    have : norm(E)^+2 == norm(#a)^+2
                         + r^+2 * norm(#b-#a)^+2
                         + r * (2%:R *( (#a*m(#b)^T) 0 0-norm(#a)^+2)).
    rewrite /E /extension invrK norm_sqr mulmxDl.
    rewrite ![_*m(r*:_+_)^T]dotC !mulmxDl.
    rewrite -!scalemxAl ![_*m(r*:(_-_))^T]dotC -!scalemxAl scalerA.
    rewrite [(# b - # a) *m (# a)^T]mulmxDl mulNmx.
    rewrite !addrA mxE mxE mxE mxE -norm_sqr -expr2 mxE mxE.
    rewrite [(- (# a *m (# a)^T)) 0 0]mxE -norm_sqr addrC !addrA -addrA.
    rewrite -mulrDr  [(#b)*m(#a)^T]dotC.
    by rewrite /GRing.natmul /= mulrDl mul1r !addrA eqxx.
  move=> /eqP ->.
  rewrite {1}/E /extension invrK dotC [X in X *m _^T]addrC.
  rewrite mulmxDl -scalemxAl mulmxDl mxE [X in (1 -(_ + X))^+ 2]mxE.
  rewrite [(# b *m (# b)^T + - # a *m (# b)^T) 0 0]mxE.
  rewrite -norm_sqr opprD addrA -/(omd_v  _ _) -/(omd  _ _).
  rewrite mulNmx mxE.
  rewrite !opprD addrA addrA addrA [norm(#a)^+2]norm_sqr.
  rewrite -/(omd_v (#a) (#a)) -/(omd _ _) -norm_sqr.
  rewrite sqrrB exprMn [K *(_)]mulrBr [K *(_)]mulrBr.
  rewrite !opprD !addrA !opprK addrC.
  rewrite !addrA addrAC addrC [K * (r ^+ 2 *_)]mulrC.
  rewrite -[r ^+ 2 * _ * K]mulrA !addrA -addrA -mulrDr.
  rewrite [omd a b * (r * (_ - _))]mulrC.
  rewrite addrC !addrA -addrA -opprD.
  rewrite -[r*(norm(#b)^+2-_)]mul1r -!mulrDl -rew2.
  rewrite addrAC addrC !addrA -addrA.
  rewrite [K * (r * (2%:R * ((_-_^+ 2))))]mulrCA.
  rewrite [2%:R * ( r * _)]mulrCA [r * (2%:R  * _)]mulrA.
  rewrite -[r * 2%:R * _ * _]mulrA -[r * 2%:R * _ ]mulrA -mulrBr.
  rewrite [K * (2%:R * _)]mulrCA -mulrBr.
  rewrite addrAC -addrA -addrA addrC !addrA.
  rewrite -addrA [- (K * omd a a) + omd a b ^+ 2]addrC addrA.
  rewrite [r^+2 *_]mulrC  [norm (# b - # a) ^+ 2 * K]mulrC.
  have : norm(#b - #a)^+2 ==  norm(#a - #b)^+2.
    rewrite !norm_sqr !mulmxBl ![_*m(_+_)^T]dotC !mulmxBl.
    rewrite [#b*m(#a)^T]dotC !opprB !addrA.
    rewrite -addrA addrACA [#b*m(#b)^T+# a *m (# a)^T]addrC.
    by rewrite addrACA !addrA eqxx.
  move=> /eqP ->.
  rewrite [r * (2%:R * _)]mulrC -[-(_*omd a b)]mulNr.
  by rewrite  opprB [(_*omd a b)]mulrC eqxx.
move=> /eqP ->.
case:(norm(E)^+2 =P 1).
  move=> /eqP.
  rewrite sqr_norm_eq1 ger0_norm ?norm_ge0 // => /eqP normE_eq1.
  rewrite normE_eq1 [1^+2]expr2 mulr1 subrr mulr0 subr0 sqrf_eq0 => omdBE_eq0.
  exfalso.
  suffices: 0 < omd_v (#b) E
    by rewrite lt_def omdBE_eq0.
  rewrite /omd_v subr_gt0.
  apply le_lt_trans with (norm(#b) * norm(E)).
    by move: (cauchy_schwartz' (#b) E) => /andP[_ ->].
  by rewrite normE_eq1 mulr1 norm_point_lt1.
move=> /eqP normE_neq1.
rewrite subr_eq0 -divf_eq1;
last by rewrite mulf_neq0 ?subr_eq0 ?lt0r_neq0 /K
    ?mulr_gt0 ?invr_gt0 ?omd_gt0 ?dist_gt0 //
  eq_sym.
rewrite /cong_v  -[_==(_/_)]divf_eq1;
last by rewrite invfM ?mulf_neq0 ?invr_neq0 -/(omd _ _) ?omd_eq0.
rewrite norm_sqr -/(omd_v _ _) => H.
rewrite invf_div -/(dist_v _ _) -/(dist _ _).
rewrite -!/(omd _ _) -[dist c d]invrK -mulrA -invfM.
by rewrite [omd b b * _ /_]mulrAC -/K.
Qed.

Lemma seg_aux7 a b c d:
  (# a *m (# b)^T) 0 0 - (# c *m (# d)^T) 0 0
  = omd c d - omd a b.
Proof.
apply /eqP.
rewrite eq_sym /omd/omd_v opprB addrA addrC !addrA.
by rewrite [-1+1]addrC subrr sub0r addrC.
Qed.

Lemma seg_aux8 a b:
  norm(#a - #b)^+2
  = omd a b - omd a a + omd a b - omd b b.
Proof.
rewrite norm_sqr -seg_aux7 -addrA -seg_aux7 mulmxBl mxE.
rewrite [(-(_*m_) )0 0]mxE ![_*m(_-_)^T]dotC !mulmxBl.
rewrite mxE [X in _ + _ -X]mxE ![(-(_*m_) )0 0]mxE.
by rewrite opprB [#b *m (#a)^T]dotC.
Qed.

Lemma segment_construction_holds_aux1 a b c d :
  2%:R *
      ((omd b b/dist c d) * (((#a)*m(#b)^T) 0 0 - norm (# a) ^+ 2)
       + omd a b * (((#a)*m(#b)^T) 0 0 - norm (# b) ^+ 2))
  /2%:R / (omd a a * omd b b) =
  1/dist c d * (1 - omd a b/ omd a a) + omd a b/ omd a a - 1/dist a b.
Proof.
apply /eqP.
rewrite [2%:R*_/_]mulrAC divff ?lt0r_neq0 ?ltr0n //.
rewrite !mul1r !norm_sqr !seg_aux7 mulrBr.
rewrite [omd b b /dist c d]mulrC.
rewrite -![(dist c d)^-1 * _ * _]mulrA.
rewrite -mulrBr [omd a b * ( _ -_)]mulrBr.
rewrite mulrDl mulrBl -expr2 -[_^+2/_]invrK.
rewrite [(_^+2/_)^-1]invf_div /omd -/(dist_v _ _).
rewrite -!/(omd _ _) -/(dist _ _).
rewrite -mulrA mulrBl [omd b b * _]mulrC divff ?mulf_neq0 ?omd_eq0 //.
rewrite mulrAC [_ * omd b b]mulrC [(omd b b * _)^-1]invfM.
rewrite mulrA divff ?omd_eq0 // mul1r mulrC.
rewrite mulrA -[_*_/omd b b]mulrA divff ?omd_eq0 //.
by rewrite mulr1 addrA eqxx.
Qed.

Lemma segment_construction_holds_aux2 a b c d :
  ((norm (# b) ^+ 2 - ((#a)*m(#b)^T) 0 0) ^+ 2 +
   omd b b/dist c d* norm (# a - # b) ^+ 2)
  /(omd a a * omd b b) =
  1/dist a b - omd a b / omd a a + omd b b / omd a a
  - omd a b / omd a a +
  1/dist c d * (omd a b / omd a a - 1 + omd a b / omd a a - omd b b / omd a a).
Proof.
rewrite norm_sqr seg_aux7 sqrrB /GRing.natmul /= seg_aux8.
rewrite !mul1r [omd b b/_]mulrC -[_*_*_]mulrA.
rewrite [omd b b * _]mulrBr.
rewrite [omd b b * _]mulrDr.
rewrite [omd b b * _]mulrBr.
rewrite mulrDl mulrDl mulrBl -[_^+2/_]invrK invf_div.
rewrite /omd -/(dist_v _ _) -/(dist _ _) -!/(omd _ _).
rewrite mulrDl [omd a a * omd b b]mulrC.
rewrite [(omd b b*_)^-1]invfM expr2 mulrA mulrA.
rewrite -![_*_*(omd b b)^-1]mulrA divff ?omd_eq0 //.
rewrite !mulr1 -mulrA [_*(_/_)]mulrBl [_*(_/_)]mulrDl.
rewrite [_*(_/_)]mulrBl ![_*omd a _]mulrC !mulrA.
rewrite -![_*_*(omd b b)^-1]mulrA divff ?omd_eq0 //.
rewrite !mulr1 divff ?omd_eq0 //.
by rewrite opprD addrA [_ - _ -_ +_]addrAC.
Qed.

Lemma segment_construction_holds_aux3 a b c d :
  (omd a b ^+ 2 - omd b b/dist c d * omd a a)/(omd a a * omd b b)
  = 1/dist a b - 1 / dist c d.
Proof.
rewrite mulrBl -[_^+2/_]invrK invf_div.
rewrite /omd -/(dist_v _ _) -/(dist _ _) -!/(omd _ _).
rewrite [(omd a a *_)^-1]invfM mulrA -[_/_*_/_]mulrA.
rewrite divff ?omd_eq0 // !mul1r mulr1.
by rewrite mulrAC divff ?omd_eq0 // mul1r.
Qed.

Lemma segment_construction_holds_aux4 a b c d :
  ((dist c d)^-1 * (1 - omd a b / omd a a) + omd a b / omd a a -
 (dist a b)^-1)^+2
  =
  ((dist c d)^-1 * (omd a b/omd a a))^+2
  - (dist c d)^-1 * (omd a b/ omd a a)^+2
  - (dist c d)^-1 * (omd a b/ omd a a)^+2
  + (omd a b/omd a a)^+2
  - 2%:R/dist c d/dist a b * (1 - omd a b/omd a a)
  + 2%:R/dist c d * (omd a b/ omd a a)
  - 2%:R/dist a b * omd a b/ omd a a
  + dist c d ^-2 * (1 - 2%:R * omd a b/omd a a)
  + (dist a b)^-2.
Proof.
apply /eqP.
rewrite eq_sym.
rewrite exprMn exprVn ![_ + dist c d ^-2 * _]addrAC.
rewrite -mulrDr /GRing.natmul /= mulrDl mulrDl -{1}[1]mulr1.
rewrite opprD addrA -mulrA -mulrBr addrA.
rewrite [_-1* (omd a b /omd a a)]addrAC.
rewrite [(omd a b/omd a a)^+2]expr2 -mulrBl.
rewrite [_ + (1 * _)]addrC -[X in (1*_)+X]opprK.
rewrite -[- ((omd a b/omd a a -1) * _)]mulNr opprB.
rewrite [X in 1 * _ - X]mulrC -mulrBl -expr2 -exprVn.
rewrite ![_+ (1 + 1) / dist c d * (omd a b / omd a a)]addrAC.
rewrite mulrDl mulrDl mul1r addrA.
rewrite  -[_ + _ + (dist c d)^-1 * _ -_]addrA -mulrBr.
rewrite -{3}[omd a b / omd a a]mul1r -mulrBl.
rewrite [_+_+ (dist c d)^-1 * _]addrAC -[_+_+_-(dist c d)^-1 * _]addrA.
rewrite -mulrBr -{4}[omd a b / omd a a]mul1r -mulrBl.
rewrite -expr2 [((dist c d)^-1  + _)*_]mulrDl.
rewrite [((dist c d)^-1*_  + _)*_]mulrDl.
rewrite [(1+1)/_]mulrDl [(1/_+_)*_]mulrDl [(1/_*_+_)*_]mulrDl.
rewrite ![_/dist a b * _]mulrAC opprD addrA opprD addrA.
rewrite -[X in X - 1 * omd a b / omd a a / dist a b]addrA.
rewrite -opprD -mulrDl mul1r [_-omd a b / omd a a / dist a b]addrAC.
rewrite -[_-omd a b / omd a a / dist a b]addrA -opprD.
rewrite -mulrDl.
rewrite -exprMn.
rewrite eq_sym sqrrB sqrrD /GRing.natmul /=  opprD !addrA.
by rewrite exprVn !mulrA eqxx.
Qed.

Lemma segment_construction_holds_aux5 a b c d:
 ((dist a b)^-1 - omd a b / omd a a + omd b b / omd a a -
 omd a b / omd a a +
 (dist c d)^-1 *
 (omd a b / omd a a - 1 + omd a b / omd a a - omd b b / omd a a)) *
((dist a b)^-1 - (dist c d)^-1)
  =
  (dist a b)^-2
  + dist c d ^-2 * ( 1 - 2%:R * omd a b/omd a a)
  - 2%:R/dist a b * omd a b / omd a a
  + 2%:R/dist c d * (omd a b/ omd a a)
  - 2%:R/dist c d/dist a b * (1 - omd a b /omd a a)
  + (dist a b)^-1 * omd b b /omd a a
  - (dist c d)^-1 * ((dist a b) ^-1 * omd b b /omd a a)
  + (dist c d)^-2 * (omd b b/ omd a a)
  - (dist c d)^-1 * (omd b b/ omd a a).
Proof.
apply /eqP.
rewrite eq_sym /GRing.natmul /=.
rewrite ![(1+1)*_]mulrDl ![(1*_+_)*_]mulrDl ![(1*_*_+_)*_]mulrDl.
rewrite !opprD !mul1r !addrA.
rewrite -[_- (dist a b)^-1 * omd a b / omd a a +
(dist c d)^-1 * (omd a b / omd a a)]addrA.
rewrite [- ((dist a b)^-1 * omd a b / omd a a) +
 (dist c d)^-1 * (omd a b / omd a a)]addrC.
rewrite -[_*omd a b/omd a a]mulrA -mulrBl.
rewrite -[_ + (dist c d)^-1 * (omd a b / omd a a)]addrAC.
rewrite -[_ + (dist c d)^-1 * (omd a b / omd a a)]addrAC.
rewrite -[_ + (dist c d)^-1 * (omd a b / omd a a) - _]addrA.
rewrite -mulrBl.
rewrite ![_+ dist c d ^-2 *(omd b b / omd a a)]addrAC.
rewrite -[_+_+dist c d^-2 * _]addrA -mulrDr.
rewrite addrAC !addrA -[_-(dist c d)^-1*(omd b b/omd a a)]addrA.
rewrite -[_ * omd b b/ omd a a]mulrA -mulrBl.
rewrite -[((dist c d)^-1 - (dist a b)^-1)]opprB mulNr.
rewrite [_+((dist a b)^-1 - (dist c d)^-1) * _]addrAC.
rewrite [_+((dist a b)^-1 - (dist c d)^-1) * _]addrAC.
rewrite [_+((dist a b)^-1 - (dist c d)^-1) * _]addrAC.
rewrite [_+((dist a b)^-1 - (dist c d)^-1) * _]addrAC.
rewrite -[_-((dist a b)^-1 - (dist c d)^-1) * _]addrA.
rewrite -mulrBr.
rewrite -[X in _+_+X+_+_+_+_]mulrN.
rewrite -[_+((dist a b)^-1 - (dist c d)^-1) * _]addrA.
rewrite -mulrDr.
rewrite {1}[(dist c d)^-1 / dist a b * _]mulrDr mulr1.
rewrite opprD !addrA ![_-(dist c d)^-1 / dist a b]addrAC.
rewrite -exprVn expr2 -mulrBl.
rewrite ![_+((dist a b)^-1 - (dist c d)^-1)*_]addrAC.
rewrite -mulrDr !addrA.
rewrite [X in _-X==_]mulrA -addrA.
rewrite -![- ((dist c d)^-1 / dist a b * _)]mulrN.
rewrite -mulrDr -addrA -mulrDr !opprD !opprK !addrA.
rewrite -[dist c d ^- 2 *_]opprK -[-(dist c d ^- 2 *_)]mulrN.
rewrite !opprB opprD !addrA addrAC.
rewrite [(_-_)-1]addrAC [(_+_)-1]addrAC.
rewrite -exprVn expr2 [(dist c d)^-1 / dist a b]mulrC.
by rewrite -mulrA -mulrA -addrA -mulrBl -mulrDr mulrC.
Qed.

Lemma segment_construction_holds_aux6 a b:
  (dist a b)^-1 * omd b b / omd a a =
  (omd a b/omd a a)^+2.
Proof.
rewrite /dist/dist_v -!/(omd _ _) invf_div invfM.
rewrite mulrA -[X in X / omd a a]mulrA [_^-1*_]mulrC.
rewrite divff ?omd_eq0 // mulr1 -mulrA -invfM -expr2.
by rewrite -exprVn -exprMn.
Qed.

Lemma segment_construction_holds_aux a b c d :
  a!=b -> c!=d ->
  exists E' : 'rV[R]_n, bet (#a) (#b) E' /\ cong_v (#b) E' (#c) (#d).
Proof.
move=> ab_neq cd_neq.
set K := omd b b/dist c d.
set pab := ((#a)*m(#b)^T) 0 0.
set c1 := (norm(#b)^+2 - pab)^+2
        + K * norm(#a - #b)^+2.
set c2 := 2%:R * (
                    K * (pab - norm(#a)^+2)
                  + omd a b * (pab - norm(#b)^+2)
                  ).
set c3 := (omd a b)^+2 - K* omd a a.
set delta := c2^+2 - 4%:R * c1 * c3.
have: 0 < delta.
  suffices : 0 < delta / 4%:R / (omd a a * omd b b) ^+ 2.
    rewrite !pmulr_lgt0 ?invr_gt0 ?ltr0n //.
    by rewrite expr2 ?mulr_gt0 ?omd_gt0.
  have: delta/4%:R/(omd a a* omd b b)^+2 ==
  ((omd a b/omd a a)^+2 - omd b b/ omd a a) *
                ((1/dist c d)^+2 - 1/dist c d).
    rewrite /delta [X in X/_==_]mulrBl [4%:R * c1 * c3 /4%:R]mulrC.
    rewrite mulrA mulrA [_^-1*_]mulrC divff ?lt0r_neq0 ?ltr0n //.
    rewrite !mul1r [X in X==_]mulrBl.
    have: 4%:R == (2%:R)^+2 :> R
      by rewrite expr2 /GRing.natmul /= mulrDl !mul1r !addrA.
    move=> /eqP ->.
    rewrite -exprVn -exprMn -exprVn -exprMn.
    rewrite [X in _ - c1 *_ *X]expr2 mulrA.
    rewrite [c1 * c3 /_]mulrAC -[c1/_*_/_]mulrA.
    rewrite segment_construction_holds_aux1.
    rewrite segment_construction_holds_aux2.
    rewrite segment_construction_holds_aux3.
    rewrite !mul1r.
    rewrite segment_construction_holds_aux4.
    rewrite segment_construction_holds_aux5.
    rewrite !opprD !opprK !addrA.
    rewrite -[_+ dist a b ^- 2 - dist a b ^- 2]addrA subrr addr0.
    rewrite -[_ -dist c d ^- 2 * (1 - 2%:R * omd a b / omd a a)]addrA.
    rewrite subrr addr0.
    rewrite -[ _ + 2%:R / dist a b * omd a b / omd a a ]addrA.
    rewrite [_ + 2%:R / dist a b * omd a b / omd a a ]addrC.
    rewrite subrr addr0.
    rewrite -[ _ - 2%:R / dist c d * (omd a b / omd a a)]addrA subrr addr0.
    rewrite -[_+2%:R / dist c d / dist a b * (1 - omd a b / omd a a)]addrA.
    rewrite [_+2%:R / dist c d / dist a b * (1 - omd a b / omd a a)]addrC.
    rewrite subrr addr0.
    rewrite segment_construction_holds_aux6.
    rewrite -[_ - (omd a b/ omd a a)^+2]addrA subrr addr0.
    rewrite exprMn /GRing.natmul /=.
    rewrite -[_ + (dist c d)^-1 * (omd a b / omd a a) ^+ 2]addrA.
    rewrite [_ + (dist c d)^-1 * (omd a b / omd a a) ^+ 2]addrC.
    rewrite subrr addr0 -mulrBl addrAC -addrA -mulrBl exprVn.
    rewrite -[(dist c d)^-1 - dist c d ^- 2]opprB.
    by rewrite mulNr -mulrBr mulrC eqxx.
  move=> /eqP ->.
  rewrite mulr_gt0 // exprMn !expr2 mulrA -mulrBl.
  rewrite -expr2 mulr_gt0 ?invr_gt0 ?omd_gt0 //.
  rewrite -[_/omd a a]mulr1 -(@divff R (omd b b)) ?omd_eq0 //.
  rewrite mulrA mulrAC -[X in _ -X]mul1r -mulrBl.
  rewrite mulr_gt0 ?omd_gt0 // -mulrA -invfM.
  rewrite subr_gt0 -invf_lt1;
  last by rewrite expr2 invfM ?mulr_gt0 ?invr_gt0 ?omd_gt0.
  by rewrite invf_div -/(dist_v _ _) -/(dist _ _) dist_lt1.
  rewrite !mul1r mulr_gt0 ?invr_gt0 ?dist_gt0 //.
  by rewrite subr_gt0 invf_gt1 ?dist_gt0 ?dist_lt1.
move => delta_gt0.
set r1 := (- c2 - Num.sqrt delta) / 2%:R / c1.
set r2 := (- c2 + Num.sqrt delta) / 2%:R / c1.
set E1' := extension (#a) (#b) r1^-1.
set E2' := extension (#a) (#b) r2^-1.
have: cong_v (#b) E1' (#c) (#d) /\ cong_v (#b) E2' (#c) (#d).
  move: (@roots_poly2 c1 c2 c3) => H.
  destruct H as [Hr1 Hr2].
    rewrite lt0r_neq0 // /c1 addrC addr_ge_gt0 ?sqr_ge0//.
    by rewrite /K ?mulr_gt0 ?invr_gt0 ?dist_gt0 ?omd_gt0 ?norm_point_subr_gt0 //;
    rewrite eq_sym ab_neq.
    by rewrite -/delta ltW.
  by rewrite (@poly_cong a b c d r1)  ?(@poly_cong a b c d r2).
have: E1' != E2'.
  rewrite /E1' /E2' /extension -subr_eq0.
  rewrite addrAC opprD !addrA -addrA [-#a +#a]addrC subrr addr0.
  rewrite -scalerBl scaler_eq0 Bool.negb_orb !subr_eq0.
  rewrite [#b == #a]eq_sym ab_neq andbT.
  rewrite /r1/r2 !invf_div.
  apply /negPf.
  rewrite -subr_eq0 -!mulrBl.
  apply /eqP /eqP.
  rewrite ?mulf_neq0 ?invr_neq0 ?[2%:R!=0]lt0r_neq0 ?ltr0n //.
  case: (c2 =P 0).
    move->.
    rewrite oppr0 !add0r subr_eq0 eq_sym -subr_eq0.
    by rewrite opprK lt0r_neq0 ?addr_gt0 ?sqrtr_gt0.
  move=> /eqP c2_neq0.
  rewrite subr_eq0.
  move: (lt_total c2_neq0).
  move=>/orP[c2_lt0|c2_gt0].
    rewrite ?invr_eq0 ?lt0r_neq0 ?addr_gt0 ?oppr_gt0 ?sqrtr_gt0 //.
    rewrite -subr_eq0 opprD opprK addrCA !addrA subrr add0r -opprD.
    by rewrite oppr_eq0 lt0r_neq0 ?addr_gt0 ?sqrtr_gt0.
  rewrite eq_sym -opprD  ?invr_eq0 ?oppr_eq0 ?lt0r_neq0 ?addr_gt0 ?oppr_gt0 ?sqrtr_gt0 //.
  rewrite -subr_eq0 opprK addrCA !addrA subrr add0r.
  by rewrite lt0r_neq0 ?addr_gt0 ?sqrtr_gt0.
  rewrite lt0r_neq0 // /c1 addrC addr_ge_gt0 ?sqr_ge0//.
  by rewrite /K ?mulr_gt0 ?invr_gt0  ?dist_gt0 ?omd_gt0 ?norm_point_subr_gt0 //;
  rewrite eq_sym ab_neq.
move => /eqP E1'E2'_neq [cong1 cong2].
suffices: bet (#a) (#b) E1' \/ bet (#a) (#b) E2'.
  move => [? | ?] ; [by exists E1' | by exists E2'].
apply /orP.
have:  bet (# a) (# b) E1' \/ bet (# b) E1' (# a) \/ bet E1' (# a) (# b)
  by apply (@extension_col R n (#a) (#b) E1' r1^-1);
  rewrite /E1'.
move=>[-> //|one_side_E1'].
have:  bet (# a) (# b) E2' \/ bet (# b) E2' (# a) \/ bet E2' (# a) (# b)
  by apply (@extension_col R n (#a) (#b) E2' r2^-1);
  rewrite /E2'.
move=>[-> |one_side_E2'].
  by rewrite orbT.
exfalso.
(* E1 and E2 are equal because they both are:
    on the line (AB)
    at the same side of B
    at the same distance of B *)
apply E1'E2'_neq; apply /eqP.
set eps := ((1-norm(#b))/2%:R/norm(#b-#a)).
have: 0 < eps
  by rewrite /eps ?mulr_gt0 ?subr_gt0 ?invr_gt0 ?norm_point_lt1
    ?ltr0n ?norm_point_subr_gt0.
move=> eps_gt0.
set f' := extension (#a) (#b) ((eps+1)^-1).
  (* f will help us proof that E1 = E2 *)
have: (f' *m (f')^T)0 0 <1.
  suffices: norm(f') < 1.
    move=> ?.
    by rewrite -norm_sqr expr2 mulr_ilt1 ?norm_ge0.
  rewrite /f'/extension invrK scalerDl scale1r addrA.
  rewrite -addrA [-#a+#a]addrC subrr addr0.
  apply le_lt_trans with (norm(eps*:(#b-#a)) + norm(#b)).
    exact: triangle_ineq.
  rewrite /norm -scalemxAl dotC -scalemxAl scalerA mxE.
  rewrite sqrtrM; last by rewrite mulr_ge0 ?ltW.
  rewrite sqrtr_sqr ger0_norm ?ltW // /eps -/(norm _).
  rewrite -mulrA [(norm (_))^-1 * norm (_)]mulrC divff;
    last by rewrite lt0r_neq0 ?norm_point_subr_gt0.
  rewrite mulr1 -/(norm _) mulrBl -addrA [X in _ + (X)]addrC.
  rewrite -{1}[norm(#b)]mulr1 -mulrBr one_sub_half -mulrDl divf_lt1 ?ltr0n //.
  rewrite /GRing.natmul /= -subr_lt0 opprD addrAC addrA subrr.
  by rewrite sub0r addrC subr_lt0 norm_point_lt1.
move=> f'_in_disk.
set f := (exist (fun p => (p *m p^T) 0 0 < 1) f' f'_in_disk).
have: bet' f b a
  by rewrite /bet' bet_sym extension_bet ?invr_gt0 ?invf_lt1 ?addr_gt0 //
   -subr_gt0 -addrA subrr addr0.
move=> bet_fba.
set E1 := (exist (fun p => (p *m p^T) 0 0 < 1) E1' (E_in_disk_aux cong1)).
set E2 := (exist (fun p => (p *m p^T) 0 0 < 1) E2' (E_in_disk_aux cong2)).
suffices: (E1 == E2)
  by rewrite point_vector_eq /=.
apply one_side_cong'_eq with f b.
move: one_side_E1' => [|bet_E1'ab].
    by apply bet_inner_transitivity.
  rewrite bet_sym in bet_E1'ab.
  apply bet_outer_transitivity' with (#a)=> //.
  by rewrite eq_sym -point_vector_neq.
move: one_side_E2'=> [|bet_E2'ab].
    by apply bet_inner_transitivity.
  rewrite bet_sym in bet_E2'ab.
  apply bet_outer_transitivity' with (#a)=>//.
  by rewrite eq_sym -point_vector_neq.
exact: (@cong_inner_transitivity_vector (# b) E1' (# b) E2' (#c) (#d)).
rewrite point_vector_neq.
rewrite /=/f'/extension invrK scalerDl scale1r.
rewrite !addrA -addrA [-#a+#a]addrC subrr addr0 -subr_eq0.
rewrite -addrA subrr addr0 scaler_eq0 subr_eq0 [#b==#a]eq_sym.
by rewrite Bool.negb_orb lt0r_neq0.
Qed.

Lemma segment_construction_holds a b c d :
  exists x : Point, bet' a b x /\ cong' b x c d.
Proof.
rewrite /bet' /cong'.
apply E_in_disk.
case: (c =P d).
  move->.
  exists (#b).
  by rewrite bet_axx /cong_v -!expr2 -!/(omd _ _)
    !divff ?expr2 ?mulf_neq0 ?omd_eq0 .
move=> /eqP cd_neq.
case: (a =P b).
  case: (c =P b).
    move=> <- ->.
    exists (#d).
    by rewrite bet_xxa /cong_v.
  move => /eqP cb_neq ->.
  move: (@segment_construction_holds_aux c b c d).
  rewrite cd_neq cb_neq.
  move => H.
  destruct H => //.
  destruct H as  [_ H2].
  exists x.
  by rewrite bet_xxa H2.
move=> /eqP ab_neq.
apply segment_construction_holds_aux => //.
Qed.

Lemma cong_pseudo_reflexivity_vector (v w : 'rV[R]_n) : cong_v v w w v.
Proof. by rewrite /cong_v omd_v_reflexivity [omd_v v v * omd_v w w]mulrC. Qed.

Lemma inner_pasch_vector (a b c p q : 'rV[R]_n) :
  bet a p c -> bet b q c ->
  a <> p -> p <> c -> b <> q -> q <> c ->
  ~ ~ (~ bet a b c /\ ~ bet b c a /\ ~ bet c a b) ->
  exists x : 'rV[R]_n, bet p x b /\ bet q x a.
Proof.
move=> Hb1 Hb2 ? ? ? ?; move: Hb1 Hb2; rewrite 2?bet_betS //.
move => Hb1 Hb2 HNC; destruct (inner_pasch' Hb1 Hb2) as [x [Hb3 Hb4]];
  last by exists x; rewrite /bet Hb3 Hb4 !orbT.
by move => [|[|]] Hb3; apply HNC; rewrite Hb3; intuition.
Qed.

Lemma inner_pasch_holds a b c p q :
  bet' a p c -> bet' b q c ->
  a <> p -> p <> c -> b <> q -> q <> c ->
  ~ ~ (~ bet' a b c /\ ~ bet' b c a /\ ~ bet' c a b) ->
  exists x : Point, bet' p x b /\ bet' q x a.
Proof.
rewrite /bet' => Hb1 Hb2 /eqP ? /eqP ? /eqP ? /eqP ? Hnc.
destruct (inner_pasch_vector Hb1 Hb2) as [x [Hb3 Hb4]];
[..|by move: Hnc; rewrite /independence.Col|] => //; [by apply /eqP..|].
by assert (Hx := Hb3); apply bet_in_disk in Hx;
[exists (exist (fun p => (p *m p^T) 0 0 < 1) x Hx)|by destruct p|by destruct b].
Qed.

Lemma bet_symmetry_vector (a b c : 'rV[R]_n) : bet a b c -> bet c b a.
Proof. by rewrite bet_sym. Qed.

Lemma bet_inner_transitivity_vector (a b c d : 'rV[R]_n) :
  bet a b d -> bet b c d -> bet a b c.
Proof. exact: bet_inner_transitivity. Qed.

Lemma euclid_aux: (exists a b c d t,
     bet' a d t /\ bet' b d c /\
     b <> d /\ d <> c /\
     ~ (bet' a b c \/ bet' b c a \/ bet' c a b) /\
     (forall (x : Point), bet' a b x ->
     (forall y' : 'rV[R]_n, bet (# a) (# c) y' ->
     bet (# x) (# t) y' -> (y' *m y'^T) 0 0 >= 1))) ->
     ~ (forall a b c d t,
        bet' a d t -> bet' b d c ->
        b <> d -> d <> c ->
        ~ (bet' a b c \/ bet' b c a \/ bet' c a b) ->
        exists (x y : Point), bet' a b x /\ bet' a c y /\ bet' x t y).
Proof.
move=> [a [b [c [d [t [bADT [bBDC [bd_neq [dc_neq [ncol H]]]]]]]]]] HF.
destruct  (HF a b c d t) as [x [y [bABX [bACY bXTY]]]] => //; clear HF.
assert (Y_out_of_disk:= H x bABX (#y) bACY bXTY); destruct y as [yC Y_in_disk].
by move:(le_lt_asym 1 ((yC *m yC^T) 0 0)); rewrite Y_in_disk Y_out_of_disk.
Qed.

Definition a' : 'rV[R]_2 := row2 0 0.

Definition b' : 'rV[R]_2 := row2 0 (1/(1+1)).

Definition c' : 'rV[R]_2 := row2 (1/(1+1)) 0.

Definition a'nD := to_nD n a'.

Definition b'nD := to_nD n b'.

Definition c'nD := to_nD n c'.

Lemma a'_in_unit_disk : (a' *m a'^T) 0 0 < 1.
Proof. by rewrite mxE !big_ord_recr /= big_ord0 !mxE /= mulr0 !addr0 ltr01. Qed.

Lemma a'nD_in_unit_disk : (a'nD *m a'nD^T) 0 0 < 1.
Proof.
by rewrite /a'nD /to_nD tr_row_mx mul_row_col mul0mx addr0 a'_in_unit_disk.
Qed.

Lemma b'_in_unit_disk : (b' *m b'^T) 0 0 < 1.
Proof.
rewrite mxE !big_ord_recr /= big_ord0 !mxE /= mulr0 addr0 add0r.
by apply mulr_ilt1 ; rewrite ?one_half_ge0 ?one_half_lt1.
Qed.

Lemma b'nD_in_unit_disk : (b'nD *m b'nD^T) 0 0 < 1.
Proof.
by rewrite /b'nD /to_nD tr_row_mx mul_row_col mul0mx addr0 b'_in_unit_disk.
Qed.

Lemma c'_in_unit_disk : (c' *m c'^T) 0 0 < 1.
Proof.
rewrite mxE !big_ord_recr /= big_ord0 !mxE /= mulr0 addr0 add0r.
by apply mulr_ilt1 ; rewrite ?one_half_ge0 ?one_half_lt1.
Qed.

Lemma c'nD_in_unit_disk : (c'nD *m c'nD^T) 0 0 < 1.
Proof.
by rewrite /c'nD /to_nD tr_row_mx mul_row_col mul0mx addr0 c'_in_unit_disk.
Qed.

Lemma c'_norm : (c' *m c'^T) 0 0 = 1/(1+1+1+1).
Proof.
by rewrite mxE !big_ord_recr /= big_ord0 !mxE mulr0 addrC !add0r quarter.
Qed.

Definition to_2D (p : 'rV[R]_(2 + n)) : 'rV[R]_2 := row2 (p 0 0) (p 0 1).

Lemma bet_2D_extension_2D (a b : 'rV[R]_2) (c :'rV[R]_(2 + n)) :
  (to_nD n a) != (to_nD n b) -> bet (to_nD n a) (to_nD n b) c ->
  c = to_nD n (to_2D c).
Proof.
rewrite /bet /betE; case: (to_nD n a =P to_nD n b) => // _ _ Hb.
apply /rowP => i; rewrite /to_nD /row_mx mxE; case: (splitP i) => [i0|i1].
  rewrite /to_2D /row2 !mxE /=; case: i0 => [] [|[|//]] /= iP1 iP2.
    by rewrite (@ord_inj _ i 0).
  by rewrite (@ord_inj _ i 1).
move=> iP; move: Hb; have -> : i = rshift 2 i1 :> 'I_(2+n) by apply val_inj.
case: (to_nD n b =P c) => [<- _|/= _]; rewrite ?row_mxEr //.
move=> /andP[] E /andP[L G]; move/eqP/rowP/(_ (rshift 2 i1)): E; rewrite /to_nD.
rewrite mxE row_mxEr mxE opp_row_mx row_mxEr 2?mxE subr0 2?mxE row_mxEr !mxE.
rewrite subr0; move=> /eqP; rewrite eq_sym mulf_eq0 => /orP[/eqP HF|/eqP-> //].
by move: L; rewrite HF ltxx.
Qed.

Lemma unit_disk_nD_2D (p : 'rV[R]_2) :
  ((to_nD n p) *m (to_nD n p)^T) 0 0 = (p *m p^T) 0 0.
Proof. by rewrite /to_nD tr_row_mx mul_row_col mul0mx addr0. Qed.

Definition a_nD : (Point' (2+n)) :=
  exist (fun p => (p *m p^T) 0 0 < 1) a'nD a'nD_in_unit_disk.

Definition b_nD : (Point' (2+n)) :=
  exist (fun p => (p *m p^T) 0 0 < 1) b'nD b'nD_in_unit_disk.

Definition c_nD : (Point' (2+n)) :=
  exist (fun p => (p *m p^T) 0 0 < 1) c'nD c'nD_in_unit_disk.

Lemma a'_eq0 : a' = 0.
Proof. by rewrite /a'; apply /eqP; rewrite vector2_eq !mxE /= eqxx. Qed.

Lemma a'nD_eq0 : a'nD = 0.
Proof. by rewrite /a'nD /to_nD a'_eq0 row_mx_const. Qed.

Lemma b'_neq0 : b' != 0.
Proof. by rewrite /b' vector2_eq !mxE eqxx /= mul1r invr_neq0 ?add11_neq0. Qed.

Lemma b'nD_neq0 : b'nD != 0.
Proof. by rewrite /b'nD /to_nD row_mx_eq0 negb_and b'_neq0. Qed.

Lemma b'c'_neq : b' == c' = false.
Proof.
rewrite row2_eq Bool.andb_false_intro2 // mul1r.
by rewrite -Bool.negb_true_iff invr_neq0 ?add11_neq0.
Qed.

Lemma bc_neq_nD : b'nD == c'nD = false.
Proof.
by rewrite -subr_eq0 opp_row_mx add_row_mx row_mx_eq0 subr_eq0 b'c'_neq.
Qed.

Lemma betR_abc : betR a'nD b'nD c'nD = 0.
Proof.
rewrite a'nD_eq0 /b /c /betR /ratio; case: pickP => /= [x|all_v_neq0 //].
rewrite !subr0 /b'nD /c'nD /to_nD /row_mx !mxE; case: (split x)=> [x0|x1];
by rewrite ?mxE ?eqxx //; case: x0 => [] [|[|//]] p /=; rewrite ?mul0r ?eqxx.
Qed.

Lemma betR_bca : betR b'nD c'nD a'nD = 1.
Proof.
rewrite /b'nD /c'nD a'nD_eq0 /betR /ratio add0r.
case: pickP => /= [x|/all_v_neq0 H];
last by exfalso; apply H; rewrite oppr_eq0 b'nD_neq0.
rewrite /to_nD /row_mx !mxE; case: (split x)=> [x0|x1]; rewrite ?mxE ?oppr_eq0;
rewrite ?eqxx //; case: x0 => [] [|[|//]] p /=; rewrite ?eqxx //.
by rewrite sub0r divff ?eqxx // oppr_eq0 mul1r invr_neq0 ?add11_neq0.
Qed.

Lemma betR_cab : betR c'nD a'nD b'nD = 0 \/ betR c'nD a'nD b'nD = 1.
Proof.
rewrite /c'nD a'nD_eq0 /b'nD /betR /ratio add0r.
case: pickP => /= [x|/all_v_neq0 H];
last by exfalso; apply H; rewrite subr_eq0 bc_neq_nD.
rewrite /to_nD /row_mx !mxE; case: (split x)=> [x0|x1]; rewrite ?mxE ?subrr;
rewrite ?eqxx //; case: x0 => [] [|[|//]] p /=; rewrite ?mulNr ?mul0r ?oppr0;
rewrite ?add0r -?mulNr ?divff; [tauto| |tauto].
by rewrite mulNr oppr_eq0 mul1r invr_neq0 ?add11_neq0.
Qed.

Lemma nbet_abc : bet a'nD b'nD c'nD = false.
Proof.
rewrite /a'nD /b'nD /c'nD /bet /betE /betS betR_abc ltxx andbF /a' /b' /c'.
by rewrite !row2_eq_nD eqxx one_half_neq0 eq_sym one_half_neq0.
Qed.

Lemma nbet_bca : bet b'nD c'nD a'nD = false.
Proof.
rewrite /a'nD /b'nD /c'nD /bet /betE /betS betR_bca ltxx !andbF /a' /b' /c'.
by rewrite !row2_eq_nD eqxx one_half_neq0 eq_sym one_half_neq0.
Qed.

Lemma nbet_cab : bet c'nD a'nD b'nD = false.
Proof.
rewrite /a'nD /b'nD /c'nD /bet /betS; elim betR_cab => ->; rewrite ltxx !andbF;
by rewrite /betE !row2_eq_nD eqxx one_half_neq0 eq_sym one_half_neq0.
Qed.

Lemma three_non_collinear_points_vector :
  ~ (bet a'nD b'nD c'nD \/ bet b'nD c'nD a'nD \/ bet c'nD a'nD b'nD).
Proof. rewrite nbet_abc nbet_cab nbet_bca; intuition. Qed.

End rcfTarski.

Section rcfTarski2D.

Variable R : rcfType.
Notation "#" := proj1_sig.

Definition a : (Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) (@a' R) (@a'_in_unit_disk R).

Definition b : (Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) (@b' R) (@b'_in_unit_disk R).

Definition c : (Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) (@c' R) (@c'_in_unit_disk R).

Lemma upper_dim_aux_2 (a p q : @Point R 2)   (k := Num.sqrt(omd p p/ omd q q)) :
  cong' a p a q -> (omd a p /omd a q == k).
Proof.
rewrite /cong'/cong_v=> cong_apaq .
have: omd a p ^+ 2 / (omd a a * omd p p) * (omd a a * omd p p)/omd a q ^+ 2 ==
omd a q ^+ 2 / (omd a a * omd q q) * (omd a a * omd p p)/omd a q ^+ 2
by rewrite -subr_eq0 -mulrBl -mulrBl !mulf_eq0 !omd_eq0 invr_eq0 sqrf_eq0
  omd_eq0 !orbF subr_eq0 cong_apaq.
set t_ap := omd a p. set t_aq := omd a q. set t_aa := omd a a.
set t_pp := omd p p. set t_qq := omd q q.
rewrite -[ (_ *_) *(_* _)]mulrA [((t_aa * t_pp)^-1*(t_aa*t_pp))]mulrC.
rewrite divff ?mulf_neq0 ?omd_eq0//.
rewrite eq_sym mulrC !mulrA expr2.
rewrite -[(t_aq * t_aq)^-1 * t_aq * t_aq ]mulrC mulrA.
rewrite -[t_aq/(t_aq*t_aq)*t_aq]mulrC mulrA divff ?mulf_neq0 ?omd_eq0 //.
rewrite mul1r invfM mulrC !mulrA mulrAC mulrC !mulrA mulrAC.
rewrite -!mulrA divff ?omd_eq0 //.
rewrite mulr1 eq_sym !mulrA mulr1 -!expr2 /k.
rewrite -eqr_sqrt ?mulr_ge0 ?invr_ge0 ?expr2 ?mulr_ge0 ?omd_ge0 //.
rewrite [X in _ == Num.sqrt(X)]mulrC => /eqP <-.
rewrite sqrtrM ?mulr_ge0 ?omd_ge0 //.
rewrite -!expr2 -exprVn !sqrtr_sqr !ger0_norm ?omd_ge0 //.
by rewrite invr_ge0 omd_ge0.
Qed.

Lemma upper_dim_aux (a p q : @Point R 2)
  (k := Num.sqrt(omd p p/ omd q q))
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

Definition d' : 'rV[R]_2 := row2 (1/(1+1+1+1)) (1/(1+1+1+1)).

Definition t' : 'rV[R]_2 := row2 (1/(1+1)) (1/(1+1)).

Lemma d'_in_unit_disk : (d' *m d'^T) 0 0 < 1.
Proof.
rewrite /d' !mxE !big_ord_recr /= big_ord0 !mxE /= add0r.
apply lt_trans with ((1/(1+1))*(1/(1+1))+(1/(1+1))*(1/(1+1))).
apply ltr_add ; exact: one_eighth_lt_one_quarter.
apply lt_le_trans with ((1/(1+1))+(1/(1+1))).
apply ltr_add ; exact: one_quarter_lt_one_half.
rewrite -mulrDl divff ?add11_neq0 //.
Qed.

Lemma t'_in_unit_disk : (t' *m t'^T) 0 0 < 1.
Proof.
rewrite /t' !mxE !big_ord_recr /= big_ord0 !mxE /= add0r.
apply lt_le_trans with ((1/(1+1))+(1/(1+1))).
apply ltr_add ; exact: one_quarter_lt_one_half.
rewrite -mulrDl divff ?add11_neq0 //.
Qed.

Definition d : (@Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) d' d'_in_unit_disk.

Definition t : (@Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) t' t'_in_unit_disk.

Lemma bet_adt: bet' a d t.
Proof.
rewrite /bet' /bet /betS /a /d /t /=.
have: betR (@a' R) d' t' = 1/(1+1).
rewrite /betR /ratio a'_eq0 /= subr0.
case: pickP => /= [x|/all_v_neq0 H].
 rewrite /t' /d' !mxE /=; case: x => [] [|[| //]] //= p;
  rewrite -quarter subr0 -!mulrA !mul1r divff ?mulr1 ?invr_eq0 ?add11_neq0 ?eqxx //.
by exfalso; apply H; rewrite  -a'_eq0 /a' /t' row2_eq one_half_neq0.
move ->.
rewrite one_half_lt1 one_half_gt0  /= /a' /d' /t' vector2_eq.
rewrite !mxE /= !subr0 quarter eqxx.
by rewrite orbT.
Qed.

Lemma bet_bdc: bet' b d c.
Proof.
rewrite /bet' /bet /betS /b /c /d.
have: betR (@b' R) d' (@c' R) == 1/(1+1).
rewrite /betR /ratio /=.
case: pickP => /= [x|/all_v_neq0 H].
  rewrite /b' /c' /d' !mxE /=; case: x => [] [|[| //]] //= p;
  rewrite -quarter ?subr0 ?sub0r.
  rewrite !mul1r -!mulrA divff ?mulr1 ?invr_eq0 add11_neq0 //.
  rewrite invrN mulrN mulrBl divff; last by rewrite mul1r invr_neq0 ?add11_neq0.
  rewrite opprB.
  rewrite mul1r mulrAC divff; last by rewrite invr_neq0 ?add11_neq0.
  rewrite subr_eq.
  rewrite -[X in _==X+_]mul1r.
  rewrite addf_divrr ?divff ?eqxx ?add11_neq0  //.
by exfalso; apply H; rewrite  /c' /b' subr_eq0 row2_eq one_half_neq0 eq_sym one_half_neq0.
move /eqP ->.
rewrite one_half_lt1 one_half_gt0  /= /b' /c' /d' vector2_eq.
rewrite !mxE /= !subr0 !sub0r quarter eqxx.
rewrite -quarter -subr_eq0 mulrN opprK addrC !addrA.
rewrite -mulrDl addf_div ?add11_neq0 //.
rewrite !mul1r [((1 + 1) * (1 + 1))]mulrDl !mul1r.
rewrite divff; last by rewrite lt0r_neq0 ?addr_gt0 ?ltr01.
by rewrite mul1r subrr eqxx orbT.
Qed.

Lemma  betR_akb (a b: 'rV[R]_2) (k : R) : 0 < k -> k < 1 -> b!=a ->
  betR a (k*:(b-a) + a) b = k.
Proof.
move=> kgt0 klt1 bneqa.
rewrite /betR /ratio.
case: pickP => /= [x|/all_v_neq0 H].
  rewrite -addrA subrr addr0.
  rewrite !mxE /=.
  move=> ba_neq0.
  by rewrite -mulrA divff ?mulr1.
by exfalso; apply H; rewrite subr_eq0 bneqa.
Qed.

Lemma betR_abk (a b: 'rV[R]_2) (k : R) :  0 < k -> k < 1 -> b!=a ->
  betR a b ((1/k)*:(b-a)+a) = k.
Proof.
move => kgt0 klt1 bneqa.
set c := ((1/k) *: (b - a) + a).
have: (b = k*:(c-a)+a).
  rewrite /c -addrA subrr addr0 scalerA mul1r.
  rewrite divff ?lt0r ?lt0r_neq0 ?kgt0 //.
  by rewrite scale1r addrAC -addrA subrr addr0.
move->.
apply betR_akb; rewrite //.
rewrite /c -subr_eq0 -addrA subrr addr0 scalemx_eq0.
rewrite subr_eq0.
move/negPf: bneqa ->.
rewrite mul1r invr_eq0.
move:kgt0.
rewrite lt0r.
by move=> /andP[/negPf -> _].
Qed.

Lemma euclid_fails_aux (a b c : 'rV[R]_2) :
  bet a b c -> bet a (c + a - b) c.
Proof.
move=> bet_abc.
rewrite (bet_trans _ _ _(-c)) subrr.
rewrite [X in bet _ X _]addrC !addrA -[-c+c]addrC subrr add0r.
rewrite bet_opp !opprB (bet_trans _ _ _ a).
rewrite -!addrA [-a+a]addrC subrr !addr0 addrC subr0.
by rewrite bet_sym.
Qed.

Global Instance Rcf_to_GI_PED :
  Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality.
Proof.
exact
(Build_Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality
  'rV_2 (@bet R 2) (@cong R 2) (@point_equality_decidability R 2)
  (@cong_pseudo_reflexivity R 2) (@cong_inner_transitivity R 2)
  (@cong_identity R 2)
  (@segment_construction R 2) (@five_segment R 2)
  (@bet_symmetry R 2) (@bet_inner_transitivity R 2) (@inner_pasch R 2)
  (@a'nD R 0) (@b'nD R 0) (@c'nD R 0)
  (@three_non_collinear_points_vector R 0)).
Defined.

Global Instance Rcf_to_GI2D : Gupta_inspired_variant_of_Tarski_2D Rcf_to_GI_PED.
Proof. split; exact (@upper_dim R). Defined.

Lemma bet_intersect (a b c d  e x y  : 'rV[R]_2) :
  ~(bet c e d \/ bet e d c \/ bet d c e) ->
  a != b -> c != d -> bet a e c ->
  bet a b x -> bet c d x ->
  bet a b y -> bet c d y ->
  x = y.
Proof.
move=> ncol /eqP ab_neq /eqP cd_neq bet_aec bet_abx bet_cdx bet_aby bet_cdy.
apply l6_21 with a b c d; try apply Ch03_bet.bet_col ; auto.
move=> col ; apply ncol.
apply col_transitivity_1 with x; Col.
move=> cx_eq; treat_equalities.
have: c=d by exact (between_identity _ _ bet_cdx). by [].
apply col_transitivity_1 with a; Col.
move=> ca_eq; treat_equalities.
have: c=e by exact (between_identity _ _ bet_aec).
by move=> ce_eq; treat_equalities; apply ncol; left; rewrite bet_xxa.
apply col_permutation_4; apply col_transitivity_1 with b; Col.
Qed.

Lemma bet_abx_x00_eq0 (x' :'rV[R]_2):
  bet (@a' R) (@b' R) x' -> x' 0 0 = 0.
Proof.
rewrite /bet=> /orP[/betEP[[_ <-]|/eqP ab_eq |<- ] |/betSP[P1 k_gt0 k_lt1]].
by rewrite /b'!mxE /=.
exfalso; move:ab_eq.
by rewrite /a' /b' row2_eq [X in _ && X]eq_sym one_half_neq0 andbF.
by rewrite /b'!mxE /=.
move/eqP:P1.
rewrite a'_eq0 !subr0 -subr_eq0 vector2_eq0 !mxE /= add0r oppr_eq0.
move: k_gt0.
rewrite lt0r mulf_eq0 a'_eq0=>/andP[/negPf -> _].
by rewrite orFb=>/andP[/eqP -> _].
Qed.

Lemma bet_abx_x01_lt1 (x: @Point R 2):
    bet (@a' R) (@b' R) (#x) -> (#x) 0 1 < 1.
Proof.
move=> bet_abx.
have: ((#x) *m (#x)^T) 0 0 < 1 by destruct x.
have: ((0<= (#x) 0 1) || ((#x) 0 1<= 0)) by apply: le_total .
move=>/orP[x01_ge0| x01_le0 _].
rewrite !mxE !big_ord_recr !big_ord0 !mxE /= add0r.
suffices:  (#x) 0 0 * (#x) 0 0 + (#x) 0 1 * (#x) 0 1 =
  # x 0 (widen_ord (leqnSn 1) ord_max) * # x 0 (widen_ord (leqnSn 1) ord_max) +
# x 0 ord_max * # x 0 ord_max.
move=><-.
by rewrite bet_abx_x00_eq0 // mulr0 add0r -expr2 expr_lt1.
by congr ((#x) 0 _ * (#x) 0 _ + (#x) 0 _ * (#x) 0 _); apply val_inj.
apply le_lt_trans with 0;
rewrite ?ltr01 //.
Qed.

Lemma bet_abx_x01_gt (x': 'rV[R]_2):
  bet (@a' R) (@b' R) x'->  x' != (@b' R) -> 1 / (1+1) < x' 0 1 .
Proof.
rewrite /bet=> /orP[/betEP[[_ <-]| /eqP ab_eq |<- ] |/betSP[]].
by rewrite eqxx.
exfalso; move:ab_eq.
by rewrite /a' /b' row2_eq [X in _ && X]eq_sym one_half_neq0 andbF.
by rewrite eqxx.
set k := betR (@a' R) (@b' R) x'.
rewrite a'_eq0 !subr0.
move=> b_kx k_gt0 k_lt1.
have: k^-1 *: (@b' R) = x'.
rewrite b_kx scalerA mulrC divff.
by rewrite scale1r.
move:k_gt0.
by rewrite lt0r=>/andP[? ?].
move=><- _.
rewrite !mxE /=.
rewrite -[X in X < _]mul1r.
rewrite -subr_lt0 -mulrBl.
rewrite pmulr_llt0.
by rewrite subr_lt0 invf_gt1.
exact: one_half_gt0.
Qed.

Lemma x_neq0 (x': 'rV[R]_2):
  bet (@a' R) (@b' R) x'->  x' != (@b' R) -> x' != 0.
Proof.
move=> ? ?.
rewrite vector2_neq0 [x' 0 1 != 0]lt0r_neq0 ?orbT //.
apply lt_trans with (1/(1+1)).
rewrite one_half_gt0 //.
by apply bet_abx_x01_gt.
Qed.

Lemma xt_neq (x': 'rV[R]_2):
  bet (@a' R) (@b' R) x' -> x' != (@b' R) -> x'!= t'.
Proof.
move=> ? ?.
rewrite -subr_eq0 vector2_neq0 !mxE /= bet_abx_x00_eq0 //.
by rewrite add0r oppr_eq0 one_half_neq0 orTb.
Qed.

Lemma bet_b1d1c A B B' C D D' T X :
 Bet A B X -> Bet A B' X -> Bet B D C -> Bet A D T -> Bet A D' T ->
 B <> D -> D <> C -> ~ Col A B C ->
 Cong X T B' C -> Cong X B A B' -> Cong A C B T -> CongA A X T A B' D' ->
 Bet B' D' C.
Proof.
intros Hb1 Hb2 Hb3 Hb4 Hb5 HBD HDC HNC Hc1 Hc2 Hc3 HConga1.
assert (HAT : A <> T) by (intro; treat_equalities; apply HNC; Col).
assert (HC : Col B' D' C).
 {
 assert (Out B' D' C); [|assert_cols; auto].
 assert (HConga2 : CongA A X T A B' C).
   {
   apply l11_10 with B T A C; try apply out_trivial; try apply l6_6, bet_out;
   try solve [assert_diffs; auto]; Between.
   apply cong3_conga; try solve [assert_diffs; auto]; split; Cong;
   split ; Cong.
   }
 assert (HOS1 : OS B' A D' D).
   {
   apply invert_one_side, out_one_side;
   try (right; intro; apply HNC; assert_diffs; ColR).
   apply bet2_out_out with T T; Between;
   [|intro; subst; treat_equalities; apply HNC; ColR|
     apply out_trivial; intro; treat_equalities;
     apply HNC; assert_diffs; ColR].
   intro; subst; treat_equalities; apply HNC.
   assert (Col A B' C); [|ColR].
   apply col_conga_col with A X T; auto.
   apply col_conga_col with A B' A; try apply conga_sym; Col.
   }
 assert (HOS2 : OS B' A C D).
   {
   apply l9_19 with B; try split; try solve [assert_diffs; ColR];
   try (intro; apply HNC; assert_diffs; ColR);
   repeat split; assert_diffs; Between.
   }
 destruct (l11_15 A X T A B' D) as [_ [_ [_ H]]];
 try (intro; apply HNC; assert_diffs; ColR).
 apply H; repeat (split; auto).
 }
assert (HD'' : TS A T B' C).
 {
 apply l9_8_2 with B.

   {
   split; try (intro; apply HNC; assert_diffs; ColR).
   split; try (intro; apply HNC; assert_diffs; ColR).
   exists D; assert_diffs; split; Col.
   }

   {
   apply out_one_side; try (right; intro; apply HNC; assert_diffs; ColR).
   apply bet2_out_out with X X; try apply out_trivial; assert_diffs; auto.
   }
 }
destruct HD'' as [_ [_ [D'' [HC' Hb6]]]].
assert (D' = D''); [|subst; auto].
apply l6_21 with B' C A T; Col; intro; apply HNC; assert_diffs; ColR.
Qed.

Lemma addcb_eqt : (@c' R) + (@b' R) = t'.
Proof.
apply /eqP.
by rewrite /c'/b' vector2_eq !mxE /= addr0 add0r eqxx.
Qed.

Lemma quad_kNN (a b : 'rV[R]_2) k :
  k *: (a - b) *m (k *: (a - b))^T = k *: (b - a) *m (k *: (b - a))^T.
Proof.
by rewrite -opprB scalerN mulNmx dotC mulNmx opprK.
Qed.

Lemma quad_NN (a b : 'rV[R]_2) :
  (a - b) *m (a - b)^T = (b - a) *m (b - a)^T.
Proof.
by rewrite -opprB mulNmx dotC mulNmx opprK.
Qed.

Lemma congA_axt_ab1d1 (a b1 d1 t x : 'rV[R]_2) :
  betS a b1 x -> betS a d1 t -> betR a b1 x == betR a d1 t ->
  a != x -> t != x -> a != b1 -> d1 != b1 ->
  CongA a x t a b1 d1.
Proof.
rewrite /CongA.
move=> /betSP[bet_eq_ab1x k_gt0 k_lt1] /betSP[bet_eq_ad1t _ _] /eqP betR_eq
/eqP ax_neq /eqP tx_neq /eqP ab1_neq /eqP d1b1_neq.
repeat (split; first by []).
clear ax_neq tx_neq ab1_neq d1b1_neq.
set k := betR a b1 x.
rewrite -/k in k_gt0.
rewrite -/k in k_lt1.
set k2 := (k / (k+1)).
set k3 := (1 / (k+1)).
have: (k2 > 0)
  by rewrite /k2 mulr_gt0 ?invr_gt0 ?addr_gt0 ?ltr01.
have: (k2 < 1).
  by rewrite /k2 divf_lt1 ?cpr_add ?addr_gt0 ?ltr01.
have: (k3 > 0)
  by rewrite /k3 mulr_gt0 ?invr_gt0 ?addr_gt0 ?ltr01.
have: (k3 < 1)
  by rewrite /k2 divf_lt1 ?cpr_add ?addr_gt0 ?ltr01.
have: k != 0 by rewrite lt0r_neq0. move=>k_neq0.
have: d1 - b1 == k *: (t - x).
  have: d1 - b1 = (d1 - a) + (a - b1).
    by rewrite addrA [X in _ = X]addrC !addrA
      [X in _ = X]addrAC -!addrA subrr addr0 addrC.
  have: t - x = (t - a) - ( x - a)
    by rewrite opprB addrA [X in _ = X]addrC !addrA
     [X in _ = X]addrAC -!addrA subrr addr0 addrC.
  move=> -> ->.
  rewrite scalerDr -[a - b1]opprB scalerN.
  rewrite bet_eq_ad1t bet_eq_ab1x.
  by rewrite /k betR_eq.
move=> /eqP keq_d1b1_tx.
exists (extension x a k3).
exists (extension x t k3).
exists (extension b1 a k2).
exists (extension b1 d1 k2).
rewrite /= !extension_bet //.
repeat (split; first try (by [])).
rewrite /extension /k3 invf_div mulrDl divff ?oner_neq0 //.
rewrite divr1 scalerBr !scalerDl !scale1r opprD -!addrA.
rewrite [- x + x]addrC subrr addr0 !addrA addrAC.
rewrite /cong -!addrA subrr addr0 -!scalerBr.
by rewrite quad_NN quad_kNN bet_eq_ab1x.

rewrite /extension /k3 invf_div mulrDl divff ?oner_neq0 //.
rewrite divr1 scalerBr !scalerDl !scale1r opprD -!addrA.
rewrite [- x + x]addrC subrr addr0 !addrA addrAC.
rewrite /cong -!addrA subrr addr0 -!scalerBr.
by rewrite keq_d1b1_tx eqxx.

rewrite /extension /k2 invf_div mulrDl divff ?k_neq0 //.
rewrite mul1r scalerBr !scalerDl !scale1r opprD -!addrA.
rewrite [- b1 + (- (k^-1 *: b1) + b1)]addrC -!addrA subrr addr0.
rewrite addrC /cong -!addrA subrr addr0 -!scalerBr.
rewrite quad_kNN quad_NN bet_eq_ab1x.
by rewrite scalerA mulrC divff ?k_neq0 ?scale1r.

rewrite /extension /k2 invf_div mulrDl divff ?k_neq0 //.
rewrite mul1r scalerBr !scalerDl !scale1r opprD -!addrA.
rewrite [- b1 + (- (k^-1 *: b1) + b1)]addrC -!addrA subrr addr0.
rewrite addrC /cong -!addrA subrr addr0 -!scalerBr.
by rewrite keq_d1b1_tx scalerA mulrC divff ?k_neq0 ?scale1r.

rewrite /extension /k3 invf_div mulrDl divff ?oner_neq0 //.
rewrite divr1 scalerBr !scalerDl !scale1r opprD -!addrA.
rewrite [- x + x]addrC subrr !addr0.
rewrite /extension /k2 invf_div mulrDl divff ?k_neq0 //.
rewrite mul1r !scalerBr !scalerDl !scale1r opprD -!addrA.
rewrite [- b1 + (- (k^-1 *: b1) + b1)]addrC -!addrA subrr addr0.
rewrite !addrA addrC [X in cong _ X _ _]addrAC.
rewrite [X in cong _ _ X _]addrC.
rewrite /cong !opprD !opprK !addrA.
rewrite addrC !addrA addrC !addrA addrAC -!addrA subrr addr0.
rewrite !addrA addrAC addrC !addrA -scalerBr addrAC.
rewrite eq_sym.
rewrite addrC !addrA addrC !addrA.
rewrite addrAC -!addrA subrr addr0.
rewrite !addrA addrAC addrC !addrA addrAC -!addrA -scalerBr.
rewrite !addrA bet_eq_ad1t -betR_eq -/k.
by rewrite scalerA -!addrA mulrC divff ?k_neq0 ?scale1r.
Qed.

Lemma euclid_fails_2D : exists a b c d t,
  bet' a d t /\ bet' b d c /\
  a <> b /\ a <> c /\ b <> d /\ d <> c /\
  ~ (bet' a b c \/ bet' b c a \/ bet' c a b) /\
  (forall (x : (@Point R 2)), bet' a b x ->
                       (forall y' : 'rV[R]_2, bet (# a) (# c) y' ->
                                              bet (# x) (# t) y' ->
                                              (y' *m y'^T) 0 0 >= 1)).
Proof.
exists a, b, c, d, t.
split ; [exact:bet_adt|].
split ; [exact:bet_bdc|].
split.
  apply /eqP; rewrite point_vector_neq /a /b /a' /b' row2_eq.
  by rewrite eqxx eq_sym one_half_neq0.
split.
  apply /eqP; rewrite point_vector_neq /a /c /a' /c' row2_eq.
  by rewrite eq_sym one_half_neq0 eqxx.
split.
  apply /eqP; rewrite point_vector_neq /b /d /b' /d' row2_eq.
  by rewrite -quarter eq_sym mulf_eq0 one_half_neq0.
split.
  apply /eqP.
  by rewrite point_vector_neq /c/d/c'/d' row2_eq
    -quarter eq_sym mulf_eq0 one_half_neq0 andbF.
have: ~ (bet' a b c \/ bet' b c a \/ bet' c a b)=> [|ncol].
  rewrite /bet' /a /b /c /=; move: (@three_non_collinear_points_vector R 0).
  by rewrite /a'nD /b'nD /c'nD !bet_nD_2D.
split=> // x.
case ((#x) =P (b' R)).
  move=>-> ? y' bet_acy bet_bty.
  exfalso.
  move: (col_2D' (bet_col bet_acy)).
  move: (col_2D' (bet_col bet_bty)).
  rewrite /b' /t' !mxE /= !add0r subrr oppr0 mul0r.
  rewrite mulf_eq0 oppr_eq0 one_half_neq0 orFb subr_eq0.
  move=> /eqP <-.
  by rewrite mulf_eq0 oppr_eq0 one_half_neq0.
move => /eqP neq_xb bet_abx y' bet_acy bet_xty.
set b1' : 'rV[R]_2 := (#x) + (@a' R) - (@b' R).
set k1 := betR (@a' R) b1' (#x).
have: betS (@a' R) b1' (#x).
  rewrite -bet_betS /b1' ?euclid_fails_aux //; apply /eqP;rewrite a'_eq0.
  by rewrite addr0 eq_sym subr_eq0.
  rewrite addr0 -subr_eq0 addrAC subrr sub0r oppr_eq0.
  by rewrite /b' row2_eq0 one_half_neq0 andbF.
move=>/betSP[/eqP ratio_b1_xa k1_gt0 k1_lt1].
rewrite -/k1 in k1_gt0 k1_lt1.
set y1' := extension (#a) (#c) k1.
suffices: y' = y1'; [move->|].
rewrite /y1' /extension /a /= a'_eq0 addr0 subr0.
rewrite -scalemxAl dotC -scalemxAl scalerA mxE.
suffices: ((@c' R) *m (@c' R)^T) 0 0 = 1/(1+1+1+1).
  move->.
  apply le_trans with ((1+1) * (1+1) * (1 / (1 + 1 + 1 + 1))).
  rewrite -quarter !mul1r !mulrA mulrC -!mulrA.
  rewrite divff ?add11_neq0 //.
  by rewrite mulr1 mulrC divff ?add11_neq0 ?lexx.
apply ler_pmul ; rewrite -?quarter ?mulr_ge0 ?invr_ge0 ?addr_ge0 ?ler01 //.
suffices: (1+1) <= k1^-1.
  move=>?.
  rewrite ler_pmul ?addr_ge0 ?ler01 //.
rewrite /k1 /betR /b1' /ratio.
case: pickP => /= [z|/all_v_neq0 H].
  rewrite a'_eq0 !mxE /= !subr0 invf_div; case: z => [] [|[| //]] //= p.
  rewrite (@ord_inj _ (Ordinal p) 0) // => /eqP x00_neq0 .
  exfalso.
  apply x00_neq0; apply /eqP.
  rewrite bet_abx_x00_eq0 //.
  rewrite (@ord_inj _ (Ordinal p) 1) // =>_.
  rewrite addr0 ler_pdivl_mulr.
  rewrite mulrBr mul1r divff ?add11_neq0 //.
  rewrite -subr_le0 mulrDl !mul1r addrAC -!addrA subrr addr0.
  rewrite subr_le0 ltW // bet_abx_x01_lt1 //.
  by rewrite subr_gt0 bet_abx_x01_gt.
exfalso; apply H; rewrite subr_eq0 a'_eq0.
by apply x_neq0.
exact: c'_norm.
apply bet_intersect with (#x) (#t) (#a) (#c) (#b).
move: ncol; rewrite /bet'=> //.
by apply xt_neq.
by rewrite eq_sym /a /c /= /a' /c' row2_eq one_half_neq0.
by move: bet_abx ; rewrite /bet' bet_sym.
by [].
by [].
set d1':= contraction (@a' R) t' k1.
set k2:=betR b1' d1' (@c' R).
have: extension (#a) d1' k1 == t' ; [|rewrite /t/= => /eqP<-].
by rewrite extension_contraction ?lt0r_neq0.
have: extension (#a) b1' k1 == (#x) ; [|clear ratio_b1_xa;move/eqP<-].
  rewrite extension_contraction ?lt0r_neq0// /contraction.
  by rewrite eq_sym -subr_eq.
apply euclid''; try by [].
case: (d1' =P b1') ; [by move ->; rewrite bet_xxa |move=> d1b1_neq].
apply (@bet_b1d1c (@a' R) (@b' R) b1' (@c' R) d' d1' t' (#x)) ;rewrite /=.
by [].
by rewrite /b1' euclid_fails_aux.
by rewrite -/(bet' b d c) bet_bdc.
by rewrite -/(bet' a d t) bet_adt.
by rewrite /d1' contraction_bet.
apply /eqP.
by rewrite eq_sym row2_eq -quarter mulf_eq0 one_half_neq0 andFb.
apply /eqP.
by rewrite row2_eq -quarter mulf_eq0 one_half_neq0 andbF.
by move: ncol ;rewrite /Col /bet' /=.
by rewrite /b1' a'_eq0 addr0 /cong opprB addrA addcb_eqt.
by rewrite /b1' a'_eq0 /cong addr0 subr0 quad_NN.
by rewrite a'_eq0 /cong -addcb_eqt -addrA subrr addr0 subr0 eqxx.
apply congA_axt_ab1d1.
  rewrite -bet_betS.
  by rewrite /b1' euclid_fails_aux.
  by apply /eqP; rewrite eq_sym /b1' a'_eq0 addr0 subr_eq0.
  apply /eqP; rewrite /b1' a'_eq0 addr0 -subr_eq0 addrAC subrr.
  by rewrite add0r oppr_eq0 row2_eq0 one_half_neq0 andbF.
  rewrite /d1' contraction_betS //.
  by rewrite a'_eq0 row2_eq0 one_half_neq0.
  by rewrite /d1' contraction_betR ?eqxx ?row2_eq ?one_half_neq0.
  by rewrite eq_sym a'_eq0 x_neq0.
  by rewrite eq_sym xt_neq.
  by rewrite /b1' a'_eq0 addr0 eq_sym subr_eq0.
  by apply /eqP.
rewrite /b1' /c/= a'_eq0 addr0 -subr_eq0 vector2_neq0.
rewrite !mxE /= bet_abx_x00_eq0 //.
by rewrite oppr0 !add0r oppr_eq0 one_half_neq0 orTb.
by rewrite extension_bet.
Qed.

Definition o'  : 'rV[R]_2 := row2 0 0.

Definition i'  : 'rV[R]_2 := row2 (-1/(1+1)) 0.

Definition i1' : 'rV[R]_2 := row2 (1/(1+1)) 0.

Definition i2' : 'rV[R]_2 := row2 0 (1/(1+1)).

Lemma o'_in_unit_disk : (o' *m o'^T) 0 0 < 1.
Proof.
rewrite /o' !mxE !big_ord_recr /= big_ord0 !mxE /= add0r mul0r add0r ltr01 //=.
Qed.

Lemma i'_in_unit_disk : (i' *m i'^T) 0 0 < 1.
Proof.
rewrite /t' !mxE !big_ord_recr /= big_ord0 !mxE /= add0r ?mul0r ?add0r ?addr0.
rewrite mulf_div mulN1r opprK mulrDl mulrDr !mulr1 !addrA -quarter.
by apply lt_trans with (1/(1+1));
  first apply one_quarter_lt_one_half;
  last apply one_half_lt1.
Qed.

Lemma i1'_in_unit_disk : (i1' *m i1'^T) 0 0 < 1.
Proof.
rewrite /t' !mxE !big_ord_recr /= big_ord0 !mxE /= add0r ?mul0r ?add0r ?addr0.
by apply lt_trans with (1/(1+1));
  first apply one_quarter_lt_one_half;
  last apply one_half_lt1.
Qed.

Lemma i2'_in_unit_disk : (i2' *m i2'^T) 0 0 < 1.
Proof.
rewrite /t' !mxE !big_ord_recr /= big_ord0 !mxE /= add0r ?mul0r ?add0r ?addr0.
by apply lt_trans with (1/(1+1));
  first apply one_quarter_lt_one_half;
  last apply one_half_lt1.
Qed.

Definition o : (@Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) o' o'_in_unit_disk.
Definition i : (@Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) i' i'_in_unit_disk.
Definition i1 : (@Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) i1' i1'_in_unit_disk.
Definition i2 : (@Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) i2' i2'_in_unit_disk.

Definition basis :=
  (cons_tuple i1 (cons_tuple i2 (nil_tuple (@Point R 2)))).

Lemma add_halfhalf : (1 / (1 + 1) + 1 / (1 + 1)) = 1 :>R.
Proof.
rewrite addf_div; try apply add11_neq0.
rewrite !mul1r !addrA mulrDr !mulr1 !addrA divff //=.
apply lt0r_neq0.
  by rewrite -addrA addr_gt0 //= addr_gt0 //= ltr01 //=.
Qed.

Lemma i_neq_i1 : # i != # i1.
Proof.
rewrite /= /row2 vector2_eq !mxE /= eqxx /= eq_sym.
rewrite -subr_eq0 -mulNr opprK add_halfhalf andbT oner_eq0 //=.
Qed.

Lemma omd_oi : omd_v (# o) (# i) = 1.
Proof. rewrite /omd_v !mxE !big_ord_recr /= big_ord0 !mxE !mul0r !add0r subr0 //=. Qed.
Lemma omd_oi1 : omd_v (# o) (# i1) = 1.
Proof. rewrite /omd_v !mxE !big_ord_recr /= big_ord0 !mxE !mul0r !add0r subr0 //=. Qed.
Lemma omd_oi2 : omd_v (# o) (# i2) = 1.
Proof. rewrite /omd_v !mxE !big_ord_recr /= big_ord0 !mxE !mul0r !add0r subr0 //=. Qed.
Lemma omd_oo : omd_v (# o) (# o) = 1.
Proof. rewrite /omd_v !mxE !big_ord_recr /= big_ord0 !mxE !mul0r !add0r subr0 //=. Qed.

Lemma omd_ii : omd_v (# i) (# i) = 1 - (1/(1+1+1+1)).
Proof.
rewrite /omd_v !mxE !big_ord_recr /= big_ord0 !mxE //=.
rewrite !mul0r ?add0r ?addr0 -mulNr mulN1r opprK mulrC -div1r -quarter mulNr //=.
Qed.
Lemma omd_i1i1 : omd_v (# i1) (# i1) = 1 - (1/(1+1+1+1)).
Proof.
rewrite /omd_v !mxE !big_ord_recr /= big_ord0 !mxE //=.
rewrite !mul0r ?add0r ?addr0 quarter //=.
Qed.
Lemma omd_i2i2 : omd_v (# i2) (# i2) = 1 - (1/(1+1+1+1)).
Proof.
rewrite /omd_v !mxE !big_ord_recr /= big_ord0 !mxE //=.
rewrite !mul0r ?add0r ?addr0 quarter //=.
Qed.

Lemma omd_i1i2 : omd_v (# i1) (# i2) = 1.
Proof.
rewrite /omd_v !mxE !big_ord_recr /= big_ord0 !mxE //=.
rewrite !mul0r !mulr0 !add0r subr0 //=.
Qed.

Lemma omd_ii2 : omd_v (# i) (# i2) = 1.
Proof.
rewrite /omd_v !mxE !big_ord_recr /= big_ord0 !mxE //=.
rewrite !mul0r !mulr0 !add0r subr0 //=.
Qed.

Lemma lower_dim_holds :
  i <> (tnth basis (inord 0)) /\ bet' i o (tnth basis (inord 0)) /\
  \big[and/True]_(0 <= j < 2) cong' o i o (tnth basis (inord j)) /\
  \big[and/True]_(0 <= j < 2)
   \big[and/True]_(j.+1 <= k < 2)
   cong' (tnth basis (inord j)) (tnth basis (inord k))
         i                      (tnth basis (inord 1)).
Proof.
rewrite 2?big_ltn 1?big_geq 2?big_ltn 1?big_geq 1?big_ltn ?big_geq;
rewrite /tnth 2?inordK //=; split; [apply /eqP|].
  by rewrite point_vector_neq; apply i_neq_i1.
split.
rewrite /bet' /bet; suff: (@betS R 2 (# i) (# o) (# i1))=> [->|];
  first by rewrite orbT.
rewrite /betS; suff: (@betR R 2 (# i) (# o) (# i1) = 1/(1+1)).
  move=> ->; rewrite betSP'_aux /row2 !mxE /= subrr mulr0 eqxx add0r.
  rewrite -mulNr opprK add_halfhalf mulr1 one_half_gt0 one_half_lt1 eqxx //=.
rewrite /betR /ratio; case: pickP => [x|/all_v_neq0 H].
  case: x => [] [|[|//]] p; rewrite /row2 !mxE.
    rewrite (@ord_inj _ (Ordinal p) 0) //= -mulNr opprK add_halfhalf oner_neq0 add0r divr1 //=.
    rewrite (@ord_inj _ (Ordinal p) 1) //= add0r oppr0 eqxx //.
    destruct H; rewrite subr_eq0 eq_sym; apply i_neq_i1.
repeat split; rewrite /cong' /cong_v.
  rewrite omd_oi omd_oi1 !omd_oo omd_ii omd_i1i1 //=.
  rewrite omd_oi omd_oi2 !omd_oo omd_ii omd_i2i2 //=.
  rewrite omd_ii omd_i1i1 omd_i2i2 omd_i1i2 omd_ii2 //=.
Qed.

End rcfTarski2D.

Section rcfTarskinD.

Variable R : rcfType.
Variable n : nat.

Lemma cong_pseudo_reflexivity :
  cong_pseudo_reflexivityP (Point R n) (@cong' R n).
Proof. by move=> a b; apply cong_pseudo_reflexivity_vector. Qed.

Lemma cong_inner_transitivity :
  cong_inner_transitivityP (Point R n) (@cong' R n).
Proof. by move=> ? ? ? ? ? ?; apply cong_inner_transitivity_vector. Qed.

Lemma cong_identity : cong_identityP (Point R n) (@cong' R n).
Proof. by move => ? ? ?; rewrite -dist_cong' dist_aa_eq1; apply dist_eq1'. Qed.

Lemma segment_construction :
  segment_constructionP (Point R n) (@bet' R n) (@cong' R n).
Proof. move=> ? ? ? ? _; apply segment_construction_holds. Qed.

Lemma five_segment : five_segmentP (Point R n) (@bet' R n) (@cong' R n).
Proof. move=> ?; apply five_segment_holds. Qed.

Lemma inner_pasch : inner_paschP (Point R n) (@bet' R n).
Proof. move=> ?; apply inner_pasch_holds. Qed.

Lemma bet_symmetry : bet_symmetryP (Point R n) (@bet' R n).
Proof. by rewrite /bet' => ? ? ?; apply bet_symmetry_vector. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP (Point R n) (@bet' R n).
Proof. move => ? ? ? ?; apply bet_inner_transitivity_vector. Qed.

Lemma lower_dim :
  lower_dimP (@Point R 2) (@bet' R 2) (@cong' R 2) 2 (@o R) (@i R) (@basis R).
Proof. apply lower_dim_holds. Qed.

End rcfTarskinD.

Section rcfTarski2pnD.

Variable R : rcfType.

Variable n : nat.

Lemma point_equality_decidability :
  forall (a b : Point R (2 + n)), a = b \/ a <> b.
Proof. by move=> a b; case: (a =P b); tauto. Qed.

Lemma pasch : forall (a b c p q : Point R (2 + n)),
  bet' a p c -> bet' b q c ->
  a <> p -> p <> c -> b <> q -> q <> c ->
  ~ (bet' a b c \/ bet' b c a \/ bet' c a b) ->
  exists x, bet' p x b /\ bet' q x a.
Proof.
move=> a b c p q ? ? ? ? ? ? Hnc.
destruct (@inner_pasch R (2 + n) a b c p q) as [x []] => //; last by exists x.
rewrite /independence.Col; intuition.
Qed.

Lemma three_non_collinear_points :
  ~ (bet' (@a_nD R n) (@b_nD R n) (@c_nD R n) \/
     bet' (@b_nD R n) (@c_nD R n) (@a_nD R n) \/
     bet' (@c_nD R n) (@a_nD R n) (@b_nD R n)).
Proof.
move: (@three_non_collinear_points_vector R n).
by rewrite /a_nD /b_nD /c_nD /bet'.
Qed.

Global Instance Rcf_to_GI_PED' :
  Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality.
Proof.
exact
(Build_Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality
  (Point R (2 + n)) (@bet' R (2 + n)) (@cong' R (2 + n)) point_equality_decidability
  (@cong_pseudo_reflexivity R (2 + n)) (@cong_inner_transitivity R (2 + n))
  (@cong_identity R (2 + n))
  (@segment_construction_holds R (2 + n)) (@five_segment R (2 + n))
  (@bet_symmetry R (2 + n)) (@bet_inner_transitivity R (2 + n))
  pasch (@a_nD R n) (@b_nD R n) (@c_nD R n) three_non_collinear_points).
Defined.

Lemma Col_Col a b c :
  independence.Col _ (@bet' R (2 + n)) a b c <->
  (@Col (@gupta_inspired_to_tarski.GI_to_T Rcf_to_GI_PED')) a b c.
Proof.
rewrite /independence.Col /Col /Bet /=; case: (bet' a b c); [intuition|].
case: (bet' b c a); [intuition|]; case: (bet' c a b); intuition.
Qed.

Lemma euclid_fails :
  ~ (forall a b c d t : Point R (2 + n),
        bet' a d t -> bet' b d c ->
        b <> d -> d <> c ->
        ~ (bet' a b c \/ bet' b c a \/ bet' c a b) ->
        exists x y : Point R (2 + n), bet' a b x /\ bet' a c y /\ bet' x t y).
Proof.
apply euclid_aux; move: (@euclid_fails_2D R); move=> [a [b [c [d [t H]]]]].
destruct a as [a aP]; destruct b as [b bP]; destruct c as [c cP].
destruct d as [d dP]; destruct t as [t tP]; move: H; rewrite /bet' /=.
move => [? [? [/eqP HNE1 [/eqP HNE2 [/eqP HNE3 [/eqP HNE4 [? H]]]]]]].
move: HNE1 HNE2 HNE3 HNE4; rewrite !point_vector_neq /= => ? ? ? ?.
move: aP bP cP dP tP; rewrite -!(@unit_disk_nD_2D R n) => aP bP cP dP tP.
exists (exist _ (to_nD n a) aP); exists (exist _ (to_nD n b) bP).
exists (exist _ (to_nD n c) cP); exists (exist _ (to_nD n d) dP).
exists (exist _ (to_nD n t) tP); rewrite /= !bet_nD_2D; split => //.
split => //; split; [|split]; [apply /eqP; rewrite point_vector_neq ..|];
rewrite ?eq_nD_2D //; split => // x Hb1 y Hb2 Hb3.
assert (Hx := Hb1); apply bet_2D_extension_2D in Hx; rewrite ?eq_nD_2D //.
assert (Hy := Hb2); apply bet_2D_extension_2D in Hy; rewrite ?eq_nD_2D //.
move: Hb1 Hb3 Hx; destruct x as [x xP] => /= Hb1 Hb3 Hx.
move: xP; rewrite Hx Hy !unit_disk_nD_2D => xP.
by apply H with (exist _ (to_2D x) xP); rewrite -!(@bet_nD_2D n) /= -?Hx -?Hy.
Qed.

Lemma euclid : ~ euclidP (Point R (2 + n)) (@bet' R (2 + n)) (@cong' R (2 + n)).
Proof.
move=> HP; apply euclid_fails; cut (tarski_s_parallel_postulate).
  rewrite /tarski_s_parallel_postulate; move=> HT A B C D T H1 H2 HBD HDC HNCol.
  apply HT with D; auto; intro; subst; apply HNCol; right; right.
  apply bet_symmetry, H2.
cut (triangle_circumscription_principle); [|rewrite /proclus_postulate].
  apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
  simpl; try tauto.
move=> a b c Hnc; destruct (HP a b c) as [x [? [? HCop]]];
[intro; subst; Col..|rewrite /independence.Col; intuition auto with col|].
exists x; split; [|split] => //; apply Cop__Coplanar.
destruct HCop as [E [F [G [? [HCopA [HCopB [HCopC HCopD]]]]]]]; exists E, F, G.
split; first by rewrite -Col_Col.
split; first by destruct HCopA as [P []]; exists P; split; rewrite -Col_Col.
split; first by destruct HCopB as [P []]; exists P; split; rewrite -Col_Col.
split; first by destruct HCopC as [P []]; exists P; split; rewrite -Col_Col.
by destruct HCopD as [P []]; exists P; split; rewrite -Col_Col.
Qed.

End rcfTarski2pnD.
