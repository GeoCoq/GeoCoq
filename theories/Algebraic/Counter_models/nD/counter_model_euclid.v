From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype choice seq.
From mathcomp Require Import order finset finfun ssralg ssrnum path.
From mathcomp Require Import generic_quotient matrix mxalgebra algC zmodp.
From mathcomp Require Import ring lra.
From mathcomp Require Import tuple fintype bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.
Require Import GeoCoq.Algebraic.coplanarity.
Require Import GeoCoq.Algebraic.Counter_models.nD.dimensional_axioms.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Main.Meta_theory.Models.tarski_to_gupta_inspired.
Require Export GeoCoq.Main.Meta_theory.Parallel_postulates.parallel_postulates.
Require Import GeoCoq.Algebraic.POF_to_Tarski.

Section Numerals.
Variable R : ringType.

Lemma add11E : 1 + 1 = 2 :> R. Proof. by []. Qed.

Lemma add1111E : 1 + 1 + 1 + 1 = 4 :> R. Proof. by rewrite -!addrA. Qed.

End Numerals.

Ltac fold_num := rewrite ?add1111E ?add11E.
Ltac num_lra := fold_num; lra.
Ltac num_field := fold_num; field.

Section rcfTarski.

Variable R : rcfType.
Variable n : nat.

Lemma quarter : (1 / (1 + 1)) * (1 / (1 + 1)) = (1 / (1 + 1 + 1 + 1)) :> R.
Proof. by rewrite add1111E add11E !mul1r -invfM -natrM. Qed.

Lemma one_half_gt0 : 0 < 1 / (1 + 1) :> R.
Proof. by num_lra. Qed.

Lemma one_half_lt1 : 1 / (1 + 1) < 1 :>R.
Proof. by num_lra. Qed.

Lemma one_half_neq0 : (1 / (1 + 1) == 0 :> R) = false.
Proof. by apply: gt_eqF; num_lra. Qed.

Definition Point' n : Type := {p : 'rV[R]_n | (p *m p^T) 0 0 < 1}.

Definition Point := Point' n.

Notation "#" := proj1_sig.

Implicit Types (a b c d: Point).

Implicit Types (u v w x y z : 'rV[R]_n).

Definition dotp u v := (u *m v^T) 0 0.

Lemma dotpDl u v w : dotp (u + v) w = dotp u w + dotp v w.
Proof. by rewrite /dotp mulmxDl mxE. Qed.

Lemma dotpDr u v w : dotp u (v + w) = dotp u v + dotp u w.
Proof. by rewrite /dotp linearD mulmxDr mxE. Qed.

Lemma dotpZl k u v : dotp (k *: u) v = k * dotp u v.
Proof. by rewrite /dotp -scalemxAl mxE. Qed.

Lemma dotpZr k u v : dotp u (k *: v) = k * dotp u v.
Proof. by rewrite /dotp linearZ -scalemxAr mxE. Qed.

Lemma dotpNl u v : dotp (- u) v = - dotp u v.
Proof. by rewrite /dotp mulNmx mxE. Qed.

Lemma dotpNr u v : dotp u (- v) = - dotp u v.
Proof. by rewrite /dotp linearN mulmxN mxE. Qed.

Lemma dotpC u v : dotp u v = dotp v u.
Proof. by rewrite /dotp mulmx_trC. Qed.

Definition dotpE := (dotpDl, dotpDr, dotpZl, dotpZr, dotpNl, dotpNr).

Definition omd_v v w := (1 - (v *m (w)^T) 0 0).

Definition dist_v v w := (omd_v v v * omd_v w w) / (omd_v v w) ^+ 2.

Definition cong_v v w x y :=
  (omd_v v w)^+2/(omd_v v v * omd_v w w) ==
  (omd_v x y)^+2/(omd_v x x * omd_v y y).

Definition bet_dist_v x y z :=
  dist_v x z ==
  (dist_v x y) * (dist_v y z) /
  (1 + Num.sqrt(1 - (dist_v x y)) * Num.sqrt(1 - (dist_v y z))) ^+ 2.

Definition norm v := Num.sqrt((v *m (v)^T) 0 0).

Definition omd a b := omd_v (#a) (#b).

Definition dist a b := dist_v (#a) (#b).

Definition cong' a b c d := cong_v (#a) (#b) (#c) (#d).

Definition bet' a b c := bet (#a) (#b) (#c).

Definition bet_dist a b c := bet_dist_v (#a) (#b) (#c).

Lemma point_vector_eq a b : a == b = (#a == #b).
Proof.
apply /eqP /eqP; first by move ->.
move: a b => [a aP] [b bP] /= eq_a_b; move: eq_a_b aP i =>-> aP _.
by have -> : (aP = bP) by apply eq_irrelevance.
Qed.

Lemma point_vector_neq a b : a != b = (#a != #b).
Proof. by rewrite point_vector_eq. Qed.

Lemma cauchy_schwarz_sqr v w :
  ((v *m w^T) 0 0) ^+ 2 <= (v *m v^T) 0 0 * (w *m w^T) 0 0.
Proof.
rewrite -!/(dotp _ _).
have [->|w_neq0] := eqVneq w 0.
  by rewrite /dotp linear0 !mulmx0 mxE expr0n mulr0.
have ww_gt0 : 0 < dotp w w by rewrite lt0r dot2_eq0 w_neq0 dot2_ge0.
set r := dotp v w / dotp w w.
have := dot2_ge0 (v - r *: w); rewrite dotE -/(dotp _ _).
have -> : dotp (v - r *: w) (v - r *: w) =
          (dotp v v * dotp w w - dotp v w ^+ 2) / dotp w w.
  by rewrite !dotpE [dotp w v]dotpC /r; field; rewrite lt0r_neq0.
by rewrite pmulr_lge0 ?invr_gt0 // subr_ge0.
Qed.

Lemma cauchy_schwarz v w :
  - norm v * norm w <= (v *m w^T) 0 0 <= norm v * norm w.
Proof.
case: (v*m v^T =P 0).
  move => /eqP ;rewrite quad_eq0 => /eqP->.
  by rewrite /norm !mul0mx !mxE /= !sqrtr0 oppr0 mul0r lexx.
move => /eqP; rewrite quad_eq0 => v_neq0.
case: (w*m w^T =P 0).
  move => /eqP ;rewrite quad_eq0 => /eqP->.
  by rewrite /norm linear0 !mulmx0 !mxE /= !sqrtr0 !mulr0 lexx.
move => /eqP; rewrite quad_eq0 => w_neq0.
move: (cauchy_schwarz_sqr v w).
rewrite -[_ ^+ 2 <= _]ler_sqrt.
- by rewrite sqrtr_sqr ler_norml  !sqrtrM !/norm -?mulNr ?dot2_ge0.
- by rewrite ?mulr_ge0 ?mulr_gt0 ?lt0r ?dot2_ge0 ?dot2_eq0 ?w_neq0 ?v_neq0.
Qed.

Lemma p_scalar_lt1 v w :
  v != w ->
  (v *m v^T) 0 0 < 1 ->
  (w *m w^T) 0 0 < 1 ->
  (v *m w^T) 0 0 < 1.
Proof.
move => vw_neq; rewrite -!/(dotp _ _).
have : 0 < dotp (v - w) (v - w).
  by rewrite lt_def dot2_ge0 dot2_eq0 subr_eq0 vw_neq.
rewrite !dotpE [dotp w v]dotpC; lra.
Qed.

Lemma p_scalar_point_lt1 a b : (#a *m (#b)^T) 0 0 < 1.
Proof.
case: ((#a)=P(#b)); first by move ->; destruct b.
by move => /eqP ab_neq; apply p_scalar_lt1; [|by destruct a|by destruct b].
Qed.

Lemma invf_eq (a b : R) : b != 0 -> (a == b) = (a^-1 == b^-1).
Proof. by move => _; rewrite (inj_eq invr_inj). Qed.

Lemma divf_le1 (a b : R) : 0 < b -> (a / b <= 1) = (a <= b).
Proof. by move => b_gt0; rewrite ler_pdivrMr ?mul1r. Qed.

Lemma divf_eq1 (a b : R) : b != 0 -> (a / b == 1) = (a == b).
Proof. by move => b_neq0; apply/eqP/eqP => [/divr1_eq|->]; rewrite ?divff. Qed.

Lemma omd_gt0 a b : 0 < omd a b.
Proof. by rewrite /omd subr_gt0 p_scalar_point_lt1. Qed.

Lemma norm_point_lt1 a : norm (#a) < 1.
Proof.
by rewrite /norm -[X in _ < X]sqrtr1 ltr_sqrt ?ltr01 //; destruct a.
Qed.

Lemma omd_ge0 a b : 0 <= omd a b.
Proof. by rewrite ltW ?omd_gt0. Qed.

Lemma omd_eq0 a b : omd a b == 0 = false.
Proof. by rewrite gt_eqF ?omd_gt0. Qed.

Lemma omd_v_reflexivity v w : omd_v v w = omd_v w v.
Proof. by rewrite /omd_v mulmx_trC. Qed.

Lemma omd_reflexivity a b : omd a b = omd b a.
Proof. by rewrite /omd omd_v_reflexivity. Qed.

Lemma dist_aa_eq1 a : dist a a = 1.
Proof.
by rewrite /dist/dist_v expr2 divff ?mulf_neq0 // -/(omd a a) omd_eq0.
Qed.

Lemma addr_ge_gt0 (x y : R) : 0 < x -> 0 <= y -> 0 < x + y.
Proof. lra. Qed.

Lemma omd_disc a b :
  omd a b ^+ 2 - omd a a * omd b b =
  dotp (#a) (#b - #a) ^+ 2 + omd a a * dotp (#b - #a) (#b - #a).
Proof.
by rewrite /omd /omd_v -!/(dotp _ _) !dotpE [dotp (#b) (#a)]dotpC; ring.
Qed.

Lemma dist'_ge0 a b : 0 <= omd a b ^+ 2 - omd a a * omd b b.
Proof. by rewrite omd_disc addr_ge0 ?sqr_ge0 ?mulr_ge0 ?omd_ge0 ?dot2_ge0. Qed.

Lemma omd_neq0 a b : omd a b != 0.
Proof. by rewrite omd_eq0. Qed.

Lemma sqrt_div_sqr (x y : R) : 0 < y -> Num.sqrt (x / y ^+ 2) = Num.sqrt x / y.
Proof.
move => y_gt0; case: (leP 0 x) => [x_ge0|x_lt0].
  by rewrite sqrtrM // -exprVn sqrtr_sqr ger0_norm // invr_ge0 ltW.
rewrite (ler0_sqrtr (ltW x_lt0)) mul0r ler0_sqrtr //.
by rewrite pmulr_lle0 ?invr_gt0 ?exprn_gt0 ?ltW.
Qed.

Lemma one_sub_dist a b :
  1 - dist a b = (omd a b ^+ 2 - omd a a * omd b b) / omd a b ^+ 2.
Proof. by rewrite /dist /dist_v -!/(omd _ _); field; rewrite omd_neq0. Qed.

Lemma sqrt_one_sub_dist a b :
  Num.sqrt (1 - dist a b) =
  Num.sqrt (omd a b ^+ 2 - omd a a * omd b b) / omd a b.
Proof. by rewrite one_sub_dist sqrt_div_sqr ?omd_gt0. Qed.

Lemma extension_affine u v k : k *: (v - u) + u = (1 - k) *: u + k *: v.
Proof. by rewrite scalerBr scalerBl scale1r addrC addrA addrAC. Qed.

Lemma omd_affine a b (x : Point) l :
  omd_v (#x) ((1 - l) *: #a + l *: #b) = (1 - l) * omd x a + l * omd x b.
Proof. by rewrite /omd /omd_v -!/(dotp _ _) !dotpE; ring. Qed.

Lemma omd_disc_affine a b c l :
  #c = (1 - l) *: #a + l *: #b ->
  omd a c ^+ 2 - omd a a * omd c c =
  l ^+ 2 * (omd a b ^+ 2 - omd a a * omd b b).
Proof.
move => c_eq; rewrite /omd /omd_v c_eq -!/(dotp _ _) !dotpE.
by rewrite [dotp (#b) (#a)]dotpC; ring.
Qed.

Lemma dist_le1 a b : dist a b <= 1.
Proof.
rewrite /dist/dist_v -!/(omd _ _).
rewrite divf_le1 ; last by rewrite expr2 mulr_gt0 ?omd_gt0.
by rewrite -subr_ge0 dist'_ge0.
Qed.

Lemma dist_gt0 a b : 0 < dist a b.
Proof.
by rewrite /dist /dist_v -!/(omd _ _) expr2 invfM ?mulr_gt0 ?invr_gt0 ?omd_gt0.
Qed.

Lemma dist_cong' a b c d : (dist a b == dist c d) = cong' a b c d.
Proof. rewrite /dist/dist_v /cong'/cong_v invf_eq.
by rewrite !invf_div.
by rewrite expr2 ?mulf_neq0 ?invr_neq0 ?mulf_neq0 -?/(omd _ _) ?omd_eq0.
Qed.

Lemma bet_dist_bet' a b c : bet' a b c -> bet_dist a b c.
Proof.
rewrite /bet_dist /bet_dist_v => /orP[|betS_abc].
  by move => /betEP[[-> <-]|->|->]; rewrite -!/(dist _ _) dist_aa_eq1 subrr
    sqrtr0 ?mulr0 ?mul0r addr0 expr1n invr1 ?mulr1 ?mul1r.
rewrite -!/(dist _ _).
have c_eq := betS_extension betS_abc.
move: betS_abc => /betSP[_ k_gt0 k_lt1].
set k := betR _ _ _ in c_eq k_gt0 k_lt1; set l := k^-1.
have l_ge1 : 1 <= l by rewrite ltW // invf_gt1.
have c_aff : #c = (1 - l) *: #a + l *: #b.
  by rewrite c_eq /extension extension_affine.
have Eac : omd a c = (1 - l) * omd a a + l * omd a b.
  by rewrite {1}/omd c_aff omd_affine.
have Ebc : omd b c = (1 - l) * omd a b + l * omd b b.
  by rewrite {1}/omd c_aff omd_affine [omd b a]omd_reflexivity.
set D := omd a b ^+ 2 - omd a a * omd b b.
have D_ge0 : 0 <= D by apply: dist'_ge0.
have Dbc : omd b c ^+ 2 - omd b b * omd c c = (l - 1) ^+ 2 * D.
  rewrite (@omd_disc_affine b a c (1 - l)); last by rewrite c_aff subKr addrC.
  by rewrite [omd b a]omd_reflexivity /D; ring.
have den : 1 + Num.sqrt (1 - dist a b) * Num.sqrt (1 - dist b c) =
           omd b b * omd a c / (omd a b * omd b c).
  rewrite !sqrt_one_sub_dist -/D Dbc sqrtrM ?sqr_ge0 // sqrtr_sqr.
  rewrite ger0_norm ?subr_ge0 //.
  have <- : omd a b * omd b c + (l - 1) * D = omd b b * omd a c.
    by rewrite Eac Ebc /D; ring.
  by rewrite -[D in RHS](sqr_sqrtr D_ge0); field; rewrite !omd_neq0.
rewrite den /dist /dist_v -!/(omd _ _); apply/eqP.
by field; rewrite !omd_neq0.
Qed.

Lemma dist_eq1' a b : dist a b == 1 -> a = b.
Proof.
rewrite /dist /dist_v -!/(omd _ _) divf_eq1 ?expf_neq0 ?omd_neq0 //.
rewrite eq_sym -subr_eq0 omd_disc paddr_eq0
        ?sqr_ge0 ?mulr_ge0 ?omd_ge0 ?dot2_ge0 //.
rewrite [omd a a * _ == 0]mulf_eq0 omd_eq0 /= /dotp dot2_eq0 subr_eq0.
by move => /andP[_ /eqP ba]; apply: val_inj.
Qed.

Lemma cong_identity_holds a b c : cong' a b c c -> a = b.
Proof.
rewrite -dist_cong' dist_aa_eq1.
exact: dist_eq1'.
Qed.

Lemma dist_eq1 a b : (dist a b == 1) = (a == b).
Proof.
apply /eqP /eqP; first by move => /eqP; exact: dist_eq1'.
by move ->; rewrite dist_aa_eq1.
Qed.

Lemma dist_neq1 a b : (dist a b != 1) = (a != b).
Proof. by rewrite dist_eq1. Qed.

Lemma dist_lt1 a b:
  dist a b < 1 = (a!=b).
Proof.
by rewrite -dist_neq1 lt_def dist_le1 andbT eq_sym.
Qed.

Lemma omd_disc_gt0 a b : a != b -> 0 < omd a b ^+ 2 - omd a a * omd b b.
Proof.
rewrite -dist_lt1 -subr_gt0 one_sub_dist.
by rewrite pmulr_lgt0 // invr_gt0 exprn_gt0 ?omd_gt0.
Qed.

Lemma cong_inner_transitivity_vector (a b c d e f : 'rV[R]_n) :
  cong_v a b e f -> cong_v c d e f -> cong_v a b c d.
Proof. by rewrite /cong_v => /eqP -> /eqP ->. Qed.

Lemma bet_in_disk (a b c : 'rV[R]_n) :
  bet a b c ->
  (a *m a^T) 0 0 < 1 ->
  (c *m c^T) 0 0 < 1 ->
  (b *m b^T) 0 0 < 1.
Proof.
rewrite /bet => /orP[/betEP[[-> _]|->|->] //|].
rewrite betS_neq13 => /andP[/betSP[b_eq r_gt0 r_lt1] ac_neq] aa_lt1 cc_lt1.
have := p_scalar_lt1 ac_neq aa_lt1 cc_lt1.
move: aa_lt1 cc_lt1; move/eqP: b_eq; rewrite subr_eq => /eqP ->.
set r := betR a b c in r_gt0 r_lt1 *.
rewrite -!/(dotp _ _) !dotpE [dotp c a]dotpC => aa_lt1 cc_lt1 ac_lt1.
have h1 : 0 < (1 - r) ^+ 2 * (1 - dotp a a) by rewrite mulr_gt0 ?exprn_gt0; lra.
have h2 : 0 < r ^+ 2 * (1 - dotp c c) by rewrite mulr_gt0 ?exprn_gt0; lra.
have h3 : 0 < r * (1 - r) * (1 - dotp a c) by rewrite !mulr_gt0; lra.
nra.
Qed.

Lemma segment_addition' (a b c a' b' c' : Point):
  cong' a b a' b' -> cong' b c b' c' -> bet' a b c -> bet' a' b' c' ->
  cong' a c a' c'.
Proof.
rewrite -!dist_cong'.
move => /eqP cong'_aba'b' /eqP cong'_bcb'c' bet'_abc bet'_a'b'c'.
apply bet_dist_bet' in bet'_abc.
apply bet_dist_bet' in bet'_a'b'c'.
move: bet'_abc bet'_a'b'c'.
rewrite /bet_dist /bet_dist_v -!/(dist _ _) => /eqP -> /eqP ->.
by rewrite cong'_aba'b' cong'_bcb'c' eqxx.
Qed.

Lemma cong_v_aabc a b c : cong_v (#a) (#a) (#b) (#c) = ((#b) == (#c)).
Proof.
apply /eqP /eqP.
  move =>/eqP; rewrite eq_sym -/(cong_v _ _ _ _) -/(cong' _ _ _ _) => H.
  by rewrite (@cong_identity_holds b c a).
by move ->; rewrite -!expr2 -!/(omd _ _) !divff ?mulf_eq0 ?omd_eq0.
Qed.

Lemma cong_v_bcaa a b c : cong_v (#b) (#c) (#a) (#a) = ((#b) == (#c)).
Proof. by rewrite /cong_v eq_sym -/(cong_v _ _ _ _) cong_v_aabc. Qed.

Definition ch a b := (Num.sqrt (dist a b))^-1.

Lemma chE a b : ch a b = omd a b / (Num.sqrt (omd a a) * Num.sqrt (omd b b)).
Proof.
rewrite /ch /dist /dist_v -!/(omd _ _) sqrt_div_sqr ?omd_gt0 //.
by rewrite sqrtrM ?omd_ge0 // invf_div.
Qed.

Lemma ch_affine a b c d l :
  #c = (1 - l) *: #a + l *: #b -> a != b ->
  ch c d = ((ch a c - ch a b * ch b c) * ch a d +
            (ch b c - ch a b * ch a c) * ch b d) / (1 - ch a b ^+ 2).
Proof.
move => c_eq ab_neq.
have Eac : omd a c = (1 - l) * omd a a + l * omd a b.
  by rewrite {1}/omd c_eq omd_affine.
have Ebc : omd b c = (1 - l) * omd a b + l * omd b b.
  by rewrite {1}/omd c_eq omd_affine [omd b a]omd_reflexivity.
have Ecd : omd c d = (1 - l) * omd a d + l * omd b d.
  by rewrite omd_reflexivity {1}/omd c_eq omd_affine !(omd_reflexivity d).
have D_neq0 := lt0r_neq0 (omd_disc_gt0 ab_neq).
rewrite !chE Ecd Eac Ebc.
have s_neq0 (p : Point) : Num.sqrt (omd p p) != 0.
  by rewrite sqrtr_eq0 -ltNge omd_gt0.
have sq (p : Point) : omd p p = Num.sqrt (omd p p) ^+ 2.
  by rewrite sqr_sqrtr ?omd_ge0.
move: (s_neq0 a) (s_neq0 b) (s_neq0 c) (s_neq0 d) D_neq0 (sq a) (sq b).
set sa := Num.sqrt (omd a a); set sb := Num.sqrt (omd b b).
set sc := Num.sqrt (omd c c); set sd := Num.sqrt (omd d d).
move => sa_neq0 sb_neq0 sc_neq0 sd_neq0 D_neq0 Eaa Ebb.
move: D_neq0; rewrite Eaa Ebb -oppr_eq0 opprB -exprMn => D_neq0; field.
by rewrite D_neq0 sa_neq0 sb_neq0 sc_neq0 sd_neq0.
Qed.

Lemma five_segment_holds a a' b b' c c' d d' :
  cong' a b a' b' -> cong' b c b' c' -> cong' a d a' d' -> cong' b d b' d' ->
  bet' a b c -> bet' a' b' c' -> a <> b ->
  cong' c d c' d'.
Proof.
move => cong1 cong2 cong3 cong4 bet1 bet2 /eqP /negPf ab_neq.
move: bet1 cong1 cong2 cong3 cong4.
rewrite point_vector_eq in ab_neq.
rewrite /bet /cong' => /orP[/betEP[[/eqP]|/eqP|->]|]; rewrite ?ab_neq //.
rewrite cong_v_aabc=> _ /eqP -> //.
move => betS_abc; move: bet2.
rewrite /bet => /orP[/betEP[[-> _]|->|->]|]; rewrite ?cong_v_bcaa ?ab_neq //.
move => _ /eqP -> //.
move => betS_a'b'c'.
rewrite -!/(cong' _ _ _ _) -!dist_cong'.
move => /eqP dist_ab /eqP dist_bc /eqP dist_ad /eqP dist_bd.
have /eqP dist_ac : dist a c == dist a' c'.
  by rewrite dist_cong' (@segment_addition' a b c a' b' c') -?dist_cong'
             /bet' /bet ?betS_abc ?betS_a'b'c' ?orbT ?dist_ab ?dist_bc.
have line (x y z : Point) :
  betS (#x) (#y) (#z) -> exists l, #z = (1 - l) *: #x + l *: #y.
  by move => /betS_extension ->; eexists; rewrite /extension extension_affine.
have [[l1 l1E] [l2 l2E]] := (line _ _ _ betS_abc, line _ _ _ betS_a'b'c').
have a'b'_neq : a' != b'.
  by move: betS_a'b'c'; rewrite betS_neq12 -point_vector_neq => /andP[].
have : ch c d = ch c' d'.
  by rewrite (ch_affine d  l1E) ?point_vector_neq ?ab_neq //
             (ch_affine d' l2E) // /ch dist_ab dist_ac dist_bc dist_ad dist_bd.
rewrite /ch => /invr_inj /(congr1 (fun r : R => r ^+ 2)).
by rewrite !sqr_sqrtr ?ltW ?dist_gt0 // => ->.
Qed.

Lemma cong_v_in_disk b c d E' :
  cong_v (#b) E' (#c) (#d) -> (E' *m E'^T) 0 0 < 1.
Proof.
rewrite /cong_v -!/(omd _ _) => /eqP H; rewrite -subr_gt0 -/(omd_v _ _) ltNge.
apply/negP => EE_le0.
have : 0 < omd c d ^+ 2 / (omd c c * omd d d).
  by rewrite divr_gt0 ?exprn_gt0 ?mulr_gt0 ?omd_gt0.
rewrite -H invfM mulrA ltNge mulr_ge0_le0 // ?invr_le0 //.
by rewrite divr_ge0 ?sqr_ge0 ?omd_ge0.
Qed.

Lemma E_in_disk (a b c d : Point) :
  (exists E' : 'rV[R]_n, bet (#a) (#b) E' /\ cong_v (#b) E' (#c) (#d)) ->
  (exists E : Point,     bet' a   b    E  /\ cong'  b    E  c    d).
Proof.
move => [E' [bet cong_v]].
assert (E'_in_disk := cong_v).
apply cong_v_in_disk in E'_in_disk.
set E := (exist (fun p => (p *m p^T) 0 0 < 1) E' E'_in_disk).
exists E.
by rewrite /bet' bet /cong' cong_v.
Qed.

Lemma dot_omd a b : dotp (#a) (#b) = 1 - omd a b.
Proof. by rewrite /dotp /omd /omd_v opprB addrC subrK. Qed.

Lemma cong_aaxx (a x : 'rV[R]_n) : cong a a x x.
Proof. by rewrite !congE !subrr eqxx. Qed.

Lemma cong_cdab (a b c d : 'rV[R]_n) : cong c d a b = cong a b c d.
Proof. by rewrite !congE eq_sym. Qed.

Lemma cong_bacd (a b c d : 'rV[R]_n) : cong b a c d = cong a b c d.
Proof. by rewrite !congE -opprB mulNmx mulmx_trC mulNmx opprK. Qed.

Lemma cong_abdc (a b c d : 'rV[R]_n) : cong a b d c = cong a b c d.
Proof. by rewrite cong_cdab cong_bacd cong_cdab. Qed.

Lemma segment_addition (a b c a' b' c' : 'rV[R]_n) :
  cong a b a' b' -> cong b c b' c' -> bet a b c -> bet a' b' c' ->
  cong a c a' c'.
Proof.
case: (a =P b).
  move ->.
  rewrite cong_cdab=> H.
  by rewrite (cong_identity H).
move => /eqP ab_neq cong_aba'b' cong_bcb'c' bet_abc bet_a'b'c'.
rewrite cong_bacd cong_abdc.
apply five_segment with a a' b b'=> //.
by rewrite cong_aaxx.
by rewrite cong_bacd cong_abdc.
by apply /eqP.
Qed.

Lemma cong_v_omd b c d E :
  omd_v (#b) E ^+ 2 = omd b b / dist c d * omd_v E E -> cong_v (#b) E (#c) (#d).
Proof.
move=> bE; have EE_neq0 : omd_v E E != 0.
  apply/eqP => EE0; move: bE; rewrite EE0 mulr0 => /eqP; rewrite sqrf_eq0.
  have nE : norm E = 1.
    move/eqP: EE0; rewrite /omd_v subr_eq0 eq_sym /norm => /eqP ->.
    by rewrite sqrtr1.
  move: (cauchy_schwarz (#b) E) => /andP[_ /le_lt_trans].
  rewrite nE mulr1 => /(_ _ (norm_point_lt1 b)) /lt_eqF bE_neq1.
  by rewrite /omd_v subr_eq0 eq_sym bE_neq1.
rewrite /cong_v bE /dist /dist_v -!/(omd _ _); apply/eqP; field.
by rewrite EE_neq0 !omd_neq0.
Qed.

Lemma segment_construction_vector a b c d :
  a != b -> c != d ->
  exists E' : 'rV[R]_n, bet (#a) (#b) E' /\ cong_v (#b) E' (#c) (#d).
Proof.
move=> ab_neq cd_neq.
set A := omd a a; set B := omd b b; set C := omd a b; set K := B / dist c d.
set N := C *+ 2 - A - B.
have N_gt0 : 0 < N.
  have -> : N = dotp (#b - #a) (#b - #a).
    rewrite /N /A /B /C !dotpE [dotp (#b) (#a)]dotpC !dot_omd; ring.
  by rewrite lt0r dot2_ge0 dot2_eq0 subr_eq0 eq_sym -point_vector_neq ab_neq.
have K_gt : B < K.
  by rewrite /K ltr_pdivlMr ?dist_gt0 // gtr_pMr ?omd_gt0 // dist_lt1.
set al := (B - C) ^+ 2 + K * N; set be := (B - C) * (B - K).
set ga := B * (B - K).
have al_gt0 : 0 < al.
  rewrite /al addrC addr_ge_gt0 ?sqr_ge0 //.
  by rewrite mulr_gt0 // (lt_trans (omd_gt0 b b)).
have ga_lt0 : ga < 0 by rewrite /ga pmulr_rlt0 ?omd_gt0 // subr_lt0.
set D := be ^+ 2 - al * ga; set s := (- be + Num.sqrt D) / al.
have D_gt0 : be ^+ 2 < D by rewrite /D; nra.
have s_gt0 : 0 < s.
  rewrite divr_gt0 // addrC subr_gt0; apply: le_lt_trans (ler_norm be) _.
  by rewrite -sqrtr_sqr ltr_sqrt // (le_lt_trans _ D_gt0) ?sqr_ge0.
have Ps : al * s ^+ 2 + 2 * be * s + ga = 0.
  have -> : ga = (be ^+ 2 - Num.sqrt D ^+ 2) / al.
    by rewrite sqr_sqrtr ?(le_trans _ (ltW D_gt0)) ?sqr_ge0 // /D; field;
       rewrite lt0r_neq0.
  by rewrite /s; field; rewrite lt0r_neq0.
exists (extension (#a) (#b) (1 + s)^-1); split.
  by rewrite extension_bet ?invr_gt0 ?invf_lt1 ?ltrDl ?addr_gt0.
apply: cong_v_omd; rewrite /extension invrK /omd_v -!/(dotp _ _) !dotpE.
rewrite ![dotp _ (#a)]dotpC !dot_omd -/A -/B -/C.
apply/eqP; rewrite -subr_eq0 -Ps /al /be /ga /N /K; apply/eqP; ring.
Qed.

Lemma segment_construction_holds a b c d :
  exists x : Point, bet' a b x /\ cong' b x c d.
Proof.
rewrite /bet' /cong'; apply E_in_disk.
case: (c =P d).
  move ->; exists (#b).
  by rewrite bet_axx /cong_v -!expr2 -!/(omd _ _) !divff
             ?expr2 ?mulf_neq0 ?omd_eq0 .
move => /eqP cd_neq.
case: (a =P b); last by move => /eqP ab_neq; apply segment_construction_vector.
case: (c =P b); first by move => <- ->; exists (#d); rewrite bet_xxa /cong_v.
move => /eqP cb_neq ->; move: (@segment_construction_vector c b c d).
rewrite cd_neq cb_neq => H; destruct H => //; destruct H as  [_ HC].
by exists x; rewrite bet_xxa HC.
Qed.

Lemma cong_pseudo_reflexivity_vector (v w : 'rV[R]_n) : cong_v v w w v.
Proof. by rewrite /cong_v omd_v_reflexivity [omd_v v v * omd_v w w]mulrC. Qed.

Lemma inner_pasch_vector (a b c p q : 'rV[R]_n) :
  bet a p c -> bet b q c ->
  a <> p -> p <> c -> b <> q -> q <> c ->
  ~ ~ (~ bet a b c /\ ~ bet b c a /\ ~ bet c a b) ->
  exists x : 'rV[R]_n, bet p x b /\ bet q x a.
Proof.
move => Hb1 Hb2 ? ? ? ?; move: Hb1 Hb2; rewrite 2?bet_betS //.
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
[exists (exist (fun p => (p *m p^T) 0 0 < 1) x Hx)|destruct p|destruct b].
Qed.

Lemma bet_symmetry_vector (a b c : 'rV[R]_n) : bet a b c -> bet c b a.
Proof. by rewrite bet_sym. Qed.

Lemma bet_inner_transitivity_vector (a b c d : 'rV[R]_n) :
  bet a b d -> bet b c d -> bet a b c.
Proof. exact: bet_inner_transitivity. Qed.

Lemma euclid_fails_of_witness :
  (exists a b c d t,
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
move => [a [b [c [d [t [bADT [bBDC [bd_neq [dc_neq [ncol H]]]]]]]]]] HF.
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

Lemma row2_dot (x y : R) : (row2 x y *m (row2 x y)^T) 0 0 = x * x + y * y.
Proof. by rewrite mxE !big_ord_recr /= big_ord0 !mxE /= add0r. Qed.

Lemma unit_disk_nD_2D (p : 'rV[R]_2) :
  ((to_nD n p) *m (to_nD n p)^T) 0 0 = (p *m p^T) 0 0.
Proof. by rewrite /to_nD tr_row_mx mul_row_col mul0mx addr0. Qed.

Lemma a'_in_unit_disk : (a' *m a'^T) 0 0 < 1.
Proof. by rewrite /a' row2_dot mulr0 addr0 ltr01. Qed.

Lemma a'nD_in_unit_disk : (a'nD *m a'nD^T) 0 0 < 1.
Proof. by rewrite unit_disk_nD_2D a'_in_unit_disk. Qed.

Lemma b'_in_unit_disk : (b' *m b'^T) 0 0 < 1.
Proof. by rewrite /b' row2_dot; num_lra. Qed.

Lemma b'nD_in_unit_disk : (b'nD *m b'nD^T) 0 0 < 1.
Proof. by rewrite unit_disk_nD_2D b'_in_unit_disk. Qed.

Lemma c'_in_unit_disk : (c' *m c'^T) 0 0 < 1.
Proof. by rewrite /c' row2_dot; num_lra. Qed.

Lemma c'nD_in_unit_disk : (c'nD *m c'nD^T) 0 0 < 1.
Proof. by rewrite unit_disk_nD_2D c'_in_unit_disk. Qed.

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
move => iP; move: Hb; have -> : i = rshift 2 i1 :> 'I_(2+n) by apply val_inj.
case: (to_nD n b =P c) => [<- _|/= _]; rewrite ?row_mxEr //.
move => /andP[] E /andP[L G]; move/eqP/rowP/(_ (rshift 2 i1)): E;
rewrite /to_nD mxE row_mxEr mxE opp_row_mx row_mxEr
        2?mxE subr0 2?mxE row_mxEr !mxE subr0.
move => /eqP; rewrite eq_sym mulf_eq0 => /orP[/eqP HF|/eqP-> //].
by move: L; rewrite HF ltxx.
Qed.

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

Section rcfTarski2pnD.

Variable R : rcfType.
Variable n : nat.
Notation "#" := proj1_sig.

Definition Point2pn := Point' R (2 + n).

Definition o' := (1 / 2) *: o n R.

Lemma o'_in_unit_disk : (o' *m o'^T) 0 0 < 1.
Proof.
suff -> : o' = a'nD R n by rewrite a'nD_in_unit_disk.
move: (@row2_eq0 R 0 0); rewrite eqxx /= /o' /o /a'nD /a'.
by move => /eqP ->; rewrite to_nD0 scaler0.
Qed.

Definition o := exist (fun p => (p *m p^T) 0 0 < 1) o' o'_in_unit_disk.

Definition i' := (1 / 2) *: i n R.

Lemma omd_v_half m (u : 'rV[R]_m) :
  (u *m u^T) 0 0 = 1 -> omd_v ((1 / 2) *: u) ((1 / 2) *: u) = 3 / 4.
Proof. by rewrite /omd_v -!/(dotp _ _) dotpZl dotpZr => ->; field. Qed.

Lemma half_in_unit_disk m (u : 'rV[R]_m) :
  (u *m u^T) 0 0 = 1 -> (((1 / 2) *: u) *m ((1 / 2) *: u)^T) 0 0 < 1.
Proof.
by move => /omd_v_half; rewrite /omd_v -subr_gt0 => ->; rewrite divr_gt0.
Qed.

Lemma dot_i : (dimensional_axioms.i n R *m
              (dimensional_axioms.i n R)^T) 0 0 = 1.
Proof. by rewrite iP mulNmx mulmx_trC mulNmx opprK trmx_delta mul_delta_mx mxE. Qed.

Lemma i'_in_unit_disk : (i' *m i'^T) 0 0 < 1.
Proof. exact: half_in_unit_disk dot_i. Qed.

Definition i := exist (fun p => (p *m p^T) 0 0 < 1) i' i'_in_unit_disk.

Lemma dot_detla_mx i :
  (@delta_mx R 1 n.+2 0 (inord i) *m
  (@delta_mx R 1 n.+2 0 (inord i))^T) 0 0 = 1.
Proof. by rewrite trmx_delta mul_delta_mx mxE. Qed.

Lemma basis'_in_unit_disk i :
  (((1 / 2) *: @delta_mx R 1 n.+2 0 (@inord (S n) i)) *m
   ((1 / 2) *: @delta_mx R 1 n.+2 0 (@inord (S n) i))^T) 0 0 < 1.
Proof. exact: half_in_unit_disk (dot_detla_mx i). Qed.

Definition basis : n.+2.-tuple Point2pn :=
  map_tuple (fun i => exist (fun p => (p *m p^T) 0 0 < 1)
                            ((1 / 2) *: @delta_mx R _ _ 0 (inord i))
                            (@basis'_in_unit_disk i))
            (iota_tuple n.+2 0).

Lemma nth_basis i :
  (i < n.+2)%N ->
  # (tnth basis (inord i)) =
  (1 / 2) *: tnth (dimensional_axioms.basis n R) (inord i).
Proof.
move => iP; rewrite /basis /dimensional_axioms.basis.
by rewrite /tnth !(@nth_map nat 0%N) ?size_iota.
Qed.

Lemma bet_basis : bet' i o (tnth basis (inord 0)).
Proof.
rewrite /bet' nth_basis /i /o //= /i' /o' scaler_bet.
- by rewrite dimensional_axioms.nth_basis ?bet_o_i_basis_nth0.
by apply /eqP; rewrite one_half_neq0.
Qed.

Lemma mx11_eq (A B : 'M[R]_1) : (A == B) = (A 0 0 == B 0 0).
Proof. by apply/eqP/eqP => [-> //|E]; apply/rowP => k; rewrite (ord1 k). Qed.

Lemma cong'oaob a b : cong' o a o b = cong (#o) (#a) (#o) (#b).
Proof.
rewrite /cong' /cong_v !congE /o /= /o' oP scaler0 !subr0 /omd_v !mul0mx mxE.
by rewrite subr0 expr1n !mul1r (inj_eq invr_inj)
           (inj_eq (addrI 1)) eqr_opp mx11_eq.
Qed.

Lemma i_neq_basis_nth0 : i <> tnth basis (inord 0).
Proof.
apply /eqP; rewrite point_vector_eq /i nth_basis /i' //=.
rewrite -subr_eq0 -scalerBr scaler_eq0 subr_eq0 one_half_neq0 /=.
rewrite dimensional_axioms.nth_basis //; apply /eqP.
by apply i_neq_basis_nth0.
Qed.

Lemma lower_dim_all1 j :
  (0 <= j < n.+2)%N -> cong' o i o (tnth basis (inord j)).
Proof.
move => jP; rewrite  cong'oaob /o /i nth_basis //= /o' /i'.
by rewrite scaler_cong ?lower_dim_all1 //; apply /eqP; rewrite one_half_neq0.
Qed.

Lemma omd_v_basis i :
  (0 <= i < n.+2)%N ->
  omd_v (# (tnth basis (inord i))) (# (tnth basis (inord i))) = 3 / 4.
Proof.
move => iP; rewrite nth_basis //; apply: omd_v_half.
by rewrite dimensional_axioms.nth_basis // dot_detla_mx.
Qed.

Lemma lower_dim_all2 j k :
  (0 <= j < k)%N -> (k < n.+2)%N ->
  cong' (tnth basis (inord j)) (tnth basis (inord k))
        i                      (tnth basis (inord 1)).
Proof.
move => jkP kP; rewrite /cong' /cong_v.
have jP : (j < n.+2)%N by rewrite (ltn_trans _ kP).
have -> : omd_v (# i) (# i) = 3 / 4 by apply: omd_v_half dot_i.
rewrite !omd_v_basis // ?(ltn_trans _ kP) //=.
rewrite -subr_eq0 -mulrBl mulf_eq0 subr_eq0.
have -> : ((3 / 4 * (3 / 4))^-1 == 0 :> R) = false.
- rewrite invr_eq0 !mulf_eq0 invr_eq0; apply /eqP.
  by rewrite eqbF_neg !negb_or !lt0r_neq0.
rewrite orbF eqf_sqr /omd_v /i' !nth_basis //.
rewrite !dimensional_axioms.nth_basis // iP.
rewrite -!scalemxAl mulNmx mulmx_trC (mulmx_trC (delta_mx 0 0)) -!scalemxAl.
rewrite !trmx_delta !mul_delta_mx_0 ?mxE ?(mulr0, oppr0) ?addr0 ?eqxx //.
all: apply /eqP => /(congr1 val); rewrite !val_insubd ?jP ?kP //=.
all: by move=> E; move: jkP; rewrite E ltnn andbF.
Qed.

Lemma lower_dim_holds :
  lower_dimP _ (@bet' R (n.+2)) (@cong' R (n.+2)) n.+2 o i basis.
Proof.
rewrite /lower_dimP /orthonormal_basis bet_basis.
split; [|split => //]; first by apply i_neq_basis_nth0.
split; [apply big_andb_and|apply big_pairs_andb_and]; rewrite big_all.
- by apply /allP => j jP; rewrite lower_dim_all1 // -mem_index_iota.
apply /allP => j jP; rewrite big_all; apply /allP => k kP.
move: jP kP; rewrite !mem_index_iota => /andP[j_ge0 _] /andP[j_lt_k k_le_np2].
by rewrite lower_dim_all2 //.
Qed.

Lemma nth_nbasisE i p p' :
  (i < n.+2)%N ->
  # p = (1 / 2) *: p' ->
  # (tnth (rot_tuple 1 (belast_tuple p basis)) (inord i)) =
  (1 / 2) *:
  tnth (rot_tuple 1 (belast_tuple p' (dimensional_axioms.basis n R)))
       (inord i).
Proof.
move => _ pE; rewrite -[LHS](tnth_map (fun x : Point2pn => # x)).
rewrite -[RHS](tnth_map (fun x => (1 / 2) *: x)) !(tnth_nth 0) /=.
by rewrite !map_cat -!belast_map -!map_comp /= pE.
Qed.

Lemma big_and_impl (r : seq nat) (P Q : nat -> Prop) :
  (forall j, j \in r -> P j -> Q j) ->
  \big[and/True]_(j <- r) P j -> \big[and/True]_(j <- r) Q j.
Proof.
elim: r => [|x r IH] PQ; rewrite ?big_nil ?big_cons // => -[Px Pr]; split.
  by apply: PQ; rewrite ?mem_head.
by apply: IH => // j jr; apply: PQ; rewrite inE jr orbT.
Qed.

Lemma cong'_center_omd (a b : Point2pn) : cong' o a o b -> omd a a = omd b b.
Proof.
rewrite cong'oaob !congE /o /= /o' oP scaler0 !subr0 => /eqP ab.
by rewrite /omd /omd_v ab.
Qed.

Lemma cong'_cong (a b c d : Point2pn) :
  omd a a = omd c c -> omd b b = omd c c -> omd d d = omd c c ->
  cong' a b c d = cong (#a) (#b) (#c) (#d).
Proof.
move => Ea Eb Ed; have cc_neq0 := omd_neq0 c c.
have -> : cong' a b c d = (omd a b == omd c d).
  rewrite /cong' /cong_v -!/(omd _ _) Ea Eb Ed.
  by rewrite (inj_eq (can_inj (divfK _))) ?mulf_neq0 // eqrXn2 ?omd_ge0.
rewrite !congE mx11_eq -!/(dotp _ _) !dotpE [dotp (#b) (#a)]dotpC
       [dotp (#d) (#c)]dotpC !dot_omd Ea Eb Ed.
by apply/eqP/eqP => E; lra.
Qed.

Lemma upper_dim_holds :
  upper_dimP _ (@bet' R (n.+2)) (@cong' R (n.+2)) n.+2 o i basis.
Proof.
have halfP : 1 / 2 <> 0 :> R by apply /eqP; rewrite one_half_neq0.
move => p _ [_ [_ [HC1 HC2]]] p_neq; rewrite /bet'.
set p'' := 2 *: #p.
have pE : #p = (1 / 2) *: p''.
  by rewrite /p'' scalerA mul1r mulVf ?scale1r // lt0r_neq0 ?ltr0n.
have omdE j : (j < n.+2)%N ->
  omd (tnth (rot_tuple 1 (belast_tuple p basis)) (inord j))
      (tnth (rot_tuple 1 (belast_tuple p basis)) (inord j)) = omd i i.
  move => jP; apply/esym/cong'_center_omd; move: HC1.
  by rewrite -big_andb_and big_all => /allP; apply; rewrite mem_index_iota.
rewrite nth_basis // pE /= /o' scaler_bet // /bet; apply/orP; right.
apply: dimensional_axioms.upper_dimS.
- by rewrite nth_new_basis //; apply: dimensional_axioms.i_neq_basis_nth0.
- by rewrite nth_new_basis // bet_o_i_basis_nth0.
- apply: big_and_impl HC1 => j; rewrite mem_index_iota => /andP[_ jP].
  by rewrite cong'oaob (nth_nbasisE _ pE) // /o /i /= /o' /i' scaler_cong.
- apply: big_and_impl HC2 => j; rewrite mem_index_iota => /andP[_ jP].
  apply: big_and_impl => k; rewrite mem_index_iota => /andP[_ kP].
  by rewrite cong'_cong ?omdE // !(nth_nbasisE _ pE) // /i /= /i' scaler_cong.
by move => E; apply: p_neq; apply: val_inj; rewrite /= nth_basis // pE E.
Qed.

End rcfTarski2pnD.

Section rcfTarski2D.

Variable R : rcfType.
Notation "#" := proj1_sig.

Definition a : (Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) (@a' R) (@a'_in_unit_disk R).

Definition b : (Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) (@b' R) (@b'_in_unit_disk R).

Definition c : (Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) (@c' R) (@c'_in_unit_disk R).

Definition d' : 'rV[R]_2 := row2 (1 / (1 + 1 + 1 + 1)) (1 / (1 + 1 + 1 + 1)).

Definition t' : 'rV[R]_2 := row2 (1 / (1 + 1)) (1 / (1 + 1)).

Lemma d'_in_unit_disk : (d' *m d'^T) 0 0 < 1.
Proof. by rewrite /d' row2_dot; num_lra. Qed.

Lemma t'_in_unit_disk : (t' *m t'^T) 0 0 < 1.
Proof. by rewrite /t' row2_dot; num_lra. Qed.

Definition d : (@Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) d' d'_in_unit_disk.

Definition t : (@Point R 2) :=
  exist (fun p => (p *m p^T) 0 0 < 1) t' t'_in_unit_disk.

Lemma bet_adt : bet' a d t.
Proof.
rewrite /bet' /bet /betS /a /d /t /=.
have -> : betR (@a' R) d' t' = 1/(1+1).
  rewrite /betR /ratio a'_eq0 /= subr0.
  case: pickP => /= [x|/all_v_neq0 H].
    by rewrite /t' /d' !mxE /=; case: x => [] [|[| //]] //= p _; num_field.
  by exfalso; apply H; rewrite -a'_eq0 /a' /t' row2_eq one_half_neq0.
rewrite one_half_lt1 one_half_gt0 /= /a' /d' /t' vector2_eq !mxE /= !subr0.
by apply/orP; right; rewrite andbT; apply/andP; split; apply/eqP; num_field.
Qed.

Lemma bet_bdc : bet' b d c.
Proof.
rewrite /bet' /bet /betS /b /c /d.
have -> : betR (@b' R) d' (@c' R) = 1/(1+1).
  rewrite /betR /ratio /=.
  case: pickP => /= [x|/all_v_neq0 H].
    by rewrite /b' /c' /d' !mxE /=; case: x => [] [|[| //]] //= p _; num_field.
  exfalso; apply H; rewrite /c' /b' subr_eq0 row2_eq.
  by rewrite one_half_neq0 eq_sym one_half_neq0.
rewrite one_half_lt1 one_half_gt0 /= /b' /c' /d' vector2_eq !mxE /=.
rewrite !subr0 !sub0r.
by apply/orP; right; rewrite andbT; apply/andP; split; apply/eqP; num_field.
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

Global Instance Rcf_to_GI2D :
  Gupta_inspired_variant_of_Tarski_2D Rcf_to_GI_PED.
Proof. split; exact (@upper_dim R). Defined.

Lemma bet_a'b' (x' : 'rV[R]_2) :
  bet (a' R) (b' R) x' -> exists2 l, 1 <= l & x' = l *: b' R.
Proof.
rewrite /bet => /orP[/betEP[[_ <-]|/eqP|<-]|/betSP[]].
- by exists 1; rewrite ?scale1r.
- by rewrite /a' /b' row2_eq [X in _ && X]eq_sym one_half_neq0 andbF.
- by exists 1; rewrite ?scale1r.
set k := betR _ _ _; rewrite a'_eq0 !subr0 => b_kx k_gt0 k_lt1.
exists k^-1; first by rewrite ltW // invf_gt1.
by rewrite b_kx scalerA mulVf ?scale1r // lt0r_neq0.
Qed.

Lemma bet_abx_x00_eq0 (x' :'rV[R]_2) :
  bet (a' R) (b' R) x' -> x' 0 0 = 0.
Proof. by case/bet_a'b' => l _ ->; rewrite /b' !mxE /= mulr0. Qed.

Lemma dot2 (u v : 'rV[R]_2) : (u *m v^T) 0 0 = u 0 0 * v 0 0 + u 0 1 * v 0 1.
Proof.
rewrite mxE !big_ord_recr big_ord0 /= add0r !mxE.
by congr (u 0 _ * v 0 _ + u 0 _ * v 0 _); apply: val_inj.
Qed.

Lemma bet_abx_x01_lt1 (x: @Point R 2) :
  bet (a' R) (b' R) (#x) -> (#x) 0 1 < 1.
Proof.
move=> /bet_abx_x00_eq0 x00; have /= := svalP x.
by rewrite dot2 x00 mulr0 add0r; move: (#x 0 1) => y; nra.
Qed.

Lemma abc_ncol : ~ (bet' a b c \/ bet' b c a \/ bet' c a b).
Proof.
rewrite /bet' /a /b /c /=; move: (@three_non_collinear_points_vector R 0).
by rewrite /a'nD /b'nD /c'nD !bet_nD_2D.
Qed.

Lemma euclid_fails_2D :
  exists a b c d t,
    bet' a d t /\ bet' b d c /\
    a <> b /\ a <> c /\ b <> d /\ d <> c /\
    ~ (bet' a b c \/ bet' b c a \/ bet' c a b) /\
    (forall (x : (@Point R 2)),
       bet' a b x ->
       (forall y' : 'rV[R]_2,
          bet (# a) (# c) y' ->
          bet (# x) (# t) y' ->
          (y' *m y'^T) 0 0 >= 1)).
Proof.
exists a, b, c, d, t.
split; first exact: bet_adt.
split; first exact: bet_bdc.
split; [|split; [|split; [|split]]];
  try (apply /eqP; rewrite point_vector_neq /=).
- by rewrite /a' /b' row2_eq eqxx eq_sym one_half_neq0.
- by rewrite /a' /c' row2_eq eq_sym one_half_neq0 eqxx.
- by rewrite /b' /d' row2_eq -quarter eq_sym mulf_eq0 one_half_neq0.
- by rewrite /c' /d' row2_eq -quarter eq_sym mulf_eq0 one_half_neq0 andbF.
split; first exact: abc_ncol.
move=> x bet_abx y' bet_acy bet_xty.
have x01_lt1 := bet_abx_x01_lt1 bet_abx.
move: bet_abx => /bet_a'b' [l l_ge1 xE].
move: (col_2D' (or_introl bet_acy)) (col_2D' (or_introl bet_xty)) x01_lt1.
rewrite /= xE /a' /c' /t' /b' dot2 !mxE /= => /eqP H1 /eqP H2 H3.
move: H1 H2 H3 l_ge1; move: (y' 0 0) (y' 0 1) => y0 y1.
fold_num => H1 H2 H3 l_ge1.
have y1E : y1 = 0 by nra.
have y0_ge1 : 1 <= y0 by rewrite y1E in H2; nra.
nra.
Qed.

End rcfTarski2D.

Section rcfTarskinD.

Variable R : rcfType.
Variable n : nat.

Lemma cong_pseudo_reflexivity :
  cong_pseudo_reflexivityP (Point R n) (@cong' R n).
Proof. by move => a b; apply cong_pseudo_reflexivity_vector. Qed.

Lemma cong_inner_transitivity :
  cong_inner_transitivityP (Point R n) (@cong' R n).
Proof. by move => ? ? ? ? ? ?; apply cong_inner_transitivity_vector. Qed.

Lemma cong_identity : cong_identityP (Point R n) (@cong' R n).
Proof. move => ? ? ?; exact: cong_identity_holds. Qed.

Lemma segment_construction :
  segment_constructionP (Point R n) (@bet' R n) (@cong' R n).
Proof. move => ? ? ? ? _; apply segment_construction_holds. Qed.

Lemma five_segment : five_segmentP (Point R n) (@bet' R n) (@cong' R n).
Proof. move => ?; apply five_segment_holds. Qed.

Lemma inner_pasch : inner_paschP (Point R n) (@bet' R n).
Proof. move => ?; apply inner_pasch_holds. Qed.

Lemma bet_symmetry : bet_symmetryP (Point R n) (@bet' R n).
Proof. by rewrite /bet' => ? ? ?; apply bet_symmetry_vector. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP (Point R n) (@bet' R n).
Proof. move => ? ? ? ?; apply bet_inner_transitivity_vector. Qed.

Lemma lower_dim :
  lower_dimP _ (@bet' R n.+2) (@cong' R n.+2) n.+2 (o R n) (i R n) (basis R n).
Proof. apply lower_dim_holds. Qed.

Lemma upper_dim :
  upper_dimP _ (@bet' R n.+2) (@cong' R n.+2) n.+2 (o R n) (i R n) (basis R n).
Proof. apply upper_dim_holds. Qed.

End rcfTarskinD.

Section rcfTarski2pnD.

Variable R : rcfType.

Variable n : nat.

Lemma point_equality_decidability :
  forall (a b : Point R (2 + n)), a = b \/ a <> b.
Proof. by move => a b; case: (a =P b); tauto. Qed.

Lemma pasch : forall (a b c p q : Point R (2 + n)),
  bet' a p c -> bet' b q c ->
  a <> p -> p <> c -> b <> q -> q <> c ->
  ~ (bet' a b c \/ bet' b c a \/ bet' c a b) ->
  exists x, bet' p x b /\ bet' q x a.
Proof.
move => a b c p q ? ? ? ? ? ? Hnc.
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
  (Point R (2 + n)) (@bet' R (2 + n)) (@cong' R (2 + n))
  point_equality_decidability
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
apply euclid_fails_of_witness; move: (@euclid_fails_2D R).
move => [a [b [c [d [t H]]]]].
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
move => HP; apply euclid_fails; cut (tarski_s_parallel_postulate).
  rewrite /tarski_s_parallel_postulate.
  move => HT A B C D T H1 H2 HBD HDC HNCol.
  apply HT with D; auto; intro; subst; apply HNCol; right; right.
  apply bet_symmetry, H2.
cut (triangle_circumscription_principle); [|rewrite /proclus_postulate].
  apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
  simpl; try tauto.
move => a b c Hnc; destruct (HP a b c) as [x [? [? HCop]]];
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