From mathcomp Require Import ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype seq order.
From mathcomp
Require Import fintype bigop.
From mathcomp
Require Import ssralg ssrnum matrix.
From mathcomp
Require Import zmodp.
From mathcomp
Require Import ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.
Require Import GeoCoq.Main.Meta_theory.Models.gupta_inspired_to_tarski.
Require Import GeoCoq.Algebraic.coplanarity.
Require Import GeoCoq.Main.Meta_theory.Parallel_postulates.parallel_postulates.
Require Import GeoCoq.Main.Tarski_dev.Ch12_parallel_inter_dec.


Local Definition dot (R : realFieldType) n (u v : 'rV[R]_n) : R :=
  (u *m v^T) 0 0.
Arguments dot R n : clear implicits.

Local Notation "''[' u , v ]" := (dot _ _ u v) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Ltac rowE := apply/rowP => ?; rewrite !mxE.

Section Aux.

Variable R : realFieldType.
Variable n : nat.

Implicit Types (v : 'rV[R]_n).

Lemma dotE v1 v2 : '[v1, v2] = (v1 *m v2^T) 0 0. Proof. by []. Qed.

Lemma mulmx_tr v1 v2 : v1 *m v2^T = '[v1, v2]%:M.
Proof. by apply/matrixP=> i j; rewrite !ord1 -mx11_scalar. Qed.

Lemma funmxN (v : 'rV[R]_n) j : (- v) 0 j = - v 0 j.
Proof. by rewrite !mxE. Qed.

Lemma dotC : commutative (dot R n).
Proof.
move=> v1 v2; rewrite dotE; congr (_ _ 0 0).
by rewrite [LHS]mx11_scalar -tr_scalar_mx -mx11_scalar trmx_mul trmxK.
Qed.

Lemma mulmx_trC v1 v2 : v1 *m v2^T = v2 *m v1^T.
Proof. by rewrite !mulmx_tr dotC. Qed.

Lemma dot0v v : '[0, v] = 0. Proof. by rewrite dotE mul0mx mxE. Qed.

Lemma dotDl v1 v2 v3 : '[v1 + v2, v3] = '[v1, v3] + '[v2, v3].
Proof. by rewrite !dotE mulmxDl mxE. Qed.

Lemma dotDr v1 v2 v3 : '[v1, v2 + v3] = '[v1, v2] + '[v1, v3].
Proof. by rewrite dotC dotDl !(dotC v1). Qed.

Lemma dotZl k v1 v2 : '[k *: v1, v2] = k * '[v1, v2].
Proof. by rewrite !dotE -scalemxAl mxE. Qed.

Lemma dotZr k v1 v2 : '[v1, k *: v2] = k * '[v1, v2].
Proof. by rewrite dotC dotZl dotC. Qed.

Lemma dotNl v1 v2 : '[- v1, v2] = - '[v1, v2].
Proof. by rewrite !dotE mulNmx mxE. Qed.

Lemma dotNr v1 v2 : '[v1, - v2] = - '[v1, v2].
Proof. by rewrite dotC dotNl dotC. Qed.

Lemma dot2N v : '[- v] = '[v]. Proof. by rewrite dotNl dotNr opprK. Qed.

Lemma dot2D v1 v2 : '[v1 + v2] = '[v1] + '[v2] + '[v1, v2] *+ 2.
Proof. by rewrite dotDl !dotDr (dotC v2); ring. Qed.

Lemma dot2B v1 v2 : '[v1 - v2] = '[v1] + '[v2] - '[v1, v2] *+ 2.
Proof. by rewrite dot2D dot2N dotNr mulNrn. Qed.

Lemma dot2_eq0 v : ('[v] == 0) = (v == 0).
Proof.
rewrite /dot; apply/eqP/eqP => [/eqP|->]; last by rewrite mul0mx mxE /=.
rewrite !mxE psumr_eq0 /=; last by move=> i _; rewrite mxE sqr_ge0.
move => /allP /= sqp_eq0; apply/rowP => k; rewrite mxE.
by have := sqp_eq0 k; rewrite mem_index_enum !mxE sqrf_eq0 => /(_ isT) /eqP.
Qed.

Lemma dot2_ge0 v : 0 <= '[v].
Proof. by rewrite /dot !mxE sumr_ge0 // => i _; rewrite mxE sqr_ge0. Qed.

Lemma dot2_gt0 v : (0 < '[v]) = (v != 0).
Proof. by rewrite lt0r dot2_eq0 dot2_ge0 andbT. Qed.

Lemma quad_eq0 v : (v *m v^T == 0) = (v == 0).
Proof.
apply/eqP/eqP => [/matrixP /(_ 0 0) /eqP|->]; last by rewrite mul0mx.
by rewrite [X in _ == X]mxE -dotE dot2_eq0 => /eqP.
Qed.

Lemma all_v_neq0 v : v != 0 ->
  ~ (fun k : 'I_n => v 0 k != 0) =1 xpred0.
Proof.
move=> /eqP v_neq0 all_v_neq0; apply: v_neq0.
by apply/rowP => k; rewrite !mxE; have/negPn/eqP := all_v_neq0 k.
Qed.

Lemma add11_neq0 : 1 + 1 != 0 :> R.
Proof. by rewrite (pnatr_eq0 _ 2). Qed.

(* revise names *)
Lemma addrBDB (ZT : zmodType) (v1 v2 v3 : ZT) : v1 - v2 + (v2 - v3) = v1 - v3.
Proof. exact: subrKA. Qed.

Lemma addrDBD (ZT : zmodType) (v1 v2 v3 : ZT) : v1 + v3 - (v2 + v3) = v1 - v2.
Proof. by rewrite [v2 + _]addrC addrKA. Qed.

Lemma addrBBB (ZT : zmodType) (v1 v2 v3 : ZT) : v1 - v2 - (v1 - v3) = v3 - v2.
Proof. by rewrite opprB addrC subrKA. Qed.

Lemma addrDBB (ZT : zmodType) (v1 v2 : ZT) : (v1 + v2 - (v1 - v2) = v2 *+ 2).
Proof. by rewrite opprB addrCA [X in _ + X]addrAC subrr add0r mulr2n. Qed.

Lemma addrBDD (ZT : zmodType) (v1 v2 : ZT) : (v1 - v2 + (v1 + v2) = v1 *+ 2).
Proof. by rewrite addrAC -!addrA subrr addr0 mulr2n. Qed.

Lemma add2r_eq (ZT : zmodType) (x y z : ZT) : (x + y == x + z) = (y == z).
Proof. exact: (inj_eq (addrI _)). Qed.

Lemma comp_ratio_gt0 (k1 k2 : R) :
  0 < k1 -> 0 < k2 -> k1 < 1 -> 0 < k1 + k2 - k1 * k2.
Proof. by move=> ? ? ?; rewrite subr_gt0 ltr_wpDl ?ltW // gtr_pMl. Qed.

Lemma eq_inv_scale (V : lmodType R) (s : R) (x y : V) :
  s != 0 -> (x == s^-1 *: y) = (s *: x == y).
Proof. exact: (fun _ => esym (can2_eq (scalerK _) (scalerKV _) _ _)). Qed.

End Aux.

Section Ratio.

Variable R : realFieldType.
Variable n : nat.

Implicit Types (v : 'rV[R]_n).

Definition ratio v1 v2 :=
  if [pick k : 'I_n | v2 0 k != 0] is Some k
  then v1 0 k / v2 0 k else 0.

Lemma ratio0p p : ratio 0 p = 0.
Proof. by rewrite /ratio; case: pickP => /= [? _|//]; rewrite mxE mul0r. Qed.

Lemma ratiovv v : v != 0 -> ratio v v = 1.
Proof.
move=> v_neq0; rewrite /ratio; case: pickP => /= [x px|/all_v_neq0 //].
by rewrite divrr ?unitfE.
Qed.

Lemma ratiop0 p : ratio p 0 = 0.
Proof.
by rewrite /ratio; case: pickP => /= [x px|//]; rewrite mxE invr0 mulr0.
Qed.

Lemma ratioNv v1 v2 : ratio (- v1) v2 = - ratio v1 v2.
Proof.
by rewrite /ratio; case: pickP => [k _|]; rewrite ?oppr0// funmxN mulNr.
Qed.

Lemma ratiovN v1 v2 : ratio v1 (- v2) = - ratio v1 v2.
Proof.
rewrite /ratio; under eq_pick => k do rewrite funmxN oppr_eq0.
by case: pickP => [k _|]; rewrite ?oppr0// funmxN invrN mulrN.
Qed.

Lemma scaler_ratio v1 v2 k : k <> 0 -> ratio (k *: v1) (k *: v2) = ratio v1 v2.
Proof.
move => k_nz; have fE : (fun x => (k *: v2) 0 x != 0) =1 (fun x => v2 0 x != 0).
- by move => x; rewrite mxE mulf_eq0; move: k_nz; case: (k =P 0) => [->|].
rewrite /ratio (eq_pick fE); case: pickP => [x px|//].
by rewrite !mxE -mulf_div divff ?mul1r //; apply /eqP.
Qed.

Lemma ratioNN v1 v2 : ratio v1 v2 = ratio (- v1) (- v2).
Proof. by rewrite ratioNv ratiovN opprK. Qed.

Lemma add_ratio v1 v2 v3 : v3 != 0 ->
  ratio v1 v3 + ratio v2 v3 = ratio (v1 + v2) v3.
Proof.
move=> v_neq0; rewrite /ratio; case: pickP => /= [x px|/all_v_neq0 //].
by rewrite -mulrDl !mxE.
Qed.

Lemma add_ratio_1 v1 v2 : v2 != 0 ->
  ratio v1 v2 + 1 = ratio (v1 + v2) v2.
Proof. by move=> v_neq0; rewrite -(ratiovv v_neq0) add_ratio. Qed.

Lemma sub_1_ratio v1 v2 : v2 != 0 ->
  1 - ratio v1 v2 = ratio (v2 - v1) v2.
Proof.
move=> v_neq0; apply /eqP; rewrite subr_eq add_ratio //.
by rewrite addrAC -addrA subrr addr0 ratiovv.
Qed.

Lemma ratio_neq0 v1 v2:
  v1 != 0 -> v2 != 0 -> v1 == ratio v1 v2 *: v2 -> ratio v1 v2 != 0.
Proof.
move=> /eqP v1P ?; rewrite /ratio; case: pickP=> /= [x px rP|/all_v_neq0 //].
by apply/eqP; move=> neq; move: rP; rewrite neq scale0r=> /eqP ?; apply v1P.
Qed.

Lemma ratio_eq v1 v2 r : v2 != 0 -> v1 == r *: v2 -> ratio v1 v2 = r.
Proof.
move=> v2_neq0 /eqP Hr. rewrite /ratio. case: pickP=> /= [x px|/all_v_neq0 //].
by rewrite Hr mxE -mulrA mulfV // mulr1.
Qed.

Lemma ratio_lt0_v1_neq0 v1 v2 : ratio v1 v2 < 0 -> v1 != 0.
Proof. by case: (v1 =P 0)=> [->|//]; rewrite ratio0p ltxx. Qed.

Lemma ratio_lt0_v2_neq0 v1 v2 : ratio v1 v2 < 0 -> v2 != 0.
Proof. by case: (v2 =P 0)=> [->|//]; rewrite ratiop0 ltxx. Qed.

End Ratio.

Section TarskiGe1.

Variable R : realFieldType.
Variable n : nat.

Implicit Types (a b c d : 'rV[R]_n).

Definition cong a b c d := '[b - a] == '[d - c].

Lemma congE a b c d :
  cong a b c d = ((b - a) *m (b - a)^T == (d - c) *m (d - c)^T).
Proof.
rewrite /cong !mulmx_tr; apply/eqP/eqP => [->//|/matrixP/(_ 0 0)].
by rewrite !mxE eqxx !mulr1n.
Qed.

Lemma scaler_cong a b c d k :
  k <> 0 -> cong (k *: a) (k *: b) (k *: c) (k *: d) = cong a b c d.
Proof.
move=> /eqP k_neq0; rewrite /cong -!scalerBr !dotZl !dotZr !mulrA.
by rewrite (inj_eq (mulfI (mulf_neq0 k_neq0 k_neq0))).
Qed.

Lemma cong_pseudo_reflexivity a b : cong a b b a.
Proof. by rewrite /cong -opprB dot2N. Qed.

Lemma cong_identity a b c : cong a b c c -> a = b.
Proof. by rewrite /cong subrr dot0v dot2_eq0 subr_eq0 => /eqP ->. Qed.

Lemma cong_inner_transitivity a b c d e f :
   cong a b e f -> cong c d e f -> cong a b c d.
Proof. by rewrite /cong => /eqP -> /eqP ->. Qed.

Lemma congC a b c d : cong a b c d = cong b a d c.
Proof. by rewrite /cong -[a - b]opprB -[c - d]opprB !dot2N. Qed.

Lemma cong_eq' a b c : cong a a b c -> b = c.
Proof. by rewrite /cong subrr dot0v eq_sym dot2_eq0 subr_eq0 => /eqP ->. Qed.

Definition betE a b c := [ || [ && a == b & b == c ], a == b | b == c ].

Lemma betEP a b c :
  reflect ([ \/ [ /\ a = b & b = c ], a = b | b = c ]) (betE a b c).
Proof.
by rewrite /betE; case: (a =P b)=>[->|?]; case: (b =P c)=>[->|?]=> /=;
constructor; [apply Or32|apply Or32|apply Or33|]=> //; case=> [[? ?]|?|?].
Qed.

Lemma betE_sym a b c : betE a b c = betE c b a.
Proof. by rewrite /betE !Bool.orb_assoc eq_sym andbC eq_sym orbAC. Qed.

Lemma scaler_betE a b c k :
  k <> 0 -> betE (k *: a) (k *: b) (k *: c) = betE a b c.
Proof.
move => k_nz; rewrite /betE -subr_eq0 -(subr_eq0 _ (k *: c)) -!scalerBr.
by rewrite !scaler_eq0 !subr_eq0; move: k_nz; case: (k =P 0) => [->|].
Qed.

Definition betR a b c := ratio (b - a) (c - a).

Lemma scaler_betR a b c k :
  k <> 0 -> betR (k *: a) (k *: b) (k *: c) = betR a b c.
Proof. by move => k_nz; rewrite /betR -!scalerBr scaler_ratio. Qed.

Definition betS a b c (r := betR a b c) :=
  [ && b - a == r *: (c - a), 0 < r & r < 1].

Lemma betSP a b c (r := betR a b c) :
  reflect ([ /\ b - a = r *: (c - a), 0 < r & r < 1 ]) (betS a b c).
Proof.
rewrite /betS -/r.
case: (b - a =P r*:(c - a))=> [<-|/=]; last by constructor; case.
by case: (0 < r); case: (r < 1)=> /=; constructor; try (case=> //).
Qed.

Lemma betS_intro a b c r :
  a != c -> 0 < r -> r < 1 -> b - a = r *: (c - a) -> betS a b c.
Proof.
move=> ac_neq r_gt0 r_lt1 baE.
have rE : betR a b c = r.
  by apply: ratio_eq; rewrite ?baE // subr_eq0 eq_sym.
by rewrite /betS rE baE eqxx r_gt0 r_lt1.
Qed.

Lemma betS_intro12 a b c r :
  a != b -> 0 < r -> r < 1 -> b - a = r *: (c - a) -> betS a b c.
Proof.
move=> ab_neq r_gt0 r_lt1 baE; apply: (betS_intro _ r_gt0 r_lt1 baE).
apply: contraNneq ab_neq => ac.
by rewrite eq_sym -subr_eq0 baE ac subrr scaler0.
Qed.

Lemma betS_sym a b c : betS a b c = betS c b a.
Proof.
rewrite /betS /betR !andbA -(addrBDB b c a) -[c - a]opprB ratiovN oppr_gt0.
case (a - c =P 0)=> [->|/eqP ?]; first by rewrite !ratiop0 ltxx !andbF.
rewrite -!add_ratio ?ratioNv ?ratiovv // andbAC subr_lt0 ltrNl ltrBrDl.
by rewrite scaleNr -scalerN scalerBl scale1r -subr_eq !opprB !addrBDB subrr.
Qed.

Lemma scaler_betS a b c k :
  k <> 0 -> betS (k *: a) (k *: b) (k *: c) = betS a b c.
Proof.
move => k_nz; rewrite /betS scaler_betR // -!scalerBr scalerA mulrC -scalerA.
rewrite -subr_eq0 -scalerBr scaler_eq0 subr_eq0.
by move: k_nz; case: (k =P 0) => [->|].
Qed.

Definition bet a b c := betE a b c || betS a b c.

Lemma bet_sym a b c : bet a b c = bet c b a.
Proof. by rewrite /bet betE_sym betS_sym. Qed.

Lemma scaler_bet a b c k :
  k <> 0 -> bet (k *: a) (k *: b) (k *: c) = bet a b c.
Proof. by move => k_nz; rewrite /bet scaler_betE // scaler_betS. Qed.

Lemma bet_symmetry a b c : bet a b c -> bet c b a.
Proof. by rewrite bet_sym. Qed.

Lemma betS_neq12 a b c : betS a b c = betS a b c && (a != b).
Proof.
rewrite /betS/ betR. case (a =P b)=> [->|/eqP ?]; last by rewrite andbT.
by rewrite subrr ratio0p ltxx /= !andbF.
Qed.

Lemma betS_neq23 a b c : betS a b c = betS a b c && (b != c).
Proof. by rewrite betS_sym eq_sym {1}betS_neq12. Qed.

Lemma betS_neq13 a b c : betS a b c = betS a b c && (a != c).
Proof.
rewrite /betS /betR. case (a =P c)=> [->|/eqP ?]; rewrite ?andbT //.
by rewrite subrr ratiop0 ltxx /= andbF !andFb.
Qed.

Lemma betS_id a b : betS a b a = false.
Proof. by rewrite /betS /betR subrr ratiop0 ltxx andbF. Qed.

Lemma bet_betE a b c : bet a b c = betE a b c || bet a b c.
Proof. by rewrite /bet orbA orbb. Qed.

Lemma betE_axx a x : betE a x x.
Proof. by rewrite /betE eqxx !orbT. Qed.

Lemma betE_xxa x a : betE x x a.
Proof. by rewrite /betE eqxx orbT. Qed.

Lemma bet_axx a x : bet a x x.
Proof. by rewrite /bet betE_axx orTb. Qed.

Lemma bet_xxa x a : bet x x a.
Proof. by rewrite /bet betE_xxa orTb. Qed.

Lemma bet_opp a b c : bet a b c = bet (-a) (-b) (-c).
Proof.
rewrite /bet /betE /betS !eqr_opp; apply orb_id2l => _.
rewrite -eqr_opp opprB opprK -scalerN opprB ![a + _]addrC.
suffices: betR a b c = betR (-a) (-b) (-c) by move ->.
by rewrite /betR !opprK ![_ +a]addrC -![a + _]opprB ratioNN.
Qed.

Lemma bet_trans a b c d : bet a b c = bet (a + d) (b + d) (c + d).
Proof.
rewrite ![_ + d]addrC /bet /betE /betS !add2r_eq ![d + _]addrC !addrDBD.
suffices: betR a b c = betR (a + d) (b + d) (c + d) by  move ->.
by rewrite /betR !addrDBD.
Qed.

Lemma betE_xax x a : betE x a x = (x == a).
Proof. by rewrite /betE [a == x]eq_sym; case: (x =P a). Qed.

Lemma bet_xax x a : bet x a x = (x == a).
Proof.
by rewrite /bet /betS /betR subrr ratiop0 lt_def eqxx andbF orbF betE_xax.
Qed.

Lemma bet_scale a b c : bet a b c -> exists r, b - a = r *: (c - a).
Proof.
case/orP => [/betEP[[<- <-]|<-|<-]|/betSP[baE _ _]].
- by exists 0; rewrite subrr scale0r.
- by exists 0; rewrite subrr scale0r.
- by exists 1; rewrite scale1r.
- by exists (betR a b c).
Qed.

Lemma bet_ratio a b k1 : 0 < k1 -> k1 < 1 -> bet a b (k1^-1 *: (b - a) + a).
Proof.
move=> k1_gt0 k1_lt1; have [->|ab_neq] := eqVneq a b; first by rewrite bet_xxa.
apply/orP; right; apply: (betS_intro12 ab_neq k1_gt0 k1_lt1).
by rewrite addrK scalerA mulfV ?scale1r // lt0r_neq0.
Qed.

Definition extension a b k := k^-1 *: (b - a) + a.

Definition contraction a b k := k *: (b - a) + a.

Lemma extension_eq a b c k :
  k != 0 -> (extension a b k == extension a c k) = (b == c).
Proof.
move=>/eqP ?; rewrite /extension -subr_eq -addrA subrr addr0.
rewrite -subr_eq0 -scalerBr opprB addrBDB scalemx_eq0 invr_eq0.
by case: (k =P 0); rewrite // subr_eq0 orFb.
Qed.

Lemma contraction_eq x y z k :
  k != 0 -> (contraction x y k == contraction x z k) = (y == z).
Proof.
move=>/eqP ?; rewrite -subr_eq -addrA subrr addr0.
rewrite -subr_eq0 -scalerBr opprB addrBDB scalemx_eq0.
by case: (k =P 0); rewrite // subr_eq0 orFb.
Qed.

Lemma extension_contraction x y z k:
  k != 0 -> extension x y k == z = (contraction x z k == y).
Proof.
move=> k_neq0; rewrite /extension /contraction.
suffices: (k *: (k^-1 *: (y - x) + x) == k *: z) = (k^-1 *: (y - x) + x == z).
  move<-; rewrite scalerDr scalerA divff // scale1r eq_sym -subr_eq.
  by rewrite -subr_eq opprK -scalerBr.
rewrite -[X in X = _]subr_eq0 -[X in _ = X]subr_eq0 -scalerBr scaler_eq0.
by move/negPf: k_neq0 ->; rewrite orFb.
Qed.

Lemma extensionP a b c :
  a != b -> b - a = ratio (b - a) (c - a) *: (c - a) ->
  extension a b (ratio (b - a) (c - a)) = c.
Proof.
move=> neq_ab ratioP; apply /eqP; rewrite /extension eq_sym -subr_eq.
case: (a =P c)=> [->|/eqP ?]; first by rewrite subrr ratiop0 invr0 scale0r.
rewrite {2}ratioP scalerA -div1r -mulrC mulrA mulr1 divff ?scale1r ?eqxx //.
by move/eqP: ratioP=> ?; rewrite ratio_neq0 // subr_eq add0r eq_sym.
Qed.

Lemma betS_extension x y z:
  betS x y z -> z = extension x y (betR x y z).
Proof.
rewrite betS_neq12=> /andP[/betSP[bet_eq betR_gt0 betR_lt1] neq_xy].
by rewrite /betR extensionP.
Qed.

Lemma extension_bet a b k1 :
  0 < k1 -> k1 < 1 -> bet a b (extension a b k1).
Proof. by move=> ? ? ; rewrite /extension bet_ratio. Qed.

Lemma contraction_bet a b k1:
  0 < k1 -> k1 < 1 -> bet a (contraction a b k1) b.
Proof.
move=> ? ?; have: extension a (contraction a b k1) k1 == b.
  by rewrite extension_contraction ?lt0r_neq0.
by move/eqP=> P1 ; rewrite -{2}P1 extension_bet.
Qed.

Lemma contraction_betR a b k1 :
  b != a -> 0 < k1 -> k1 < 1 -> betR a (contraction a b k1) b = k1.
Proof.
move=> ? ? ?; rewrite /betR /contraction -addrA subrr addr0.
by apply ratio_eq; rewrite ?subr_eq0 ?eqxx.
Qed.

Lemma contraction_betS a b k :
  b != a -> 0 < k -> k < 1 -> betS a (contraction a b k) b.
Proof.
move=> ? k_gt0 k_lt1; rewrite /betS contraction_betR// /contraction -!addrA.
by rewrite subrr addr0 eqxx k_gt0 k_lt1.
Qed.

Lemma extension_col a b c k :
  c == extension a b k -> bet a b c \/ bet b c a \/ bet c a b.
Proof.
rewrite /extension; case: (k =P 0)=> [->|/eqP k_neq0].
  by rewrite invr0 scale0r add0r=> /eqP ->; rewrite bet_axx /=; auto.
move: k_neq0=> /lt_total /orP[k_lt0|k_gt0] /eqP c_def.
  suffices: (bet c a b) by auto. set k' := k / (k - 1).
  have: (c == extension b a k')=> [|/eqP ->]; [|rewrite bet_sym].
    rewrite c_def /extension /k' invf_div mulrBl divff ?ltr0_neq0 //.
    rewrite eq_sym scalerBl scale1r addrAC -!addrA addrC !addrA.
    by rewrite [-b + b]addrC subrr add0r -scalerN opprB mul1r eqxx.
  have: (k < 1)=> [|k_lt1]; first by apply: (@lt_trans _ _ 0); rewrite ?ltr01.
  rewrite extension_bet ?/k' // ?nmulr_rgt0 ?invr_lt0 ?subr_lt0 // -1?subr_gt0.
  have: (1 == (k - 1) / (k - 1)) by rewrite divff ?ltr0_neq0 ?subr_lt0 //.
  move=> /eqP {1}->; rewrite -mulrBl addrAC subrr add0r mulNr -mulrN.
  by rewrite mulr_gt0 ?ltr01 // oppr_gt0 invr_lt0 subr_lt0.
move: c_def; case: (k =P 1)=> [->|/eqP k_neq1 c_def].
  by rewrite invr1 scale1r addrAC addrK=> ->; rewrite bet_axx; auto.
move: k_neq1=> /lt_total /orP[k_lt1|k_gt1].
  by rewrite c_def extension_bet; auto.
suffices: (bet b c a) by auto. set k' := k^-1; have: (c == contraction a b k').
  by rewrite c_def /extension /contraction /k' eqxx.
by move=> /eqP ->; rewrite bet_sym contraction_bet ?/k' ?invr_gt0 ?invf_lt1.
Qed.

Lemma betS_inner_transitivity a b c d :
  betS a b d -> betS b c d -> betS a b c.
Proof.
rewrite betS_neq12 => /andP[/betSP[baE k1_gt0 k1_lt1] ab_neq].
move=> /betSP[cbE k2_gt0 k2_lt1].
move: (betR a b d) (betR b c d) baE cbE k1_gt0 k1_lt1 k2_gt0 k2_lt1.
move=> k1 k2 /eqP + /eqP; rewrite !subr_eq => /eqP bE /eqP cE.
move=> k1_gt0 k1_lt1 k2_gt0 k2_lt1; subst c; subst b.
have s_gt0 := comp_ratio_gt0 k1_gt0 k2_gt0 k1_lt1.
apply: (betS_intro12 (r := k1 / (k1 + k2 - k1 * k2)) ab_neq).
- by rewrite divr_gt0.
- have : k1 * k2 < k2 by rewrite gtr_pMl.
  by rewrite ltr_pdivrMr // mul1r; lra.
- by rowE; field; rewrite lt0r_neq0.
Qed.

Lemma bet_inner_transitivity a b c d: bet a b d -> bet b c d -> bet a b c.
Proof.
rewrite {2}/bet /betE. case: (c =P d)=> [-> //|?]. rewrite {1}/bet bet_betE.
rewrite /betE; case: (b =P c)=> [->|?]; rewrite ?orbT ?orTb // andbF !orFb.
case: (a =P b)=> [->|?]; rewrite ?orTb ?orbT // andFb !orFb.
case: (b =P d)=> [->|?]; rewrite ?subrr ?betS_id // orFb.
by move=> bet1 bet2; rewrite /bet (@betS_inner_transitivity a b c d) ?orbT.
Qed.

Lemma bet_betS a b c : a <> b -> b <> c -> bet a b c = betS a b c.
Proof.
rewrite /bet /betE. case: (a =P b)=>[-> /eqP|? ?]; first by rewrite eqxx.
case: (b =P c)=> [-> /eqP|? ?]; by rewrite ?eqxx andFb !orFb.
Qed.

Lemma inner_pasch'' a b c p q :
  a <> q -> b <> p -> betS a p c -> betS b q c ->
  exists x, betS p x b /\ betS q x a.
Proof.
move=> /eqP aq_neq /eqP bp_neq /betSP[paE k1_gt0 k1_lt1].
move=> /betSP[qbE k2_gt0 k2_lt1].
move: (betR a p c) (betR b q c) paE qbE k1_gt0 k1_lt1 k2_gt0 k2_lt1.
move=> k1 k2 /eqP + /eqP; rewrite !subr_eq => /eqP pE /eqP qE.
move=> k1_gt0 k1_lt1 k2_gt0 k2_lt1; subst p; subst q.
have s_gt0 := comp_ratio_gt0 k1_gt0 k2_gt0 k1_lt1.
have s_neq0 := lt0r_neq0 s_gt0.
set p := k1 *: (c - a) + a; set q := k2 *: (c - b) + b.
pose t := (k1 - k1 * k2) / (k1 + k2 - k1 * k2).
pose t' := (k2 - k1 * k2) / (k1 + k2 - k1 * k2).
exists (t *: (b - p) + p); split.
  apply: (betS_intro (r := t)); rewrite ?addrK // 1?eq_sym //.
    by rewrite divr_gt0 // subr_gt0 gtr_pMr.
  by rewrite ltr_pdivrMr // mul1r; lra.
apply: (betS_intro (r := t')); rewrite 1?eq_sym //.
- by rewrite divr_gt0 // subr_gt0 gtr_pMl.
- by rewrite ltr_pdivrMr // mul1r; lra.
- by rowE; rewrite /t /t'; field.
Qed.

Lemma inner_pasch' a b c p q (k1 := betR a p c) (k2 := betR b q c) :
  betS a p c -> betS b q c ->
  ~ (bet a b c \/ bet b c a \/ bet c a b) ->
  exists x, betS p x b /\ betS q x a.
Proof.
rewrite /bet; case: (b =P p) => [-> -> ? ?|bp_neq];
first by exfalso; intuition auto with bool.
case: (a =P q)=> [-> _|aq_neq ? ? _].
  by rewrite [betS c q b]betS_sym=> -> ?; exfalso; intuition auto with bool.
by destruct (@inner_pasch'' a b c p q) as [x []]=> //; exists x.
Qed.

Lemma inner_pasch a b c p q :
  bet a p c -> bet b q c ->
  a <> p -> p <> c -> b <> q -> q <> c ->
  ~ (bet a b c \/ bet b c a \/ bet c a b) ->
  exists x, bet p x b /\ bet q x a.
Proof.
move=> ? ? ? ? ? ? ? . destruct (@inner_pasch' a b c p q) as [x [Hb1 Hb2]];
by rewrite -?bet_betS // /bet; exists x; rewrite Hb1 Hb2 !orbT.
Qed.

Lemma inner_pasch_gen a b c p q :
  bet a p c -> bet b q c ->
  exists x, bet p x b /\ bet q x a.
Proof.
case: (a =P p)=> [->|?]; first by exists p; rewrite bet_xxa bet_axx.
case: (p =P c)=> [->|?]; first by exists q; rewrite bet_xxa bet_sym.
case: (b =P q)=> [->|?]; first by exists q; rewrite bet_xxa bet_axx.
case: (q =P c)=> [->|?]; first by exists p; rewrite bet_xxa bet_sym.
have: (  (bet a b c \/ bet b c a \/ bet c a b) \/
       ~ (bet a b c \/ bet b c a \/ bet c a b)).
  by case: (bet a b c); case: (bet b c a); case: (bet c a b); intuition.
suff: (forall a b c p q, bet a b c -> a <> p -> p <> c -> b <> q -> q <> c ->
                         bet a p c -> bet b q c ->
                         exists x, bet p x b /\ bet q x a).
  move=> H [[?|[?|?]]|?] ? ?; [..|by apply inner_pasch with c];
  [apply (H a b c p q)|exists c|destruct (H b a c q p) as [x []]]=> //;
  [split| |by exists x; split]; rewrite bet_sym //;
  [apply bet_inner_transitivity with a|apply bet_inner_transitivity with b];
  by rewrite // bet_sym.
clear dependent p; clear dependent q; clear a b c=> a b c p q Hb1 Hc1 Hc2.
rewrite bet_betS //; clear Hc1 Hc2 => Hc1 Hc2 Hb2; rewrite bet_betS //.
clear Hc1 Hc2; move: Hb1 Hb2; case: (a =P q)=> [-> ? Hb1 Hb2|?].
  exists q; rewrite bet_axx; split; rewrite // bet_sym.
  by apply bet_inner_transitivity with c; rewrite /bet ?Hb1 ?Hb2 orbT.
case: (b =P p)=> [-> ? ? Hb|? _ ? ?];
last by destruct (@inner_pasch'' a b c p q) as [x [Hb1 Hb2]];
[..|exists x; split]; rewrite // /bet ?Hb1 ?Hb2 orbT.
exists p; split; rewrite ?bet_axx // bet_sym.
by apply bet_inner_transitivity with c; rewrite // /bet Hb orbT.
Qed.

Lemma bet_colF a b c :
  bet a b c -> ~ (bet b a c \/ bet a c b \/ bet c b a) -> False.
Proof.
by move=> /bet_symmetry Hb Hnb; exfalso; apply Hnb; rewrite Hb; right; right.
Qed.

Lemma euclid'' a b c d k1 (k2 := betR b d c) :
  0 < k1 -> k1 < 1 -> bet b d c -> b != c ->
  bet (extension a b k1) (extension a d k1) (extension a c k1).
Proof.
set x:= extension a b k1; set t:= extension a d k1; set y:= extension a c k1.
move=> k1_gt0 k1_lt1 bet_bdc bc_neq; have: (k1 != 0) by rewrite lt0r_neq0.
move=> k1_neq0; move: bet_bdc; rewrite /bet /betE !extension_eq ?k1_neq0 //.
case (b =P d); [rewrite orbT //|]; case (d =P c) ; [rewrite orbT //|rewrite /=].
move=> _ _ /betSP[P1 k2_gt0 k2_lt1]; rewrite /betS.
suff: (t - x == k2 *: (y - x))=> [/eqP P2|]; [suff: (betR x t y = k2)=> [->|]|].
    by rewrite P2 k2_gt0 k2_lt1 eqxx.
  by apply ratio_eq; rewrite ?P2 ?eqxx // subr_eq0 extension_eq // eq_sym.
rewrite /x /t /y /extension addrDBD -scalerBr opprB addrBDB addrDBD -scalerBr.
by rewrite opprB addrBDB scalerA mulrC -scalerA P1 eqxx.
Qed.

Lemma euclid' a b c d t (k1 := betR a d t) (k2 := betR b d c) :
  betS a d t -> bet b d c ->
  exists x y, bet a b x /\ bet a c y /\ bet x t y.
Proof.
case: (b =P c)=> [-> betS_adt|/eqP bc_neq betS_adt bet_bdc].
  by rewrite bet_xax=> /eqP ->; exists t, t; rewrite bet_xxa /bet betS_adt orbT.
set x:=extension a b k1; set y:=extension a c k1; exists x, y.
have: (t == extension a d k1); [|move/betSP: betS_adt =>[_ k1_gt0 k1_lt1]].
  move: betS_adt; rewrite betS_neq12 /betS /betR=> /andP[/andP[/eqP ? _] ?].
  by apply /eqP; rewrite /k1 /betR extensionP.
by move=> /eqP t_def; rewrite !extension_bet // t_def /x /y euclid''.
Qed.

Lemma euclid a b c d t (k1 := betR a d t) (k2 := betR b d c) :
  bet a d t -> bet b d c -> b <> d -> d <> c ->
  ~ (bet a b c \/ bet b c a \/ bet c a b) ->
  exists x y, bet a b x /\ bet a c y /\ bet x t y.
Proof.
move=> /orP[/betEP[[->->]|->|->] b2 _ _ H|]; try solve[by apply bet_colF in H];
[exists b,c|move=> b1 b2 _ _ _]; by [rewrite !bet_axx|move: b2; apply euclid'].
Qed.

Lemma betS_ratio a b c (r := betR a b c) :
  betS a b c -> c - b = ((1 - r) / r) *: (b - a).
Proof.
rewrite /r; move=> /betSP[]; move: (betR a b c) => k /eqP + k_gt0 _.
by rewrite subr_eq => /eqP ->; rowE; field; rewrite lt0r_neq0.
Qed.

Lemma betS_gt0 a b c (r := betR a b c) :
  betS a b c -> 0 < (1 - r) / r.
Proof. by move=> /betSP[? ? ?]; rewrite divr_gt0 /r ?subr_gt0. Qed.

Lemma bet_cong_ratio_eq a b c a' b' c' (r := betR a b c) (r' := betR a' b' c') :
  betS a b c -> betS a' b' c' ->
  cong b a b' a' -> cong b c b' c' ->
  (1 - r) / r = (1 - r') / r'.
Proof.
move=> b1 b2; have ab_neq0 : '[a - b] != 0.
  by rewrite dot2_eq0 subr_eq0; move: b1; rewrite betS_neq12 => /andP[].
rewrite /cong (betS_ratio b1) (betS_ratio b2) => /eqP c1.
rewrite !dotZl !dotZr -[b - a]opprB -[b' - a']opprB !dot2N -c1 -/r -/r'.
set s := (1 - r) / r; set s' := (1 - r') / r'.
rewrite (mulrA s) (mulrA s') (inj_eq (mulIf ab_neq0)) -!expr2 eqf_sqr.
case/orP => /eqP // E; have := addr_gt0 (betS_gt0 b1) (betS_gt0 b2).
by rewrite -/r -/r' -/s -/s' E addNr ltxx.
Qed.

Lemma betS_dot2 (x y z w : 'rV[R]_n) (s := (1 - betR x y z) / betR x y z) :
  betS x y z ->
  '[w - z] = '[w - y] + s ^+ 2 * '[y - x] -
             s * ('[w - x] - '[w - y] - '[y - x]).
Proof.
move=> /betS_ratio zyE.
have -> : w - z = (w - y) - (z - y) by rewrite opprB subrKA.
have -> : w - x = (w - y) + (y - x) by rewrite subrKA.
by rewrite (dot2B (w - y)) (dot2D (w - y)) zyE dotZl !dotZr -/s; ring.
Qed.

Lemma five_segment a a' b b' c c' d d' :
  cong a b a' b' -> cong b c b' c' -> cong a d a' d' -> cong b d b' d' ->
  bet a b c -> bet a' b' c' -> a <> b -> cong c d c' d'.
Proof.
move=> c1 c2 c3 c4 bet1 bet2 ab_neq.
have [bc_eq|bc_neq] := eqVneq b c.
  by move: c2; rewrite -bc_eq => /cong_eq' <-.
have [b'c'_eq|b'c'_neq] := eqVneq b' c'.
  by move: c2 bc_neq; rewrite -b'c'_eq => /cong_identity ->; rewrite eqxx.
have a'b'_neq : a' <> b'.
  by move=> a'b'_eq; move: c1; rewrite a'b'_eq => /cong_identity.
have b1 : betS a b c by rewrite -bet_betS //; apply/eqP.
have b2 : betS a' b' c' by rewrite -bet_betS //; apply/eqP.
have c1' : cong b a b' a' by rewrite congC.
move: c1 c3 c4; rewrite /cong (betS_dot2 d b1) (betS_dot2 d' b2).
by rewrite (bet_cong_ratio_eq b1 b2 c1' c2) => /eqP-> /eqP-> /eqP->.
Qed.

Definition midpoint a b := 2%:R^-1 *: (a + b).

Lemma midpointLR a b : midpoint a b = midpoint b a.
Proof. by rewrite /midpoint addrC. Qed.

Lemma midpointBL a b : midpoint a b - a = 2%:R^-1 *: (b - a).
Proof. by rowE; field. Qed.

Lemma midpointBR a b : midpoint a b - b = 2%:R^-1 *: (a - b).
Proof. by rewrite midpointLR midpointBL. Qed.

Lemma midpointxx a : midpoint a a = a.
Proof. by rowE; field. Qed.

Lemma betS_midpoint a b : a != b -> betS a (midpoint a b) b.
Proof.
move=> ab_neq; apply: (betS_intro (r := 2%:R^-1)) => //.
- by rewrite invr_gt0 ltr0n.
- by rewrite invf_lt1 ?ltr0n // ltr1n.
- exact: midpointBL.
Qed.

Lemma bet_midpoint a b : bet a (midpoint a b) b.
Proof.
have [<-|ab_neq] := eqVneq a b; first by rewrite midpointxx bet_axx.
by rewrite /bet betS_midpoint ?orbT.
Qed.

Lemma cong_midpoint a b : cong a (midpoint a b) b (midpoint a b).
Proof. by rewrite /cong midpointBL midpointBR -opprB scalerN dot2N. Qed.

Lemma point_equality_decidability a b : a = b \/ ~ a = b.
Proof. by case: (a =P b); tauto. Qed.

Lemma onemx_neq0 : const_mx 0 != const_mx 1 :> 'rV[R]_n.+1.
Proof. by apply/eqP=> /matrixP/(_ 0 0)/eqP; rewrite !mxE eq_sym oner_eq0. Qed.

End TarskiGe1.

Arguments onemx_neq0 {R n}.

Section Tarski2D.

Variable R : realFieldType.

Implicit Types (a b c d : 'rV[R]_2).

Lemma ord2_ind (P : 'I_2 -> Prop) : P 0 -> P 1 -> forall i, P i.
Proof.
move=> P0 P1 [[|[|//]] i_lt2].
  by rewrite (@ord_inj _ (Ordinal i_lt2) 0).
by rewrite (@ord_inj _ (Ordinal i_lt2) 1).
Qed.

Lemma vector2_eq a b : a == b = (a 0 0 == b 0 0) && (a 0 1 == b 0 1).
Proof.
apply/eqP/andP => [->|[/eqP eq0 /eqP eq1]]; first by rewrite !eqxx.
by apply/rowP; apply: ord2_ind.
Qed.

Lemma vector2_eq0 (v : 'rV[R]_2) : (v == 0) = (v 0 0 == 0) && (v 0 1 == 0).
Proof. by rewrite vector2_eq !mxE. Qed.

Lemma vector2_neq0 (v : 'rV[R]_2) : (v != 0) = (v 0 0 != 0) || (v 0 1 != 0).
Proof. by rewrite vector2_eq0 negb_and. Qed.

Definition sqr_L2_norm_2D a b :=
  (b 0 0 - a 0 0) ^+ 2 + (b 0 1 - a 0 1) ^+ 2.

Lemma dot2_2D (v : 'rV[R]_2) : '[v] = v 0 0 ^+ 2 + v 0 1 ^+ 2.
Proof.
rewrite dotE mxE !big_ord_recr /= big_ord0 add0r !mxE -!expr2.
by congr (v 0 _ ^+ 2 + v 0 _ ^+ 2); apply: val_inj.
Qed.

Lemma congP_aux' a b : (b - a) *m (b - a)^T = (sqr_L2_norm_2D a b)%:M.
Proof. by rewrite mulmx_tr dot2_2D !mxE. Qed.

Lemma congP_aux a b c d :
  cong a b c d = (sqr_L2_norm_2D a b == sqr_L2_norm_2D c d).
Proof. by rewrite /cong !dot2_2D !mxE. Qed.

Lemma congP a b c d :
  reflect (sqr_L2_norm_2D a b = sqr_L2_norm_2D c d) (cong a b c d).
Proof. by rewrite congP_aux; exact: eqP. Qed.

Lemma betSP' a b c (r := betR a b c) :
  reflect ([ /\ b 0 0 - a 0 0 = r * (c 0 0 - a 0 0),
               b 0 1 - a 0 1 = r * (c 0 1 - a 0 1), 0 < r & r < 1])
          (betS a b c).
Proof.
rewrite /betS -/r vector2_eq !mxE -andbA.
apply: (iffP and4P) => [[/eqP e0 /eqP e1 r_gt0 r_lt1]|[e0 e1 r_gt0 r_lt1]].
  by split.
by rewrite e0 e1 !eqxx r_gt0 r_lt1.
Qed.

Lemma col_2D_scale a b c :
  (b 0 0 - a 0 0) * (c 0 1 - a 0 1) = (b 0 1 - a 0 1) * (c 0 0 - a 0 0) ->
  a != c -> exists r, b - a = r *: (c - a).
Proof.
move=> E; rewrite eq_sym -subr_eq0 vector2_neq0 !mxE => /orP[N0|N1].
  exists ((b 0 0 - a 0 0) / (c 0 0 - a 0 0)); apply/rowP; apply: ord2_ind.
    by rewrite !mxE divfK.
  by rewrite !mxE mulrAC E mulfK.
exists ((b 0 1 - a 0 1) / (c 0 1 - a 0 1)); apply/rowP; apply: ord2_ind.
  by rewrite !mxE mulrAC -E mulfK.
by rewrite !mxE divfK.
Qed.

Lemma col_2D a b c :
  (a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0) ->
  bet a b c \/ bet b c a \/ bet c a b.
Proof.
move=> /eqP E.
have [<-|ab_neq] := eqVneq a b; first by left; rewrite bet_xxa.
have [<-|bc_neq] := eqVneq b c; first by left; rewrite bet_axx.
have [<-|ac_neq] := eqVneq a c; first by right; left; rewrite bet_axx.
have [r baE] : exists r, b - a = r *: (c - a).
  apply: col_2D_scale => //; apply/eqP; rewrite -subr_eq0; apply/eqP.
  transitivity ((a 0 0 - b 0 0) * (b 0 1 - c 0 1) -
                (a 0 1 - b 0 1) * (b 0 0 - c 0 0)); first by ring.
  by rewrite E subrr.
have r_neq0 : r != 0.
  apply: contraNneq ab_neq => r0.
  by rewrite eq_sym -subr_eq0 baE r0 scale0r.
have r_neq1 : r != 1.
  apply: contraNneq bc_neq => r1.
  have -> : b = (b - a) + a by rewrite subrK.
  by rewrite baE r1 scale1r subrK.
have [r_lt0|r_ge0] := ltP r 0.
  right; right; apply/orP; right.
  apply: (betS_intro (r := (1 - r)^-1)); rewrite 1?eq_sym //.
  - by rewrite invr_gt0 subr_gt0 (lt_trans r_lt0) ?ltr01.
  - by rewrite invf_lt1 ?subr_gt0 ?(lt_trans r_lt0) ?ltr01 // ltrDl oppr_gt0.
  move/eqP: baE; rewrite subr_eq => /eqP ->.
  by rowE; field; rewrite subr_eq0 eq_sym.
have r_gt0 : 0 < r by rewrite lt_neqAle eq_sym r_neq0.
have [r_lt1|r_ge1] := ltP r 1.
  by left; apply/orP; right; apply: (betS_intro ac_neq r_gt0 r_lt1).
have r_gt1 : 1 < r by rewrite lt_neqAle eq_sym r_neq1.
right; left; rewrite bet_sym; apply/orP; right.
apply: (betS_intro (r := r^-1)) => //.
- by rewrite invr_gt0.
- by rewrite invf_lt1.
- by rewrite baE scalerA mulVf ?scale1r.
Qed.

Lemma col_2D' a b c : (bet a b c \/ bet b c a \/ bet c a b) ->
  (a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0).
Proof.
move=> [|[]] /bet_scale [r /eqP]; rewrite subr_eq => /eqP ->;
by rewrite !mxE; apply/eqP; ring.
Qed.

Lemma cong_col_2D a b c p q :
  p <> q -> cong a p a q -> cong b p b q -> cong c p c q ->
  (a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0).
Proof.
move=> /eqP; rewrite vector2_eq negb_and !congP_aux /sqr_L2_norm_2D.
move=> pq_neq /eqP Ha /eqP Hb /eqP Hc.
set w0 := p 0 0 - q 0 0; set w1 := p 0 1 - q 0 1.
set X0 := a 0 0 - b 0 0; set X1 := a 0 1 - b 0 1.
set Y0 := b 0 0 - c 0 0; set Y1 := b 0 1 - c 0 1.
have EX : w0 * X0 + w1 * X1 = 0 by rewrite /w0 /w1 /X0 /X1; lra.
have EY : w0 * Y0 + w1 * Y1 = 0 by rewrite /w0 /w1 /Y0 /Y1; lra.
rewrite -subr_eq0; apply/eqP.
case/orP: pq_neq => [w0_neq0|w1_neq0].
  apply: (mulfI (_ : w0 != 0)); first by rewrite subr_eq0.
  rewrite mulr0;
  transitivity (Y1 * (w0 * X0 + w1 * X1) - X1 * (w0 * Y0 + w1 * Y1)).
    by ring.
  by rewrite EX EY !mulr0 subrr.
apply: (mulfI (_ : w1 != 0)); first by rewrite subr_eq0.
rewrite mulr0.
transitivity (X0 * (w0 * Y0 + w1 * Y1) - Y0 * (w0 * X0 + w1 * X1)).
  by ring.
by rewrite EX EY !mulr0 subrr.
Qed.

Lemma upper_dim a b c p q :
  p <> q -> a <> b -> a <> c -> b <> c ->
  cong a p a q -> cong b p b q -> cong c p c q ->
  (bet a b c \/ bet b c a \/ bet c a b).
Proof. by move=> pq_neq _ _ _ Ha Hb Hc; apply/col_2D/(cong_col_2D pq_neq). Qed.

Definition row2 {R : ringType} (a b : R) : 'rV[R]_2 :=
  \row_p [eta \0 with 0 |-> a, 1 |-> b] p.

Definition a2D : 'rV[R]_2 := row2 0 0.
Definition b2D : 'rV[R]_2 := row2 0 1.
Definition c2D : 'rV[R]_2 := row2 1 0.

Variable n : nat.

Definition to_nD (v : 'rV[R]_2) : 'rV[R]_(2 + n) :=
  row_mx v (@const_mx R 1 n 0).

Definition a := to_nD a2D.
Definition b := to_nD b2D.
Definition c := to_nD c2D.

Lemma row2_eq (a b c d : R) : row2 a b == row2 c d = ((a == c) && (b == d)).
Proof. by rewrite vector2_eq !mxE. Qed.

Lemma row2_eq_nD (a b c d : R) :
  (row_mx (row2 a b) (@const_mx R 1 n 0) ==
   row_mx (row2 c d) (@const_mx R 1 n 0)) = ((a == c) && (b == d)).
Proof.
rewrite -subr_eq0 opp_row_mx add_row_mx subrr.
by rewrite row_mx_eq0 eqxx andbT subr_eq0 row2_eq.
Qed.

Lemma row2_eq0 (a b : R) : row2 a b == 0 = ((a == 0) && (b == 0)).
Proof. by rewrite vector2_eq0 !mxE. Qed.

Lemma row2_eq0_nD (a b : R) :
  (row_mx (row2 a b) (@const_mx R 1 (n.+2) 0) == 0) = ((a == 0) && (b == 0)).
Proof. by rewrite row_mx_eq0 eqxx andbT row2_eq0. Qed.

Lemma a2D_eq0 : a2D = 0.
Proof. by rewrite /a2D; apply /eqP; rewrite row2_eq0 eqxx. Qed.

Lemma a_eq0 : a = 0.
Proof. by rewrite /a /to_nD a2D_eq0 row_mx_const. Qed.

Lemma b2D_neq0 : b2D != 0.
Proof. by rewrite /b2D row2_eq0 eqxx oner_eq0. Qed.

Lemma b_neq0 : b != 0.
Proof. by rewrite /b /to_nD row_mx_eq0 negb_and b2D_neq0. Qed.

Lemma c2D_neq0 : c2D != 0.
Proof. by rewrite /c2D row2_eq0 eqxx oner_eq0. Qed.

Lemma c_neq0 : c != 0.
Proof. by rewrite /c /to_nD row_mx_eq0 negb_and c2D_neq0. Qed.

Lemma ab_neq_2D : a2D == b2D = false.
Proof. by rewrite row2_eq eqxx /= eq_sym oner_eq0. Qed.

Lemma ab_neq : a == b = false.
Proof.
by rewrite /a /b -subr_eq0 opp_row_mx add_row_mx row_mx_eq0 subr_eq0 ab_neq_2D.
Qed.

Lemma bc_neq_2D : b2D == c2D = false.
Proof. by rewrite row2_eq oner_eq0 andbC. Qed.

Lemma bc_neq : b == c = false.
Proof.
by rewrite /b /c -subr_eq0 opp_row_mx add_row_mx row_mx_eq0 subr_eq0 bc_neq_2D.
Qed.

Lemma ca_neq_2D : c2D == a2D = false.
Proof. by rewrite row2_eq oner_eq0. Qed.

Lemma ca_neq : c == a = false.
Proof.
by rewrite /c /a -subr_eq0 opp_row_mx add_row_mx row_mx_eq0 subr_eq0 ca_neq_2D.
Qed.

Lemma betR_abc : betR a b c = 0.
Proof.
rewrite a_eq0 /b /c /betR /ratio; case: pickP => /= [x|all_v_neq0 //].
rewrite !subr0 /b /c /to_nD /row_mx !mxE; case: (split x)=> [x0|x1];
by rewrite ?mxE ?eqxx //; case: x0 => [] [|[|//]] p /=; rewrite ?divr1 ?eqxx.
Qed.

Lemma betR_bca : betR b c a = 1.
Proof.
rewrite /b /c a_eq0 /betR /ratio add0r; case: pickP => /= [x|/all_v_neq0 H];
last by exfalso; apply H; rewrite oppr_eq0 b_neq0.
rewrite /to_nD /row_mx !mxE; case: (split x)=> [x0|x1]; rewrite ?mxE ?oppr_eq0;
rewrite ?eqxx //; case: x0 => [] [|[|//]] p /=; rewrite ?eqxx //.
by rewrite sub0r divff ?eqxx // oppr_eq0 oner_eq0.
Qed.

Lemma betR_cab : betR c a b = 0 \/ betR c a b = 1.
Proof.
rewrite /c a_eq0 /b /betR /ratio add0r; case: pickP => /= [x|/all_v_neq0 H];
last by exfalso; apply H; rewrite subr_eq0 bc_neq.
rewrite /to_nD /row_mx !mxE; case: (split x)=> [x0|x1]; rewrite ?mxE ?subrr;
rewrite ?eqxx //; case: x0 => [] [|[|//]] p /=; rewrite ?add0r ?subr0 ?divr1;
by rewrite ?oppr0 ?divff ?oppr_eq0 ?oner_eq0; tauto.
Qed.

Lemma lower_dim : ~ (bet a b c \/ bet b c a \/ bet c a b).
Proof.
move=> H; move: H; rewrite /bet /betE ab_neq bc_neq ca_neq /=.
rewrite /betS betR_abc betR_bca; elim (betR_cab)=> [->|->]; rewrite !ltxx ltr01;
by rewrite /= ![_ && false]andbC /=; firstorder.
Qed.

End Tarski2D.

Section RcfTarski.

Variable R : rcfType.
Variable n : nat.

Implicit Types (a b c d : 'rV[R]_n).

Definition normv (x : 'rV[R]_n) : R := Num.sqrt ((x *m x^T) 0 0).

Lemma segment_construction a b c d :
    exists e, bet a b e /\ cong b e c d.
Proof.
have [->|ba_neq] := eqVneq b a.
  exists ((c - d) + a); split; first by rewrite /bet betE_xxa.
  by rewrite /cong addrK -opprB dot2N.
have [->|dc_neq] := eqVneq d c.
  by exists b; rewrite /bet /cong betE_axx !subrr.
have norm_gt0 x y : x != y -> 0 < normv (x - y).
  by rewrite -subr_eq0 => ?; rewrite sqrtr_gt0 -dotE dot2_gt0.
pose k := normv (d - c) / normv (b - a).
have k_gt0 : 0 < k by rewrite divr_gt0 ?norm_gt0.
exists (k *: (b - a) + b); split; last first.
  rewrite /cong addrK dotZl dotZr mulrA -expr2 expr_div_n /normv -!dotE.
  rewrite !sqr_sqrtr ?dot2_ge0 // divfK //.
  by rewrite dot2_eq0 subr_eq0.
apply/orP; right; apply: (betS_intro12 (r := (1 + k)^-1)); rewrite 1?eq_sym //.
- by rewrite invr_gt0 addr_gt0.
- by rewrite invf_lt1 ?addr_gt0 // ltrDl.
- by rowE; field; rewrite lt0r_neq0 // addr_gt0.
Qed.

End RcfTarski.

Section Rcf_to_independent_Tarski_nD_euclidean.

Variable R : rcfType.
Variable n : nat.

Global Instance Rcf_to_GI_PED :
  Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality.
Proof.
exact
(Build_Gupta_inspired_variant_of_Tarski_neutral_dimensionless_with_decidable_point_equality
   'rV[R]_(n.+2) (@bet R (n.+2)) (@cong R (n.+2))
   (@point_equality_decidability R (n.+2))
   (@cong_pseudo_reflexivity R (n.+2)) (@cong_inner_transitivity R (n.+2))
   (@cong_identity R (n.+2))
   (@segment_construction R (n.+2)) (@five_segment R (n.+2))
   (@bet_symmetry R (n.+2)) (@bet_inner_transitivity R (n.+2))
   (@inner_pasch R (n.+2))
   (@a R n) (@b R n) (@c R n)
   (@lower_dim R n)).
Defined.

Global Instance Rcf_to_T : Tarski_neutral_dimensionless.
Proof. apply GI_to_T. Defined.

Global Instance Rcf_to_T_PED :
  Tarski_neutral_dimensionless_with_decidable_point_equality Rcf_to_T.
Proof. split; exact (@point_equality_decidability R (n.+2)). Defined.

Global Instance Rcf_to_GI_euclidean :
  Gupta_inspired_variant_of_Tarski_euclidean Rcf_to_GI_PED.
Proof. split; exact (@euclid R (n.+2)). Defined.

Global Instance Rcf_to_T_euclidean : Tarski_euclidean Rcf_to_T_PED.
Proof. split; exact euclidT. Defined.

Implicit Types (a b c d p q : 'rV[R]_(n.+2)).

Lemma Midpoint_midpoint a b : @Definitions.Midpoint Rcf_to_T (midpoint a b) a b.
Proof.
split; first exact: bet_midpoint.
suff: cong a (midpoint a b) (midpoint a b) b by [].
by rewrite /cong -[b - midpoint a b]opprB dot2N; apply: cong_midpoint.
Qed.

Definition colI a b c := ~ (~ bet a b c /\ ~ bet b c a /\ ~ bet c a b).

Definition inplane p a b c := exists q, colI a b q /\ colI c p q.

Definition cop a b c d := exists e f g,
  ~ colI e f g /\ inplane a e f g /\ inplane b e f g /\
                 inplane c e f g /\ inplane d e f g.

Lemma Bet_bet p q r : Bet p q r = bet p q r.
Proof. by []. Qed.

Lemma Col_colI p q r : Col p q r <-> colI p q r.
Proof.
rewrite /Col /colI !Bet_bet.
by case: (bet p q r); case: (bet q r p); case: (bet r p q); intuition.
Qed.

Lemma tcp a b c :
  ~ colI a b c -> exists x, cong a x b x /\ cong a x c x /\ cop a b c x.
Proof.
cut (triangle_circumscription_principle); [|have: tarski_s_parallel_postulate].
    move=> HP HNC1; destruct (HP a b c) as [x [HC1 [HC2 HCop]]]; [|exists x].
      by move: HNC1; rewrite /Col /colI; intuition.
    split; [|split]; [intuition..|move: HCop; rewrite -Cop__Coplanar].
    move => [e [f [g [HNC2 [[iaP aP] [[ibP bP] [[icP cP] [ixP xP]]]]]]]].
    rewrite !Col_colI in HNC2 aP bP cP xP.
    exists e, f, g; split; first by [].
    split; first by exists iaP.
    split; first by exists ibP.
    split; first by exists icP.
    by exists ixP.
  by unfold tarski_s_parallel_postulate; apply euclidT.
apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
simpl; tauto.
Qed.

Definition col a b c := bet a b c \/ bet b c a \/ bet c a b.

Lemma col__colI a b c : col a b c <-> colI a b c.
Proof.
split=> [[H|[H|H]] [H1 [H2 H3]]|H]; [exact: H1 H|exact: H2 H|exact: H3 H|].
case Hb1: (bet a b c); first by left.
case Hb2: (bet b c a); first by right; left.
case Hb3: (bet c a b); first by right; right.
by exfalso; apply: H; rewrite Hb1 Hb2 Hb3.
Qed.

Definition coplanar a b c d :=
  exists x, (col a b x /\ col c d x) \/
            (col a c x /\ col b d x) \/
            (col a d x /\ col b c x).

Definition par_strict a b c d :=
  coplanar a b c d /\ ~ exists x, col x a b /\ col x c d.

Definition par a b c d :=
  par_strict a b c d \/ (a <> b /\ c <> d /\ col a c d /\ col b c d).

Lemma proclus a b c d p q :
  par a b c d -> col a b p -> ~ col a b q -> coplanar c d p q ->
  exists y, col p q y /\ col c d y.
Proof.
cut (proclus_postulate); [move => HP HPar HC HNC HCop|]; last first.
have: tarski_s_parallel_postulate.
  by unfold tarski_s_parallel_postulate; apply euclidT.
apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
simpl; tauto.
destruct (HP a b c d p q) as [x []]; [..|exists x]; [|intuition..].
move: HPar => {HC HNC HCop} [HParS|]; [left|right; intuition].
move: HParS => [HCop HNI]; split; [intuition|].
by move => [x [? ?]]; apply HNI; exists x; intuition.
Qed.

End Rcf_to_independent_Tarski_nD_euclidean.

Section Rcf_to_independent_Tarski_2D.

Variable R : rcfType.

Global Instance Rcf_to_GI2D :
  Gupta_inspired_variant_of_Tarski_2D (@Rcf_to_GI_PED R 0).
Proof. split; exact (@upper_dim R). Defined.

Global Instance Rcf_to_T2D : Tarski_2D (@Rcf_to_T_PED R 0).
Proof. split; exact upper_dimT. Defined.

End Rcf_to_independent_Tarski_2D.