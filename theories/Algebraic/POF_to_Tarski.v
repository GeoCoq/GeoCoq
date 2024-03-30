Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype seq order.
From mathcomp
Require Import fintype bigop.
From mathcomp
Require Import ssralg ssrnum matrix.
From mathcomp
Require Import zmodp.

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

Reserved Notation "'[ u , v ]"
  (at level 2, format "'[hv' ''[' u , '/ '  v ] ']'").
Reserved Notation "'[ u ]" (at level 2, format "''[' u ]").

Local Definition dot (R : realFieldType) n (u v : 'rV[R]_n) : R := (u *m v^T) 0 0.
Arguments dot R n : clear implicits.

Local Notation "''[' u , v ]" := (dot _ _ u v) : ring_scope.
Local Notation "''[' u ]" := '[u, u]%R : ring_scope.

Section Aux.

Definition andb_assoc := Bool.andb_assoc.

Variable R : realFieldType.
Variable n : nat.

Implicit Types (v : 'rV[R]_n).

Lemma dotE v1 v2 : '[v1, v2] = (v1 *m v2^T) 0 0. Proof. by []. Qed.
Lemma mulmx_tr v1 v2 : v1 *m v2^T = '[v1, v2]%:M.
Proof. by apply/matrixP=> i j; rewrite !ord1 -mx11_scalar. Qed.

(* generalize to any matrix *)
Lemma funmxN (v : 'rV[R]_n) j : (- v) 0 j = - v 0 j.
Proof. by rewrite !mxE. Qed.

(* TODO change naming (no "pick") suggestion oppmx_eq0 *)
Lemma eq_pick_neq0 v k : (v 0 k != 0) = ((- v) 0 k != 0).
Proof. by rewrite funmxN oppr_eq0. Qed.

(* keep only one of these *)
Lemma dot2_eq0 v : ('[v] == 0) = (v == 0).
Proof.
rewrite /dot; apply/eqP/eqP => [/eqP|->]; last by rewrite mul0mx mxE /=.
rewrite !mxE psumr_eq0 /=; last by move=> i _; rewrite mxE sqr_ge0.
move => /allP /= sqp_eq0; apply/rowP => k; rewrite mxE.
by have := sqp_eq0 k; rewrite mem_index_enum !mxE sqrf_eq0 => /(_ isT) /eqP.
Qed.

Lemma quad_eq0' v : ((v *m v^T) 0 0 == 0) = (v == 0).
Proof. by rewrite -dotE dot2_eq0. Qed.

Lemma quad_eq0 v : (v *m v^T == 0) = (v == 0).
Proof.
apply/eqP/eqP => [/matrixP /(_ 0 0) /eqP|->]; last by rewrite mul0mx.
by rewrite [X in _ == X]mxE quad_eq0' => /eqP.
Qed.

(* remove *)
Lemma quad_neq0 v : ((v *m v^T) 0 0 != 0) = (v != 0).
Proof. by rewrite quad_eq0'. Qed.

Lemma dot_ge0 v : 0 <= '[v].
Proof. by rewrite /dot !mxE sumr_ge0 // => i _; rewrite mxE sqr_ge0. Qed.

Lemma quad_ge0 v : 0 <= (v *m v^T) 0 0.
Proof. by rewrite -dotE dot_ge0. Qed.

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

Lemma bet_gt0 (k1 k2 : R) : 0 < k1 -> k2 < 1 -> 0 < k1 - k1 * k2.
Proof. by move=> k1_gt0 k2_lt1; rewrite subr_gt0 gtr_pmulr. Qed.

(* find a name for "thing" and for "stuff" *)
Section thing_and_stuff.
Variables (k1 k2 k3 : R).
Variables (k1_gt0 : k1 > 0) (k2_gt0 : k2 > 0).
Variables (k1_lt1 : k1 < 1) (k3_gt0 : k3 > 0).

Let thing := k1 + k2 - k1 * k2.
Let stuff := thing / k3.

Lemma thing_gt0 : thing > 0.
Proof. by rewrite subr_gt0 ltr_paddl ?ltW// gtr_pmull. Qed.
Hint Resolve thing_gt0: core.

Lemma thing_neq0 : thing != 0. Proof. by rewrite gt_eqF. Qed.

Lemma stuff_gt0 : stuff > 0. Proof. by rewrite divr_gt0. Qed.
Hint Resolve stuff_gt0: core.

Lemma stuff_neq0 : stuff != 0. Proof. by rewrite gt_eqF. Qed.

End thing_and_stuff.

(* most of this can be added to the section about thing and stuff *)
(* naming with ' is not recommended, change all namings *)
Lemma bet_gt0' (k1 k2 k3 : R) :
  0 < k1 -> 0 < k2 -> k1 < 1 -> 0 < k3 -> 0 < ((k1 + k2 - k1 * k2) / k3)^-1.
Proof. by move=> *; rewrite invr_gt0 stuff_gt0. Qed.

(* this is exactly stuff_neq0 *)
Lemma bet_neq0 (k1 k2 k3 : R) :
  0 < k1 -> 0 < k2 -> k1 < 1 -> 0 < k3 -> (k1 + k2 - k1 * k2) / k3 != 0.
Proof. exact: stuff_neq0. Qed.

(* this is exactly thing_neq0 *)
Lemma bet_neq0' (k1 k2 : R) :
   0 < k1 -> 0 < k2 -> k1 < 1 -> k1 + k2 - k1 * k2 != 0.
Proof. exact: thing_neq0. Qed.

Lemma bet_lt (k1 k2 : R) : 0 < k2 -> k1 - k1 * k2 < k1 + k2 - k1 * k2.
Proof. by move=> ?; rewrite -addrA ltr_add2l -{1}[-(k1 * k2)]add0r ltr_add2r. Qed.

(* add this to things about stuff *)
Lemma bet_lt1 (k1 k2 k3 : R) :
  0 < k1 -> 0 < k2 -> k1 < 1 -> 0 < k3 -> k3 < k1 + k2 - k1 * k2 ->
  ((k1 + k2 - k1 * k2) / k3)^-1 < 1.
Proof. by move=> *; rewrite invf_lt1 ?stuff_gt0// ltr_pdivl_mulr ?mul1r. Qed.

(* replace eq_inv_scale by -(can2_eq (scalerK _) (scalerKV _)) *)
Lemma eq_inv_scale (V : lmodType R) (s : R) (x y : V) :
  s != 0 -> (x == s^-1 *: y) = (s *: x == y).
Proof. exact: (fun _ => esym (can2_eq (scalerK _) (scalerKV _) _ _)). Qed.

Lemma eq_div_scale (V : lmodType R) (s1 s2 : R) (x y : V) :
  s2 != 0 -> (x == (s1 / s2) *: y) = (s2 *: x == s1 *: y).
Proof. by move=> s2_neq0; rewrite -scalerA -eq_inv_scale// !scalerA mulrC. Qed.

(* this is an instance of mulrDl *)
Lemma addf_divrr (F : fieldType) (x1 x2 y : F) :
   y != 0 (*useless*) -> x1 / y + x2 / y = (x1 + x2) / y.
Proof. by rewrite mulrDl. Qed.

(* this is the real dotC *)
Lemma dotC' : commutative (dot R n).
Proof.
move=> v1 v2; rewrite dotE; congr (_ _ 0 0).
by rewrite [LHS]mx11_scalar -tr_scalar_mx -mx11_scalar trmx_mul trmxK.
Qed.

Lemma dotC v1 v2 : v1 *m v2^T = v2 *m v1^T.
Proof. by rewrite !mulmx_tr dotC'. Qed.

Lemma dot2D v1 v2 : '[v1 + v2] = '[v1] + '[v2] + '[v1, v2] *+ 2.
Proof.
rewrite !dotE !mulmxDl raddfD/= !mulmxDr [X in _ (_ + X) _ _]addrC addrACA.
by rewrite !mulmx_tr dotC' -mulr2n !mxE.
Qed.

Lemma dotvN v1 v2 : '[v1, - v2] = - '[v1, v2].
Proof. by rewrite !dotE raddfN/= mulmxN !mxE. Qed.

Lemma dotNv v1 v2 : '[- v1, v2] = - '[v1, v2].
Proof. by rewrite !dotE mulNmx !mxE. Qed.

Lemma dot2N v : '[- v] = '[v]. Proof. by rewrite dotvN dotNv opprK. Qed.

Lemma dot2B v1 v2 : '[v1 - v2] = '[v1] + '[v2] - '[v1, v2] *+ 2.
Proof. by rewrite dot2D dot2N dotvN mulNrn. Qed.

(* reuse dot maybe swap the operands in ((v2 - v1) *m (v3 - v1)^T) *)
Lemma cosine_rule v1 v2 v3 :
  (v3 - v2) *m (v3 - v2)^T = (v3 - v1) *m (v3 - v1)^T + (v2 - v1) *m (v2 - v1)^T
                             - 2%:R * ((v2 - v1) *m (v3 - v1)^T).
Proof.
have -> : v3 - v2 = v3 - v1 - (v2 - v1) by rewrite opprB subrKA.
by rewrite !mulmx_tr dot2B !rmorphD rmorphN rmorphMn/= mulr_natl dotC'.
Qed.

(* is this necessary? if so reuse dot *)
Lemma cosine_rule' v1 v2 v3 :
  2%:R * ((v1 - v2) *m (v3 - v1)^T) =
  (v3 - v2) *m (v3 - v2)^T
  - ((v3 - v1) *m (v3 - v1)^T + (v2 - v1) *m (v2 - v1)^T).
Proof.
apply /eqP; rewrite -[v1 - v2]opprB mulNmx mulrN eq_sym subr_eq.
by rewrite [X in _ == X]addrC (cosine_rule v1).
Qed.

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

(* rename to ratioNv *)
Lemma ratioNr v1 v2 : ratio (- v1) v2 = - ratio v1 v2.
Proof.
by rewrite /ratio; case: pickP => [k _|]; rewrite ?oppr0// funmxN mulNr.
Qed.

Lemma ratiorN v1 v2 : ratio v1 (- v2) = - ratio v1 v2.
Proof.
rewrite /ratio; under eq_pick => k do rewrite funmxN oppr_eq0.
by case: pickP => [k _|]; rewrite ?oppr0// funmxN invrN mulrN.
Qed.

Lemma ratioNN v1 v2 : ratio v1 v2 = ratio (- v1) (- v2).
Proof. by rewrite ratioNr ratiorN opprK. Qed.

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

Lemma ratio_bet' v1 v2 k1 :
  0 < k1 -> v1 != v2 -> k1 = ratio (v2 - v1) (k1^-1 *: (v2 - v1)).
Proof.
move=> ? ?; rewrite /ratio. have: (k1^-1 *: (v2 - v1) != 0)
by rewrite scalemx_eq0 negb_or invr_eq0 lt0r_neq0 // subr_eq0 eq_sym.
move=> neq; case: pickP => /=[x px|/all_v_neq0 //].
rewrite !mxE -{1}[(v2 0 x - v1 0 x)]mul1r -mulf_div mulfV;
last by apply /eqP; move=> eq; move/eqP: px; rewrite !mxE eq mulr0.
by rewrite mulr1 -[k1^-1]div1r invf_div divr1 mul1r.
Qed.

Lemma ratio_bet'' v1 v2 k1 :
  0 < k1 -> v1 != v2 -> k1^-1 = ratio (v2 - v1) (k1 *: (v2 - v1)).
Proof.
move=> ? ?; rewrite /ratio. have: (k1 *: (v2 - v1) != 0)
by rewrite scalemx_eq0 negb_or lt0r_neq0 // subr_eq0 eq_sym.
move=> neq; case: pickP => /=[x px|/all_v_neq0 //].
rewrite !mxE -{1}[(v2 0 x - v1 0 x)]mul1r -mulf_div mulfV ?mulr1 ?div1r //.
by apply /eqP; move=> eq; move/eqP: px; rewrite !mxE eq mulr0.
Qed.

Lemma ratio_lt0_v1_neq0 v1 v2 : ratio v1 v2 < 0 -> v1 != 0.
Proof. by case: (v1 =P 0)=> [->|//]; rewrite ratio0p ltxx. Qed.

Lemma ratio_lt0_v2_neq0 v1 v2 : ratio v1 v2 < 0 -> v2 != 0.
Proof. by case: (v2 =P 0)=> [->|//]; rewrite ratiop0 ltxx. Qed.

(* use ^-1 *)
Lemma ratio_inv v1 v2 :
  v1 != 0 -> v2 != 0 -> v1 == ratio v1 v2 *: v2 ->
  ratio v1 v2 = 1 / ratio v2 v1.
Proof.
move=> NE1 NE2 /eqP E; apply /eqP; rewrite eq_sym /ratio {2}E /ratio.
case: pickP=> [x /eqP px|/all_v_neq0 //]; case: pickP=> [y py|/all_v_neq0 //].
rewrite mxE [X in _ / (_ / X)]mulrC -{1}[v2 0 x]mulr1 -mulf_div mulfV ?mul1r;
rewrite ?invf_div //; by apply /eqP=> px'; apply px; rewrite E mxE px' mulr0.
Qed.

End Ratio.

Section TarskiGe1.

Variable R : realFieldType.
Variable n : nat.

Implicit Types (a b c d : 'rV[R]_n).

Definition cong a b c d := (b - a) *m (b - a)^T == (d - c) *m (d - c)^T.

Lemma cong_pseudo_reflexivity a b : cong a b b a.
Proof. by rewrite /cong -opprB linearN mulmxN mulNmx opprK. Qed.

Lemma cong_identity a b c : cong a b c c -> a = b.
Proof. by rewrite /cong subrr linear0 mulmx0 quad_eq0 subr_eq0 => /eqP ->. Qed.

Lemma cong_inner_transitivity a b c d e f :
   cong a b e f -> cong c d e f -> cong a b c d.
Proof. by rewrite /cong => /eqP -> /eqP ->. Qed.

Definition betE a b c := [ || [ && a == b & b == c ], a == b | b == c ].

Lemma betEP a b c :
  reflect ([ \/ [ /\ a = b & b = c ], a = b | b = c ]) (betE a b c).
Proof.
by rewrite /betE; case: (a =P b)=>[->|?]; case: (b =P c)=>[->|?]=> /=;
constructor; [apply Or32|apply Or32|apply Or33|]=> //; case=> [[? ?]|?|?].
Qed.

Lemma betE_sym a b c : betE a b c = betE c b a.
Proof. by rewrite /betE !Bool.orb_assoc eq_sym andbC eq_sym orbAC. Qed.

Definition betR a b c := ratio (b - a) (c - a).

Definition betS a b c (r := betR a b c) :=
  [ && b - a == r *: (c - a), 0 < r & r < 1].

Lemma betSP a b c (r := betR a b c) :
  reflect ([ /\ b - a = r *: (c - a), 0 < r & r < 1 ]) (betS a b c).
Proof.
rewrite /betS -/r; case: (b - a =P r*:(c - a))=> [<-|/=]; last by constructor; case.
by case: (0 < r); case: (r < 1)=> /=; constructor; try (case=> //).
Qed.

Lemma betS_sym a b c : betS a b c = betS c b a.
Proof.
rewrite /betS /betR !andb_assoc -(addrBDB b c a) -[c - a]opprB ratiorN oppr_gt0.
case (a - c =P 0)=> [->|/eqP ?]; first by rewrite !ratiop0 ltxx !andbF.
rewrite -add_ratio ?ratioNr ?ratiovv // andbAC subr_lt0 ltr_oppl ltr_subr_addl.
by rewrite scaleNr -scalerN scalerBl scale1r -subr_eq !opprB !addrBDB subrr.
Qed.

Definition bet a b c := betE a b c || betS a b c.

Lemma bet_sym a b c : bet a b c = bet c b a.
Proof. by rewrite /bet betE_sym betS_sym. Qed.

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

Lemma bet_ratio a b k1 : 0 < k1 -> k1 < 1 -> bet a b (k1^-1 *: (b - a) + a).
Proof.
case: (a =P b)=> [->|/eqP neq_ab L G]; rewrite ?bet_xxa // /bet /betS /betR.
apply /orP; right; rewrite -addrA subrr addr0 -ratio_bet' //.
by rewrite scalerA mulfV ?lt0r_neq0 // scale1r L G eqxx !andbb.
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
suffices: (k*:(k^-1 *: (y - x) + x) == k*:z) = (k^-1 *: (y - x) + x == z).
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
  have: (k < 1)=> [|k_lt1]; first by apply: (@lt_trans _ _ 0); rewrite ?ltr01 //.
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

Lemma ratio_betS a b c k1 k2 k3 :
  a != b -> 0 < k1 -> 0 < k2 -> k1 < 1 -> 0 < k3 -> k3 < k1 + k2 - k1 * k2 ->
  b - a == ((k1 + k2 - k1 * k2) / k3)^-1 *: (c - a) -> betS a b c.
Proof.
move=> H ? ? ? ? ?; rewrite /betS/ betR; move: H. case: (a =P c)=> [->|];
rewrite ?subrr ?scaler0 ?subr_eq0; [by move=> /eqP HF /eqP H; rewrite H in HF|].
move=> ? /eqP ? k3_eq. suff: (ratio (b - a) (c - a) = ((k1 + k2 - k1 * k2) / k3)^-1).
  by move=> ->; rewrite bet_gt0' ?bet_lt1 // k3_eq.
by apply ratio_eq => //; rewrite subr_eq0 eq_sym; apply /eqP.
Qed.

Lemma ratio_bet a b c k1 k2 k3 :
  0 < k1 -> 0 < k2 -> k1 < 1 -> 0 < k3 -> k3 < k1 + k2 - k1 * k2 ->
  b - a == ((k1 + k2 - k1 * k2) / k3)^-1 *: (c - a) -> bet a b c.
Proof.
move=> L1 L2 L3 L4 L5; rewrite /bet /betE. case: (a =P b)=> [->|/eqP ab_neq].
  have: (0 < k1 + k2 - k1 * k2)=> [|L6]; first by rewrite (lt_trans L4).
  rewrite subrr eq_sym scalemx_eq0 subr_eq0 [c == b]eq_sym => /orP[HF|-> //].
  rewrite lt0r in L4; rewrite lt0r in L6; move: HF L4 L6.
  by rewrite invr_eq0 mulf_eq0 invr_eq0 => /orP[/eqP->|/eqP->]; rewrite eqxx.
by move=> ?; apply /orP; right; apply (ratio_betS ab_neq L1 L2 L3 L4).
Qed.

Lemma betS_inner_transitivity a b c d (k1 := betR a b d) (k2 := betR b c d) :
  betS a b d -> betS b c d -> betS a b c.
Proof.
rewrite betS_neq12=> /andP[/betSP[k1P ? ?] ?] /betSP[k2P ? ?].
apply ratio_betS with k1 k2 k1=> //.
  by rewrite -addrA -ltr_subl_addl subrr subr_gt0 gtr_pmull.
rewrite eq_inv_scale ?bet_neq0 // -addrA addrC -addf_divrr ?divff ?lt0r_neq0 //.
rewrite scalerDl scale1r eq_sym -subr_eq opprB eq_div_scale ?lt0r_neq0 //.
rewrite addrBDB k2P scalerA scalerBl eq_sym subr_eq.
by rewrite -scalerDr addrBDB k1P scalerA mulrC.
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

Lemma inner_pasch'' a b c p q (k1 := betR a p c) (k2 := betR b q c) :
  a <> q -> b <> p -> betS a p c -> betS b q c ->
  exists x, betS p x b /\ betS q x a.
Proof.
move=> ? ? /betSP[P1 G1 L1] /betSP[P2 G2 L2].
suff: (((k2 + k1 - k2 * k1) / (k2 - k2 * k1))^-1 *: (a - q) + q ==
       ((k1 + k2 - k1 * k2) / (k1 - k1 * k2))^-1 *: (b - p) + p)=> [/eqP E|].
  exists (((k1 + k2 - k1 * k2) / (k1 - k1 * k2))^-1*:(b - p) + p); apply/andP;
  rewrite -!bet_betS ?[bet p _ _](ratio_bet G1 G2 _ (bet_gt0 G1 L2)) ?bet_lt //;
  rewrite ?(ratio_bet G2 G1 _ (bet_gt0 G2 L1)) ?bet_lt //;
  [rewrite -E| |rewrite -E..| |]; [| |apply /eqP..]; rewrite -!addrA ?subrr;
  rewrite ?addr0 // eq_sym -?subr_eq -1?subr_eq0 -1?[X in X - _]scale1r;
  rewrite -?scalerBl ?scale1r -?addrA ?subrr ?addr0 scaler_eq0 negb_or;
  rewrite ?lt0r_neq0 ?subr_gt0 ?addrA ?bet_gt0' ?bet_lt1 //= ?subr_eq0;
  rewrite ?[k1 + k2]addrC ?bet_lt ?[k2 + k1]addrC ?bet_lt ?subr_gt0;
  rewrite 1?mulrC ?gtr_pmull //; by apply /eqP.
rewrite [X in X - _]addrC eq_sym [X in X - _]addrC -!addrA !invf_div.
rewrite -subr_eq [k2 * _]mulrC !addrA -addrA [k2 + k1]addrC.
rewrite eq_div_scale ?bet_neq0' // scalerDr scalerA mulrCA mulfV ?bet_neq0' //.
rewrite  mulr1 -subr_eq0 -[a - q]opprB scalerN !scalerBl !opprB.
rewrite addrACA -[X in _ + X]addrA -!scaleNr -scalerDr addrBDB -addrCA addrAC.
rewrite -[X in _ + (X + _)]addrA -scalerDr addrBDB -addrCA scalerDl -!addrA.
rewrite  -scalerDr addrBDB addrCA addr_eq0 addrA -scalerDr addrBDB -[b - q]opprB.
by rewrite P1 P2 -scalerN opprB !scalerA [k2 * _]mulrC -scalerDr addrBDB scaleNr.
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

Lemma bet_col a b c:
  bet a b c -> (bet a b c \/ bet b c a \/ bet c a b).
Proof. by auto. Qed.

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

Lemma congC a b c d: cong a b c d = cong b a d c.
Proof.
rewrite /cong -opprB mulNmx dotC -mulNmx 2?opprB eq_sym -opprB.
by rewrite mulNmx [X in -X]dotC -mulNmx 2?opprB eq_sym.
Qed.

Lemma cong_eq a b c : cong a b c c -> a = b.
Proof. apply cong_identity. Qed.

Lemma cong_eq' a b c : cong a a b c -> b = c.
Proof.
by rewrite /cong subrr linear0 mulmx0 eq_sym quad_eq0 subr_eq0 => /eqP ->.
Qed.

Lemma betS_ratio a b c (r := betR a b c) :
  betS a b c -> (c - b = ((1 - r) / r) *: (b - a)).
Proof.
move=> b1. have: betS c b a by rewrite betS_sym. rewrite betS_neq13; move: b1.
move=> /betSP[E1 ? ?] /andP[/betSP[E2 ? ?]?]. apply /eqP; rewrite -opprB E1 E2.
rewrite eq_div_scale /r ?lt0r_neq0 // sub_1_ratio ?subr_eq0 // opprB addrBDB.
by rewrite /betR -scalerN opprB !scalerA mulrC -opprB ratioNr -ratiorN opprB.
Qed.

Lemma betS_gt0 a b c (r := ratio (b - a) (c - a)) : betS a b c -> 0 < (1 - r) / r.
Proof. by move=> /betSP[? ? ?]; rewrite divr_gt0 /r ?subr_gt0. Qed.

Lemma bet_cong_ratio_eq a b c a' b' c' (r := betR a b c) (r' := betR a' b' c') :
  betS a b c -> betS a' b' c' ->
  cong b a b' a' -> cong b c b' c' ->
  (1 - r) / r = (1 - r') / r'.
Proof.
rewrite /cong betS_neq12=> /andP[b1 NE] b2 /eqP c1 /eqP c2.
suff: ((((1 - r) / r)^+2 - ((1 - r') / r')^+2)*:((a - b) *m (a - b)^T) == 0).
rewrite scaler_eq0 ?quad_eq0 ?subr_eq0=> /orP[|/eqP E]; rewrite ?eqf_sqr;
last by rewrite E in NE; move/eqP: NE=> //. move=> /orP[/eqP ->//|].
rewrite eq_sym -sub0r subr_eq=>/eqP E. have: (0 < (1 - r) / r + (1 - r') / r');
first by rewrite addr_gt0 ?betS_gt0 //. by rewrite lt0r -E eqxx andFb //.
rewrite scalerBl {2}c1 subr_eq0 !expr2 -scalerA scalemxAl dotC.
rewrite  scalemxAl eq_sym -scalerA scalemxAl dotC scalemxAl.
rewrite -[a - b]opprB -[a'-b']opprB !scalerN -(betS_ratio b2) -(betS_ratio b1).
by rewrite !mulNmx dotC [X in _ == -X]dotC !mulNmx c2.
Qed.

Lemma five_segment a a' b b' c c' d d' :
  cong a b a' b' -> cong b c b' c' -> cong a d a' d' -> cong b d b' d' ->
  bet a b c -> bet a' b' c' -> a <> b -> cong c d c' d'.
Proof.
move=> c1 c2 c3 c4 /orP[/betEP[[->->]|->|E]|b1 /orP[/betEP[[E _]|E|E]|b2]]=> //;
try solve[rewrite E in c2; apply cong_eq' in c2; move=> _ _; rewrite -c2 -E //];
try solve[rewrite -E in c1; apply cong_eq in c1; rewrite -c1 //];
try solve[rewrite -E in c2; apply cong_eq in c2; rewrite -c2 -E //].
move: c1 c2 c3 c4; rewrite congC /cong=> /eqP c1 /eqP c2 /eqP c3 /eqP c4 _.
rewrite (cosine_rule b) c2 c4 [X in _ == X](cosine_rule b') -!addrA !add2r_eq.
rewrite (betS_ratio b1) (betS_ratio b2) -!scalemxAl -!scalerAr !cosine_rule'.
by rewrite (bet_cong_ratio_eq b1 b2) /cong ?c1 ?c2 ?c3 ?c4.
Qed.

Lemma point_equality_decidability a b : a = b \/ ~ a = b.
Proof. by case: (a =P b); tauto. Qed.

End TarskiGe1.

Section Tarski2D.

Variable R : realFieldType.

Implicit Types (a b c d : 'rV[R]_2).

Lemma vector2_eq a b : a == b = (a 0 0 == b 0 0) && (a 0 1 == b 0 1).
Proof.
apply /eqP/andP=> [->|[/eqP eq0 /eqP eq1]]; rewrite ?eqxx //.
apply /rowP=> j; case: j => [] [|[|//]] p.
  by rewrite (@ord_inj _ (Ordinal p) 0).
by rewrite (@ord_inj _ (Ordinal p) 1).
Qed.

Lemma vector2_eq0 (v : 'rV[R]_2) : (v == 0) = (v 0 0 == 0) && (v 0 1 == 0).
Proof.
apply /eqP; case: (v 0 0 =P 0); case: (v 0 1 =P 0)=> V01 V00 /=;
try (by apply /rowP=> H; try apply V01; try apply V00; rewrite H mxE).
apply /rowP=> j;  case: j => [] [|[|//]] p.
  by rewrite (@ord_inj _ (Ordinal p) 0) // V00 mxE.
by rewrite (@ord_inj _ (Ordinal p) 1) // V01 mxE.
Qed.

Lemma vector2_neq0 (v : 'rV[R]_2) : (v != 0) = (v 0 0 != 0) || (v 0 1 != 0).
Proof.
apply /eqP; case: (v 0 0 =P 0)=> Hv0; case: (v 0 1 =P 0)=> Hv1 /=;
try (by apply /rowP=> H; try apply Hv0; try apply Hv1; rewrite H mxE).
apply /rowP=> j;  case: j => [] [|[|//]] p.
  by rewrite (@ord_inj _ (Ordinal p) 0) // Hv0 mxE .
by rewrite (@ord_inj _ (Ordinal p) 1) // Hv1 mxE.
Qed.

Definition sqr_L2_norm_2D a b :=
  (b 0 0 - a 0 0) ^+ 2 + (b 0 1 - a 0 1) ^+ 2.

Lemma congP_aux' a b : (b - a) *m (b - a)^T = (sqr_L2_norm_2D a b)%:M.
Proof.
rewrite [X in X=_]mx11_scalar /sqr_L2_norm_2D !mxE.
rewrite !big_ord_recr /= big_ord0 add0r !mxE -!expr2.
by congr ((b 0 _ - a 0 _) ^+ 2 + (b 0 _ - a 0 _) ^+ 2)%:M; apply: val_inj.
Qed.

Lemma congP_aux a b c d :
  cong a b c d = (sqr_L2_norm_2D a b == sqr_L2_norm_2D c d).
Proof.
rewrite /cong !congP_aux' /sqr_L2_norm_2D; apply /eqP/eqP=> [|->] //.
move=>/matrixP /(_ 0 0) /eqP. by rewrite !mxE /= !mulr1n; apply /eqP.
Qed.

Lemma congP a b c d :
  reflect (sqr_L2_norm_2D a b = sqr_L2_norm_2D c d) (cong a b c d).
Proof. by rewrite !congP_aux; exact /eqP. Qed.

Definition betSP'_aux a b c k :
  b - a == k *: (c - a) = (b 0 0 - a 0 0 == k * (c 0 0 - a 0 0)) &&
                          (b 0 1 - a 0 1 == k * (c 0 1 - a 0 1)).
Proof.
apply /eqP/andP=> [/matrixP eq|[/eqP eq0 /eqP eq1]]; [apply /andP|].
  have eq_i i: (b 0 i - a 0 i = (b - a) 0 i) by rewrite !mxE.
  by rewrite !eq_i !eq !mxE !eq_refl.
apply/rowP=> j; rewrite !mxE; case: j => [] [|[| //]] //= p.
  rewrite (@ord_inj _ (Ordinal p) 0) //.
by rewrite (@ord_inj _ (Ordinal p) 1).
Qed.

Lemma betSP' a b c (r := betR a b c) :
  reflect ([ /\ b 0 0 - a 0 0 = r * (c 0 0 - a 0 0),
               b 0 1 - a 0 1 = r * (c 0 1 - a 0 1), 0 < r & r < 1])
          (betS a b c).
Proof.
rewrite /betS -/r betSP'_aux. case: (b 0 0 - a 0 0 =P r * (c 0 0 - a 0 0))=> [<-|];
case: (b 0 1 - a 0 1 =P r * (c 0 1 - a 0 1))=> [<-|]; try solve[by constructor; case].
by case: (0 < r); case: (r < 1)=> /=; constructor; try (case=> //).
Qed.

Lemma markov_betE a b c :
  ~ ~ [ /\ [ \/ a 0 0 != b 0 0 | a 0 1 != b 0 1 ] &
           [ \/ b 0 0 != c 0 0 | b 0 1 != c 0 1 ] ] ->
 [ /\ [ \/ a 0 0 != b 0 0 | a 0 1 != b 0 1 ] &
      [ \/ b 0 0 != c 0 0 | b 0 1 != c 0 1 ] ].
Proof.
case: (a 0 0 =P b 0 0); case: (a 0 1 =P b 0 1); case: (b 0 0 =P c 0 0);
case: (b 0 1 =P c 0 1)=> _ _ _ _ /= ?; apply Decidable.not_not=> //;
apply Decidable.dec_and; apply Decidable.dec_or; solve[left=> //|right=> //].
Qed.

Lemma betEP' a b c :
  reflect (~ [ /\ [ \/ a 0 0 != b 0 0 | a 0 1 != b 0 1 ] &
             [ \/ b 0 0 != c 0 0 | b 0 1 != c 0 1 ] ]) (betE a b c).
Proof.
rewrite /betE; case: (a =P b)=>[->|/eqP N1]; case: (b =P c)=>[->|/eqP N2]=> /=;
constructor; try solve[move=> [[/eqP H|/eqP H] _]; apply H=> //];
             try solve[move=> [_ [/eqP H|/eqP H]]; apply H=> //].
move: N1 N2. rewrite !vector2_eq !negb_and=> /orP N1 /orP N2.
move=> H; apply Decidable.not_and in H; first by move: H=> [H|H].
case: (a 0 0 =P b 0 0)=> ?; case: (a 0 1 =P b 0 1)=> ?; intuition.
Qed.

Lemma ratioP_aux (v1 v2 : 'rV[R]_2) :
  v1 0 0 != 0 -> v1 0 1 != 0 -> v2 0 0 != 0 -> v2 0 1 != 0 ->
  v1 0 0 * v2 0 1 == v1 0 1 * v2 0 0 -> ratio v1 v2 = v1 0 0 / v2 0 0.
Proof.
move=> NE1 NE2 NE3 NE4 /eqP E; apply ratio_eq; [by rewrite vector2_neq0 NE3|].
apply /eqP/rowP=> j; rewrite !mxE; case: j => [] [|[|//]] p.
  by rewrite (@ord_inj _ (Ordinal p) 0) // -mulrA mulVf // mulr1.
by rewrite (@ord_inj _ (Ordinal p) 1) // -mulrAC E -mulrA divff // mulr1.
Qed.

Lemma ratioP (v1 v2 : 'rV[R]_2) :
  v1 0 0 != 0 -> v1 0 1 != 0 -> v2 0 0 != 0 -> v2 0 1 != 0 ->
  v1 0 0 * v2 0 1 == v1 0 1 * v2 0 0 -> v1 = ratio v1 v2 *: v2.
Proof.
move=> NE1 NE2 NE3 NE4 /eqP E; rewrite ratioP_aux 1?E //.
apply/rowP=> j; rewrite !mxE; case: j => [] [|[| //]] //= p.
  by rewrite (@ord_inj _ (Ordinal p) 0) // -mulrA mulVf // mulr1.
by rewrite (@ord_inj _ (Ordinal p) 1) // -mulrAC E -mulrA divff // mulr1.
Qed.

Lemma ratio_e0_n1 (v1 v2 : 'rV[R]_2) :
  v2 0 0 = 0 -> v2 0 1 != 0 -> ratio v1 v2 = v1 0 1 / v2 0 1.
Proof.
move=> E NE; rewrite /ratio; case: pickP=> [x|/all_v_neq0 H]; [elim x=> m i|];
last by move: H; rewrite vector2_neq0 NE orbT=> H; exfalso; apply H.
have: ((m == 1)%N || (m == 0)%N) by rewrite -leqn0 -ltnS -leq_eqVlt -ltnS.
move=> /orP[/eqP E'|/eqP E']; move: i; rewrite E'=> i.
  by rewrite (@ord_inj _ (Ordinal i) 1) // (@ord_inj _ (Ordinal p) 0).
by rewrite (@ord_inj _ (Ordinal i) 0) // E=> /eqP NE'.
Qed.

Lemma ratio_e1_n0 (v1 v2 : 'rV[R]_2) :
  v2 0 0 != 0 -> v2 0 1 = 0 -> ratio v1 v2 = v1 0 0 / v2 0 0.
Proof.
move=> NE E; rewrite /ratio; case: pickP=> [x|/all_v_neq0 H]; [elim x=> m i|];
last by move: H; rewrite vector2_neq0 NE orTb=> H; exfalso; apply H.
have: ((m == 1)%N || (m == 0)%N) by rewrite -leqn0 -ltnS -leq_eqVlt -ltnS.
move=> /orP[/eqP E'|/eqP E']; move: i; rewrite E'=> i.
  by rewrite (@ord_inj _ (Ordinal i) 1) // E=> /eqP NE'.
by rewrite (@ord_inj _ (Ordinal i) 0) // (@ord_inj _ (Ordinal p) 0).
Qed.

Lemma ratio_cp'_aux_1 (a b c : R) :
  b - a != 0 ->
  1 < (b - a) / (c - a) -> 0 < (c - b) / (a - b) < 1.
Proof.
rewrite subr_eq0 eq_sym -{1}[b]add0r -subr_eq0 add0r=> ? ?.
have: (0 < ((b - a) / (c - a)))=> [|H].
  by apply le_lt_trans with 1; rewrite ?ler01.
rewrite andbC -subr_lt0 andbC -(ltr_addr (-1)) -[1]divr1.
rewrite {1}divr1 -mulNr addf_div ?oner_neq0 // !mulr1 mulNr mul1r opprB addrBDB.
by rewrite -[a - b]opprB invrN mulrN oppr_lt0 -[X in _ < X]mulN1r ltr_nmulr;
rewrite ?oppr_lt0 ?ltr01 // -invf_div invr_gt0 H andbT invf_cp1.
Qed.

Lemma ratio_cp'_aux_2 (a b c : R) :
  a - b != 0 -> (b - a) / (c - a) < 0 -> 0 < (c - b) / (a - b).
Proof.
move=> ? ?; rewrite -[X in _ < X]addr0 -{2}(subrr 1) addrCA -{2}[1]divr1 -mulNr.
rewrite addf_div ?oner_neq0 // !mulr1 mulNr mul1r opprB addrBDB -[a - b]opprB.
by rewrite invrN mulrN subr_gt0; apply lt_le_trans with 0;
rewrite ?ler01 // -invr_lt0 invf_div.
Qed.

Lemma ratio_cp' (a b c : R) :
  b - a != 0 -> c - a != 0 -> b - c != 0 ->
  [|| 0 < (b - a) / (c - a) < 1, 0 < (c - b) / (a - b) < 1 | 0 < (a - c) / (b - c) < 1].
Proof.
move=> H1 H2 H; have: ((b - a) / (c - a) != 1)=> [|H4].
  rewrite -[X in _ != X]add0r -subr_eq -[1]divr1 -mulNr addf_div ?oner_neq0 //.
  by rewrite !mulr1 mulNr mul1r opprB addrBDB mulf_neq0 // invr_neq0.
have: ((c - b) / (a - b) != 1)=> [|H5].
  rewrite -[X in _ != X]add0r -subr_eq -[1]divr1 -mulNr addf_div ?oner_neq0 //;
  rewrite ?mulr1 ?mulNr ?mul1r ?opprB ?addrBDB ?mulf_neq0 // ?invr_neq0 //;
  by rewrite subr_eq add0r eq_sym -[X in _ != X]add0r -subr_eq.
move: (lt_total H1) (lt_total H2)=> /orP[L1|G1] /orP[L2|G2].
      have: (0 < (b - a) / (c - a)); first by rewrite nmulr_lgt0 // invr_lt0.
      move: (lt_total H4)=> /orP[->->//=|G1 ?]; move: (lt_gtF G1)=> ->.
      by rewrite andbF /= ratio_cp'_aux_1.
    have:  ((b - a) / (c - a) < 0); first by rewrite nmulr_rlt0 // invr_gt0.
    move=> L2; move: (lt_gtF L2)=> -> /=; apply ratio_cp'_aux_2 in L2=> //;
    last by rewrite subr_eq add0r eq_sym -[X in _ != X]add0r -subr_eq.
    move: (lt_total H5) L2=> /orP[->->//=|G1 ?]; move: (lt_gtF G1)=> ->.
    by rewrite andbF /= ratio_cp'_aux_1 //;
    rewrite subr_eq add0r eq_sym -[X in _ != X]add0r -subr_eq.
  have:  ((b - a) / (c - a) < 0); first by rewrite pmulr_rlt0  // invr_lt0.
  move=> L1; move: (lt_gtF L1)=> -> /=; apply ratio_cp'_aux_2 in L1=> //;
  last by rewrite subr_eq add0r eq_sym -[X in _ != X]add0r -subr_eq.
  move: (lt_total H5) L1=> /orP[->->//=|G2 ?]; move: (lt_gtF G2)=> ->.
  by rewrite andbF /= ratio_cp'_aux_1 //;
  rewrite subr_eq add0r eq_sym -[X in _ != X]add0r -subr_eq.
have: (0 < (b - a) / (c - a)); first by rewrite pmulr_rgt0 // invr_gt0.
move: (lt_total H4)=> /orP[->->//=|G3 ?]; move: (lt_gtF G3)=> ->.
by rewrite andbF /= ratio_cp'_aux_1.
Qed.

Lemma ratio_cp (a b c : R) :
  a - b != 0 ->  b - c != 0 -> c - a != 0 ->
  0 < (b - a) / (c - a) < 1 \/ 0 < (c - b) / (a - b) < 1 \/ 0 < (a - c) / (b - c) < 1.
Proof.
by rewrite subr_eq add0r eq_sym -[X in _ != X]add0r -subr_eq=> H1 H3 H2;
move: (ratio_cp' H1 H2 H3)=> /or3P HE;
elim HE=> H; [left|right; left|right; right].
Qed.

Lemma col_2D_aux_1 a b c :
  ((a 0 1 - c 0 1) * (b 0 0 - c 0 0) == (a 0 0 - c 0 0) * (b 0 1 - c 0 1)) =
  ((a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0)).
Proof.
rewrite eq_sym -(addrBDB _ (b 0 0)) -[X in _ == X * _](addrBDB _ (b 0 1)).
rewrite mulrDl [X in _ + X]mulrC addrC [X in _ == X]mulrDl [X in _ == X] addrC.
by rewrite add2r_eq.
Qed.

Lemma col_2D_aux_2 a b c :
  ((c 0 1 - b 0 1) * (a 0 0 - b 0 0) == (c 0 0 - b 0 0) * (a 0 1 - b 0 1)) =
  ((a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0)).
Proof.
rewrite mulrC [X in _ == X]mulrC -[X in _ * X]opprB.
by rewrite mulrN eqr_oppLR -mulrN opprB.
Qed.

Lemma col_2D_aux_3 a b c :
  ((b 0 1 - a 0 1) * (c 0 0 - a 0 0) == (b 0 0 - a 0 0) * (c 0 1 - a 0 1)) =
  ((a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0)).
Proof.
rewrite -opprB mulNr -mulrN opprB eq_sym -opprB mulNr -mulrN opprB.
rewrite -[X in _ * X](addrBDB _ (b 0 1)) -[X in _ == _ * X](addrBDB _ (b 0 0)).
by rewrite mulrDr [X in _ == X]mulrDr mulrC add2r_eq.
Qed.

Lemma col_2D_aux a b c :
  ((a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0)) ->
  c 0 0 != a 0 0 \/ c 0 1 != a 0 1 ->
  a 0 0 != b 0 0 \/ a 0 1 != b 0 1 ->
  b 0 0 != c 0 0 \/ b 0 1 != c 0 1 ->
  [ \/ [ /\ b 0 0 = a 0 0, c 0 0 = a 0 0,
         a 0 1 - b 0 1 != 0, b 0 1 - c 0 1 != 0 & c 0 1 - a 0 1 != 0],
       [ /\ b 0 1 = a 0 1, c 0 1 = a 0 1,
         a 0 0 - b 0 0 != 0, b 0 0 - c 0 0 != 0 & c 0 0 - a 0 0 != 0] |
       [ /\ [ /\ a 0 0 - b 0 0 != 0, b 0 0 - c 0 0 != 0 & c 0 0 - a 0 0 != 0] &
            [ /\ a 0 1 - b 0 1 != 0, b 0 1 - c 0 1 != 0 & c 0 1 - a 0 1 != 0]]].
Proof.
rewrite !subr_eq0; case: (a 0 0 =P b 0 0)=> [->|? /=].
  rewrite subrr mul0r eq_sym mulf_eq0 !subr_eq0=> /orP[/eqP->|/eqP->];
  rewrite ?eqxx /=; move=> [?|?] [?|?] [?|?] //;
  apply Or31; apply And5 => //; by rewrite eq_sym.
case: (a 0 1 =P b 0 1)=> [->|? /=]; rewrite ?subrr ?mul0r ?mulf_eq0.
  rewrite !subr_eq0=> /orP[/eqP ? //|/eqP-> /=]; rewrite eqxx /=.
  move=> [?|//] _ [?|//]; apply Or32; apply And5 => //; by rewrite eq_sym.
case: (b 0 0 =P c 0 0)=> [->|?] /=; rewrite ?subrr ?mulr0 ?mulf_eq0.
  rewrite !subr_eq0; move=> /orP[/eqP->|/eqP->]; move=> [/eqP ?|?] _ [?|/eqP ?];
  move=> //; apply Or31; apply And5=> //; by [rewrite eq_sym|apply /eqP].
case: (b 0 1 =P c 0 1)=> [->|?] /=; rewrite ?subrr ?mulr0 eq_sym.
  rewrite mulf_eq0 !subr_eq0; move=> /orP[/eqP->|/eqP ? //] [?|/eqP ? //] _ _.
  by apply Or32; apply And5=> //; rewrite eq_sym.
case: (c 0 0 =P a 0 0)=> [->|?] /=; [|case: (c 0 1 =P a 0 1)=> [->|?] /=].
    rewrite -[X in _ == X *_]opprB mulNr -addr_eq0 mulrC -mulrDr mulf_eq0.
    rewrite addrBDB !subr_eq0 [X in X || _]eq_sym [X in _ || X]eq_sym.
    move=> /orP[/eqP //|/eqP ?] [/eqP //|/eqP //].
  rewrite -[X in _ == _ * X]opprB mulrN -addr_eq0 mulrC -mulrDl mulf_eq0.
  rewrite addrC addrBDB !subr_eq0 eq_sym.
  move=> /orP[/eqP ?|/eqP //] [/eqP //|/eqP //].
by move=> _ _ _ _; apply Or33.
Qed.

Lemma col_2D a b c :
  (a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0) ->
  (bet a b c \/ bet b c a \/ bet c a b).
Proof.
rewrite /bet; case: (betEP' a b c); case: (betEP' b c a); case: (betEP' c a b);
move=> N1 N2 N3 E; rewrite ?orbT ?orTb ?orbF ?orFb; auto.
apply markov_betE in N1; apply markov_betE in N2; apply markov_betE in N3.
move: N1 N2 N3=> _ [_ N1] [N2 N3]; case: (col_2D_aux E N1 N2 N3).
    rewrite /betS /betR; move=> [E1 E2 N4 N5 N6]; rewrite !ratio_e0_n1;
    rewrite ?mxE ?E1 ?E2 ?subrr // !vector2_eq !mxE !E1 !E2 subrr !mulr0;
    by rewrite -!mulrA !mulVf // !mulr1 !eqxx /=; apply ratio_cp.
  rewrite /betS /betR; move=> [E1 E2 N4 N5 N6]; rewrite !ratio_e1_n0;
  rewrite ?mxE ?E1 ?E2 ?subrr // !vector2_eq !mxE !E1 !E2 subrr !mulr0;
  by rewrite -!mulrA !mulVf // !mulr1 !eqxx /=; apply ratio_cp.
move=> [[N4 N5 N6] [N7 N8 N9]]; rewrite /betS /betR -!ratioP ?ratioP_aux ?eqxx;
rewrite ?mxE //=; try apply ratio_cp; rewrite // ?subr_eq ?add0r 1?eq_sym;
rewrite -1?[X in _ != X]add0r -?subr_eq //; try solve [rewrite col_2D_aux_1 //];
by solve[rewrite col_2D_aux_2 //|rewrite col_2D_aux_3 //].
Qed.

Lemma col_2D' a b c : (bet a b c \/ bet b c a \/ bet c a b) ->
  (a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0).
Proof.
rewrite /bet /betE. case: (a =P b)=> [->|]; first by rewrite !subrr !mul0r eqxx.
move=> ab_neq; case: (b =P c)=> [->|]; first by rewrite !subrr !mulr0 eqxx.
move=> bc_neq; case: (c =P a)=> [->|ca_neq] /=; [|move=> HC].
  by rewrite -[b 0 1 - a 0 1]opprB mulrN -mulNr opprB mulrC.
elim HC; clear HC; [|move=> HC; elim HC; clear HC]; move=> /betSP'[E0 E1 _ _].
    rewrite -[b 0 0 - c 0 0](addrBDB _ (a 0 0)) -[a 0 0 - b 0 0]opprB E0.
    rewrite -[b 0 1 - c 0 1](addrBDB _ (a 0 1)) -[a 0 1 - b 0 1]opprB E1.
    rewrite -[a 0 0 - c 0 0]opprB -{3}[c 0 0 - a 0 0]mul1r.
    rewrite -[a 0 1 - c 0 1]opprB -{2}[c 0 1 - a 0 1]mul1r.
    rewrite -!mulrBl mulrCA [X in _ == X]mulrCA !mulNr -!mulrA.
    by rewrite [X in _ * - (_ * X)]mulrC.
  rewrite -[b 0 0 - c 0 0]opprB E0 -[b 0 1 - c 0 1]opprB E1 !mulrN mulrCA.
  by rewrite [X in _ * X]mulrC eq_sym mulrCA.
rewrite -[a 0 0 - b 0 0](addrBDB _ (c 0 0)) -[a 0 1 - b 0 1](addrBDB _ (c 0 1)).
rewrite E0 E1 -[c 0 0 - b 0 0]opprB -[c 0 1 - b 0 1]opprB -[X in _ - X]mul1r.
by rewrite eq_sym -[X in _ - X]mul1r -!mulrBl mulrAC.
Qed.

Lemma cong_perp_aux1 (a p m : 'rV[R]_2) i :
  (m 0 i - a 0 i) - (m 0 i - p 0 i) = p 0 i - a 0 i.
Proof. by apply /eqP; rewrite opprB addrC addrBDB eqxx. Qed.

Lemma cong_perp_aux2 (a p q : 'rV[R]_2) (m := (1 / (1 + 1)) *: (p + q)) i :
  (m 0 i - a 0 i) + (m 0 i - p 0 i) = q 0 i - a 0 i.
Proof.
rewrite addrAC addrA /m !mxE -mulrDl addf_divrr ?divff ?add11_neq0 //.
by rewrite mul1r -addrA addrACA subrr add0r.
Qed.

Lemma cong_perp (a p q : 'rV[R]_2) (m := (1 / (1 + 1)) *: (p + q)) :
  cong a p a q ->
  (p 0 0 - m 0 0) * (m 0 0 - a 0 0) + (p 0 1 - m 0 1) * (m 0 1 - a 0 1) = 0.
Proof.
move=> /congP/eqP E; move: E; rewrite /sqr_L2_norm_2D.
rewrite -(cong_perp_aux1 a p m) -[p 0 1 - a 0 1](cong_perp_aux1 a p m).
rewrite -(cong_perp_aux2 a p q) -[q 0 1 - a 0 1](cong_perp_aux2 a p) -!/m.
rewrite -[p 0 0 - m 0 0]opprB; set x0 := m 0 0 - a 0 0; set y0 := m 0 0 - p 0 0.
rewrite -[p 0 1 - m 0 1]opprB; set x1 := m 0 1 - a 0 1; set y1 := m 0 1 - p 0 1.
rewrite !mulNr -subr_eq eq_sym -addrA [X in _ == X]addrC -subr_eq !subr_sqr.
rewrite eq_sym -opprB mulNr -sub0r subr_eq eq_sym !addrDBB [X in _ * X]addrC.
rewrite !addrBDD !mulrnAl !mulrnAr -!mulrnA -mulrnDl mulrn_eq0 muln_eq0 /=.
by rewrite addr_eq0=> /eqP E; rewrite -E addrC subrr.
Qed.

Lemma upper_dim_dgc_aux0 (p q : 'rV[R]_2) (m := (1 / (1 + 1)) *: (p + q)) :
  p 0 0 - m 0 0 == 0 -> p <> q ->
  (m 0 0 - p 0 0 == 0) && (m 0 1 - p 0 1 != 0).
Proof.
move=> /eqP E; move/eqP: (cong_perp_aux2 p p q 0); rewrite -[X in _ + X]opprB.
rewrite -/m E subr0 subr_eq addrAC -addrA subrr addr0; move/eqP: E.
rewrite subr_eq0=> /eqP E1 /eqP E2 HF; rewrite E1 subrr eqxx /= subr_eq0.
apply /eqP => NE; move/eqP: HF; rewrite -subr_eq0 vector2_neq0 !mxE.
rewrite E1 E2 subrr eqxx /= -NE -opprB -(cong_perp_aux2 _ p) -/m NE subrr addr0.
by rewrite oppr_eq0 eqxx.
Qed.

Lemma upper_dim_dgc_aux1 (p q : 'rV[R]_2) (m := (1 / (1 + 1)) *: (p + q)) :
  p 0 1 - m 0 1 == 0 -> p <> q ->
  (m 0 1 - p 0 1 == 0) && (m 0 0 - p 0 0 != 0).
Proof.
move=> /eqP E; move/eqP: (cong_perp_aux2 p p q 1); rewrite -[X in _ + X]opprB.
rewrite -/m E subr0 subr_eq addrAC -addrA subrr addr0; move/eqP: E.
rewrite subr_eq0=> /eqP E1 /eqP E2 HF; rewrite E1 subrr eqxx /=.
rewrite subr_eq0; apply /eqP => NE; move/eqP: HF; rewrite -subr_eq0 vector2_neq0 !mxE.
rewrite E1 E2 subrr eqxx /= -NE -opprB -(cong_perp_aux2 _ p) -/m NE subrr addr0.
by rewrite oppr_eq0 eqxx.
Qed.

Lemma upper_dim_dgc1_aux (a p q : 'rV[R]_2) (m := (1 / (1 + 1)) *: (p + q)) :
  m 0 0 - p 0 0 = 0 -> m 0 1 - p 0 1 != 0 ->
  cong a p a q ->
  m 0 1 = a 0 1.
Proof.
move=> E NE /congP/eqP C; move: C; rewrite /sqr_L2_norm_2D.
rewrite -(cong_perp_aux1 a p m) -[p 0 1 - a 0 1](cong_perp_aux1 a p m).
rewrite -(cong_perp_aux2 a p q) -[q 0 1 - a 0 1](cong_perp_aux2 a p) -!/m E.
rewrite subr0 addr0 add2r_eq sqrrB [X in _ == X]sqrrD -!addrA add2r_eq.
rewrite !addrA -subr_eq -addrA subrr addr0 -mulr2n eq_sym -subr_eq0.
rewrite -mulNrn -mulNr opprB -mulNrn -mulNr opprB -mulrnDr  mulrn_eq0 mulf_eq0.
by rewrite /= subr_eq0 => /orP [/eqP->//|/eqP H]; move: NE; rewrite H eqxx.
Qed.

Lemma upper_dim_dgc1 (a b c p q : 'rV[R]_2) (m := (1 / (1 + 1)) *: (p + q)) :
  p 0 0 - m 0 0 == 0 -> p <> q ->
  cong a p a q -> cong b p b q -> cong c p c q ->
  (a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0).
Proof.
move=> E F; move: E F (upper_dim_dgc_aux0 E F); rewrite -/m=> _ _.
move=> /andP[/eqP ? ?] C1 C2 C3; apply upper_dim_dgc1_aux in C1=> //.
apply upper_dim_dgc1_aux in C2=> //; apply upper_dim_dgc1_aux in C3=> //.
by rewrite -C1 -C2 -C3 subrr mulr0 mul0r.
Qed.

Lemma upper_dim_dgc2_aux (a p q : 'rV[R]_2) (m := (1 / (1 + 1)) *: (p + q)) :
  m 0 1 - p 0 1 = 0 -> m 0 0 - p 0 0 != 0 ->
  cong a p a q ->
  m 0 0 = a 0 0.
Proof.
move=> E NE /congP/eqP C; move: C; rewrite /sqr_L2_norm_2D.
rewrite -(cong_perp_aux1 a p m) -[p 0 1 - a 0 1](cong_perp_aux1 a p m).
rewrite -(cong_perp_aux2 a p q) -[q 0 1 - a 0 1](cong_perp_aux2 a p) -!/m E.
rewrite subr0 addr0 addrC [X in _ == X]addrC add2r_eq sqrrB [X in _ == X]sqrrD.
rewrite -!addrA add2r_eq !addrA -subr_eq -addrA subrr addr0 -mulr2n eq_sym.
rewrite -subr_eq0 -mulNrn -mulNr opprB -mulNrn -mulNr opprB -mulrnDr  mulrn_eq0.
rewrite mulf_eq0 /= subr_eq0 => /orP [/eqP->//|/eqP H].
by move: NE; rewrite H eqxx.
Qed.

Lemma upper_dim_dgc2 (a b c p q : 'rV[R]_2) (m := (1 / (1 + 1)) *: (p + q)) :
  m 0 1 - p 0 1 == 0 -> p <> q ->
  cong a p a q -> cong b p b q -> cong c p c q ->
  (a 0 0 - b 0 0) * (b 0 1 - c 0 1) == (a 0 1 - b 0 1) * (b 0 0 - c 0 0).
Proof.
rewrite subr_eq0 eq_sym -subr_eq0=> E F; move: E F (upper_dim_dgc_aux1 E F).
rewrite -/m=> _ _ /andP[/eqP ? ?] C1 C2 C3; apply upper_dim_dgc2_aux in C1=> //.
apply upper_dim_dgc2_aux in C2=> //; apply upper_dim_dgc2_aux in C3=> //.
by rewrite -C1 -C2 -C3 subrr mul0r mulr0.
Qed.

Lemma upper_dim_aux (a b m : 'rV[R]_2) (c0 c1: R) :
  c0 * (m 0 0 - a 0 0) + c1 * (m 0 1 - a 0 1) = 0 ->
  c0 * (m 0 0 - b 0 0) + c1 * (m 0 1 - b 0 1) = 0 ->
  c0 * (b 0 0 - a 0 0) = - c1 * (b 0 1 - a 0 1).
Proof.
move=> /eqP E1 /eqP E2; move: E1 E2; rewrite !addr_eq0 -!mulNr.
move=> /eqP E1 /eqP E2; apply /eqP; rewrite -(addrBBB (m 0 0)) eq_sym.
by rewrite -(addrBBB (m 0 1)) mulrBr eq_sym mulrBr -E1 -E2.
Qed.

Lemma upper_dim a b c p q :
  p <> q -> a <> b -> a <> c -> b <> c ->
  cong a p a q -> cong b p b q -> cong c p c q ->
  (bet a b c \/ bet b c a \/ bet c a b).
Proof.
move=> ? _ _ _ H1 H2 H3; apply col_2D.
move: (cong_perp H1) (cong_perp H2) (cong_perp H3); set m := (1 / (1 + 1)) *: (p + q).
move=> HP1 HP2 HP3; move: (upper_dim_aux HP2 HP1) (upper_dim_aux HP3 HP2).
rewrite opprB; set mp0 := p 0 0 - m 0 0; set pm1 := m 0 1 - p 0 1.
set ba0 := a 0 0 - b 0 0; set ba1 := a 0 1 - b 0 1; set cb0 := b 0 0 - c 0 0;
set cb1 := b 0 1 - c 0 1; move=> E1 E2.
have: (mp0 * pm1 * (ba0 * cb1) == mp0 * pm1 * (ba1 * cb0)).
  by apply /eqP; rewrite mulrACA E1 -E2 -mulrACA [pm1* mp0]mulrC.
rewrite -subr_eq0 -mulrBr mulf_eq0 subr_eq0 mulf_eq0=> /orP[/orP[C1|C2]|->//];
by [apply upper_dim_dgc1 with p q|apply upper_dim_dgc2 with p q].
Qed.

Definition row2 {R : ringType} (a b : R) : 'rV[R]_2 :=
  \row_p [eta \0 with 0 |-> a, 1 |-> b] p.

Definition a2D : 'rV[R]_2 := row2 0 0.
Definition b2D : 'rV[R]_2 := row2 0 1.
Definition c2D : 'rV[R]_2 := row2 1 0.

Variable n : nat.

Definition to_nD (v : 'rV[R]_2) : 'rV[R]_(2 + n) := row_mx v (@const_mx R 1 n 0).

Definition a := to_nD a2D.
Definition b := to_nD b2D.
Definition c := to_nD c2D.

Lemma row2_eq (a b c d : R) : row2 a b == row2 c d = ((a == c) && (b == d)).
Proof.
apply /eqP; case: (a =P c)=> [->|/eqP Hv0]; case: (b =P d)=> [->|/eqP Hv1] //=;
by apply/eqP; rewrite vector2_eq !mxE ?eqxx //= andbC //= negb_and Hv0 Hv1.
Qed.

Lemma row2_eq_nD (a b c d : R) :
  (row_mx (row2 a b) (@const_mx R 1 n 0) ==
   row_mx (row2 c d) (@const_mx R 1 n 0)) = ((a == c) && (b == d)).
Proof.
rewrite -subr_eq0 opp_row_mx add_row_mx subrr.
by rewrite row_mx_eq0 eqxx andbT subr_eq0 row2_eq.
Qed.

Lemma row2_eq0 (a b : R) : row2 a b == 0 = ((a == 0) && (b == 0)).
Proof.
apply /eqP; case: (a =P 0)=> [->|/eqP Hv0]; case: (b =P 0)=> [->|/eqP Hv1] //=;
by apply/eqP; rewrite vector2_eq !mxE ?eqxx //= andbC //= negb_and Hv0 Hv1.
Qed.

Lemma row2_eq0_nD (a b : R) :
  (row_mx (row2 a b) (@const_mx R 1 (n.+2) 0) == 0) = ((a == 0) && (b == 0)).
Proof. by rewrite row_mx_eq0 eqxx andbT row2_eq0. Qed.

Lemma a2D_eq0 : a2D = 0.
Proof. by rewrite /a2D; apply /eqP; rewrite vector2_eq !mxE /= eqxx. Qed.

Lemma a_eq0 : a = 0.
Proof. by rewrite /a /to_nD a2D_eq0 row_mx_const. Qed.

Lemma b2D_neq0 : b2D != 0.
Proof. by rewrite /b2D vector2_eq !mxE /= eqxx oner_eq0. Qed.

Lemma b_neq0 : b != 0.
Proof. by rewrite /b /to_nD row_mx_eq0 negb_and b2D_neq0. Qed.

Lemma c2D_neq0 : c2D != 0.
Proof. by rewrite /c2D vector2_eq !mxE /= eqxx oner_eq0. Qed.

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
have [->|neq_ba] := eqVneq b a; [|move: neq_ba; rewrite -subr_eq0=> neq_ba].
  exists ((c - d) + a); rewrite /bet /cong betE_xxa; split=> //.
  by rewrite -!addrA subrr addr0 -opprB mulNmx eq_sym dotC opprB -mulNmx opprB.
have [->|neq_dc] := eqVneq d c ; [|move: neq_dc; rewrite -subr_eq0=> neq_dc].
  by exists b; rewrite /bet /cong betE_axx !subrr mul0mx eqxx; split.
exists (normv(d - c) / normv(b - a) *: (b - a) + b); rewrite /bet /cong; split.
  rewrite /betS /betR; apply/orP; right; rewrite -addrA.
  rewrite -[X in _ *: _ + X]scale1r -scalerDl scalerA -ratio_bet'' ?mulVf;
  rewrite ?scale1r ?eqxx ?invr_gt0 ?invf_lt1 ?lt0r_neq0 -1?{2}[1]add0r;
  rewrite ?ltr_add2r ?addr_gt0 ?ltr01 1?eq_sym -1?subr_eq0 //= divr_gt0 //;
  by rewrite sqrtr_gt0 lt0r quad_neq0 quad_ge0 ?neq_ba ?neq_dc.
rewrite -addrA subrr addr0 -scalemxAl dotC -scalemxAl scalerA mulf_div -!expr2.
rewrite [X in _ *: X == _]mx11_scalar !sqr_sqrtr ?quad_ge0 // -!scalerA.
by rewrite scale_scalar_mx mulrC divff ?quad_neq0 // scalemx1 -mx11_scalar.
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
   'rV[R]_(n.+2) (@bet R (n.+2)) (@cong R (n.+2)) (@point_equality_decidability R (n.+2))
   (@cong_pseudo_reflexivity R (n.+2)) (@cong_inner_transitivity R (n.+2))
   (@cong_identity R (n.+2))
   (@segment_construction R (n.+2)) (@five_segment R (n.+2))
   (@bet_symmetry R (n.+2)) (@bet_inner_transitivity R (n.+2)) (@inner_pasch R (n.+2))
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

Definition colI a b c := ~ (~ bet a b c /\ ~ bet b c a /\ ~ bet c a b).

Definition inplane p a b c := exists q, colI a b q /\ colI c p q.

Definition cop a b c d := exists e f g,
  ~ colI e f g /\ inplane a e f g /\ inplane b e f g /\
                 inplane c e f g /\ inplane d e f g.

Lemma tcp a b c :
  ~ colI a b c -> exists x, cong a x b x /\ cong a x c x /\ cop a b c x.
Proof.
cut (triangle_circumscription_principle); [|have: tarski_s_parallel_postulate].
    move=> HP HNC1; destruct (HP a b c) as [x [HC1 [HC2 HCop]]]; [|exists x].
      by move: HNC1; rewrite /Col /colI; intuition.
    split; [|split]; [intuition..|move: HCop; rewrite -Cop__Coplanar].
    move => [e [f [g [HNC2 [[iaP aP] [[ibP bP] [[icP cP] [ixP xP]]]]]]]].
    exists e, f, g; split; first by rewrite /Col /colI; intuition auto with col.
    split; first by exists iaP; move: aP; rewrite /Col /colI; intuition.
    split; first by exists ibP; move: bP; rewrite /Col /colI; intuition.
    split; first by exists icP; move: cP; rewrite /Col /colI; intuition.
    by exists ixP; move: xP; rewrite /Col /colI; intuition.
  by unfold tarski_s_parallel_postulate; apply euclidT.
apply equivalent_postulates_without_decidability_of_intersection_of_lines_bis;
simpl; tauto.
Qed.

Definition col a b c := bet a b c \/ bet b c a \/ bet c a b.

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
