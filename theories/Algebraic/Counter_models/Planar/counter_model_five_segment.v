From mathcomp Require Import ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq.
From mathcomp
Require Import fintype finset finfun bigop order.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra.
From mathcomp
Require Import zmodp.
From mathcomp
Require Import ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.TTheory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.POF_to_Tarski.
Require Import GeoCoq.Algebraic.Counter_models.nD.counter_model_five_segment.
Require Import GeoCoq.Algebraic.Counter_models.Planar.independence.

Section RfTarski2D.

Variable R : realFieldType.
Definition Point := 'rV[R]_2.
Implicit Types (a b c d : Point).

Definition bet' a b c := counter_model_five_segment.bet' a b c.

Lemma bet'P a b c :
  bet' a b c =
  bet (a 0 0)%:M (b 0 0)%:M (c 0 0)%:M && bet (a 0 1)%:M (b 0 1)%:M (c 0 1)%:M.
Proof.
rewrite /bet' /counter_model_five_segment.bet'.
have E : forall p, @head 0 R p = p 0 0 by move => p; rewrite /head lshift0.
suff {E} -> : bet (behead a) (behead b) (behead c) =
              bet (a 0 1)%:M (b 0 1)%:M (c 0 1)%:M by rewrite !E.
suff {a b c} E : forall p, @behead 0 R p = (p 0 1)%:M by rewrite !E.
move => p; rewrite /behead lshift0 /col'; apply /rowP => i; rewrite !mxE.
case: i => i; case: i => // i.
have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
have -> : @inord 0 0 = 0 by apply val_inj; rewrite val_insubd.
have -> : @lift 2 0 0 = inord 1 by apply: val_inj; rewrite val_insubd.
have -> : @inord 1 1 = 1 by apply: val_inj; rewrite val_insubd.
by rewrite eqxx mulr1n.
Qed.

Definition cong' a b c d := counter_model_five_segment.cong' a b c d.

Definition a' : 'rV[R]_2 := row2 (-1) 0.
Definition b' : 'rV[R]_2 := row2 0 1.
Definition c' : 'rV[R]_2 := row2 1 0.

Lemma five_segment : ~ five_segmentP Point bet' cong'.
Proof. by apply five_segment. Qed.

Lemma point_equality_decidability : point_equality_decidabilityP Point.
Proof. by move=> a b; case: (a =P b); tauto. Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point bet'.
Proof. by apply bet_inner_transitivity. Qed.

Lemma cong_pseudo_reflexivity :
  cong_pseudo_reflexivityP Point cong'.
Proof. by apply cong_pseudo_reflexivity. Qed.

Lemma cong_identity : cong_identityP Point cong'.
Proof. by apply cong_identity. Qed.

Lemma cong_inner_transitivity :
  cong_inner_transitivityP Point cong'.
Proof. by apply cong_inner_transitivity. Qed.

Lemma inner_pasch : inner_paschP Point bet'.
Proof.
move=> a b c p q HB1 HB2 ap_neq pc_neq bq_neq qc_neq HNC.
destruct (@inner_pasch 0 R a b c p q) as [x [HB3 HB4]] => //; [|by exists x].
by intuition.
Qed.

Lemma bet_symmetry : bet_symmetryP Point bet'.
Proof. by apply bet_symmetry. Qed.

Lemma neq_mx (n : nat) (a b : R) : ((a%:M : 'M[R]_n.+1) == b%:M) = (a == b).
Proof.
by apply/eqP/eqP => [/matrixP/(_ 0 0)|->//]; rewrite !mxE eqxx !mulr1n.
Qed.

Lemma bet1I (x y z : R) :
  ((x <= y) && (y <= z)) || ((z <= y) && (y <= x)) -> bet x%:M y%:M z%:M.
Proof.
wlog /andP[xy yz] : x z / (x <= y) && (y <= z).
  move=> W D; case/orP: (D) => H; first exact: W H D.
  by rewrite bet_sym (W z x H) // H.
move=> _; have [<-|xy'] := eqVneq x y; first by rewrite bet_xxa.
have [<-|yz'] := eqVneq y z; first by rewrite bet_axx.
have xy_lt : x < y by rewrite lt_neqAle xy' xy.
have yz_lt : y < z by rewrite lt_neqAle yz' yz.
have xz_lt := lt_trans xy_lt yz_lt.
apply/orP; right; apply: (betS_intro (r := (y - x) / (z - x))).
- by rewrite neq_mx lt_eqF.
- by rewrite divr_gt0 // subr_gt0.
- by rewrite ltr_pdivrMr ?subr_gt0 // mul1r; lra.
- apply/rowP => i; rewrite ord1 !mxE eqxx !mulr1n.
  by field; rewrite subr_eq0 gt_eqF.
Qed.

Lemma bet1E (x y z : R) :
  bet x%:M y%:M z%:M = ((x <= y) && (y <= z)) || ((z <= y) && (y <= x)).
Proof.
apply/idP/idP; last exact: bet1I.
case/orP => [|/betSP[]].
  by rewrite /betE !neq_mx => /orP[/andP[/eqP-> /eqP->]|/orP[]/eqP->]; lra.
move: (betR _ _ _) => r /matrixP/(_ 0 0).
rewrite !mxE eqxx !mulr1n => yxE r_gt0 r_lt1.
by nra.
Qed.

Lemma nbet_abc : (bet' a' b' c') = false.
Proof. by apply/negbTE; rewrite bet'P /a' /b' /c' !mxE /= !bet1E; lra. Qed.

Lemma nbet_bca : (bet' b' c' a') = false.
Proof. by apply/negbTE; rewrite bet'P /a' /b' /c' !mxE /= !bet1E; lra. Qed.

Lemma nbet_cab : (bet' c' a' b') = false.
Proof. by apply/negbTE; rewrite bet'P /a' /b' /c' !mxE /= !bet1E; lra. Qed.

Lemma lower_dim : lower_dimP Point bet' a' b' c'.
Proof.
by rewrite /lower_dimP /Col nbet_abc nbet_cab nbet_bca; move=> [|[|]].
Qed.

Lemma upper_dim : upper_dimP Point bet' cong'.
Proof.
move => a b c p q pq_neq ab_neq ac_neq bc_neq HCa HCb HCc.
destruct (@POF_to_Tarski.upper_dim R a b c p q) as [HB|[HB|HB]] => //.
- by left; apply bet_bet'.
- by right; left; apply bet_bet'.
- by right; right; apply bet_bet'.
Qed.

End RfTarski2D.

Section RcfTarski2D.

Variable R : rcfType.

Implicit Types (a b c d : 'rV[R]_(2)).

Lemma segment_construction :
  segment_constructionP (@Point R) (@bet' R) (@cong' R).
Proof.
move=> a b c d; destruct (POF_to_Tarski.segment_construction a b c d) as [e []].
by exists e; split => //; apply bet_bet'.
Qed.

Lemma line_intersection_1 a b c d :
  (a 0 0 <= b 0 0) -> (c 0 0 <= d 0 0) ->
  (c 0 1 <= a 0 1) -> (d 0 1 <= a 0 1) ->
  (c 0 1 <= b 0 1) -> (d 0 1 <= b 0 1) ->
  exists y, Col (Point R) (@bet' R) a d y /\ Col (Point R) (@bet' R) b c y.
Proof.
move=> *; exists (row2 (Num.max (a 0 0) (c 0 0)) (Num.min (a 0 1) (b 0 1))).
split; right; left; rewrite bet'P !mxE /= !bet1E;
by case: (leP (a 0 0) (c 0 0)) => ?; case: (leP (a 0 1) (b 0 1)) => ?; lra.
Qed.

Lemma line_intersection_2 a b c d :
  (a 0 0 <= b 0 0) -> (c 0 0 <= d 0 0) ->
  (c 0 1 <= a 0 1) -> (d 0 1 <= a 0 1) ->
  (c 0 1 <= b 0 1) -> (d 0 1 <= b 0 1) ->
  exists y, Col (Point R) (@bet' R) a b y /\ Col (Point R) (@bet' R) c d y.
Proof.
move=> *; case: (leP (a 0 1) (b 0 1)) => ?.
  exists (row2 (Num.min (a 0 0) (c 0 0)) (c 0 1)).
  split; right; right; rewrite bet'P !mxE /= !bet1E;
  by case: (leP (a 0 0) (c 0 0)) => ?; lra.
exists (row2 (Num.max (b 0 0) (d 0 0)) (d 0 1)).
split; left; rewrite bet'P !mxE /= !bet1E;
by case: (leP (b 0 0) (d 0 0)) => ?; lra.
Qed.

Lemma line_intersection_3 a b c d :
  (a 0 0 <= b 0 0) -> (c 0 0 <= d 0 0) ->
  (c 0 1 <= a 0 1) -> (d 0 1 <= a 0 1) ->
  (c 0 1 <= b 0 1) -> (d 0 1 <= b 0 1) ->
  exists y, Col (Point R) (@bet' R) a c y /\ Col (Point R) (@bet' R) b d y.
Proof.
move=> *; case: (leP (a 0 0) (c 0 0)) => ?.
  exists (row2 (d 0 0) (Num.min (c 0 1) (d 0 1))).
  split; left; rewrite bet'P !mxE /= !bet1E;
  by case: (leP (c 0 1) (d 0 1)) => ?; lra.
exists (row2 (b 0 0) (Num.max (a 0 1) (b 0 1))).
split; right; right; rewrite bet'P !mxE /= !bet1E;
by case: (leP (a 0 1) (b 0 1)) => ?; lra.
Qed.

Lemma bet'_sym a b c : bet' a b c = bet' c b a.
Proof.
by rewrite !bet'P bet_sym [bet (a 0 1)%:M (b 0 1)%:M (c 0 1)%:M] bet_sym.
Qed.

Lemma col_213 a b c :
  Col (Point R) (@bet' R) a b c -> Col (Point R) (@bet' R) b a c.
Proof.
by rewrite /Col bet'_sym [bet' b c a]bet'_sym [bet' c a b]bet'_sym; tauto.
Qed.

Definition meet a b c d :=
  exists y, Col (Point R) (@bet' R) a b y /\ Col (Point R) (@bet' R) c d y.

Lemma meetC a b c d : meet a b c d -> meet c d a b.
Proof. by case=> y [? ?]; exists y. Qed.

Lemma meet_swapl a b c d : meet a b c d -> meet b a c d.
Proof. by case=> y [? ?]; exists y; split; first exact: col_213. Qed.

Lemma meet_swapr a b c d : meet a b c d -> meet a b d c.
Proof. by move=> /meetC /meet_swapl /meetC. Qed.

Lemma all_lines_meet a b c d :
  exists y, Col (Point R) (@bet' R) a b y /\ Col (Point R) (@bet' R) c d y.
Proof.
rewrite -/(meet a b c d).
wlog ba : a b / b 0 1 <= a 0 1.
  by move=> H; case: (leP (b 0 1) (a 0 1)) => [/H|/ltW/H/meet_swapl].
wlog dc : c d / d 0 1 <= c 0 1.
  by move=> H; case: (leP (d 0 1) (c 0 1)) => [/H|/ltW/H/meet_swapr].
wlog ca : a b c d ba dc / c 0 1 <= a 0 1.
  move=> H; case: (leP (c 0 1) (a 0 1)) => [|/ltW] ?; first exact: H.
  by apply/meetC/H.
have da := le_trans dc ca.
have [cb|/ltW bc] := leP (c 0 1) (b 0 1).
  have db := le_trans dc cb; clear ba dc.
  wlog ab : a b ca da cb db / a 0 0 <= b 0 0.
    move=> H; case: (leP (a 0 0) (b 0 0)) => [|/ltW] ?; first exact: H.
    by apply/meet_swapl/H.
  wlog cd : c d ca da cb db / c 0 0 <= d 0 0.
    move=> H; case: (leP (c 0 0) (d 0 0)) => [|/ltW] ?; first exact: H.
    by apply/meet_swapr/H.
  exact: line_intersection_2.
clear ca; wlog ac : a b c d ba da bc dc / a 0 0 <= c 0 0.
  move=> H; case: (leP (a 0 0) (c 0 0)) => [|/ltW] ?; first exact: H.
  by apply/meetC/H.
case: (leP (b 0 0) (d 0 0)) => [|/ltW] ?; first exact: line_intersection_3.
exact: line_intersection_1.
Qed.

Lemma euclid : euclidP (@Point R) (@bet' R).
Proof.
by move=> a b c d p q; move: (all_lines_meet p q c d)=> [y yP]; exists y.
Qed.

End RcfTarski2D.