Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq.
From mathcomp
Require Import fintype finset finfun bigop order.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra.
From mathcomp
Require Import zmodp.

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

(* Definition of the counter-model *)
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

(* Proof that the following axiom does not hold in the given model *)
Lemma five_segment : ~ five_segmentP Point bet' cong'.
Proof. by apply five_segment. Qed.

(* Proof that the following axioms hold in the given model *)
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

Lemma bet_1D (a b c : Point) i :
  a 0 i - c 0 i != 0 ->
  0 < (b 0 i - a 0 i) / (c 0 i - a 0 i) < 1 ->
  bet (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M.
Proof.
move=> NE /andP[HGt HLt]; rewrite /bet /betS.
have: (betR (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M = (b 0 i-a 0 i) / (c 0 i-a 0 i)).
  apply ratio_eq; rewrite -[(a 0 i) %:M]scalemx1 -1?[(b 0 i)%:M]scalemx1;
  rewrite -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA ?scalemx_eq0 ?negb_or;
  rewrite ?matrix_nonzero1 ?andbT -1?mulrAC -?mulrA ?divff ?mulr1 //;
  by rewrite subr_eq0 eq_sym -subr_eq0.
move=> ->; rewrite HLt HGt !andbT -[(a 0 i) %:M]scalemx1 -[(b 0 i)%:M]scalemx1.
rewrite -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA -mulrAC -mulrA divff ?mulr1;
by rewrite ?eqxx ?orbT // subr_eq0 eq_sym -subr_eq0.
Qed.

Lemma neq_mx10 (n : nat) : ((1%:M : 'M[R]_n.+1) == 0) = false.
Proof. by apply /eqP => H; move: (@matrix_nonzero1 R n); rewrite H eqxx. Qed.

Lemma neq_mx (n : nat) (a b : R) : ((a%:M : 'M[R]_n.+1) == b%:M) = (a == b).
Proof.
by rewrite -scalemx1 -[b%:M]scalemx1 -subr_eq0 -scalerBl scalemx_eq0
           neq_mx10 orbF subr_eq0.
Qed.

Lemma nbetS_abc : @betS R 1 0%:M 1%:M 0%:M = false.
Proof.
rewrite /betS /betR /ratio /=.
case: pickP => /= [i|/all_v_neq0 H]; last by rewrite ltxx /= andbF.
by rewrite subrr ord1 mxE eqxx.
Qed.

Lemma nbet_abc : (bet' a' b' c') = false.
Proof.
rewrite bet'P /bet /betE /a' /b' /c' !mxE /= !neq_mx.
by rewrite ![0 == 1]eq_sym oppr_eq0 !oner_eq0 nbetS_abc !andbF.
Qed.

Lemma nbetS_bca : @betS R 1 0%:M 1%:M (-1)%:M = false.
Proof.
rewrite /betS /betR /ratio /=.
case: pickP => /= [i|/all_v_neq0 H]; last by rewrite ltxx /= andbF.
rewrite ord1 !mxE eqxx !mulr1n !subr0 divrN divff ?oner_eq0 //.
by rewrite ltrNr oppr0 ltr10 andbF.
Qed.

Lemma nbet_bca : (bet' b' c' a') = false.
Proof.
rewrite bet'P /bet /betE /a' /b' /c' !mxE /= !neq_mx.
rewrite ![0 == 1]eq_sym -(subr_eq0 1 (-1)) opprK !oner_eq0.
by move: (add11_neq0 R) => /negPf => ->; rewrite nbetS_bca.
Qed.

Lemma nbetS_cab : @betS R 1 1%:M (-1)%:M 0%:M = false.
Proof.
rewrite /betS /betR /ratio /=.
case: pickP => /= [i|/all_v_neq0 H]; last by rewrite ltxx /= andbF.
rewrite ord1 !mxE eqxx !mulr1n add0r divrN divr1 opprB opprK.
by rewrite -ltrBrDr subrr ltr10 !andbF.
Qed.

Lemma nbet_cab : (bet' c' a' b') = false.
Proof.
rewrite bet'P /bet /betE /a' /b' /c' !mxE /= !neq_mx.
rewrite ![0 == 1]eq_sym -(subr_eq0 1 (-1)) opprK oppr_eq0 !oner_eq0.
by move: (add11_neq0 R) => /negPf => ->; rewrite nbetS_cab.
Qed.

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

Lemma bet_1Di a b c i :
  a 0 i <= b 0 i -> b 0 i <= c 0 i ->
  bet (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M.
Proof.
rewrite !le_eqVlt; case: (a 0 i =P b 0 i)=> [->|_]; rewrite ?bet_xxa //=.
case: (b 0 i =P c 0 i)=> [->|_]; rewrite ?bet_axx //= => HLt HGt.
have: (0 < c 0 i - a 0 i)=> [|ac_lt]; first by rewrite subr_gt0 (lt_trans HLt).
have: (0 < (b 0 i-a 0 i) / (c 0 i-a 0 i)); [|move: HLt=> _ HLt].
  by rewrite ltr_pdivlMr // mul0r subr_gt0.
have: ((b 0 i-a 0 i) / (c 0 i-a 0 i) < 1); [|move: HGt=> _ HGt].
  by rewrite ltr_pdivrMr // mul1r ltrBrDr addrAC -addrA subrr addr0.
have: (betR (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M = (b 0 i-a 0 i) / (c 0 i-a 0 i)).
  by apply ratio_eq; rewrite -[(a 0 i) %:M]scalemx1 -1?[(b 0 i)%:M]scalemx1;
  rewrite -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA ?scalemx_eq0 ?negb_or;
  rewrite ?matrix_nonzero1 -1?mulrAC -?mulrA ?divff ?lt0r_neq0 // mulr1 eqxx.
rewrite /bet /betS=> ->; rewrite HLt HGt -[(a 0 i) %:M]scalemx1;
rewrite -[(b 0 i)%:M]scalemx1 -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA;
by rewrite -mulrAC -mulrA divff ?mulr1 ?eqxx ?orbT // lt0r_neq0.
Qed.

Lemma bet_1Dd a b c i :
  c 0 i <= b 0 i -> b 0 i <= a 0 i ->
  bet (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M.
Proof.
rewrite !le_eqVlt; case: (b 0 i =P a 0 i)=> [->|_]; rewrite ?bet_xxa //=.
case: (c 0 i =P b 0 i)=> [->|_]; rewrite ?bet_axx //= => HLt HGt.
have: (c 0 i - a 0 i < 0)=> [|ac_lt]; first by rewrite subr_lt0 (lt_trans HLt).
have: (0 < (b 0 i-a 0 i) / (c 0 i-a 0 i)); [|move: HGt=> _ HGt].
  by rewrite ltr_ndivlMr // mul0r subr_lt0.
have: ((b 0 i-a 0 i) / (c 0 i-a 0 i) < 1); [|move: HLt=> _ HLt].
  by rewrite ltr_ndivrMr // mul1r ltrBrDr addrAC -addrA subrr addr0.
have: (betR (a 0 i)%:M (b 0 i)%:M (c 0 i)%:M = (b 0 i-a 0 i) / (c 0 i-a 0 i)).
  by apply ratio_eq; rewrite -[(a 0 i) %:M]scalemx1 -1?[(b 0 i)%:M]scalemx1;
  rewrite -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA ?scalemx_eq0 ?negb_or;
  rewrite ?matrix_nonzero1 -1?mulrAC -?mulrA ?divff ?ltr0_neq0 // mulr1 eqxx.
rewrite /bet /betS=> ->; rewrite HLt HGt -[(a 0 i) %:M]scalemx1;
rewrite -[(b 0 i)%:M]scalemx1 -[(c 0 i)%:M]scalemx1 -!scalerBl ?scalerA;
by rewrite -mulrAC -mulrA divff ?mulr1 ?eqxx ?orbT // ltr0_neq0.
Qed.

Lemma permP a b c d : exists e f g h : Point R,
  [&& perm_eq [:: a; b; c; d] [:: e; f; g; h],
  (e 0 0 <= f 0 0), (g 0 0 <= h 0 0) &
  [&& (g 0 1 <= e 0 1), (h 0 1 <= e 0 1), (g 0 1 <= f 0 1) & (h 0 1 <= f 0 1)]].
Proof.
move: (perm_sort (fun p q : (@Point R) => q 0 1 <= p 0 1) [:: a; b; c; d]).
have: (total (fun p q : (@Point R) => q 0 1 <= p 0 1))=> [p q|totalP].
  case: (p 0 1 =P q 0 1)=> [->|/eqP H]; rewrite ?lexx //.
  by move: (lt_total H)=> /orP[HLt|HLt]; rewrite (ltW HLt) ?orbT.
pose s := (sort (fun p q : Point R => q 0 1 <= p 0 1) [:: a; b; c; d]).
move: totalP (sort_sorted totalP [:: a; b; c; d]); rewrite -/s=> _ seqP1 seqP2.
have: (exists e f g h, s = [:: e; f; g; h])=> [|[e [f [g [h sP]]]]].
  exists (nth a s 0), (nth a s 1), (nth a s 2), (nth a s 3).
  move: (size_sort (fun p q : Point R => q 0 1 <= p 0 1) [:: a; b; c; d]).
  rewrite -/s=> Hsize; apply eq_from_nth with a; first by move: Hsize.
  rewrite Hsize; move=> i; case i=> //=; repeat (move=> n; case: n => //=).
move: seqP1; rewrite sP=> /= /and4P[HLe1 HLe2 HLe3 _].
suff: ([:: e; f; g; h] = [:: e; f] ++ [:: g; h])=> [Eq1|//=].
suff: ([:: f; e; g; h] = [:: f; e] ++ [:: g; h])=> [Eq2|//=].
suff: ([:: e; f; h; g] = [:: e; f] ++ [:: h; g])=> [Eq3|//=].
suff: ([:: f; e; h; g] = [:: f; e] ++ [:: h; g])=> [Eq4|//=].
suff: ([:: f; e] = rcons [:: f] e)=> [Eq5|//=].
suff: ([:: h; g] = rcons [:: h] g)=> [Eq6|//=].
case: (e 0 0 =P f 0 0)=> [ef_eq|/eqP H]; [|move: H (lt_total H)=> _].
  case: (g 0 0 =P h 0 0)=> [gh_eq|/eqP H]; [|move: H (lt_total H)=> _].
    exists e, f, g, h; rewrite -ef_eq -gh_eq !lexx -sP perm_sym permEl //.
    by rewrite !(le_trans HLe3) ?(le_trans HLe2) ?lexx.
  move=> /orP[HLt|HLt]; [exists e, f, g, h|exists e, f, h, g];
  rewrite !(le_trans HLe3) ?(le_trans HLe2) ?lexx // -ef_eq lexx (ltW HLt);
  rewrite !andbT; apply perm_trans with s; rewrite perm_sym;
  rewrite sP ?perm_refl //; try solve [rewrite -sP permEl //].
  by rewrite Eq1 Eq3 Eq6 perm_cat2l perm_rcons perm_refl.
case: (g 0 0 =P h 0 0)=> [gh_eq|/eqP H]; [|move: H (lt_total H)=> _].
  move=> /orP[HLt|HLt]; [exists e, f, g, h|exists f, e, g, h];
  rewrite !(le_trans HLe3) ?(le_trans HLe2) ?lexx // -gh_eq lexx (ltW HLt);
  rewrite !andbT; apply perm_trans with s; rewrite perm_sym;
  rewrite sP ?perm_eq_refl //; try solve [rewrite -sP permEl //].
  by rewrite Eq1 Eq2 Eq5 perm_cat2r perm_rcons perm_refl.
move=> /orP[HLt1|HLt1] /orP[HLt2|HLt2];
[exists e, f, g, h|exists f, e, g, h|exists e, f, h, g|exists f, e, h, g];
rewrite !(le_trans HLe3) ?(le_trans HLe2) ?lexx // (ltW HLt1) (ltW HLt2);
rewrite !andbT; apply perm_trans with s; rewrite perm_sym;
rewrite sP ?perm_refl //; try solve [rewrite -sP permEl //];
[| |apply perm_trans with ([:: e; f; h; g])]; rewrite ?Eq1 ?Eq2 ?Eq3 ?Eq4;
by rewrite ?Eq5 ?Eq6 ?perm_cat2l ?perm_cat2r ?perm_rcons perm_refl.
Qed.

Lemma line_intersection_1 a b c d :
  (a 0 0 <= b 0 0) -> (c 0 0 <= d 0 0) ->
  (c 0 1 <= a 0 1) -> (d 0 1 <= a 0 1) ->
  (c 0 1 <= b 0 1) -> (d 0 1 <= b 0 1) ->
  exists y, Col (Point R) (@bet' R) a d y /\ Col (Point R) (@bet' R) b c y.
Proof.
move=> ab_le0 cd_le0 ca_le1 da_le1 cb_le1 db_le1.
have: (bet (d 0 1)%:M (Num.min (a 0 1) (b 0 1))%:M (a 0 1)%:M)=> [|betPy1].
  case: (a 0 1 =P b 0 1)=> [->|/eqP H]; first by rewrite minxx bet_axx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // ?bet_axx // bet_1Di ?lexx // ltW.
have: (bet (c 0 1)%:M (Num.min (a 0 1) (b 0 1))%:M (b 0 1)%:M)=> [|betPy2].
  case: (a 0 1 =P b 0 1)=> [->|/eqP H]; first by rewrite minxx bet_axx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // bet_1Di ?lexx // ltW.
exists (row2 (Num.max (a 0 0) (c 0 0)) (Num.min (a 0 1) (b 0 1))).
split; right; left; rewrite bet'P.
  rewrite !mxE /= ?betPy1 ?betPy2 andbT.
  case: (a 0 0 =P c 0 0)=> [->|/eqP H]; first by rewrite max_l ?bet_1Dd ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
  by rewrite ?ltW // ?bet_axx // bet_1Dd ?lexx // ltW.
case: (a 0 0 =P c 0 0)=> [->|/eqP]; first by rewrite max_l ?mxE ?bet_xxa ?lexx.
move => H; move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
by rewrite ?ltW // !mxE ?bet_xxa // bet_1Di ?lexx // ltW.
Qed.

Lemma line_intersection_2 a b c d :
  (a 0 0 <= b 0 0) -> (c 0 0 <= d 0 0) ->
  (c 0 1 <= a 0 1) -> (d 0 1 <= a 0 1) ->
  (c 0 1 <= b 0 1) -> (d 0 1 <= b 0 1) ->
  exists y, Col (Point R) (@bet' R) a b y /\ Col (Point R) (@bet' R) c d y.
Proof.
move=> ab_le0 cd_le0 ca_le1 da_le1 cb_le1 db_le1.
have: (bet (Num.min (a 0 0) (c 0 0))%:M (a 0 0)%:M (b 0 0)%:M)=> [|betPx1].
  case: (a 0 0 =P c 0 0)=> [->|/eqP H]; first by rewrite min_l ?bet_xxa ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // bet_1Di ?lexx // ltW.
have: (bet (a 0 0)%:M (b 0 0)%:M (Num.max (b 0 0) (d 0 0))%:M)=> [|betPx2].
  case: (b 0 0 =P d 0 0)=> [->|/eqP H]; first by rewrite max_l ?bet_axx ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
  by rewrite ?ltW // bet_1Di ?lexx // ltW.
have: (bet (Num.min (a 0 0) (c 0 0))%:M (c 0 0)%:M (d 0 0)%:M)=> [|betPx3].
  case: (a 0 0 =P c 0 0)=> [->|/eqP H]; first by rewrite min_l ?bet_xxa ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // bet_1Di ?lexx // ltW.
have: (bet (c 0 0)%:M (d 0 0)%:M (Num.max (b 0 0) (d 0 0))%:M)=> [|betPx4].
  case: (b 0 0 =P d 0 0)=> [->|/eqP H]; first by rewrite max_l ?bet_axx ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
  by rewrite ?ltW // bet_1Di ?lexx // ltW.
case: (a 0 1 =P b 0 1)=> [H|/eqP H]; [|move: (lt_total H)=> /orP[?|?]].
    exists (row2 (Num.max (b 0 0) (d 0 0)) (d 0 1)).
    by split; left; rewrite bet'P !mxE /= ?H ?bet_xxa ?bet_axx ?betPx2 ?betPx4.
  exists (row2 (Num.min (a 0 0) (c 0 0)) (c 0 1)); split; right; right;
  by rewrite bet'P !mxE /= ?bet_xxa ?betPx1 ?betPx3 ?bet_1Di // ?ltW.
exists (row2 (Num.max (b 0 0) (d 0 0)) (d 0 1)); split; left;
by rewrite bet'P !mxE /= ?bet_axx ?betPx2 ?betPx4 ?bet_1Dd // ?ltW.
Qed.

Lemma line_intersection_3 a b c d :
  (a 0 0 <= b 0 0) -> (c 0 0 <= d 0 0) ->
  (c 0 1 <= a 0 1) -> (d 0 1 <= a 0 1) ->
  (c 0 1 <= b 0 1) -> (d 0 1 <= b 0 1) ->
  exists y, Col (Point R) (@bet' R) a c y /\ Col (Point R) (@bet' R) b d y.
Proof.
move=> ab_le0 cd_le0 ca_le1 da_le1 cb_le1 db_le1.
have: (bet (Num.max (a 0 1) (b 0 1))%:M (a 0 1)%:M (c 0 1)%:M)=> [|betPx1].
  case: (a 0 1 =P b 0 1)=> [->|/eqP H]; first by rewrite max_l ?bet_xxa ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
  by rewrite ?ltW // bet_1Dd ?lexx // ltW.
have: (bet (a 0 1)%:M (c 0 1)%:M (Num.min (c 0 1) (d 0 1))%:M)=> [|betPx2].
  case: (c 0 1 =P d 0 1)=> [->|/eqP H]; first by rewrite min_l ?bet_axx ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // bet_1Dd ?lexx // ltW.
have: (bet (Num.max (a 0 1) (b 0 1))%:M (b 0 1)%:M (d 0 1)%:M)=> [|betPx3].
  case: (a 0 1 =P b 0 1)=> [->|/eqP H]; first by rewrite max_l ?bet_xxa ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite max_r|rewrite max_l];
  by rewrite ?ltW // bet_1Dd ?lexx // ltW.
have: (bet (b 0 1)%:M (d 0 1)%:M (Num.min (c 0 1) (d 0 1))%:M)=> [|betPx4].
  case: (c 0 1 =P d 0 1)=> [->|/eqP H]; first by rewrite min_l ?bet_axx ?lexx.
  move: (lt_total H)=> /orP[?|?]; [rewrite min_l|rewrite min_r];
  by rewrite ?ltW // bet_1Dd ?lexx // ltW.
case: (a 0 0 =P c 0 0)=> [H|/eqP H]; [|move: (lt_total H)=> /orP[?|?]].
    exists (row2 (d 0 0) (Num.min (c 0 1) (d 0 1))).
    by split; left; rewrite bet'P !mxE /= ?H ?bet_xxa ?bet_axx ?betPx2 ?betPx4.
  exists (row2 (d 0 0) (Num.min (c 0 1) (d 0 1))); split; left;
  by rewrite bet'P !mxE /= ?bet_axx ?betPx2 ?betPx4 ?bet_1Di // ?ltW.
exists (row2 (b 0 0) (Num.max (a 0 1) (b 0 1))); split; right; right;
by rewrite bet'P !mxE /= ?bet_xxa ?betPx1 ?betPx3 ?bet_1Dd // ?ltW.
Qed.

Lemma col_axx a x : Col _ (fun b c d : Point R => bet' b c d) a x x.
Proof. by left; rewrite /Col bet'P !bet_axx. Qed.

Lemma col_xax x a : Col _  (fun b c d : Point R => bet' b c d) x a x.
Proof. by right; left; rewrite /Col bet'P !bet_axx. Qed.

Lemma col_xxa x a : Col _  (fun b c d : Point R => bet' b c d) x x a.
Proof. by left; rewrite /Col bet'P !bet_xxa. Qed.

Lemma dup_meet a b c d :
  uniq [:: a; b; c; d] = false ->
  exists y, Col (Point R) (@bet' R) a b y /\ Col (Point R) (@bet' R) c d y.
Proof.
move=> H; have: (~~ uniq [:: a; b; c; d]) by rewrite H. move: H=> _ H.
move/uniqPn: H=> H; move: H (H a)=> _ [i [j [H1 H2 H3]]]; move: H1 H2 H3.
case: j; rewrite ?ltn0 //= => j; repeat try (case: j=> [|j //=]);
repeat try (case: i=> [|i //=])=> /=; move=> _ _ ->;
[exists d|exists c|exists c|exists d|exists d|exists b];
by split; try apply col_axx; try apply col_xax; apply col_xxa.
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

Lemma all_lines_meet a b c d :
  exists y, Col (Point R) (@bet' R) a b y /\ Col (Point R) (@bet' R) c d y.
Proof.
move: (permP a b c d)=> [e [f [g [h /and4P[H H1 H2 /and4P[H3 H4 H5 H6]]]]]].
move: H (perm_mem H) (perm_uniq H)=> _ H; move: H (H a) (H b) (H c) (H d).
move: (line_intersection_1 H1 H2 H3 H4 H5 H6)=> [y1 [Y11 Y12]].
move: (line_intersection_2 H1 H2 H3 H4 H5 H6)=> [y2 [Y21 Y22]].
move: (line_intersection_3 H1 H2 H3 H4 H5 H6)=> [y3 [Y31 Y32]].
move=> _ aP bP cP dP; move: H1 H2 H3 H4 H5 H6=> _ _ _ _ _ _.
case (uniq [:: e; f; g; h] =P true)=> [H|]; rewrite ?H;
  last by rewrite Bool.not_true_iff_false => ->; apply dup_meet.
move=> H1; have: (uniq [:: a; b; c; d] = uniq [:: e; f; g; h]) by rewrite H H1.
move=> H2; move: Y22 (col_213 Y22) Y31 (col_213 Y31) Y32 (col_213 Y32).
move: H2 H H1 aP bP cP dP Y11 (col_213 Y11) Y12 (col_213 Y12) Y21 (col_213 Y21).
rewrite /uniq !in_cons !eqxx !orbT /= !in_nil=> uniqP.
case: (e =P f)=> [-> //=|]; case: (e =P g)=> [-> //=|].
case: (e =P h)=> [-> //=|]; case: (f =P g)=> [-> //=|].
case: (f =P h)=> [-> //=|]; case: (g =P h)=> [-> //=|/=]; move: uniqP.
case: (a =P b)=> [-> //=|]; case: (a =P c)=> [-> //=|].
case: (a =P d)=> [-> //=|]; case: (b =P c)=> [-> //=|].
case: (b =P d)=> [-> //=|]; case: (c =P d)=> [-> //=|/=].
move=> H1 H2 H3 H4 H5 H6 uniqP; move: uniqP H1 H2 H3 H4 H5 H6.
case: (a =P e)=> [ae_eq|_]; case: (a =P f)=> [af_eq|_];
case: (a =P g)=> [ag_eq|_]; case: (a =P h)=> [ah_eq|_];
rewrite -?ae_eq -?af_eq -?ag_eq -?ah_eq // ?ae_eq ?af_eq ?ag_eq ?ah_eq;
case: (b =P e)=> [be_eq|_]; case: (b =P f)=> [bf_eq|_];
case: (b =P g)=> [bg_eq|_]; case: (b =P h)=> [bh_eq|_];
rewrite -?be_eq -?bf_eq -?bg_eq -?bh_eq // ?be_eq ?bf_eq ?bg_eq ?bh_eq;
case: (c =P e)=> [ce_eq|_]; case: (c =P f)=> [cf_eq|_];
case: (c =P g)=> [cg_eq|_]; case: (c =P h)=> [ch_eq|_];
rewrite -?ce_eq -?cf_eq -?cg_eq -?ch_eq // ?ce_eq ?cf_eq ?cg_eq ?ch_eq;
case: (d =P e)=> [de_eq|_]; case: (d =P f)=> [df_eq|_];
case: (d =P g)=> [dg_eq|_]; case: (d =P h)=> [dh_eq|_];
rewrite -?de_eq -?df_eq -?dg_eq -?dh_eq // ?de_eq ?df_eq ?dg_eq ?dh_eq;
move=> _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _;
move=> Y11 Y11' Y12 Y12' Y21 Y21' Y22 Y22' Y31 Y31' Y32 Y32';
try solve [exists y1; split; rewrite ?Y11 ?Y11' ?Y12 ?Y12'=> //];
try solve [exists y2; split; rewrite ?Y21 ?Y21' ?Y22 ?Y22'=> //];
by exists y3; split; rewrite ?Y31 ?Y31' ?Y32 ?Y32'.
Qed.

Lemma euclid : euclidP (@Point R) (@bet' R).
Proof.
by move=> a b c d p q; move: (all_lines_meet p q c d)=> [y yP]; exists y.
Qed.

End RcfTarski2D.
