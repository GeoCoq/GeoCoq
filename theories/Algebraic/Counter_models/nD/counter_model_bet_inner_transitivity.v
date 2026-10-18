From mathcomp Require Import ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq order.
From mathcomp
Require Import fintype finset finfun bigop.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra.
From mathcomp
Require Import zmodp.
From mathcomp Require Import tuple fintype bigop.
From mathcomp Require Import ring lra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Axioms.gupta_inspired_variant_axioms.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.
Require Import GeoCoq.Algebraic.tcp_ndc.
Require Import GeoCoq.Algebraic.coplanarity.
Require Import GeoCoq.Algebraic.Counter_models.nD.dimensional_axioms.
Require Import GeoCoq.Algebraic.POF_to_Tarski.

Section RfTarskinD.

Variable n : nat.
Variable R : realFieldType.

Definition Point := 'rV[R]_n.+1.
Implicit Types (a b c d : Point).

Definition bet' a b c :=
  bet a b c && ~~ ((a == b) && (b == c)).
Definition cong' a b c d := cong a b c d.

Lemma bet'_midpoint a b (m := midpoint a b) : a <> b -> bet' a m b.
Proof.
rewrite /m /bet' bet_midpoint /= eq_sym -subr_eq0 midpointBL.
rewrite scaler_eq0 invr_eq0 subr_eq0 mulr2n paddr_eq0 ?ler01 ?oner_eq0 //.
by case: (b =P a) => [->|].
Qed.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point cong'.
Proof. by unfold cong_pseudo_reflexivityP; apply cong_pseudo_reflexivity. Qed.

Lemma cong_inner_transitivity : cong_inner_transitivityP Point cong'.
Proof. by unfold cong_inner_transitivityP; apply cong_inner_transitivity. Qed.

Lemma cong_identity : cong_identityP Point cong'.
Proof. by unfold cong_identityP; apply cong_identity. Qed.

Lemma five_segment : five_segmentP Point bet' cong'.
Proof.
move => a a' b b' c c' d d' ? ? ? ? /andP[? _] /andP[? _] ?.
by apply (@five_segment R (n.+1) a a' b b' c c' d d').
Qed.

Lemma inner_pasch : inner_paschP Point bet'.
Proof.
move=> a b c p q /andP[Hb1 _] /andP[Hb2 _] Hap Hpc Hbq Hqc HNC.
have ac_neq : a != c.
  by apply/eqP=> ac; subst c; move: Hb1; rewrite bet_xax => /eqP /Hap.
have ab_neq : a <> b.
  move=> ab; subst b; apply: HNC => -[H _]; apply: H.
  by rewrite /bet' bet_xxa eqxx ac_neq.
have HNC' : ~ (bet a b c \/ bet b c a \/ bet c a b).
  move/eqP: ab_neq => ab_neq HC; apply: HNC => -[H1 [H2 H3]].
  case: HC => [H|[H|H]]; [apply: H1|apply: H2|apply: H3]; rewrite /bet' H /=.
  - by rewrite (negbTE ab_neq).
  - by apply: contra ab_neq => /andP[/eqP-> /eqP->].
  - by rewrite (negbTE ab_neq) andbF.
have pb_neq : p != b by apply/eqP=> pb; subst p; apply: HNC'; left.
have qa_neq : q != a.
  by apply/eqP=> qa; subst q; apply: HNC'; right; right; rewrite bet_sym.
have [x [Hb3 Hb4]] := POF_to_Tarski.inner_pasch Hb1 Hb2 Hap Hpc Hbq Hqc HNC'.
exists x; rewrite /bet' Hb3 Hb4; split.
  by apply: contra pb_neq => /andP[/eqP-> /eqP->].
by apply: contra qa_neq => /andP[/eqP-> /eqP->].
Qed.

Lemma bet_symmetry : bet_symmetryP Point bet'.
Proof.
move=> a b c; rewrite /bet' bet_sym [a == b]eq_sym [b == c]eq_sym.
by rewrite [X in _ && ~~ X]andbC.
Qed.

Lemma bet_inner_transitivity : ~ bet_inner_transitivityP Point bet'.
Proof.
move=> HF; move: (HF (const_mx 0) (const_mx 0) (const_mx 0) (const_mx 1));
rewrite /bet' !bet_xxa eqxx /= onemx_neq0.
by move=> /(_ isT isT).
Qed.

End RfTarskinD.

Section RcfTarskinp2D.

Variable n : nat.
Variable R : realFieldType.

Definition o := o n R.

Definition i := i n R.

Definition basis := basis n R.

Lemma lower_dim :
  lower_dimP (@Point n.+1 R) (@bet' n.+1 R) (@cong' n.+1 R) n.+2 o i basis.
Proof.
move: (dimensional_axioms.lower_dim n R) => [oi_nz [_ ldP]].
split => //; split => //; rewrite /bet' /o /i.
rewrite nth_basis // bet_o_i_basis_nth0 /= negb_and.
by move: (betS_o_i_basis_nth0 n R); rewrite betS_neq12 => /andP[_ ->].
Qed.

Lemma upper_dim :
  upper_dimP (@Point n.+1 R) (@bet' n.+1 R) (@cong' n.+1 R) n.+2 o i basis.
Proof.
have bet'P : forall a b c, @betS R n.+2 a b c -> bet' a b c.
- move => a b c; rewrite /bet' /bet betS_neq12 => /andP[-> ab_nz].
  rewrite ab_nz orbT; suff -> : (a == b) = false by [].
  by apply /negbTE.
move => p ob1P [_ [_ [HC1 HC2]]] pP; apply bet'P, upper_dimS => //.
- by rewrite nth_new_basis //; apply i_neq_basis_nth0.
- by rewrite nth_new_basis // bet_o_i_basis_nth0.
Qed.

End RcfTarskinp2D.

Section RcfTarskinD.

Variable n : nat.
Variable R : rcfType.

Lemma segment_construction :
  segment_constructionP (@Point n R) (@bet' n R) (@cong' n R).
Proof.
move=> a b c d ab_neq; destruct (segment_construction a b c d) as [x [Hb Hc]].
exists x; rewrite /bet' /cong' Hb Hc; split; move=> //=; move: ab_neq.
by case: (a =P b)=> [-> //|/=].
Qed.

Lemma Col__col a b c :
  independence.Col (@Point (n.+1) R) (@bet' (n.+1) R) a b c -> @col R n a b c.
Proof.
move=> HC; case Hb1: (bet a b c); first by left.
case Hb2: (bet b c a); first by right; left.
case Hb3: (bet c a b); first by right; right.
by exfalso; apply: HC; rewrite /bet' Hb1 Hb2 Hb3.
Qed.

Lemma col__Col a b c :
  a <> b -> @col R n a b c ->
  independence.Col (@Point (n.+1) R) (@bet' (n.+1) R) a b c.
Proof.
rewrite /independence.Col /bet' /col /bet /betE [c == a]eq_sym.
case: (a =P b)=> [-> //|_]; case: (a =P c)=> [->//|_]; case: (b =P c)=> [->//|];
case: (betS a b c); case: (betS b c a); case: (betS c a b)=> /=; intuition.
Qed.

Lemma ncol__ncolI a b c : ~ @col R n a b c <-> ~ colI a b c.
Proof. by rewrite col__colI. Qed.

Lemma colI__Col a b c :
  a <> b -> colI a b c ->
  independence.Col (@Point (n.+1) R) (@bet' (n.+1) R) a b c.
Proof. by rewrite -col__colI; apply col__Col. Qed.

Lemma ColD a b c : @col R n a b c \/ ~ @col R n a b c.
Proof.
case Hb1: (bet a b c); first by left; left.
case Hb2: (bet b c a); first by left; right; left.
case Hb3: (bet c a b); first by left; right; right.
by right; rewrite /col Hb1 Hb2 Hb3; case=> [|[]].
Qed.

Lemma coplanar_midpoint a b (m := midpoint a b) :
  a <> b -> independence.Coplanar (Point n.+1 R) (@bet' n.+1 R) a a b m.
Proof.
move=> ab_neq; move: (@tcp_aligned_plane_exists _ (Rcf_to_T_PED R n) a b m).
move=> HE; destruct (HE ab_neq (Midpoint_midpoint a b)) as [p [q [r Hpqr]]].
destruct Hpqr as [mar [mbr [? [? [? [HNC []]]]]]]; exists p, q, r; clear HE.
move: (@tcp_aligned_inplane _ _ (Rcf_to_T_euclidean R n)
                            a b m p q r mar mbr)=> HE.
destruct HE as [Ha [Hb Hm]]=> //; first by apply Midpoint_midpoint.
split; [by move => HF; apply HNC, Col__col|repeat split];
[destruct Ha as [x Hx]..|destruct Hb as [x Hx]|destruct Hm as [x Hx]];
by destruct Hx as [[? [? []]] [? [? []]]]; exists x; split; apply col__Col.
Qed.

Lemma Col_23 a b c :
  independence.Col _ (@bet' (n.+1) R) a b c ->
  independence.Col _ (@bet' (n.+1) R) a c b.
Proof.
rewrite /independence.Col /bet' (eq_sym b a) (eq_sym c a) (eq_sym c b).
rewrite !(bet_sym c) (bet_sym b c a); case: (a =P b) => [->|];
first by rewrite bet_xxa bet_xax; case: (b =P c); intuition.
case: (a =P c) => [->|]; first by rewrite ?bet_xxa ?bet_xax ?bet_axx; intuition.
by case: (b =P c) => [->|]; rewrite ?bet_axx ?bet_xax; intuition.
Qed.

Lemma col__Col_13 a b c :
  a <> c -> @col R n a b c -> independence.Col _ (@bet' (n.+1) R) a b c.
Proof.
by move => ? ?; apply Col_23, col__Col, (@col_permutation_5 (Rcf_to_T R n)).
Qed.

Lemma colI__Col_13 a b c :
  a <> c -> colI a b c -> independence.Col _ (@bet' (n.+1) R) a b c.
Proof. by rewrite -col__colI; apply col__Col_13. Qed.

Lemma inplane__InP p e f g :
  e <> f -> ~ colI e f g -> inplane p e f g ->
  independence.InP _ (@bet' (n.+1) R) p e f g.
Proof.
move=> ef_neq efgP [y [efy gpy]].
have gy_neq : g <> y by move=> gy; subst y; exact: efgP efy.
by exists y; split; [exact: colI__Col|exact: colI__Col_13].
Qed.

Lemma euclid : euclidP (@Point (n.+1) R) (@bet' (n.+1) R) (@cong' (n.+1) R).
Proof.
move => a b c; case: (a =P b) => [->|ab_neq HNC].
- case: (b =P c) => [->|bc_neq] _; last first.
  + exists (midpoint b c); rewrite /cong' {1}congE eqxx; split => //.
    have -> : cong b (midpoint b c) c (midpoint b c)
      by move: (cong_midpoint b c); rewrite /cong' !congE.
    by split => //; apply coplanar_midpoint.
  exists c; rewrite /independence.Coplanar /InP.
  rewrite /cong' !congE subrr mul0mx eqxx; split; [|split]; [intuition..|].
  destruct (@another_point (Rcf_to_T R n) c) as [d cdP].
  destruct (@not_col_exists _ (Rcf_to_T_PED R n) c d) as [e HNC] => //.
  exists e, d, c => {a b cdP}.
  split; first by move => HF; apply HNC, col_permutation_3, Col__col.
  have edP : independence.Col _ (fun a b c => bet' a b c) e d d.
  + rewrite /independence.Col /bet' eqxx bet_axx.
    case: (e =P d) => [E|]; last by intuition.
    by exfalso; apply HNC; rewrite E; Col.
  have cdP : independence.Col _ (fun a b c => bet' a b c) c c d.
  + rewrite /independence.Col /bet' eqxx bet_xxa.
    case: (c =P d) => [E|]; last by intuition.
    by exfalso; apply HNC; rewrite E; Col.
  by repeat split; exists d; split.
have: (~ col a b c) by move=> HF; apply col__Col in HF. rewrite col__colI.
clear HNC; move=> HNC; destruct (@tcp R n a b c) as [x [? [? xP]]]=> //.
exists x; split; [|split]; [by []..|].
destruct xP as [e [f [g [efgP [aP [bP [cP xP]]]]]]].
have ef_neq : e <> f.
  by move=> ef; subst f; apply/efgP/col__colI; left; exact: bet_xxa.
exists e, f, g; split; first by move=> /Col__col /col__colI.
by do 3 (split; first exact: inplane__InP); exact: inplane__InP.
Qed.

End RcfTarskinD.