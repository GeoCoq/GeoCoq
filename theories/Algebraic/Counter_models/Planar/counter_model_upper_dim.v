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
Require Import GeoCoq.Algebraic.Counter_models.Planar.independence.

Section Tarski3D.

Variable R: realFieldType.

Definition Point := 'rV[R]_3.

Definition row3 (a b c : R) : Point :=
\row_p [eta \0 with 0 |-> a, 1 |-> b, 2%:R |-> c] p.

Definition a' : Point := row3 0 0 0.
Definition b' : Point := row3 0 1 0.
Definition c' : Point := row3 1 0 0.
Definition d' : Point := row3 0 0 1.
Definition e' : Point := row3 0 0 (-1).

Lemma eq3 (a b : Point) :
a == b = ((a 0 0 == b 0 0) && ((a 0 1 == b 0 1) && (a 0 2%:R == b 0 2%:R))).
Proof.
apply /eqP/and3P=> [->|[/eqP eq0 /eqP eq1 /eqP eq2]] ; rewrite ?eqxx //.
apply/rowP=> j; case: j => [] [|[| []] //] //= p.
rewrite (@ord_inj _ (Ordinal p) 0) //.
rewrite (@ord_inj _ (Ordinal p) 1) //.
rewrite (@ord_inj _ (Ordinal p) 2%:R) //.
Qed.

Lemma negb_and3 (a b c : bool) :
~~ (a && b && c) = ~~ a || ~~ b || ~~ c.
Proof. by case: a; case: b; case: c. Qed.



Lemma row3_eq (a b c d e f : R) :
row3 a b c == row3 d e f = [&& (a == d), (b == e) & (c == f)].
Proof.
apply /eqP;
case: (a =P d)=> [->|/eqP Hv0];
case: (b =P e)=> [->|/eqP Hv1];
case: (c =P f)=> [->|/eqP Hv2] //;
apply /eqP;
rewrite eq3 !mxE ?eqxx //= andbC //;
rewrite ?negb_and ?negb_and3 ?Hv0 ?Hv1 ?Hv2 //.
Qed.

Lemma a_eq0 : a' = 0.
Proof.
rewrite /a'; apply /eqP; rewrite eq3 !mxE eqxx //.
Qed.

Lemma ab_neq : a' == b' = false.
Proof. by rewrite row3_eq eqxx eq_sym oner_eq0. Qed.

Lemma bc_neq : b' == c' = false.
Proof. by rewrite row3_eq oner_eq0 andbC. Qed.

Lemma ca_neq : c' == a' = false.
Proof. by rewrite row3_eq oner_eq0. Qed.

Lemma betR_abc : betR a' b' c' = 0.
Proof.
rewrite /betR /ratio.
case: pickP => /= [x|/all_v_neq0 //].
rewrite /a' /b' /c' !mxE /=.
case: x => [] [|[|[|//]]] //= p;
rewrite !subr0 ?divr1 ?eqxx //.
Qed.

Lemma betR_bca : betR b' c' a' = 1.
Proof.
rewrite /betR /ratio a_eq0 sub0r; case: pickP => /= [x|/all_v_neq0 H].
rewrite /b' /c' !mxE /=; case: x => [] [|[|[|//]]] //= p;
rewrite oppr_eq0 ?eqxx // sub0r divff // oppr_eq0 oner_eq0 //.
exfalso; apply H; rewrite oppr_eq0 -a_eq0 /a' /b' row3_eq oner_eq0 eqxx //.
Qed.

Lemma betR_cab : betR c' a' b' = 0 \/ betR c' a' b' = 1.
Proof.
rewrite /betR /ratio a_eq0 sub0r; case: pickP => /= [x| //]; last tauto.
rewrite /b' /c' !mxE /=; case: x => [] [|[|[| //]]] //= p;
rewrite ?subr0 ?eqxx // ?sub0r ?divff ?divr1 ?oppr0 ?oppr_eq0 ?oner_eq0; tauto.
Qed.

Lemma lower_dim : lower_dimP Point (@bet R 3) a' b' c'.
Proof.
unfold lower_dimP.
move=> H.
move: H.
rewrite /Col /bet /betE.
rewrite ab_neq bc_neq ca_neq /=.
rewrite /betS.
rewrite betR_abc.
rewrite betR_bca.
 elim (betR_cab)=> [->|->];
rewrite ?ltxx ?ltr01 /= ?[_ && false] andbC /=;
firstorder.
Qed.

Definition sqr_L2_norm_3D (a b : Point) :=
  (b 0 0 - a 0 0) ^+ 2 + (b 0 1 - a 0 1) ^+ 2 + (b 0 2%:R - a 0 2%:R) ^+ 2.

Lemma congP_aux' a b : (b - a) *m (b - a)^T = (sqr_L2_norm_3D a b)%:M.
Proof.
rewrite [X in X=_] mx11_scalar /sqr_L2_norm_3D !mxE.
rewrite !big_ord_recr /= big_ord0 add0r !mxE -!expr2.
congr ((b 0 _ - a 0 _) ^+ 2 + (b 0 _ - a 0 _) ^+ 2 + (b 0 _ - a 0 _) ^+ 2)%:M;
apply: val_inj; rewrite //.
Qed.

Lemma congP_aux a b c d :
cong a b c d = (sqr_L2_norm_3D a b == sqr_L2_norm_3D c d).
Proof.
rewrite /cong !congP_aux' /sqr_L2_norm_3D; apply /eqP/eqP=> [|->] //.
move=>/matrixP /(_ 0 0) /eqP; rewrite !mxE /= !mulr1n; apply /eqP.
Qed.

Lemma oner_neqm1: 1 != -1 :> R.
Proof.
rewrite -addr_eq0 lt0r_neq0 ?addr_gt0 ?ltr01 //.
Qed.

Lemma oner_eqm1: 1 == -1 :> R = false.
Proof.
rewrite (negbTE oner_neqm1) //.
Qed.

Lemma de_neq : (d' == e') = false.
Proof.
rewrite row3_eq eqxx //= oner_eqm1 //.
Qed.

Lemma ac_neq : (a' == c') = false.
Proof.
rewrite eq_sym ca_neq //.
Qed.

Lemma cong_adae: cong a' d' a' e'.
Proof.
rewrite congP_aux /sqr_L2_norm_3D /a' /d' /e' !mxE /= ?add0r ?subr0 ?sqrrN //.
Qed.

Lemma cong_bdbe: cong b' d' b' e'.
Proof.
rewrite congP_aux /sqr_L2_norm_3D /b' /d' /e' !mxE /= ?add0r ?subr0 ?sqrrN //.
Qed.

Lemma cong_cdce: cong c' d' c' e'.
Proof.
rewrite congP_aux /sqr_L2_norm_3D /c' /d' /e' !mxE /= ?add0r ?subr0 ?sqrrN //.
Qed.

Lemma neq (a b : Point) : (a == b) = false -> a <> b.
Proof.
case: (a =P b) => [//| //].
Qed.

Lemma upper_dim : ~(upper_dimP Point (@bet R 3) (@cong R 3)).
Proof.
rewrite /upper_dimP => H.
assert (HF := H a' b' c' d' e').
apply lower_dim, HF.
apply: neq de_neq.
apply: neq ab_neq.
apply: neq ac_neq.
apply: neq bc_neq.
apply: cong_adae.
apply: cong_bdbe.
apply: cong_cdce.
Qed.

End Tarski3D.
