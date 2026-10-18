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
Require Import GeoCoq.Algebraic.Counter_models.Planar.independence.

Section Tarski3D.

Variable R: realFieldType.

Definition Point := 'rV[R]_3.

Definition a' : Point := @a R 1.
Definition b' : Point := @b R 1.
Definition c' : Point := @c R 1.

Definition d' : Point := delta_mx 0 ord_max.
Definition e' : Point := - d'.

Lemma lower_dim : lower_dimP Point (@bet R 3) a' b' c'.
Proof. exact: (@POF_to_Tarski.lower_dim R 1). Qed.

Lemma to_nD_z v : (@to_nD R 1 v) 0 ord_max = 0.
Proof.
have -> : ord_max = rshift 2 (0 : 'I_1) :> 'I_(2 + 1) by apply: val_inj.
by rewrite row_mxEr mxE.
Qed.

Lemma cong_de (x : Point) : x 0 ord_max = 0 -> cong x d' x e'.
Proof.
move=> x_z; rewrite /cong /e' -opprD dot2N (dot2B d') (dot2D d') dotC.
by rewrite (dotE x d') /d' trmx_delta -colE mxE x_z mul0rn subr0 addr0.
Qed.

Lemma upper_dim : ~ upper_dimP Point (@bet R 3) (@cong R 3).
Proof.
move=> HF; apply: lower_dim; apply: HF; try apply: cong_de; try exact: to_nD_z.
- move=> /rowP/(_ ord_max); rewrite !mxE eqxx /= mulr1n; lra.
- by apply/eqP; rewrite ab_neq.
- by apply/eqP; rewrite eq_sym ca_neq.
- by apply/eqP; rewrite bc_neq.
Qed.

End Tarski3D.