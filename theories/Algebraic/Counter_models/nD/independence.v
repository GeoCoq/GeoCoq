From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import tuple fintype bigop.

Lemma nth_nseq (T : Type) (x0 x : T) (m n : nat) :
  seq.nth x0 (seq.nseq m x) n = (if n < m then x else x0).
Proof. by elim: m n => [|m IHm] []. Qed.

Lemma tnth_nseq n T (x : T) i : tnth (@nseq_tuple n T x) i = x.
Proof.
by rewrite (tnth_nth (tnth_default (nseq_tuple n x) i)) nth_nseq ltn_ord.
Qed.

Lemma big_andb_and (F : nat -> bool) r :
  \big[andb/true]_(i <- r) F i <-> \big[and/True]_(i <- r) F i.
Proof.
elim r=> [|a l]; first by rewrite !big_nil.
rewrite unlock /= => IHl; split => [/andP|] [-> ?] /=;
[split|] => //; by apply IHl.
Qed.

Lemma big_pairs_andb_and (F : nat -> nat -> bool) r1 r2 :
  \big[andb/true]_(i1 <- r1) \big[andb/true]_(i2 <- r2 i1) F i1 i2 <->
  \big[and/True]_(i1 <- r1) \big[and/True]_(i2 <- r2 i1) F i1 i2.
Proof.
elim r1=> [|a1 l1]; first by rewrite !big_nil.
suff IHl2: reducebig True (r2 a1) (fun i2 => BigBody i2 and true (F a1 i2)) <->
           reducebig true (r2 a1) (fun i2 => BigBody i2 andb true (F a1 i2)).
- rewrite unlock /= => IHl1; split => [/andP|] [Ha1 Hl1]; [|apply /andP];
  by split; try (by apply IHl1); apply IHl2.
elim r2 => [//|a2 l2] /= IHl2; split => [|/andP] [-> ?] /=;
[|split] => //; by apply IHl2.
Qed.

Section Axioms.

Variable Point : Type.

Lemma decidability__stability :
  (forall (A B : Point), A = B \/ A <> B) ->
  (forall (A B : Point), ~ ~ A = B -> A = B).
Proof. intros DP A B HAB; elim (DP A B); tauto. Qed.

Variable Bet : Point -> Point -> Point -> Prop.

Variable Cong : Point -> Point -> Point -> Point -> Prop.

Definition Col A B C :=  ~ (~ Bet A B C /\ ~ Bet B C A /\ ~ Bet C A B).

Definition cong_pseudo_reflexivityP := forall A B, Cong A B B A.

Definition cong_inner_transitivityP := forall A B C D E F,
  Cong A B E F -> Cong C D E F -> Cong A B C D.

Definition cong_identityP := forall A B C, Cong A B C C -> A = B.

Definition segment_constructionP := forall A B C D,
  A <> B -> exists X, Bet A B X /\ Cong B X C D.

Definition five_segmentP := forall A A' B B' C C' D D',
  Cong A B A' B' -> Cong B C B' C' -> Cong A D A' D' -> Cong B D B' D' ->
  Bet A B C -> Bet A' B' C' -> A <> B ->
  Cong C D C' D'.

(* The same model as the one that is given by Szczerba
   except that, now, we would use 'rV[R]_(n.+1) everywhere *)

Definition inner_paschP := forall A B C P Q,
  Bet A P C -> Bet B Q C ->
  A <> P -> P <> C -> B <> Q -> Q <> C -> ~ Col A B C ->
  exists X, Bet P X B /\ Bet Q X A.

Definition bet_symmetryP := forall A B C, Bet A B C -> Bet C B A.

Definition bet_inner_transitivityP := forall A B C D,
  Bet A B D -> Bet B C D -> Bet A B C.

Definition orthonormal_basis n :=
  match n with
    | O    => fun _ _ _ => True
    | k.+1 => fun (O I : Point) (Ps : k.+1.-tuple Point) =>
      I <> (tnth Ps (inord 0)) /\ Bet I O (tnth Ps (inord 0)) /\
      \big[and/True]_(0 <= i < n) Cong O I O (tnth Ps (inord i)) /\
      \big[and/True]_(0 <= i < n)
       \big[and/True]_(i.+1 <= j < n)
       Cong (tnth Ps (inord i)) (tnth Ps (inord j))
            I                   (tnth Ps (inord 1))
  end.

(* The same mode as the one that was used in 2D except that,
   now, we use 'rV[R]_(n) instead of 'rV[R]_(1) *)

Definition lower_dimP := orthonormal_basis.

Definition no_more_orthogonal_point n :=
  match n with
    | O    => fun O _ _ P => O = P
    | 1    => fun O I _ P => Col O I P
    | k.+2 => fun O I (Ps : k.+2.-tuple Point) P =>
        orthonormal_basis k.+2 O I Ps ->
        orthonormal_basis k.+2 O I (rot_tuple 1 (belast_tuple P Ps)) ->
        (tnth Ps (inord k.+1)) <> P -> Bet (tnth Ps (inord k.+1)) O P
  end.

(* The same model as the one that was used in 2D except that,
   now, we use 'rV[R]_(n.+2) instead of 'rV[R]_(3) *)

Definition upper_dimP (n : nat) (O I : Point) (Ps : n.-tuple Point) :=
  forall P, no_more_orthogonal_point n O I Ps P.

Definition InP P A B C := exists Q, Col A B Q /\ Col C P Q.

Definition Coplanar A B C D := exists E F G,
  ~ Col E F G /\ InP A E F G /\ InP B E F G /\
                 InP C E F G /\ InP D E F G.

Definition euclidP := forall A B C,
  ~ Col A B C -> exists X, Cong A X B X /\ Cong A X C X /\ Coplanar A B C X.

(* The same model as the one that is given by Gupta
   except that, now, we would use 'rV[R]_(n.+2) everywhere *)

Definition continuityP := forall (Xi Upsilon : Point -> Prop),
  (exists A, forall X Y, Xi X -> Upsilon Y -> Bet A X Y) ->
  (exists B, forall X Y,
        Xi X -> Upsilon Y -> B <> X -> B <> Y -> X <> Y -> Bet X B Y).

End Axioms.
