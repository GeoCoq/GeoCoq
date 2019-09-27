Require Import Arith.
Require Import Bool.
Require Import NArith.
Require Import Notations.
Require Import Sorted.
Require Export GeoCoq.Tactics.Coinc.tactics_axioms.
Require Import Coq.Program.Equality.
Require Export GeoCoq.Utils.TCSets.
Require Import GeoCoq.Utils.Mergesort.
Require Import List.

Open Scope list_scope.

Lemma Pos_lt_not_eq : forall x y,
  Pos.lt x y -> ~ Pos.eq x y.
Proof. intros x y L E; rewrite E in L; apply (Pos.lt_irrefl y); auto. Qed.

Global Instance S : OrderedType.
Proof.
exact (Build_OrderedType Pos.eq Pos.eqb Pos.lt Pos.compare
                         Pos.eqb_eq
                         (@Logic.eq_refl positive)
                         (@Logic.eq_sym positive)
                         (@Logic.eq_trans positive)
                         Pos.lt_trans
                         Pos_lt_not_eq
                         Pos.compare_spec).
Defined.

Global Instance SS : OrderedType.
Proof.
exact (Build_OrderedType (@Equal S) (@equal S) (@lt_set S) (@compare_set S)
                         (@equal_Equal S)
                         (@Equal_refl S)
                         (@Equal_sym S)
                         (@Equal_trans S)
                         (@lt_set_trans S)
                         (@lt_set_not_Equal S)
                         (@Compare_set S)).
Defined.

Definition fstpp (pair : (positive * positive)) :=
  match pair with
    | (a,b) => Pos.min a b
  end.

Definition sndpp (pair : (positive * positive)) :=
  match pair with
    | (a,b) => Pos.max a b
  end.

Definition t := (positive * positive).

Definition eq (t1 t2 : t) :=
  Pos.eq (fstpp(t1)) (fstpp(t2)) /\ Pos.eq (sndpp(t1)) (sndpp(t2)).

Definition eqb (t1 t2 : t) :=
  Pos.eqb (fstpp(t1)) (fstpp(t2)) && Pos.eqb (sndpp(t1)) (sndpp(t2)).

Lemma eqb_eq : forall t1 t2, eqb t1 t2 = true <-> eq t1 t2.
Proof.
intros; unfold eqb; unfold eq; split; intro H;
[apply andb_true_iff in H; induction H|induction H; apply andb_true_iff];
split; apply Pos.eqb_eq; assumption.
Qed.

Lemma eq_refl : forall t, eq t t.
Proof. unfold eq; intuition. Qed.

Lemma eq_sym : forall t t', eq t t' -> eq t' t.
Proof. unfold eq; intuition. Qed.

Lemma eq_trans : forall t1 t2 t3, eq t1 t2 -> eq t2 t3 -> eq t1 t3.
Proof. unfold eq; intuition; eapply Logic.eq_trans; eauto. Qed.

Definition lt (t1 t2 : t) :=
  let ft1 := fstpp(t1) in
  let ft2 := fstpp(t2) in
  let st1 := sndpp(t1) in
  let st2 := sndpp(t2) in
  if Pos.eqb ft1 ft2 then Pos.lt st1 st2
                     else Pos.lt ft1 ft2.

Lemma lt_trans : forall t1 t2 t3, lt t1 t2 -> lt t2 t3 -> lt t1 t3.
Proof.
assert (HTP := Pos.lt_trans).
intros t1 t2 t3; unfold lt; case_eq (Pos.eqb (fstpp t1) (fstpp t2)).

  {
  intro HEq12; case_eq (Pos.eqb (fstpp t2) (fstpp t3)).

    {
    intro HEq23; assert (HEq13 : Pos.eqb (fstpp t1) (fstpp t3) = true)
        by (apply Pos.eqb_eq in HEq12; rewrite HEq12; assumption).
    rewrite HEq13; apply HTP.
    }

    {
    intro HNEq23; assert (HNEq13 : Pos.eqb (fstpp t1) (fstpp t3) = false)
      by (apply Pos.eqb_eq in HEq12; rewrite HEq12; assumption).
    rewrite HNEq13; apply Pos.eqb_eq in HEq12; rewrite HEq12; intuition.
    }
  }

  {
  intro HNEq12; case_eq (Pos.eqb (fstpp t2) (fstpp t3)).

    {
    intro HEq23; assert (HNEq13 : Pos.eqb (fstpp t1) (fstpp t3) = false)
      by (apply Pos.eqb_eq in HEq23; rewrite <- HEq23; assumption).
    rewrite HNEq13; apply Pos.eqb_eq in HEq23; rewrite HEq23; auto.
    }

    {
    intro HNEq23; case_eq (Pos.eqb (fstpp t1) (fstpp t3)).

      {
      intro HEq13; intros.
      assert (HLt13 : Pos.ltb (fstpp t1) (fstpp t3) = true)
        by (apply Pos.ltb_lt; apply HTP with (fstpp t2); assumption).
      apply Pos.eqb_eq in HEq13; rewrite HEq13 in HLt13.
      apply Pos.ltb_lt in HLt13.
      exfalso; apply (Pos.lt_irrefl (fstpp t3)); auto.
      }

      {
      intros; apply HTP with (fstpp t2); assumption.
      }
    }
  }
 Qed.

Lemma lt_not_eq : forall t t', lt t t' -> ~ eq t t'.
Proof.
intros t t'; unfold lt, eq; case_eq (Pos.eqb (fstpp t) (fstpp t'));
[|intros _ L; intuition; apply (Pos_lt_not_eq _ _ L); auto].
intros E L. apply Pos.eqb_eq in E; rewrite E; intuition.
apply (Pos_lt_not_eq _ _ L); auto.
Qed.

Definition compare t1 t2 :=
  let ft1 := fstpp(t1) in
  let ft2 := fstpp(t2) in
  let st1 := sndpp(t1) in
  let st2 := sndpp(t2) in
  match (Pos.compare ft1 ft2) with
    | Lt => Lt
    | Eq => Pos.compare st1 st2
    | Gt => Gt
  end.

Lemma Compare : forall t1 t2,
  CompareSpec (eq t1 t2) (lt t1 t2) (lt t2 t1) (compare t1 t2).
Proof.
intros t1 t2; unfold compare.
destruct (Pos.compare_spec (fstpp(t1)) (fstpp(t2))) as [E|L|L];
[|apply CompLt; unfold lt|apply CompGt; unfold lt];
[|case_eq (Pos.eqb (fstpp(t1)) (fstpp(t2))); auto; intro HF|
  case_eq (Pos.eqb (fstpp(t2)) (fstpp(t1))); auto; intro HF];
try solve [apply Pos.eqb_eq in HF; exfalso; apply (Pos_lt_not_eq _ _ L); auto].
destruct (Pos.compare_spec (sndpp(t1)) (sndpp(t2))) as [E'|L|L];
[apply CompEq; unfold eq|apply CompLt; unfold lt|apply CompGt; unfold lt];
[split; auto|case_eq (Pos.eqb (fstpp(t1)) (fstpp(t2))); auto; intro HF|
             case_eq (Pos.eqb (fstpp(t2)) (fstpp(t1))); auto; intro HF];
[|apply Logic.eq_sym in E]; apply Pos.eqb_neq in HF; intuition.
Qed.

Global Instance SP : OrderedType.
Proof.
exact (Build_OrderedType eq eqb lt compare
                         eqb_eq
                         eq_refl
                         eq_sym
                         eq_trans
                         lt_trans
                         lt_not_eq
                         Compare).
Defined.

Global Instance  SSP : OrderedType.
Proof.
exact (Build_OrderedType (@Equal SP) (@equal SP) (@lt_set SP) (@compare_set SP)
                         (@equal_Equal SP)
                         (@Equal_refl SP)
                         (@Equal_sym SP)
                         (@Equal_trans SP)
                         (@lt_set_trans SP)
                         (@lt_set_not_Equal SP)
                         (@Compare_set SP)).
Defined.

Lemma leb_total : forall p1 p2, Pos.leb p1 p2 = true \/ Pos.leb p2 p1 = true.
Proof.
intros; rewrite !Pos.leb_le.
generalize (Pos.leb_le p1 p2); generalize (Pos.leb_gt p1 p2).
case (Pos.leb p1 p2); [|intros; right; apply Pos.lt_le_incl]; intuition.
Qed.

Global Instance PosOrder : TotalLeBool.
Proof. exact (Build_TotalLeBool positive Pos.leb leb_total). Defined.

Definition OCPAux {n : nat}
           (cp : cartesianPower positive (Datatypes.S (Datatypes.S n))) :=
  (sort (CPToList cp)).

Lemma OCPALengthOK {n : nat} :
  forall (cp : cartesianPower positive (Datatypes.S (Datatypes.S n))),
    (length (OCPAux cp)) = (Datatypes.S (Datatypes.S n)).
Proof.
intro cp.
unfold OCPAux.
assert (HPerm := Permuted_sort (CPToList cp)).
apply Permutation.Permutation_length in HPerm.
rewrite <- HPerm.
apply Logic.eq_sym.
apply lengthOfCPToList.
Defined.

Lemma OCPSortedTl :
  forall (l : list positive),
  StronglySorted (fun x x0 : positive => is_true (x <=? x0)%positive) l ->
  StronglySorted (fun x x0 : positive => is_true (x <=? x0)%positive) (tl l).
Proof.
intros l HSorted.
induction l.
simpl; apply SSorted_nil.
clear IHl.
simpl; apply StronglySorted_inv in HSorted; destruct HSorted as [HSorted Hhd].
assumption.
Qed.

Lemma PermSorted : forall (l l' : list positive),
  Permutation.Permutation l l' ->
  StronglySorted (fun x x0 : positive => is_true (x <=? x0)%positive) l ->
  StronglySorted (fun x x0 : positive => is_true (x <=? x0)%positive) l' ->
  l = l'.
Proof.
intro l; induction l.

  intro l'; induction l'.

    reflexivity.

    intro HPerm.
    apply Permutation.Permutation_nil_cons in HPerm.
    intuition.

  intro l'; induction l'.

    intro HPerm.
    apply Permutation.Permutation_sym in HPerm.
    apply Permutation.Permutation_nil_cons in HPerm.
    intuition.

    intros HPerm Hl Hl'.
    assert (HIna' : In a (a :: l)) by (apply in_eq).
    assert (HIna : In a (a0 :: l')) by (apply Permutation.Permutation_in with (a :: l); assumption).
    assert (HIna0' : In a0 (a0 :: l')) by (apply in_eq).
    assert (HIna0 : In a0 (a :: l))
      by (apply Permutation.Permutation_in with (a0 :: l'); apply Permutation.Permutation_sym in HPerm;assumption).
    clear HIna'; clear HIna0'; apply in_inv in HIna; apply in_inv in HIna0.
    elim HIna; clear HIna; intro HIna; elim HIna0; clear HIna0; intro HIna0;
    try (rewrite HIna in *); try (rewrite <- HIna0 in *).

      assert (HPerm' : Permutation.Permutation l l')
        by (apply Permutation.Permutation_app_inv_l with (a :: nil); simpl; assumption).
      apply OCPSortedTl in Hl; apply OCPSortedTl in Hl'.
      apply IHl in HPerm'; try assumption.
      rewrite HPerm'; reflexivity.

      assert (HPerm' : Permutation.Permutation l l')
        by (apply Permutation.Permutation_app_inv_l with (a :: nil); simpl; assumption).
      apply OCPSortedTl in Hl; apply OCPSortedTl in Hl'.
      apply IHl in HPerm'; try assumption.
      rewrite HPerm'; reflexivity.

      assert (HPerm' : Permutation.Permutation l l')
        by (apply Permutation.Permutation_app_inv_l with (a :: nil); simpl; assumption).
      apply OCPSortedTl in Hl; apply OCPSortedTl in Hl'.
      apply IHl in HPerm'; try assumption.
      rewrite HPerm'; reflexivity.

      assert (Hle1 := Hl); assert (Hle2 := Hl').
      apply StronglySorted_inv in Hle1; apply StronglySorted_inv in Hle2.
      destruct Hle1 as [Hclear Hle1]; clear Hclear; destruct Hle2 as [Hclear Hle2]; clear Hclear.
      assert (Haa0 : (forall x, In x l -> is_true (Pos.leb a x))) by (apply Forall_forall; assumption).
      assert (Ha0a : (forall x, In x l' -> is_true (Pos.leb a0 x))) by (apply Forall_forall; assumption).
      apply Ha0a in HIna.
      apply Haa0 in HIna0.
      unfold is_true in *.
      apply Pos.leb_le in HIna; apply Pos.leb_le in HIna0.
      assert (H := Pos.le_antisym a0 a HIna HIna0).
      rewrite H in *.
      assert (HPerm' : Permutation.Permutation l l')
        by (apply Permutation.Permutation_app_inv_l with (a :: nil); simpl; assumption).
      apply OCPSortedTl in Hl; apply OCPSortedTl in Hl'.
      apply IHl in HPerm'; try assumption.
      rewrite HPerm'; reflexivity.
Qed.

Definition OCP {n : nat}
           (cp : cartesianPower positive (Datatypes.S (Datatypes.S n))) :
  cartesianPower positive (Datatypes.S (Datatypes.S n)).
Proof.
assert (H := OCPALengthOK cp).
rewrite <- H.
exact (ListToCP (OCPAux cp) (fst cp)).
Defined.

Lemma OCPSortedAux {n : nat} :
  forall (cp : cartesianPower positive (Datatypes.S (Datatypes.S n))),
  StronglySorted (fun x x0 : positive => is_true (x <=? x0)%positive) (CPToList (OCP cp)).
Proof.
intros cp.
unfold OCP.
unfold OCPAux.
elim_eq_rect; simpl.
rewrite CPLOK.
apply (@StronglySorted_sort PosOrder).
intros x1 x2 x3.
unfold is_true.
intros Hx1x2 Hx2x3.
apply Pos.leb_le in Hx1x2.
apply Pos.leb_le in Hx2x3.
apply Pos.leb_le.
transitivity x2; assumption.
Qed.

Lemma OCPPerm {n : nat} :
  forall (cp : cartesianPower positive (Datatypes.S (Datatypes.S n))),
  Permutation.Permutation (CPToList cp) (CPToList (OCP cp)).
Proof.
intro cp.
unfold OCP.
unfold OCPAux.
elim_eq_rect; simpl.
rewrite CPLOK.
apply (@Permuted_sort PosOrder).
Qed.

Lemma CPLOCPTlOK {n : nat} :
  forall (cp : cartesianPower positive
                              (Datatypes.S (Datatypes.S (Datatypes.S n)))),
  headCP cp = headCP (OCP cp) ->
  CPToList (OCP (tailCP cp)) = CPToList (tailCP (OCP cp)).
Proof.
intros cp Hhd.
apply PermSorted.

  assert (H := OCPPerm cp).
  rewrite CPToListOK in H.
  apply Permutation.Permutation_sym in H.
  rewrite CPToListOK in H.
  rewrite <- Hhd in H.
  apply Permutation.Permutation_app_inv_l with ((headCP cp) :: nil).
  assert (H' : (headCP cp :: nil) ++ CPToList (OCP (tailCP cp)) = headCP cp :: (CPToList (OCP (tailCP cp))))
    by (simpl; reflexivity); rewrite H'; clear H'.
  assert (H' : (headCP cp :: nil) ++ CPToList (tailCP (OCP cp)) = headCP cp :: (CPToList (tailCP (OCP cp))))
    by (simpl; reflexivity); rewrite H'; clear H'.
  apply Permutation.Permutation_sym in H.
  apply Permutation.perm_trans with (headCP cp :: CPToList (tailCP cp)); try assumption; clear H.
  assert (H := OCPPerm (tailCP cp)).
  apply Permutation.Permutation_sym in H.
  apply Permutation.perm_skip.
  assumption.

  apply OCPSortedAux.

  rewrite <- CPToListTl.
  apply OCPSortedTl.
  apply OCPSortedAux.
Qed.

Lemma OCPTlOK {n : nat} :
  forall (cp : cartesianPower positive
                              (Datatypes.S (Datatypes.S (Datatypes.S n)))),
  headCP cp = headCP (OCP cp) ->
  OCP (tailCP cp) = tailCP (OCP cp).
Proof.
intros cp Hhd.
apply CPLOCPTlOK in Hhd.
apply CPLCP; assumption.
Qed.

Lemma InCPOCP {n : nat} :
  forall p (cp : cartesianPower positive (Datatypes.S (Datatypes.S n))),
  InCP p cp <-> InCP p (OCP cp).
Proof.
intros p cp.
unfold OCP.
unfold OCPAux.
unfold InCP.
elim_eq_rect; simpl.
induction n.

  rewrite CPLOK.
  assert (HPerm1 := Permuted_sort (CPToList cp)); simpl in HPerm1.
  assert (HPerm2 := HPerm1); apply Permutation.Permutation_sym in HPerm2.
  assert (HInOK : In p (sort (fst cp :: snd cp :: nil)) <-> In p (fst cp :: snd cp :: nil))
    by (split; intro HIn; [apply (Permutation.Permutation_in _ HPerm2 HIn)|];
        apply (Permutation.Permutation_in _ HPerm1 HIn)).
  split; intro HIn.

    apply HInOK; simpl; assumption.

    apply HInOK in HIn; simpl in HIn; assumption.

  clear IHn.
  rewrite CPLOK.
  set (sscp := (nat_rect (fun n : nat => cartesianPower positive (Datatypes.S n) -> list positive)
                       (fun cp0 : cartesianPower positive 1 => cp0 :: nil)
                       (fun (n : nat) (IHn : cartesianPower positive (Datatypes.S n) -> list positive)
                       (cp0 : cartesianPower positive (Datatypes.S (Datatypes.S n))) =>
                       fst cp0 :: IHn (tailCP cp0)) n (tailCP (snd cp)))).
  assert (HPerm := Permuted_sort (fst cp :: fst (snd cp) :: sscp)).
  split; intro HIn.

    elim HIn; clear HIn; intro HIn.

      subst.
      apply Permutation.Permutation_in with (fst cp :: fst (snd cp) :: sscp); try assumption.
      apply in_eq.

      elim HIn; clear HIn; intro HIn.

        subst.
        apply Permutation.Permutation_in with (fst cp :: fst (snd cp) :: sscp); try assumption.
        apply in_cons.
        apply in_eq.

        apply Permutation.Permutation_in with (fst cp :: fst (snd cp) :: sscp); try assumption.
        do 2 (apply in_cons).
        assumption.

    apply Permutation.Permutation_sym in HPerm.
    assert (HInOKAux := Permutation.Permutation_in).
    assert (HInOK := HInOKAux positive (sort (fst cp :: fst (snd cp) :: sscp))
                                       (fst cp :: fst (snd cp) :: sscp) p HPerm HIn); clear HInOKAux; clear HIn.
    rename HInOK into HIn.
    assumption.
Qed.

Fixpoint eqList (l1 l2 : list positive) :=
  match l1, l2 with
    | nil         , nil          => True
    | (hd1 :: tl1), (hd2 :: tl2) => (Pos.eq hd1 hd2) /\ (eqList tl1 tl2)
    | _           , _            => False
  end.

Fixpoint eqbList (l1 l2 : list positive) :=
  match l1, l2 with
    | nil         , nil          => true
    | (hd1 :: tl1), (hd2 :: tl2) => (Pos.eqb hd1 hd2) && (eqbList tl1 tl2)
    | _           , _            => false
  end.

Fixpoint ltList (l1 l2 : list positive) :=
  match l1, l2 with
    | nil         , nil          => False
    | nil         , _            => True
    | _           , nil          => False
    | (hd1 :: tl1), (hd2 :: tl2) => match Pos.compare hd1 hd2 with
                                      | Lt => True
                                      | Gt => False
                                      | _  => ltList tl1 tl2
                                    end
  end.

Fixpoint compareList (l1 l2 : list positive) :=
  match l1, l2 with
    | nil         , nil          => Eq
    | nil         , _            => Lt
    | _           , nil          => Gt
    | (hd1 :: tl1), (hd2 :: tl2) => match Pos.compare hd1 hd2 with
                                      | Lt => Lt
                                      | Eq => compareList tl1 tl2
                                      | Gt => Gt
                                    end
    end.

Lemma eqbListEqList : forall l1 l2, eqbList l1 l2 = true <-> eqList l1 l2.
Proof.
intro l1; induction l1; intro l2; induction l2; simpl; try solve [intuition].
split; intro H; [apply andb_true_iff in H|apply andb_true_iff];
destruct H as [Hhd Htl]; [rewrite (IHl1 l2) in Htl|rewrite <- (IHl1 l2) in Htl];
split; try assumption; apply Pos.eqb_eq; assumption.
Qed.

Lemma eqListRefl : forall l, eqList l l.
Proof.
intro l; induction l; simpl; [trivial|].
split; [reflexivity|assumption].
Qed.

Lemma eqListSym : forall l l', eqList l l' -> eqList l' l.
Proof.
intro l; induction l; [intro l'; induction l'; auto|].
intro l'; induction l'; auto; simpl; intros [Haa0 Hll']; split; intuition.
Qed.

Lemma eqListTrans : forall l1 l2 l3,
  eqList l1 l2 -> eqList l2 l3 -> eqList l1 l3.
Proof.
intro l1; induction l1; intro l2; induction l2; intro l3; induction l3; simpl;
trivial; [intuition|intros [Haa0 Hl1l2] [Ha0a1 Hl2l3]].
split; [transitivity a0; assumption|apply IHl1 with l2; assumption].
Qed.

Lemma lengthOne : forall (l : list positive),
  length l = 1 -> exists a, l = a :: nil.
Proof.
intros l Hl; induction l; [discriminate|].
induction l; [exists a; reflexivity|discriminate].
Qed.

Lemma lengthAtLeastOne : forall (l : list positive) n,
  length l = (Datatypes.S n) -> exists a0 l0, l = a0 :: l0.
Proof.
intros l n Hl; induction l; [discriminate|exists a, l; reflexivity].
Qed.

Lemma ltListTrans : forall m x y z,
  length x = (Datatypes.S m) ->
  length y = (Datatypes.S m) ->
  length z = (Datatypes.S m) ->
  ltList x y -> ltList y z -> ltList x z.
Proof.
intro m; induction m; intros x y z lx ly lz Hxy Hyz.

  {
  destruct (lengthOne x lx) as [hdx Hx].
  destruct (lengthOne y ly) as [hdy Hy].
  destruct (lengthOne z lz) as [hdz Hz].
  subst; simpl in *; revert Hxy Hyz.
  generalize (Pos.compare_lt_iff hdx hdy).
  elim (Pos.compare hdx hdy); [intuition| |intuition].
  intros H _; assert (Hxy : Pos.lt hdx hdy) by (intuition); clear H.
  generalize (Pos.compare_lt_iff hdy hdz).
  elim (Pos.compare hdy hdz); [intuition| |intuition].
  intros H _; assert (Hyz : Pos.lt hdy hdz) by (intuition); clear H.
  assert (Hxz : Pos.lt hdx hdz) by (transitivity hdy; auto).
  rewrite <- Pos.compare_lt_iff in Hxz; rewrite Hxz; auto.
  }

  {
  destruct (lengthAtLeastOne x (Datatypes.S m) lx) as [hdx [tlx Hx]].
  destruct (lengthAtLeastOne y (Datatypes.S m) ly) as [hdy [tly Hy]].
  destruct (lengthAtLeastOne z (Datatypes.S m) lz) as [hdz [tlz Hz]].
  subst; simpl in *; revert Hxy Hyz.
  generalize (Pos.compare_lt_iff hdx hdy) (Pos.compare_eq hdx hdy).
  elim (Pos.compare hdx hdy); [intros _ H HLxy|intros H _ _|intuition].

    {
    assert (Hxy : hdx = hdy) by intuition; clear H.
    generalize (Pos.compare_lt_iff hdy hdz) (Pos.compare_eq hdy hdz).
    elim (Pos.compare hdy hdz); [intros _ H HLyz|intros H _ _|intuition].

      {
      assert (hdx = hdz); [transitivity hdy; intuition|subst].
      rewrite Pos.compare_refl; apply IHm with tly; auto.
      }

      {
      assert (Hxz : Pos.lt hdx hdz) by (subst; intuition).
      rewrite <- Pos.compare_lt_iff in Hxz; rewrite Hxz; auto.
      }
    }

    {
    assert (Hxy : Pos.lt hdx hdy) by intuition; clear H.
    generalize (Pos.compare_lt_iff hdy hdz) (Pos.compare_eq hdy hdz).
    elim (Pos.compare hdy hdz); [intros _ H HLyz|intros H _ _|intuition].

      {
      assert (Hyz : hdy = hdz) by intuition.
      assert (Hxz : Pos.lt hdx hdz) by (subst; auto).
      rewrite <- Pos.compare_lt_iff in Hxz; rewrite Hxz; auto.
      }

      {
      assert (Hyz : Pos.lt hdy hdz) by intuition; clear H.
      assert (Hxz : Pos.lt hdx hdz) by (transitivity hdy; auto).
      rewrite <- Pos.compare_lt_iff in Hxz; rewrite Hxz; auto.
      }
    }
  }
Qed.

Lemma ltListNotEqList : forall m x y,
  length x = (Datatypes.S m) ->
  length y = (Datatypes.S m) ->
  ltList x y -> ~ eqList x y.
Proof.
intro m; induction m; intros x y lx ly Hxy.

  {
  destruct (lengthOne x lx) as [hdx Hx].
  destruct (lengthOne y ly) as [hdy Hy].
  subst; simpl in *; revert Hxy; rewrite <- Pos.compare_eq_iff.
  elim (Pos.compare hdx hdy); intuition discriminate.
  }

  {
  destruct (lengthAtLeastOne x (Datatypes.S m) lx) as [hdx [tlx Hx]].
  destruct (lengthAtLeastOne y (Datatypes.S m) ly) as [hdy [tly Hy]].
  subst; simpl in *; revert Hxy; rewrite <- Pos.compare_eq_iff.
  elim (Pos.compare hdx hdy); try intuition discriminate.
  intros HLt [_ HEq]; apply (IHm tlx tly); auto.
  }
Qed.

Lemma compareListSpec : forall l1 l2,
  CompareSpec (eqList l1 l2) (ltList l1 l2) (ltList l2 l1) (compareList l1 l2).
Proof.
intro l1; induction l1; intro l2; induction l2; simpl;
[apply CompEq|apply CompLt|apply CompGt|clear IHl2]; auto.
generalize (Pos.compare_eq a a0); rewrite (Pos.compare_antisym a a0).
elim (Pos.compare a a0); simpl; intro H; [|apply CompLt|apply CompGt]; auto.
rewrite H; auto; clear H; elim (IHl1 l2); intro H;
[apply CompEq; split|apply CompLt|apply CompGt]; auto; apply Pos.eq_refl.
Qed.

Lemma eqListOK : forall l1 l2, eqList l1 l2 -> l1 = l2.
Proof.
intro l1; induction l1; intro l2; induction l2; simpl; try solve [intuition].
intros [Hhd Htl]; rewrite Hhd, (IHl1 l2); [reflexivity|auto].
Qed.

Section Set_of_tuple_of_positive.

Context {Ar : Arity}.

Definition tST := cartesianPower positive (Datatypes.S (Datatypes.S n)).

Definition eqST (cp1 cp2 : tST) :=
  eqList (sort (CPToList cp1)) (sort (CPToList cp2)).

Definition eqbST (cp1 cp2 : tST) :=
  eqbList (sort (CPToList cp1)) (sort (CPToList cp2)).

Definition ltST (cp1 cp2 : tST) :=
  ltList (sort (CPToList cp1)) (sort (CPToList cp2)).

Definition compareST (cp1 cp2 : tST) :=
  compareList (sort (CPToList cp1)) (sort (CPToList cp2)).

Lemma eqbST_eqST : forall cp1 cp2, eqbST cp1 cp2 = true <-> eqST cp1 cp2.
Proof. intros; apply eqbListEqList. Qed.

Lemma eqST_refl : forall cp, eqST cp cp.
Proof. intros; apply eqListRefl. Qed.

Lemma eqST_sym : forall cp1 cp2, eqST cp1 cp2 -> eqST cp2 cp1.
Proof. intros cp1 cp2; apply eqListSym. Qed.

Lemma eqST_trans : forall cp1 cp2 cp3,
  eqST cp1 cp2 -> eqST cp2 cp3 -> eqST cp1 cp3.
Proof. intros cp1 cp2 cp3; apply eqListTrans. Qed.

Lemma sortOK : forall m l, length l = m -> length (sort l) = m.
Proof.
intros m l Hl; rewrite <- Hl; apply Permutation.Permutation_length.
apply Permutation.Permutation_sym, Permuted_sort.
Qed.

Lemma ltST_trans : forall cp1 cp2 cp3,
  ltST cp1 cp2 -> ltST cp2 cp3 -> ltST cp1 cp3.
Proof.
unfold ltST; intros cp1 cp2 cp3; apply ltListTrans with (Datatypes.S n);
apply sortOK; rewrite <- lengthOfCPToList; reflexivity.
Qed.

Lemma ltST_not_eqST : forall cp1 cp2, ltST cp1 cp2 -> ~ eqST cp1 cp2.
Proof.
intros cp1 cp2; apply ltListNotEqList with (Datatypes.S n);
apply sortOK; rewrite <- lengthOfCPToList; reflexivity.
Qed.

Lemma CompareST : forall cp1 cp2,
  CompareSpec (eqST cp1 cp2) (ltST cp1 cp2) (ltST cp2 cp1) (compareST cp1 cp2).
Proof. intros; apply compareListSpec. Qed.

Global Instance ST : OrderedType.
Proof.
exact (Build_OrderedType eqST eqbST ltST compareST
                         eqbST_eqST
                         eqST_refl
                         eqST_sym
                         eqST_trans
                         ltST_trans
                         ltST_not_eqST
                         CompareST).
Defined.

Lemma eqListSortOCP : forall (cp : tST),
  eqList (CPToList (OCP cp)) (sort (CPToList cp)).
Proof.
intro cp; unfold OCP, OCPAux; elim_eq_rect; simpl.
rewrite CPLOK; apply eqListRefl.
Qed.

(*
TODO: try to see if using sorted lists would not make the tactic faster.
*)

(*
  Definition STelt := tST.

  Definition STt := list tST.

  Definition STempty : STt := nil.

  Lemma eqST_dec : forall x y, {eqST x y} + {~ eqST x y}.
  Proof.
    intros x y; case_eq (eqbST x y); intro HEq.

      apply eqbST_eqST in HEq; left; auto.

      right; intro HEqST; apply eqbST_eqST in HEqST; rewrite HEq in *; discriminate.
  Qed.

  Definition STadd (x : STelt) (s : STt) := cons x s.

  Fixpoint STexists_ (f : STelt -> bool) (s : STt) :=
    match s with
      | nil      => false
      | hd :: tl => f hd || STexists_ f tl
    end.

  Fixpoint STmem elt l :=
    match l with
      | nil      => false
      | hd :: tl => if eqST_dec hd elt then true else STmem elt tl
    end.

  Lemma STempty_b : forall y : STelt, STmem y STempty = false.
  Proof. intros. reflexivity. Qed.

  Lemma STexists_mem_4 :
    forall f (s : STt),
      STexists_ f s = true ->
      exists x : STelt ,  STmem x s = true /\ f x = true.
  Proof.
    intros f s HEx; induction s;
    simpl in *; [discriminate|].
    case_eq (f a); intro Hfa; rewrite Hfa in *; simpl in *.

      exists a; elim (eqST_dec a a);
      [intuition|intro H; exfalso; apply H; unfold eqST; apply eqListRefl].

      destruct (IHs HEx) as [x [Hmem Hfx]]; exists x.
      elim (eqST_dec a x); intro; intuition.
  Qed.

  Lemma STadd_iff : forall (s : STt) (x y : STelt),
    STmem y (STadd x s) = true <-> (eqST x y \/ STmem y s = true).
  Proof. intros; simpl; elim (eqST_dec x y);intro;intuition. Qed.
*)

End Set_of_tuple_of_positive.