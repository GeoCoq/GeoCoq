Require Import Bool List OrdersFacts OrdersLists.
Set Implicit Arguments.

Open Scope bool_scope.

Class OrderedType :=
{
  type : Type;
  eq : type -> type -> Prop;
  eqb: type -> type -> bool;
  lt : type -> type -> Prop;
  compare : type -> type -> comparison;
  eqb_eq : forall x y, eqb x y = true <-> eq x y;
  eq_refl : forall x, eq x x;
  eq_sym : forall x y, eq x y -> eq y x;
  eq_trans : forall x y z, eq x y -> eq y z -> eq x z;
  lt_trans : forall x y z, lt x y -> lt y z -> lt x z;
  lt_not_eq : forall x y, lt x y -> ~ eq x y;
  Compare : forall x y, CompareSpec (eq x y) (lt x y) (lt y x) (compare x y)
}.

Section TCSetList.

Context {OT : OrderedType}.

Instance eq_equiv : Equivalence eq.
Proof. split; [exact eq_refl|exact eq_sym|exact eq_trans]. Qed.

Lemma lt_antirefl x : ~ lt x x.
Proof. intro H; apply lt_not_eq in H; apply H, eq_refl. Qed.

Instance lt_strorder : StrictOrder lt.
Proof. split; [exact lt_antirefl|exact lt_trans]. Qed.

Hint Resolve eq_refl eq_sym.

Lemma lt_eq : forall x y z, lt x y -> eq y z -> lt x z.
Proof.
intros x y z HLt HEq; elim (Compare x z); intro C; auto;
[elim (lt_not_eq _ _ HLt); apply eq_trans with z; auto|
 elim (lt_not_eq _ _ (lt_trans _ _ _ C HLt)); auto].
Qed.

Lemma eq_lt : forall x y z, eq x y -> lt y z -> lt x z.
Proof.
intros x y z HEq HLt; elim (Compare x z); intro C; auto;
[elim (lt_not_eq _ _ HLt); apply eq_trans with x; auto|
 elim (lt_not_eq _ _ (lt_trans _ _ _ HLt C)); auto].
Qed.

Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof.
intros x y HEq1 x' y' HEq2; split; intro HLt; eauto using eq_lt, lt_eq.
Qed.

Lemma lt_le x y : lt x y -> ~ lt y x.
Proof.
intro H; intro H'; apply (lt_trans y) in H; auto; apply (lt_antirefl y); auto.
Qed.

Definition elt := type.

Definition t_aux := list elt.

Definition inf x l :=
  match l with
    | nil    => true
    | y :: l' =>
        match compare x y with
          | Lt => true
          | _  => false
        end
  end.

Fixpoint isok l :=
  match l with
    | nil    => true
    | x :: l' => inf x l' && isok l'
  end.

Notation Sort l := (isok l = true).

Class Ok (l : t_aux) : Prop := ok : Sort l.

Record t := Mkt {this : t_aux; is_ok : Ok this}.

Inductive Inf a : t_aux -> Prop :=
  | Inf_nil : Inf a nil
  | Inf_cons b l : lt a b -> Inf a (b :: l).

Inductive Sorted : t_aux -> Prop :=
  | Sorted_nil : Sorted nil
  | Sorted_cons a l : Sorted l -> Inf a l -> Sorted (a :: l).

Lemma inf_iff : forall x l, Inf x l <-> inf x l = true.
Proof.
intros x l; split; intro H.

  {
  destruct H; simpl in *; [reflexivity|].
  elim (Compare x b); try reflexivity; intro H';
  [exfalso; apply (lt_not_eq x b H)|apply lt_le in H]; auto.
  }

  {
  destruct l as [|y ys]; simpl in *; [constructor; fail|].
  revert H; case_eq (Compare x y); try discriminate; [].
  intros Ha _ _; constructor; auto.
  }
Qed.

Notation sort := Sorted (only parsing).

Lemma isok_iff : forall l, sort l <-> Ok l.
Proof.
intro l; split; intro H.

  {
  elim H; [constructor; fail|].
  intros x l' Ha Hb Hc.
  change (inf x l' && isok l' = true).
  rewrite inf_iff in Hc; rewrite Hc; simpl; assumption.
  }

  {
  induction l as [|x l]; [constructor|].
  change (inf x l && isok l = true) in H.
  rewrite andb_true_iff, <- inf_iff in H.
  destruct H; constructor; auto.
  }
Qed.

Lemma Sorted_inv : forall a l,
  Sorted (a :: l) -> Sorted l /\ Inf a l.
Proof. intros a l H; inversion H; auto. Qed.

Lemma Ok_inv : forall a l,
  Ok (a :: l) -> Ok l /\ Inf a l.
Proof.
intros a l HOk; rewrite <- isok_iff in *; apply Sorted_inv; assumption.
Qed.

(*
Global Instance isok_OK s `(isok s = true) : Ok s | 10.
Proof. intros; assumption. Qed.

Hint Extern 1 (Ok _) => rewrite <- isok_iff.
*)

Ltac inv_ok :=
  match goal with
    | H : sort (_ :: _) |- _    => inversion_clear H; inv_ok
    | H : sort nil      |- _    => clear H; inv_ok
    | H : sort ?l       |- _    => change (Ok l) in H; inv_ok
    | H : Ok _          |- _    => rewrite isok_iff in H; inv_ok
    |                   |- Ok _ => rewrite <- isok_iff
    | _                         => idtac
  end.

Inductive In_list (x : elt) : t_aux -> Prop :=
  | In_cons_hd : forall y l, eq x y -> In_list x (y :: l)
  | In_cons_tl : forall y l, In_list x l -> In_list x (y :: l).

Hint Resolve In_cons_hd In_cons_tl.

Definition In x s := In_list x (this s).

Lemma In_cons : forall (x y : elt) (l : t_aux),
  In_list x (y :: l) <-> eq x y \/ In_list x l.
Proof.
intros x y s; split; [intro; invlist In_list; auto|intros [Heq|HIn]]; auto.
Qed.

Lemma In_alt : forall (x : elt) (l : t_aux),
  In_list x l <-> (exists y, eq x y /\ List.In y l).
Proof.
intros x l; induction l.

  {
  intuition; invlist In_list; destruct H as [y [_ H]]; exfalso; apply (in_nil H).
  }

  {
  split.

    {
    rewrite In_cons; intros [HEq|HIn]; [exists a; split; auto; apply in_eq|].
    rewrite IHl in HIn; destruct HIn as [y [HEq HIn]].
    exists y; split; auto; apply in_cons; auto.
    }

    {
    intros [y [HEq HIn]]; apply in_inv in HIn; destruct HIn as [HIn|HIn];
    [rewrite HIn; apply In_cons_hd; auto|
     apply In_cons_tl, IHl; exists y; split; auto].
    }
  }
Qed.

Lemma InP : forall (l : t_aux) (x : elt),
  InA eq x l <-> In_list x l.
Proof. intros l x; rewrite InA_alt, In_alt; tauto. Qed.

Ltac inv := invlist In_list; inv_ok; invlist Inf.

Definition empty_aux : t_aux := nil.

Global Instance empty_ok : Ok empty_aux.
Proof. constructor. Qed.

Definition empty : t := Mkt empty_ok.

Definition is_empty_aux (l : t_aux) := if l then true else false.

Definition is_empty (s : t) := is_empty_aux (this s).

Fixpoint mem_aux (x : elt) (l : t_aux) :=
  match l with
    | nil    => false
    | y :: l' =>
        match compare x y with
          | Lt => false
          | Eq => true
          | Gt => mem_aux x l'
        end
  end.

Definition mem x (s : t) := mem_aux x (this s).

Fixpoint add_aux (x : elt ) (l : t_aux) : t_aux :=
  match l with
    | nil    => x :: nil
    | y :: l' =>
        match compare x y with
          | Lt => x :: l
          | Eq => l
          | Gt => y :: add_aux x l'
        end
  end.

Lemma add_inf : forall (l : t_aux) (x a : elt),
  Inf a l -> lt a x -> Inf a (add_aux x l).
Proof.
simple induction l; simpl; [intuition; apply Inf_cons; auto|].
intros; elim (Compare x a); intro; inv; apply Inf_cons; auto.
Qed.

Global Instance add_ok l x : forall `(Ok l), Ok (add_aux x l).
Proof.
repeat rewrite <- isok_iff; revert l x.
simple induction l; simpl; intros;
[apply Sorted_cons; [apply Sorted_nil|apply Inf_nil]|].
elim (Compare x a); intro; inv.

  {
  apply Sorted_cons; auto.
  }

  {
  apply Sorted_cons; [apply Sorted_cons; auto|apply Inf_cons; auto].
  }

  {
  apply Sorted_cons; auto; apply add_inf; auto.
  }
Qed.

Definition add x (s : t) := Mkt (add_ok x (is_ok s)).

Definition singleton_aux (x : elt) : t_aux := x :: nil.

Global Instance singleton_ok x : Ok (singleton_aux x).
Proof.
unfold singleton_aux; inv; apply Sorted_cons; [apply Sorted_nil|apply Inf_nil].
Qed.

Definition singleton x : t := Mkt (singleton_ok x).

Fixpoint remove_aux x (l : t_aux) : t_aux :=
  match l with
    | nil    => nil
    | y :: l' =>
        match compare x y with
          | Lt => l
          | Eq => l'
          | Gt => y :: remove_aux x l'
        end
  end.

Lemma remove_inf : forall (l : t_aux) (x a : elt) (Hs : Ok l),
  Inf a l -> Inf a (remove_aux x l).
Proof.
induction l; simpl; [intuition|intros; elim (Compare x a); intro; inv; auto];
try solve [apply Inf_cons; auto]; induction l; [apply Inf_nil|apply Inf_cons].
apply lt_trans with a; auto.
apply Ok_inv in Hs; destruct Hs as [_ HInf]; inv; auto.
Qed.

Global Instance remove_ok l x : forall `(Ok l), Ok (remove_aux x l).
Proof.
repeat rewrite <- isok_iff; revert l x; induction l; simpl; [intuition|].
intros; elim (Compare x a); intro; inv; auto; [apply Sorted_cons; auto|].
apply Sorted_cons; auto; apply remove_inf; inv; auto.
Qed.

Definition remove (x : elt) s := Mkt (remove_ok x (is_ok s)).

Fixpoint union_aux (l : t_aux) : t_aux -> t_aux :=
  match l with
    | nil    => fun l' => l'
    | x :: l' =>
        (fix union_aux_aux (l'' : t_aux) : t_aux :=
           match l'' with
             | nil      => l
             | x' :: l''' =>
                  match compare x x' with
                    | Lt => x  :: union_aux l' l''
                    | Eq => x  :: union_aux l' l'''
                    | Gt => x' :: union_aux_aux l'''
                  end
           end)
  end.

Ltac elim_compare com1 com2 := elim (compare com1 com2); intro.

Lemma union_inf : forall (l l' : t_aux) (a : elt) (Hs : Ok l) (Hs' : Ok l'),
  Inf a l -> Inf a l' -> Inf a (union_aux l l').
Proof.
intro l; elim l; clear l; [simpl; auto|intros x l IHl l'; simpl].
destruct l' as [|x' l']; [simpl; auto|intros a Hl Hl'].
generalize (Compare x x'); elim (compare x x');
intros; inv; apply Inf_cons; auto.
Qed.

Global Instance union_ok l l' : forall `(Ok l, Ok l'), Ok (union_aux l l').
Proof.
repeat rewrite <- isok_iff; revert l'; elim l; clear l; [simpl; auto|].
intros x l IHl l'; elim l'; clear l'; [simpl; auto|intros x' l' IHl' Hl Hl'].
simpl; destruct (Compare x x') as [E|L|G]; simpl.

  {
  constructor; [apply IHl|]; rewrite isok_iff in *;
  apply Ok_inv in Hl; apply Ok_inv in Hl'; try solve [intuition].
  apply union_inf; try solve [intuition].
  clear Hl; clear IHl; clear IHl'; clear l.
  destruct Hl' as [_ HInf]; revert HInf; rewrite !inf_iff.
  destruct l' as [|x'' l']; auto; simpl; destruct (Compare x x'') as [E'|L|G];
  auto; destruct (Compare x' x'') as [|HF|]; auto; exfalso;
  [apply (lt_not_eq _ _ HF); apply eq_trans with x; auto|
   apply (lt_not_eq _ _ (lt_trans _ _ _ HF G)); auto].
  }

  {
  constructor; [apply IHl|]; rewrite isok_iff in *; apply Ok_inv in Hl;
  intuition; apply union_inf; try apply Inf_cons; auto.
  }

  {
  cut (Sorted (x' :: union_aux (x :: l) l')); [simpl; auto|].
  constructor; [apply IHl'|apply union_inf]; try solve [constructor; auto];
  rewrite isok_iff in *; auto; apply Ok_inv in Hl'; intuition.
  }
Qed.

Definition union s s' := Mkt (union_ok (is_ok s) (is_ok s')).

Fixpoint inter_aux (l : t_aux) : t_aux -> t_aux :=
  match l with
    | nil    => fun _ => nil
    | x :: l' =>
        (fix inter_aux_aux (l'' : t_aux) : t_aux :=
           match l'' with
             | nil      => nil
             | x' :: l''' =>
                  match compare x x' with
                    | Lt => inter_aux l' l''
                    | Eq => x :: inter_aux l' l'''
                    | Gt => inter_aux_aux l'''
                  end
           end)
  end.

Lemma lt_Inf : forall a x l, lt a x -> Inf x l -> Inf a l.
Proof.
intros a x l; induction l; [intros; apply Inf_nil|].
intros; constructor; inv; apply lt_trans with x; auto.
Qed.

Lemma inter_inf : forall (l l' : t_aux) (a : elt) (Hs : Ok l) (Hs' : Ok l'),
  Inf a l -> Inf a l' -> Inf a (inter_aux l l').
Proof.
intro l; elim l; clear l; [auto|intros x l IHl l']; elim l'; clear l'; [auto|].
intros x' l' IHl' a Hl Hl'; simpl; assert (H1 := Hl); assert (H2 := Hl').
apply Ok_inv in H1; apply Ok_inv in H2; elim (Compare x x'); simpl; intros;
[inv; constructor; auto|apply IHl|apply IHl']; try solve [intuition];
[apply lt_Inf with x|apply lt_Inf with x']; inv; intuition.
Qed.

Global Instance inter_ok l l' : forall `(Ok l, Ok l'), Ok (inter_aux l l').
Proof.
repeat rewrite <- isok_iff; revert l'; elim l; clear l; [simpl; auto|].
intros x l IHl l'; elim l'; clear l'; [simpl; auto|intros x' l' IHl' Hl Hl'].
simpl; destruct (Compare x x') as [E|L|G]; simpl.

  {
  constructor; [apply IHl|]; rewrite isok_iff in *;
  apply Ok_inv in Hl; apply Ok_inv in Hl'; try solve [intuition].
  apply inter_inf; try solve [intuition].
  clear Hl; clear IHl; clear IHl'; clear l.
  destruct Hl' as [_ HInf]; revert HInf; rewrite !inf_iff.
  destruct l' as [|x'' l']; auto; simpl; destruct (Compare x x'') as [E'|L|G];
  auto; destruct (Compare x' x'') as [|HF|]; auto; exfalso;
  [apply (lt_not_eq _ _ HF); apply eq_trans with x; auto|
   apply (lt_not_eq _ _ (lt_trans _ _ _ HF G)); auto].
  }

  {
  apply IHl; auto; rewrite isok_iff in *; apply Ok_inv in Hl; intuition.
  }

  {
  cut (Sorted (inter_aux (x :: l) l')); [simpl; auto|apply IHl'; auto].
  rewrite isok_iff in *; auto; apply Ok_inv in Hl'; intuition.
  }
Qed.

Definition inter s s' := Mkt (inter_ok (is_ok s) (is_ok s')).

Fixpoint equal_aux (l l' : t_aux) : bool :=
  match l, l' with
    | nil     , nil        => true
    | x :: l'', x' :: l''' =>
        match compare x x' with
          | Eq => equal_aux l'' l'''
          | _  => false
        end
    | _,      _        => false
  end.

Definition equal s s' := equal_aux (this s) (this s').

Definition flip {A B C : Type} (f : A -> B -> C) := fun x y => f y x.

Definition fold_aux (A : Type) (f : elt -> A -> A) l i : A :=
  fold_left (flip f) l i.

Definition fold (A : Type) (f : elt -> A -> A) s i := fold_aux f (this s) i.

Fixpoint filter_aux (f : elt -> bool) (l : t_aux) : t_aux :=
  match l with
    | nil     => nil
    | x :: l' => if f x then x :: filter_aux f l' else filter_aux f l'
  end.

Global Instance filter_ok f l : forall `(Ok l), Ok (filter_aux f l).
Proof.
rewrite <- !isok_iff; elim l; [simpl; auto|clear l; intros x l IHl].
simpl; case (f x); intro Hl; [|apply IHl; inv; auto].
constructor; [apply IHl; inv; auto|clear IHl; revert Hl].
elim l; clear l; [simpl; intros; apply Inf_nil|intros y l IHl].
simpl; case (f y); [intro; inv; constructor; auto|intro Hl].
apply IHl; inv; constructor; auto; eapply lt_Inf; eauto.
Qed.

Definition filter f s := Mkt (filter_ok f (is_ok s)).

Fixpoint for_all_aux (f : elt -> bool) (l : t_aux) : bool :=
  match l with
    | nil     => true
    | x :: l' => if f x then for_all_aux f l' else false
  end.

Definition for_all f s := for_all_aux f (this s).

Fixpoint exists_aux (f : elt -> bool) (l : t_aux) : bool :=
  match l with
    | nil     => false
    | x :: l' => if f x then true else exists_aux f l'
  end.

Definition exists_ f s := exists_aux f (this s).

Fixpoint partition (f : elt -> bool) (l : t_aux) : t_aux * t_aux :=
  match l with
    | nil     => (nil, nil)
    | x :: l' =>
        let (s1, s2) := partition f l' in
        if f x then (x :: s1, s2) else (s1, x :: s2)
  end.

Definition cardinal_aux (l : t_aux) : nat := length l.

Definition cardinal s := cardinal_aux (this s).

Definition elements_aux (l : t_aux) : list elt := l.

Definition elements s := elements_aux (this s).

Definition choose_aux (l : t_aux) : option elt :=
  match l with
    | nil    => None
    | x :: _ => Some x
  end.

Definition choose s := choose_aux (this s).

Definition Equal_aux l l' := forall a : elt, In_list a l <-> In_list a l'.

Definition Equal s s' := Equal_aux (this s) (this s').

Lemma Equal_refl : forall s, Equal s s.
Proof. intros s x; intuition. Qed.

Lemma Equal_sym : forall s s', Equal s s' -> Equal s' s.
Proof. unfold Equal, Equal_aux; intros; apply iff_sym; auto. Qed.

Lemma Equal_trans : forall s1 s2 s3, Equal s1 s2 -> Equal s2 s3 -> Equal s1 s3.
Proof. unfold Equal, Equal_aux; intros s1 s2 s3 H1 H2 x; rewrite H1; auto. Qed.

Inductive lt_list : list elt -> list elt -> Prop :=
  | lt_list_nil     : forall x l, lt_list nil (x :: l)
  | lt_list_cons_lt : forall x y l l',
      lt x y -> lt_list (x :: l) (y :: l')
  | lt_list_cons_eq : forall x y l l',
      eq x y -> lt_list l l' -> lt_list (x :: l) (y :: l').

Hint Resolve lt_list_nil lt_list_cons_lt lt_list_cons_eq.

Definition lt_set s s' := lt_list (this s) (this s').

Lemma nlt_list_nil_nil : ~ lt_list nil nil.
Proof. intro; invlist lt_list. Qed.

Lemma nlt_list_cons_nil : forall a l, ~ lt_list (a :: l) nil.
Proof. intros a l HF; invlist lt_list. Qed.

Lemma lt_list_cons : forall a1 a2 l1 l2,
  lt_list (a1 :: l1) (a2 :: l2) -> lt a1 a2 \/ (eq a1 a2 /\ lt_list l1 l2).
Proof. intros a1 a2 l1 l2 Hlt; invlist lt_list; auto. Qed.

Lemma lt_list_trans : forall l1 l2 l3,
  Ok l1 -> Ok l2 -> Ok l3 -> lt_list l1 l2 -> lt_list l2 l3 -> lt_list l1 l3.
Proof.
intros l1; elim l1; clear l1;  [|intros a1 l1 IHl]; intro l2.

  {
  destruct l2 as [|a2 l2]; intro l3; [intros _ _ _ HF|destruct l3 as [|a3 l3]];
  [exfalso; apply nlt_list_nil_nil; auto|
   intros _ _ _ _ HF; exfalso; eapply nlt_list_cons_nil; eauto|
   intros; apply lt_list_nil].
  }

  {
  destruct l2 as [|a2 l2]; intro l3;
  [intros _ _ _ HF; exfalso; eapply nlt_list_cons_nil; eauto|].
  destruct l3 as [|a3 l3]; intros Hl1 Hl2 Hl3 L1 L2;
  [exfalso; eapply nlt_list_cons_nil; eauto|].
  apply lt_list_cons in L1; apply lt_list_cons in L2.
  destruct L1 as [L1|[E1 L1]]; destruct L2 as [L2|[E2 L2]].

    {
    apply lt_list_cons_lt; apply lt_trans with a2; auto.
    }

    {
    apply lt_list_cons_lt; apply lt_eq with a2; auto.
    }

    {
    apply lt_list_cons_lt; apply eq_lt with a2; auto.
    }

    {
    apply lt_list_cons_eq; [apply eq_trans with a2; auto|].
    apply IHl with l2; auto; eapply Ok_inv; eauto.
    }
  }
Qed.

Lemma lt_set_trans : forall s1 s2 s3,
  lt_set s1 s2 -> lt_set s2 s3 -> lt_set s1 s3.
Proof.
unfold lt_set; intros s1 s2 s3; apply lt_list_trans;
[destruct s1 as [s Hs]|destruct s2 as [s Hs]|destruct s3 as [s Hs]]; auto.
Qed.

Definition For_all_aux (P : elt -> Prop) l := forall x, In_list x l -> P x.

Definition For_all P s := For_all_aux P (this s).

Definition Exists_aux (P : elt -> Prop) (l : t_aux) :=
  exists x, In_list x l /\ P x.

Definition Exists P s := Exists_aux P (this s).

Definition Empty_aux l := forall a : elt, ~ In_list a l.

Definition Empty s := Empty_aux (this s).

Lemma Sort_Inf_In : forall l (x a : elt),
  Sorted l -> Inf a l -> In_list x l -> lt a x.
Proof.
simple induction l; [intros x a _ _ HIn; exfalso; inv|].
intros a l' Hl x a' HSort HInf HIn; rewrite In_cons in HIn.
destruct HIn as [Heq|HIn]; [inversion HInf; apply lt_eq with a; auto|].
apply Hl; try solve [eapply Sorted_inv; eauto]; auto.
induction l'; [apply Inf_nil|clear IHl'].
apply Sorted_inv in HSort; destruct HSort as [_ HInf'].
inversion HInf; clear H; clear H1; clear l0; clear b.
inversion HInf'; clear H; clear H2; clear l0; clear b.
apply Inf_cons, lt_trans with a; auto.
Qed.

Ltac sort_inf_in :=
  match goal with
    | H : Inf ?x ?l, H' : In_list ?y ?l |- _ =>
        cut (lt x y); [ intro | apply Sort_Inf_In with l; auto]
    | _                                 =>
        fail
  end.

Lemma mem_spec : forall (l : t_aux) (x : elt) (Hs : Ok l),
  mem_aux x l = true <-> In_list x l.
Proof.
induction l; intros x Hl; inv; simpl; [intuition; [discriminate|inv]|].
destruct (Compare x a) as [E|L|G]; rewrite In_cons; intuition; try discriminate;
try solve [right; apply IHl; auto; eapply Ok_inv; eauto];
try solve [exfalso; apply (lt_not_eq _ _ L); auto];
try solve [exfalso; apply (lt_not_eq _ _ G); auto];
apply Ok_inv in Hl; destruct Hl as [HOk HInf]; [|rewrite IHl; auto].
sort_inf_in; [|rewrite <- isok_iff in HOk; auto].
assert (HF : lt a a) by (apply lt_trans with x; auto).
exfalso; apply (lt_not_eq _ _ HF); auto.
Qed.

Lemma add_spec : forall (l : t_aux) (x y : elt) (Hs : Ok l),
  In_list y (add_aux x l) <-> eq x y \/ In_list y l.
Proof.
intro l; elim l; clear l; simpl; [intuition; inv; auto|intros a l IHl x y Hl].
apply Ok_inv in Hl; destruct Hl as [HOk HInf].
simpl; elim (Compare x a); intro; rewrite !In_cons, ?IHl; intuition.
left; apply eq_trans with x; auto.
Qed.

Lemma remove_spec : forall (l : t_aux) (x y : elt) (Hs : Ok l),
  In_list y (remove_aux x l) <-> In_list y l /\ ~ eq y x.
Proof.
intro l; elim l; clear l; simpl; [intuition; inv|intros a l IHl x y Hl].
apply Ok_inv in Hl; destruct Hl as [HOk HInf].
simpl; elim (Compare x a); intro HC; rewrite !In_cons, ?IHl; intuition;
try sort_inf_in; try solve [rewrite <- isok_iff in HOk; auto].

  {
  assert (C : lt a y) by auto.
  apply (lt_not_eq _ _ C); apply eq_trans with x; auto.
  }

  {
  exfalso; assert (eq y x) by (apply eq_trans with a; auto); intuition.
  }

  {
  apply (lt_not_eq _ _ HC), (eq_trans _ y); auto.
  }

  {
  apply (lt_le _ _ HC), (lt_eq _ y); auto.
  }

  {
  apply (lt_not_eq _ _ HC), (eq_trans _ y); auto.
  }
Qed.

Lemma singleton_spec : forall (x y : elt),
  In_list y (singleton_aux x) <-> eq x y.
Proof. unfold singleton_aux; simpl; split; intros; inv; auto. Qed.

Lemma union_spec_aux : forall l l' (x : elt) (Hl : Ok l) (Hl' : Ok l'),
  In_list x (union_aux l l') <-> In_list x l \/ In_list x l'.
Proof.
intro l; elim l; clear l; simpl; [intuition; inv|].
intros a l IHl l'; elim l'; clear l'; [intuition; inv|].
intros a' l' IHl' x Hl Hl'; simpl; elim (Compare a a'); intro HC;
rewrite !In_cons, ?IHl, ?IHl'; intuition;
try solve [eapply Ok_inv; eauto]; inv; auto.
left; apply eq_trans with a'; auto.
Qed.

Lemma union_spec : forall s s' x,
  In x (union s s') <-> In x s \/ In x s'.
Proof. unfold In; intros [s Hs] [s' Hs'] x; apply union_spec_aux; auto. Qed.

Lemma inter_spec_aux : forall l l' (x : elt) (Hl : Ok l) (Hl' : Ok l'),
  In_list x (inter_aux l l') <-> In_list x l /\ In_list x l'.
Proof.
intro l; elim l; clear l; simpl; [intuition; inv|].
intros a l IHl l'; elim l'; clear l'; [intuition; inv|].
intros a' l' IHl' x Hl Hl'; simpl; elim (Compare a a'); intro HC;
rewrite !In_cons, ?IHl, ?IHl'; intuition;
try solve [eapply Ok_inv; eauto]; inv; auto;
try solve [left; apply eq_trans with a'; auto];
try solve [left; apply eq_trans with a; auto];
try solve [exfalso; apply (lt_not_eq _ _ HC); apply eq_trans with x; auto];
[apply Ok_inv in Hl'; destruct Hl'|apply Ok_inv in Hl; destruct Hl];
[cut (lt a' x)|cut (lt a x)];
try solve [eapply Sort_Inf_In; eauto; rewrite <- isok_iff in *; auto];
intro L; assert (HF := lt_trans _ _ _ HC L);
exfalso; apply (lt_not_eq _ _ HF); auto.
Qed.

Lemma inter_spec : forall s s' x,
  In x (inter s s') <-> In x s /\ In x s'.
Proof. unfold In; intros [s Hs] [s' Hs'] x; apply inter_spec_aux; auto. Qed.

Lemma nEqual_aux_nil_cons : forall x l, Ok (x :: l) -> ~ Equal_aux nil (x :: l).
Proof.
intros x l Hl E; assert (HF := E x); do 2 rewrite <- mem_spec in HF; auto;
try apply empty_ok; simpl in HF; apply diff_false_true; rewrite HF.
elim (Compare x x); auto; intro L; exfalso; apply (lt_not_eq _ _ L); auto.
Qed.

Lemma equal_spec : forall (l l' : t_aux) (Hl : Ok l) (Hl' : Ok l'),
  equal_aux l l' = true <-> Equal_aux l l'.
Proof.
induction l as [|x l IHl]; intros [|x' l'] Hl Hl'; simpl;
try solve [unfold Equal_aux; intuition];
[split; [discriminate|intro HF; apply nEqual_aux_nil_cons in Hl'; auto]|
 split; [discriminate|intro HF; apply nEqual_aux_nil_cons in Hl;
                      exfalso; apply Hl; intro a; rewrite (HF a); tauto]|].
elim (Compare x x'); intro HC.

  {
  rewrite IHl; try solve [eapply Ok_inv; eauto].
  split; intros E y; specialize (E y).

    {
    rewrite !In_cons; intuition; left;
    [apply eq_trans with x|apply eq_trans with x']; auto.
    }

    {
    rewrite !In_cons in E; rename E into E'.
    assert (E : eq y x \/ In_list y l <-> eq y x \/ In_list y l')
      by (intuition; left; apply eq_trans with x'; auto).
    clear E'; apply Ok_inv in Hl; apply Ok_inv in Hl'.
    destruct Hl as [HOk HInf]; destruct Hl' as [HOk' HInf']; intuition;
    try (cut (lt x y); [intro L; exfalso; apply (lt_not_eq _ _ L);
                        auto; apply eq_trans with x; auto|
                        eapply Sort_Inf_In; eauto;
                        rewrite <- isok_iff in *; auto]);
    try (cut (lt x' y); [intro L; exfalso; apply (lt_not_eq _ _ L);
                    auto; apply eq_trans with x; auto|
                    eapply Sort_Inf_In; eauto;
                    rewrite <- isok_iff in *; auto]).
    }
  }

  {
  split; intro E; [discriminate|].
  assert (In_list x (x' :: l')) by (specialize (E x); rewrite <- E; auto).
  exfalso; inv; [apply (lt_not_eq _ _ HC); auto|].
  apply Ok_inv in Hl'; destruct Hl' as [HOk' HInf']; sort_inf_in;
  [apply (lt_le _ _ HC)|apply isok_iff]; auto.
  }

  {
  split; intro E; [discriminate|].
  assert (In_list x' (x :: l)) by (specialize (E x'); rewrite E; auto).
  exfalso; inv; [apply (lt_not_eq _ _ HC); auto|].
  apply Ok_inv in Hl; destruct Hl as [HOk HInf]; sort_inf_in;
  [apply (lt_le _ _ HC)|apply isok_iff]; auto.
  }
Qed.

Lemma equal_Equal : forall s s', equal s s' = true <-> Equal s s'.
Proof.
intros; destruct s; destruct s'.
unfold equal, Equal; simpl; apply equal_spec; auto.
Qed.

Fixpoint compare_list (l l' : t_aux) : comparison :=
  match l, l' with
    | nil   , nil          => Eq
    | nil   , _            => Lt
    | _     , nil          => Gt
    | x :: l'', x' :: l''' =>
        match compare x x' with
          | Lt => Lt
          | Eq => compare_list l'' l'''
          | Gt => Gt
        end
  end.

Definition compare_set s s' := compare_list (this s) (this s').

Lemma Compare_list : forall l l',
  Ok l -> Ok l' ->
  CompareSpec (Equal_aux l l') (lt_list l l') (lt_list l' l)
              (compare_list l l').
Proof.
intro l; elim l; clear l.

  {
  intro l'; elim l'; clear l'; simpl; intros;
  [apply CompEq; unfold Equal_aux; intuition|apply CompLt, lt_list_nil].
  }

  {
  intros a l IHl l'; elim l'; clear l';
  [intros; simpl; apply CompGt, lt_list_nil|].
  intros a' l' _ Hl Hl'; generalize (Compare a a'); intro C; simpl.
  elim (Compare a a'); intro E; [|apply CompLt, lt_list_cons_lt; auto|
                                  apply CompGt, lt_list_cons_lt; auto].
  destruct (IHl l') as [E'|L|G]; try (eapply Ok_inv; eauto);
  [apply CompEq|apply CompLt|apply CompGt];
  try apply lt_list_cons_eq; auto; rewrite <- equal_spec in *; auto;
  try (eapply Ok_inv; eauto); simpl; elim (Compare a a'); auto;
  intro HF; exfalso; apply (lt_not_eq _ _ HF); auto.
  }
Qed.

Lemma Compare_set : forall s s',
  CompareSpec (Equal s s') (lt_set s s') (lt_set s' s) (compare_set s s').
Proof. intros [s Hs] [s' Hs']; apply Compare_list; auto. Qed.

Lemma lt_list_not_Equal : forall l1 l2,
  Ok l1 -> Ok l2 -> lt_list l1 l2 -> ~ Equal_aux l1 l2.
Proof.
intro l1; elim l1; clear l1; [|intros a1 l1 IHl]; intro l2.

  {
  destruct l2 as [|a2 l2];
  [intros _ _ HF; exfalso; apply nlt_list_nil_nil; auto|].
  intros; rewrite <- equal_spec; simpl; auto.
  }

  {
  destruct l2 as [|a2 l2];
  [intros _ _ HF; exfalso; eapply nlt_list_cons_nil; eauto|].
  intros Hl1 Hl2 L; rewrite <- equal_spec; auto.
  apply lt_list_cons in L; destruct L as [L|[E L]];
  simpl; elim (Compare a1 a2); auto;
  [intro H; exfalso; apply (lt_not_eq _ _ L); auto|
   intro E'; rewrite equal_spec; [apply IHl| |]; auto; eapply Ok_inv; eauto].
  }
Qed.

Lemma lt_set_not_Equal : forall s s', lt_set s s' -> ~ Equal s s'.
Proof. intros [s Hs] [s' Hs']; apply lt_list_not_Equal; auto. Qed.

Lemma empty_spec : Empty_aux empty_aux.
Proof. unfold Empty, Empty_aux, empty_aux; intuition; inv. Qed.

Lemma is_empty_spec : forall (s : t_aux),
  is_empty_aux s = true <-> Empty_aux s.
Proof.
intros [|x s]; [split; auto; intro; inv; apply empty_spec|].
split; [discriminate|intro H; elim (H x); auto].
Qed.

Lemma elements_spec2w : forall (s : t_aux) (Hs : Ok s),
  NoDupA eq (elements_aux s).
Proof.
intro s; repeat rewrite <- isok_iff; intro; apply SortA_NoDupA with lt;
[exact eq_equiv|exact lt_strorder|exact lt_compat|].
unfold elements; revert H; induction s; [intro; apply Sorted.Sorted_nil|].
intro HSorted; apply Sorted_inv in HSorted; destruct HSorted as [HSorted HInf].
apply Sorted.Sorted_cons; [apply IHs; auto|].
revert HInf; clear HSorted; clear IHs; induction s; intro; [apply HdRel_nil|].
apply HdRel_cons; revert HInf; rewrite inf_iff; unfold inf.
elim (Compare a a0); auto; discriminate.
Qed.

Lemma choose_spec1 : forall (s : t_aux) (x : elt),
  choose_aux s = Some x -> In_list x s.
Proof. destruct s; simpl; inversion 1; apply In_cons_hd, eq_refl. Qed.

Lemma choose_spec2 : forall (s : t_aux),
  choose_aux s = None -> Empty_aux s.
Proof. destruct s; simpl; red; intuition; [inv|discriminate]. Qed.

Lemma filter_spec : forall (s : t_aux) (x : elt) (f : elt -> bool),
  Proper (eq ==> Logic.eq) f ->
  (In_list x (filter_aux f s) <-> In_list x s /\ f x = true).
Proof.
induction s; simpl; intros x f Hf; [split; intuition; inv|].
destruct (f a) eqn:F; rewrite !In_cons, ?IHs; intuition;
[rewrite (Hf x a); auto|].
rewrite (Hf a x) in F; auto; rewrite F in *; discriminate.
Qed.

Lemma for_all_spec : forall (s : t_aux) (f : elt -> bool),
  Proper (eq ==> Logic.eq) f  ->
  (for_all_aux f s = true <-> For_all_aux (fun x => f x = true) s).
Proof.
unfold For_all_aux; induction s; simpl; intros f Hf; [split; intuition; inv|].
destruct (f a) eqn:F;
[rewrite IHs; auto; firstorder; inv; auto; rewrite (Hf x a); auto|
 split; intro H'; [discriminate|rewrite H' in F; auto; discriminate]].
Qed.

Lemma exists_spec : forall (s : t_aux) (f : elt -> bool),
  Proper (eq ==> Logic.eq) f ->
  (exists_aux f s = true <-> Exists_aux (fun x => f x = true) s).
Proof.
unfold Exists_aux; induction s; simpl; intros f Hf;
[firstorder; [discriminate|inv]|].
destruct (f a) eqn:F; firstorder; rewrite IHs; auto.
exists x; split; auto; rewrite In_cons in H; intuition.
rewrite (Hf a x) in F; auto; rewrite F in *; discriminate.
Qed.

Lemma elements_spec1 : forall (s : t_aux) (x : elt),
  In_list x (elements_aux s) <-> In_list x s.
Proof. intuition. Qed.

Lemma partition_spec1 : forall (s : t_aux) (f : elt -> bool),
  Proper (eq  ==> Logic.eq) f ->
  Equal_aux (fst (partition f s)) (filter_aux f s).
Proof.
simple induction s; simpl; unfold Equal_aux; [intros; split; auto|].
intros x l Hrec f Hf; generalize (Hrec f Hf); clear Hrec.
destruct (partition f l) as [s1 s2]; simpl; intro H.
case (f x); simpl; auto.
split; inversion_clear 1; auto; constructor 2; [rewrite <- H|rewrite H]; auto.
Qed.

Lemma partition_spec2 : forall (s : t_aux) (f : elt -> bool),
  Proper (eq  ==> Logic.eq) f ->
  Equal_aux (snd (partition f s)) (filter_aux (fun x => negb (f x)) s).
simple induction s; simpl; unfold Equal_aux; [intros; split; auto|].
intros x l Hrec f Hf; generalize (Hrec f Hf); clear Hrec.
destruct (partition f l) as [s1 s2]; simpl; intro H.
case (f x); simpl; auto.
split; inversion_clear 1; auto; constructor 2; [rewrite <- H|rewrite H]; auto.
Qed.

Lemma fold_spec : forall (s : t_aux) (A : Type) (i : A) (f : elt -> A -> A),
  fold_aux f s i = fold_left (flip f) (elements_aux s) i.
Proof. reflexivity. Qed.

Lemma cardinal_spec : forall (s : t_aux) (Hs : Ok s),
  cardinal_aux s = length (elements_aux s).
Proof. auto. Qed.

Lemma mem_1 : forall (s : t) (x : elt),
  In x s -> mem x s = true.
Proof. intros; destruct s; apply <- mem_spec; auto. Qed.

Lemma mem_2 : forall (s : t) (x : elt),
  mem x s = true -> In x s.
Proof. intros; destruct s; apply mem_spec; auto. Qed.

Lemma equal_1 : forall (s s' : t),
  Equal s s' -> equal s s' = true.
Proof. intros; destruct s; destruct s'; apply <- equal_spec; auto. Qed.

Lemma equal_2 : forall (s s' : t),
  equal s s' = true -> Equal s s'.
Proof. intros; destruct s; destruct s'; apply equal_spec; auto. Qed.

Lemma remove_3 : forall (s : t) (x y : elt),
  In y (remove x s) -> In y s.
Proof.
intros s x y; destruct s; unfold In; simpl; intro H.
rewrite remove_spec in H; intuition.
Qed.

Lemma singleton_1 : forall (x y : elt),
  In y (singleton x) -> eq x y.
Proof. intros; apply singleton_spec; auto. Qed.

Lemma union_1 : forall (s s' : t) (x : elt),
  In x (union s s') -> In x s \/ In x s'.
Proof. intros; destruct s; destruct s'; apply union_spec; auto. Qed.

Lemma filter_1 : forall (s : t) (x : elt) (f : elt -> bool),
  Proper (eq ==> Logic.eq) f -> In x (filter f s) -> In x s.
Proof. intros s x f P; unfold In; simpl; rewrite filter_spec; intuition. Qed.

Lemma filter_2 : forall (s : t) (x : elt) (f : elt -> bool),
  Proper (eq ==> Logic.eq) f -> In x (filter f s) -> f x = true.
Proof. intros s x f P; unfold In; simpl; rewrite filter_spec; intuition. Qed.

Lemma for_all_1 : forall (s : t) (f : elt -> bool),
  Proper (eq ==> Logic.eq) f ->
  For_all (fun x => f x = true) s -> for_all f s = true.
Proof. intros s f Hf H; apply <- for_all_spec; auto. Qed.

Lemma exists_2 : forall (s : t) (f : elt -> bool),
  Proper (eq ==> Logic.eq) f ->
  exists_ f s = true -> Exists (fun x => f x = true) s.
Proof. intros s f P; apply exists_spec; auto. Qed.

Lemma singleton_equal_add : forall (x : elt),
  Equal (singleton x) (add x empty).
Proof.
intro x; unfold Equal; rewrite <- equal_spec;
[|apply singleton_ok|apply add_ok, empty_ok].
simpl; elim (Compare x x); auto; intro H; assert (HF := lt_not_eq _ _ H); auto.
Qed.

Lemma In_eq_iff_aux : forall s (x y : elt),
  eq x y -> (In_list x s <-> In_list y s).
Proof.
intros s x y E; apply iff_sym; induction s; [intuition; inv; auto|].
intuition; inv; try solve [apply In_cons_tl; auto];
apply In_cons_hd; [apply eq_trans with y|apply eq_trans with x]; auto.
Qed.

Lemma In_eq_iff : forall s (x y : elt),
  eq x y -> (In x s <-> In y s).
Proof.
intros s x y; destruct s as [s Hs]; unfold In; simpl; apply In_eq_iff_aux.
Qed.

Lemma mem_iff : forall (s : t) (x : elt),
  In x s <-> mem x s = true.
Proof. intros; destruct s; apply iff_sym, mem_spec; simpl; auto. Qed.

Lemma not_mem_iff : forall (s : t) (x : elt),
  ~ In x s <-> mem x s = false.
Proof. intros; destruct s as [s Hs]; unfold In; simpl.
rewrite <- mem_spec; auto. unfold mem; simpl; destruct (mem_aux x s); intuition.
Qed.

Lemma empty_iff : forall (x : elt),
 In x empty <-> False.
Proof. intuition; apply (empty_spec H). Qed.

Lemma is_empty_iff : forall (s : t),
  Empty s <-> is_empty s = true.
Proof. intro s; apply iff_sym, is_empty_spec. Qed.

Lemma add_iff : forall (s : t) (x y : elt),
  In y (add x s) <-> eq x y \/ In y s.
Proof. intros; unfold In; simpl; destruct s; rewrite add_spec; intuition. Qed.

Lemma add_neq_iff : forall (s : t) (x y : elt),
  ~ eq x y -> (In y (add x s) <-> In y s).
Proof.
intros s x y; unfold In; simpl; destruct s; rewrite add_spec; intuition.
Qed.

Lemma remove_iff : forall (s : t) (x y : elt),
  In y (remove x s) <-> In y s /\ ~ eq x y.
Proof.
intros s x y; unfold In; simpl; destruct s;rewrite remove_spec; intuition.
Qed.

Lemma remove_neq_iff : forall (s : t) (x y : elt),
  ~ eq x y -> (In y (remove x s) <-> In y s).
Proof.
intros s x y; unfold In; simpl; destruct s;rewrite remove_spec; intuition.
Qed.

Lemma for_all_iff : forall (s : t) (f : elt -> bool),
  Proper (eq ==> Logic.eq) f ->
  (For_all (fun x => f x = true) s <-> for_all f s = true).
Proof. intros; apply iff_sym, for_all_spec; auto. Qed.

Lemma exists_iff : forall (s : t) (f : elt -> bool),
  Proper (eq ==> Logic.eq) f ->
  (Exists (fun x => f x = true) s <-> exists_ f s = true).
Proof. intros s f Hf; apply iff_sym, exists_spec; auto. Qed.

Lemma elements_iff : forall (s : t) (x : elt),
  In x s <-> In_list x (elements s).
Proof. intros; apply iff_sym, elements_spec1. Qed.

Lemma empty_b : forall (y : elt),
  mem y empty = false.
Proof.
intro y; generalize (empty_iff y) (mem_iff empty y).
destruct (mem y empty); intuition.
Qed.

Lemma add_b : forall (s : t) (x y : elt), mem y (add x s) = eqb x y || mem y s.
Proof.
intros; generalize (mem_iff (add x s) y) (mem_iff s y) (add_iff s x y).
generalize (eqb_eq x y); destruct (eqb x y); destruct (mem y s);
destruct (mem y (add x s)); intuition.
Qed.

Lemma add_neq_b : forall (s : t) (x y : elt),
  ~ eq x y -> mem y (add x s) = mem y s.
Proof.
intros s x y E.
generalize (mem_iff (add x s) y) (mem_iff s y) (add_neq_iff s x y E).
destruct (mem y s); destruct (mem y (add x s)); intuition.
Qed.

Lemma remove_neq_b : forall (s : t) (x y : elt),
  ~ eq x y -> mem y (remove x s) = mem y s.
Proof.
intros s x y E.
generalize (mem_iff (remove x s) y) (mem_iff s y) (remove_neq_iff s x y E).
destruct (mem y s); destruct (mem y (remove x s)); intuition.
Qed.

Lemma union_b : forall (s s' : t) (x : elt),
  mem x (union s s') = mem x s || mem x s'.
Proof.
intros; generalize (mem_iff (union s s') x) (union_spec s s' x).
generalize (mem_iff s x) (mem_iff s' x).
destruct (mem x s); destruct (mem x s'); destruct (mem x (union s s')); intuition.
Qed.

Lemma inter_b : forall (s s' : t) (x : elt),
  mem x (inter s s') = mem x s && mem x s'.
Proof.
intros; generalize (mem_iff (inter s s') x) (inter_spec s s' x).
generalize (mem_iff s x) (mem_iff s' x).
destruct (mem x s); destruct (mem x s'); destruct (mem x (inter s s')); intuition.
Qed.

Lemma filter_b : forall (s : t) (x : elt) (f : elt -> bool),
  Proper (eq ==> Logic.eq) f -> mem x (filter f s) = mem x s && f x.
Proof.
intros s x f Hf.
generalize (mem_iff (filter f s) x) (mem_iff s x) (filter_spec (this s) x Hf).
destruct (mem x s); destruct (mem x (filter f s)); destruct (f x);
simpl; intuition.
Qed.

Lemma for_all_b : forall (s : t) (f : elt -> bool),
  Proper (eq ==> Logic.eq) f -> for_all f s = forallb f (elements s).
Proof.
intros s f Hf.
generalize (forallb_forall f (elements s)) (for_all_iff s Hf) (elements_iff s).
unfold For_all.
destruct (forallb f (elements s)); destruct (for_all f s); auto; intros H1 H2.

  {
  rewrite <- H2; intros H x HIn; destruct H1 as [H1 _].
  rewrite (H x) in HIn; apply In_alt in HIn; destruct HIn as [y [HEq HIn]].
  rewrite (Hf x y HEq); apply H1; auto.
  }

  {
  symmetry; rewrite H1; intros x HIn.
  destruct H2 as [_ H2]; apply H2; auto; unfold In in H; rewrite H, In_alt.
  exists x; auto.
  }
Qed.

Lemma exists_b : forall (s : t) (f : elt -> bool),
    Proper (eq ==> Logic.eq) f -> exists_ f s = existsb f (elements s).
Proof.
intros s f Hf.
generalize (existsb_exists f (elements s)) (exists_iff s Hf) (elements_iff s).
unfold Exists.
destruct (existsb f (elements s)), (exists_ f s); auto; intros H1 H2 H3.

  {
  rewrite <- H2; destruct H1 as [[x [Hx1 Hx2]] _]; auto.
  exists x; split; auto.
  unfold In in H3; rewrite H3, In_alt; exists x; split; auto.
  }

  {
  symmetry; rewrite H1; destruct H2 as [_ [x [Hx1 Hx2]]]; auto.
  rewrite (H3 x) in Hx1; rewrite (In_alt x (elements s)) in Hx1.
  destruct Hx1 as [y [Hy1 Hy2]]; exists y; split; auto.
  rewrite <- (Hf _ _ Hy1); auto.
  }
Qed.

Instance In_m : Proper (eq ==> Equal ==> iff) In.
Proof.
intros x y H s s' H'; rewrite (In_eq_iff s _ _ H); unfold In; auto.
Qed.

Instance Empty_m : Proper (Equal ==> iff) Empty.
Proof.
intros s s' H; split; intros HF a HIn; [|apply Equal_sym in H];
apply (HF a); rewrite (In_m a a (eq_refl a) H); apply HIn.
Qed.

Instance mem_m : Proper (eq ==> Equal ==> Logic.eq) mem.
Proof.
intros x x' Hx s s' Hs; generalize (mem_iff s x).
rewrite (In_m x x' Hx Hs); destruct (mem x s), (mem x s');
intuition; try solve [apply mem_1 in H; auto];
apply Logic.eq_sym; rewrite <- not_mem_iff; intuition.
Qed.

Instance remove_m : Proper (eq ==> Equal ==> Equal) remove.
Proof.
intros x x' Hx s s' Hs a; assert (H := remove_iff); unfold In in H.
rewrite !H, (In_m a a (eq_refl a) Hs); intuition.
  {
  assert (eq x a) by (apply eq_trans with x'; auto); intuition.
  }

  {
  assert (eq x' a) by (apply eq_trans with x; auto); intuition.
  }
Qed.

Instance is_empty_m : Proper (Equal ==> Logic.eq) is_empty.
Proof.
intros s s' H; generalize (is_empty_iff s); rewrite (Empty_m H).
rewrite is_empty_iff; destruct (is_empty s); destruct (is_empty s'); intuition.
Qed.

Lemma filter_ext : forall (f f' : elt -> bool),
  Proper (eq ==> Logic.eq) f -> (forall x, f x = f' x)->
  forall (s s' : t), Equal s s' -> Equal (filter f s) (filter f' s').
Proof.
intros f f' Hf Hff' s s' Hss' x; unfold filter; simpl; rewrite 2 filter_spec;
auto; [rewrite Hff', (In_m x x (eq_refl x) Hss'); intuition|].
red; red; intros; rewrite <- 2 Hff'; auto.
Qed.

Lemma is_empty_1 : forall (s : t),
  Empty s -> is_empty s = true.
Proof. intros s H; apply <- is_empty_spec; auto. Qed.

Lemma choose_mem_1 : forall (s : t) (x : elt),
  choose s = Some x -> mem x s = true.
Proof. intros s x H; apply choose_spec1 in H; apply mem_1; auto. Qed.

Lemma choose_mem_3 : forall (s : t),
  is_empty s = false -> {x : elt | choose s = Some x /\ mem x s = true}.
Proof.
intros s H; generalize (choose_spec1 (this s)) (@choose_spec2 (this s)).
unfold choose; destruct (choose_aux (this s)); intros H1 H2;
[exists e; split; auto; apply mem_1, H1; auto|].
assert (H3 : Empty s) by (apply H2; auto).
rewrite (is_empty_1 H3) in H; discriminate.
Qed.

Lemma inter_equal_1 : forall s1 s2 s3,
  Equal s1 s2 -> Equal (inter s1 s3) (inter s2 s3).
Proof.
intros [s1 Hs1] [s2 Hs2] [s3 Hs3] H a; unfold Equal in *; simpl in *.
rewrite !inter_spec_aux; intuition; apply H; auto.
Qed.

Lemma inter_equal_2 : forall s1 s2 s3,
  Equal s2 s3 -> Equal (inter s1 s2) (inter s1 s3).
Proof.
intros [s1 Hs1] [s2 Hs2] [s3 Hs3] H a; unfold Equal in *; simpl in *.
rewrite !inter_spec_aux; intuition; apply H; auto.
Qed.

Lemma fold_spec_right s (A : Type) (i : A) (f : elt -> A -> A) :
  fold_aux f s i = List.fold_right f i (rev (elements_aux s)).
Proof. rewrite fold_spec; symmetry; apply fold_left_rev_right. Qed.

Lemma fold_0 : forall s (Hs : Ok s) (A : Type) (i : A) (f : elt -> A -> A),
  exists l : list elt,
    NoDupA eq l /\ (forall x : elt, In_list x s <-> InA eq x l) /\
    (fold_aux f s i = fold_right f i l).
Proof.
intros s Hs A i f; exists (rev (elements_aux s)); split;
[apply NoDupA_rev; [exact eq_equiv|apply elements_spec2w; auto]|].
split; [intro; rewrite <- elements_spec1|apply fold_spec_right].
rewrite In_alt, InA_alt.
split; destruct 1;
generalize (In_rev (elements_aux s) x0); exists x0; intuition.
Qed.

Lemma fold_1 : forall (A : Type) (eqA : A -> A -> Prop) (f : elt -> A -> A),
  Equivalence eqA -> Proper (eq ==> eqA ==> eqA) f -> transpose eqA f ->
  forall s (Hs : Ok s) i,
  Empty_aux s -> eqA (fold_aux f s i) i.
Proof.
unfold Empty_aux; intros A eqA f fP1 fP2 fP3 s Hs i HIn.
destruct (fold_0 Hs i f) as [l [Hl1 [Hl2 Hl3]]].
rewrite Hl3; clear Hl3.
generalize HIn Hl2; clear HIn; clear Hl2; case l; simpl; [reflexivity|].
clear Hl1; clear l; intros e l HIn Hl2; elim (HIn e); elim (Hl2 e); intuition.
Qed.

Definition Add x s s' := forall y, In_list y s' <-> eq x y \/ In_list y s.

Lemma fold_2 : forall (A : Type) (eqA : A -> A -> Prop) (f : elt -> A -> A),
  Equivalence eqA -> Proper (eq ==> eqA ==> eqA) f -> transpose eqA f ->
  forall s (Hs : Ok s) s' (Hs' : Ok s') x i,
    ~ In_list x s -> Add x s s' -> eqA (fold_aux f s' i) (f x (fold_aux f s i)).
Proof.
intros A eqA f fP1 fP2 fP3 s Hs s' Hs' x i HIn HAdd.
destruct (fold_0 Hs i f) as [l [Hl1 [Hl2 Hl3]]].
destruct (fold_0 Hs' i f) as [l' [Hl'1 [Hl'2 Hl'3]]].
rewrite Hl3, Hl'3; clear Hl3; clear Hl'3.
apply fold_right_add with (eqA:=eq) (eqB:=eqA); auto; [exact eq_equiv| |];
[eauto with *; rewrite <- Hl2; auto|].
intro a; rewrite InA_cons, <- Hl2, <- Hl'2; rewrite (HAdd a); intuition.
Qed.

Lemma fold_equal : forall (A : Type) (eqA : A -> A -> Prop) (f : elt -> A -> A),
  Equivalence eqA -> Proper (eq ==> eqA ==> eqA) f -> transpose eqA f ->
  forall i s (Hs : Ok s) s' (Hs' : Ok s'),
  Equal_aux s s' -> eqA (fold_aux f s i) (fold_aux f s' i).
Proof.
intros A eqA f E Comp Ass i s.
elim s; [intros Hs s' Hs' Hss'|intros a s'' _ Hs s' Hs' Hss'].

  {
  transitivity i; [apply fold_1; auto; apply empty_spec|symmetry].
  apply fold_1; auto; intros a HF; apply Hss' in HF; inv.
  }

  {
  transitivity (f a (fold_aux f s'' i)); [|symmetry];
  apply fold_2 with (eqA:=eqA); auto;
  try solve [apply Ok_inv in Hs; destruct Hs; auto];
  try (intro e;  unfold Equal_aux in *; rewrite <- Hss'; revert e);
  try solve [intro; split; intro H;
             [apply In_cons in H|apply In_cons]; intuition];
  clear Hss'; clear Hs'; clear s'; clear i; clear Ass; clear Comp;
  clear E; clear f; clear eqA; clear A; clear s; revert Hs; revert a;
  elim s''; clear s''; try (intro a; rewrite <- InP, InA_nil; auto);
  intros y s IHs x Hs; rewrite In_cons; intuition;
  try solve [apply Ok_inv in Hs; destruct Hs as [_ Hs]; inv;
             apply (lt_not_eq x y); auto];
  apply IHs with x; auto;
  clear IHs; revert Hs; revert y; revert dependent x; intros x _; revert x;
  elim s; clear s; try solve [intros; apply singleton_ok];
  intros z s IHs x y Hs;
  apply Ok_inv in Hs; destruct Hs as [Hs L1];
  apply Ok_inv in Hs; destruct Hs as [Hs L2];
  inv; apply Sorted_cons; try (apply isok_iff; auto); apply Inf_cons;
  apply lt_trans with y; auto.
  }
Qed.

Lemma fold_add : forall (A : Type) (eqA : A -> A -> Prop) (f : elt -> A -> A),
  Equivalence eqA -> Proper (eq ==> eqA ==> eqA) f -> transpose eqA f ->
  forall i s (Hs : Ok s) x,
    ~ In_list x s -> eqA (fold_aux f (add_aux x s) i) (f x (fold_aux f s i)).
Proof.
intros A eqA f E Comp Ass i s Hs x HIn.
apply fold_2 with (eqA:=eqA); auto;
[apply add_ok; auto|intro; apply add_spec; auto].
Qed.

Lemma add_fold : forall (A : Type) (eqA : A -> A -> Prop) (f : elt -> A -> A),
  Equivalence eqA -> Proper (eq ==> eqA ==> eqA) f -> transpose eqA f ->
  forall  i s (Hs : Ok s) x,
    In_list x s -> eqA (fold_aux f (add_aux x s) i) (fold_aux f s i).
Proof.
intros A eqA f E Comp Ass i s Hs x HIn.
apply fold_equal; auto;
[apply add_ok; auto|intro].
rewrite add_spec; intuition; apply In_eq_iff_aux with x; auto.
Qed.

Lemma cardinal_fold : forall s (Hs : Ok s),
  cardinal_aux s = fold_aux (fun _ => S) s 0.
Proof.
intros; rewrite cardinal_spec; auto; rewrite fold_spec.
symmetry; apply fold_left_length.
Qed.

Lemma cardinal_1_aux : forall s, Empty_aux s -> cardinal_aux s = 0.
Proof.
intros s H; rewrite cardinal_fold; [apply fold_1|]; auto; try congruence;
[exact eq_equivalence| |]; unfold Empty_aux in H; revert H; elim s;
try (intros a l _ H; exfalso; apply (H a), InP, InA_cons_hd, eq_refl);
intros _; apply isok_iff, Sorted_nil.
Qed.

Lemma cardinal_Empty : forall s, Empty s <-> cardinal s = 0.
Proof.
intros [s Hs]; split; [apply cardinal_1_aux|].
revert Hs; elim s; [intros; apply empty_spec|intros a l _ Hs HF].
unfold cardinal in HF; simpl in *; discriminate.
Qed.

Lemma cardinal_inv_2 : forall s n, cardinal s = S n -> { x : elt | In x s }.
Proof.
intros [s Hs] n; destruct s; [unfold cardinal; simpl; discriminate|].
exists e; apply InP, InA_cons_hd, eq_refl.
Qed.

Lemma cardinal_inv_2b : forall s, cardinal s <> 0 -> { x : elt | In x s }.
Proof.
intro; generalize (@cardinal_inv_2 s); destruct cardinal; [intuition|eauto].
Qed.

Lemma remove_fold_1 : forall (A : Type) (eqA : A -> A -> Prop) (f : elt -> A -> A),
  Equivalence eqA -> Proper (eq ==> eqA ==> eqA) f -> transpose eqA f ->
  forall i s (Hs : Ok s) x,
    In_list x s -> eqA (f x (fold_aux f (remove_aux x s) i)) (fold_aux f s i).
Proof.
intros; symmetry; apply fold_2 with (eqA:=eqA); auto;
[apply remove_ok; auto|rewrite remove_spec; intuition|intro y].
assert (Hxy : eq x y \/ ~ eq x y)
  by (rewrite <- eqb_eq; case (eqb x y); intuition).
elim Hxy; [intuition; [apply In_eq_iff_aux with x; eauto|]|].

  {
  assert (HR := @remove_3 (Mkt Hs)); unfold In in HR; simpl in HR.
  apply HR with x; auto.
  }

  {
  assert (HR := @remove_3 (Mkt Hs));   assert (HR':= @remove_neq_iff (Mkt Hs)).
  unfold In in *; simpl in *.
  intuition; [right; apply HR'; auto|apply HR with x; auto].
  }
Qed.

Lemma add_cardinal_1_aux : forall s (Hs : Ok s) (x : elt),
  In_list x s -> cardinal_aux (add_aux x s) = cardinal_aux s.
Proof.
intros.
rewrite cardinal_fold; [rewrite cardinal_fold; auto|apply add_ok; auto].
change S with ((fun _ => S) x).
apply add_fold with (eqA:=@Logic.eq nat);
auto; try congruence; exact eq_equivalence.
Qed.

Lemma add_cardinal_1 : forall s  (x : elt),
  In x s -> cardinal (add x s) = cardinal s.
Proof. intros [s Hs]; apply add_cardinal_1_aux. auto. Qed.

Lemma add_cardinal_2_aux : forall s (Hs : Ok s) (x : elt),
  ~ In_list x s -> cardinal_aux (add_aux x s) = S (cardinal_aux s).
Proof.
intros.
rewrite cardinal_fold; [rewrite cardinal_fold; auto|apply add_ok; auto].
change S with ((fun _ => S) x).
apply fold_add with (eqA:=@Logic.eq nat);
auto; try congruence; exact eq_equivalence.
Qed.

Lemma add_cardinal_2 : forall s  (x : elt),
  ~ In x s -> cardinal (add x s) = S (cardinal s).
Proof. intros [s Hs]; apply add_cardinal_2_aux. auto. Qed.

Lemma remove_cardinal_1_aux : forall s (Hs : Ok s) (x : elt),
  In_list x s -> S (cardinal_aux (remove_aux x s)) = cardinal_aux s.
Proof.
intros.
rewrite cardinal_fold; [rewrite cardinal_fold; auto|apply remove_ok; auto].
change S with ((fun _ => S) x).
apply remove_fold_1 with (eqA:=@Logic.eq nat);
auto; try congruence; exact eq_equivalence.
Qed.

Lemma remove_cardinal_1 : forall s  (x : elt),
  In x s -> S (cardinal (remove x s)) = cardinal s.
Proof. intros [s Hs]; apply remove_cardinal_1_aux; auto. Qed.

Lemma filter_mem :  forall (f : elt -> bool),
  Proper (eq ==> Logic.eq) f ->
  forall (s : t) (x : elt), mem x (filter f s) = mem x s && f x.
Proof. intros; rewrite filter_b; auto. Qed.

Lemma for_all_exists : forall (f : elt -> bool),
  Proper (eq ==> Logic.eq) f ->
  forall (s : t), exists_ f s = negb (for_all (fun x => negb (f x)) s).
Proof.
intros f Hf s; rewrite for_all_b.

  {
  rewrite exists_b; auto; induction (elements s); simpl; auto.
  destruct (f a); simpl; auto.
  }

  {
  intros x y HEq; apply negb_sym; rewrite negb_involutive.
  apply (Hf y x); auto.
  }
Qed.

Lemma for_all_filter : forall (f : elt -> bool),
  Proper (eq ==> Logic.eq) f ->
  forall (s : t), for_all f s = is_empty (filter (fun x => negb (f x)) s).
Proof.
intros f Hf s; apply bool_1; split; intro H.

  {
  apply is_empty_1; unfold Empty; intro a; simpl; rewrite filter_spec.

    {
    red; intros [H1 H2]; rewrite <- (@for_all_iff s f) in H; auto.
    rewrite (H a H1) in H2; discriminate.
    }

    {
    intros x y HEq; apply negb_sym; rewrite negb_involutive.
    apply (Hf y x); auto.
    }
  }

  {
  apply for_all_1; auto; red; intros a HIn.
  revert H; rewrite <- is_empty_iff; unfold Empty; intro H; generalize (H a).
  clear H; simpl; rewrite filter_spec; [destruct (f a); auto|].
  intros x y HEq; apply negb_sym; rewrite negb_involutive.
  apply (Hf y x); auto.
  }
Qed.

Lemma for_all_mem_4 : forall (f : elt -> bool),
  Proper (eq ==> Logic.eq) f ->
  forall (s : t), for_all f s = false ->
                  {x : elt | mem x s = true /\ f x = false}.
Proof.
intros f Hf s H.
rewrite for_all_filter in H; auto; destruct (choose_mem_3 _ H) as [a [H1 H2]].
exists a; rewrite filter_b in H2;
[elim (andb_prop _ _ H2); split; auto; rewrite <- negb_true_iff; auto|].
intros x y HEq; apply negb_sym; rewrite negb_involutive.
apply (Hf y x); auto.
Qed.

Lemma exists_mem_4 : forall (f : elt -> bool),
  Proper (eq ==> Logic.eq) f ->
  forall (s : t), exists_ f s = true ->
                  {x : elt | mem x s = true /\ f x = true}.
Proof.
intros f Hf s H; rewrite for_all_exists in H; auto.
rewrite negb_true_iff in H.
assert (Hf' :  Proper (eq ==> Logic.eq) (fun x : elt => negb (f x))).
  {
  intros x y HEq; apply negb_sym; rewrite negb_involutive.
  apply (Hf y x); auto.
  }
destruct (@for_all_mem_4 (fun x => negb (f x)) Hf' s) as [x []]; auto.
exists x; split; auto; rewrite <- negb_false_iff; auto.
Qed.

Lemma In_dec : forall (x : elt) (s : t), {In x s} + {~ In x s}.
Proof. intros; generalize (mem_iff s x); case (mem x s); intuition. Qed.

Lemma empty_is_empty_1 : forall (s : t),
  Empty s -> Equal s empty.
Proof.
intros [s Hs] Hs'; induction s; [unfold Equal, Equal_aux; intuition|exfalso].
apply (Hs' a), In_cons_hd, eq_refl.
Qed.

End TCSetList.