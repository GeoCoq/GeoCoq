Require Import Bool.
Require Import List.
Require Import Morphisms.
Require Import NArith.
Require Import Recdef.
Require Import GeoCoq.Utils.Mergesort.
Require Import GeoCoq.Utils.sets.
Require Import GeoCoq.Tactics.Coinc.Permutations.

Section Coinc_refl.

Context {AR : Arity}.

Definition pick_variety_auxCP {m : nat} (s : (@elt SS))
           (cp : cartesianPower positive (Datatypes.S (Datatypes.S m))) : bool.
Proof.
induction m; [exact (((@mem S) (fst cp) s) && ((@mem S) (snd cp) s))|].
exact (((@mem S) (fst cp) s) && (IHm (tailCP cp))).
Defined.

Definition pick_variety_aux (s : (@elt SS)) (t : (@elt ST)) :=
  pick_variety_auxCP s t.

Lemma pick_variety_auxCP_forallT {m : nat} :
  forall s (cp : cartesianPower positive (Datatypes.S (Datatypes.S m))),
  pick_variety_auxCP s cp = true <->
  (forall p, InCP p cp -> (@mem S) p s = true).
Proof.
induction m; intros s cp; [unfold InCP|]; simpl; split.

  {
  intro Hmem; apply andb_true_iff in Hmem; destruct Hmem as [Hmem1 Hmem2].
  intros p H; do 2 (try (elim H; clear H; intro; subst)); auto.
  }

  {
  intro H; apply andb_true_iff; split;
  [apply (H (fst cp))|apply (H (snd cp))]; auto.
  }

  {
  intro Hmem; apply andb_true_iff in Hmem; destruct Hmem as [Hmem1 Hmem2].
  intros p H; apply InCPOK in H; elim H; clear H; intro HIn; subst; simpl; auto.
  destruct (IHm s (tailCP cp)) as [H _]; apply H; auto.
  }

  {
  destruct (IHm s (tailCP cp)) as [_ H]; clear IHm; rename H into IHm.
  intro H; apply andb_true_iff; split;
  [apply (H (fst cp))|apply IHm; intros p HIn; apply H]; apply InCPOK; auto.
  }
Qed.

Lemma pick_variety_auxCP_existsF {m : nat} :
  forall s (cp : cartesianPower positive (Datatypes.S (Datatypes.S m))),
  pick_variety_auxCP s cp = false <->
  (exists p, InCP p cp /\ (@mem S) p s = false).
Proof.
induction m; intros s cp; [unfold InCP|]; simpl; split.

  {
  intro H; apply andb_false_iff in H; elim H; clear H; intro H;
  [exists (fst cp)|exists (snd cp)]; auto.
  }

  {
  intro H; destruct H as [p [H Hmem]]; apply andb_false_iff.
  do 2 (try (elim H; clear H; intro H; subst)); intuition.
  }

  {
  intro H; apply andb_false_iff in H.
  destruct (IHm s (tailCP cp)) as [H' _]; clear IHm; rename H' into IHm.
  elim H; clear H; intro Hmem.

    {
    exists (fst cp); unfold InCP; simpl; auto.
    }

    {
    destruct (IHm Hmem) as [p [HIn Hmem']]; exists p;
    split; try apply InCPOK; auto.
    }
  }

  {
  destruct (IHm s (tailCP cp)) as [_ H]; clear IHm; rename H into IHm.
  intro H; destruct H as [p [HIn Hmem]]; apply InCPOK in HIn;
  apply andb_false_iff; elim HIn; clear HIn; intro HIn; subst; auto.
  right; apply IHm; exists p; auto.
  }
Qed.

Lemma proper_00 :
  forall s,
  Proper
  ((fun t1 t2 => TCSets.eq t1 t2) ==> Logic.eq)
  (fun t => pick_variety_aux s t).
Proof.
unfold pick_variety_aux, eqST.
intros s t1 t2 HEq.
case_eq (pick_variety_auxCP s t1); intro Ht1.

  {
  destruct (pick_variety_auxCP_forallT s t1) as [H1 H2]; clear H2.
  assert (H := H1 Ht1); clear H1; clear Ht1; rename H into Ht1.
  destruct (pick_variety_auxCP_forallT s t2) as [H1 H2]; clear H1.
  rewrite H2; try reflexivity; clear H2; intros p HIn; apply Ht1.
  clear Ht1; apply InCPOCP; apply InCPOCP in HIn.
  assert (H : eqList (CPToList (OCP t1)) (CPToList (OCP t2))).
    {
    assert (Ht1 := eqListSortOCP t1).
    assert (Ht2 := eqListSortOCP t2).
    apply eqListTrans with ((@sort PosOrder) (CPToList t1)); try assumption.
    apply eqListTrans with ((@sort PosOrder) (CPToList t2)); try assumption.
    apply eqListSym; assumption.
    }
  clear HEq; rename H into HEq; apply eqListOK in HEq.
  unfold InCP in *; rewrite HEq; auto.
  }

  {
  destruct (pick_variety_auxCP_existsF s t1) as [H1 H2]; clear H2.
  assert (H := H1 Ht1); clear H1; clear Ht1; rename H into Ht1.
  destruct (pick_variety_auxCP_existsF s t2) as [H1 H2]; clear H1.
  rewrite H2; try reflexivity; clear H2.
  destruct Ht1 as [p [HIn Hmem]]; exists p; split; auto.
  apply InCPOCP; apply InCPOCP in HIn.
  assert (H : eqList (CPToList (OCP t1)) (CPToList (OCP t2))).
    {
    assert (Ht1 := eqListSortOCP t1).
    assert (Ht2 := eqListSortOCP t2).
    apply eqListTrans with ((@sort PosOrder) (CPToList t1)); try assumption.
    apply eqListTrans with ((@sort PosOrder) (CPToList t2)); try assumption.
    apply eqListSym; assumption.
    }
  clear HEq; rename H into HEq; apply eqListOK in HEq.
  unfold InCP in *; rewrite <- HEq; auto.
  }
Qed.

Definition pick_variety (s : (@elt SS)) (st : (@TCSets.t ST)) :=
  exists_ (fun t => pick_variety_aux s t) st.

Lemma proper_0 :
  Proper ((@Equal S) ==> Logic.eq ==> Logic.eq) pick_variety.
Proof.
intros x1 y1 HXY1 x2 [y2 Hy2] HXY2.
rewrite HXY2; clear HXY2; clear x2.
unfold pick_variety, pick_variety_aux, exists_; simpl.
induction y2; [reflexivity|simpl; rewrite IHy2; clear IHy2];
[|rewrite <- isok_iff in Hy2; apply Sorted_inv in Hy2;
  rewrite <- isok_iff; intuition].
assert (HE : forall e, mem e x1 = mem e y1)
  by (intro; apply mem_m; intuition); clear HXY1.
assert (HF : forall n a,
           (@pick_variety_auxCP n) x1 a = (@pick_variety_auxCP n) y1 a)
  by (induction n; simpl; intro; rewrite !HE; [|rewrite IHn]; reflexivity).
rewrite HF; reflexivity.
Qed.

Lemma proper_1 : forall s1 st,
  Proper (Equal ==>Logic.eq) (fun s2 => pick_variety (inter s1 s2) st).
Proof.
intros s1 st x y HXY.
assert (HEqI : Equal (inter s1 x) (inter s1 y))
  by (apply inter_equal_2; assumption).
apply proper_0; auto.
Qed.

Definition exists_witness (f : (@elt SS) -> bool) s := choose (filter f s).

Lemma exists_witness_ok : forall e f s,
  Proper (Equal ==> Logic.eq) f ->
  exists_witness f s = Some e -> In e s.
Proof.
intros e f s HP H; apply mem_2; apply choose_mem_1 in H;
rewrite filter_mem in H; [|assumption]; apply andb_true_iff in H; intuition.
Qed.

Definition pick_varieties_aux s1 ss st :=
  match ((exists_witness (fun s2 => let i := inter s1 s2 in
                                    pick_variety i st)) ss) with
    | None    => None
    | Some s2 => Some(s1,s2)
  end.

Definition pick_varieties ss st :=
  match (exists_witness (fun s =>
                           match (pick_varieties_aux s (remove s ss) st) with
                             | None => false
                             | _    => true
                           end) ss) with
    | None    => None
    | Some s1 => pick_varieties_aux s1 (remove s1 ss) st
  end.

Definition eqop (p1 p2 : option (@elt SS)) :=
  match p1,p2 with
    | None   , None    => True
    | Some s1, Some s2 => True
    | _      , _       => False
  end.

Lemma proper_2 : forall (f1 f2 : (@elt SS) -> bool) s1 s2,
  Proper (Equal ==> Logic.eq) f1 ->
  Proper (Equal ==> Logic.eq) f2 ->
  (forall x, f1 x = f2 x) ->
  Equal s1 s2 ->
  eqop (exists_witness f1 s1) (exists_witness f2 s2).
Proof.
intros f1 f2 s1 s2 H1 H2 H3 H4; unfold eqop, exists_witness in *.
assert (Equal (filter f1 s1) (filter f2 s2)) by (apply filter_ext; assumption).
case_eq (choose (filter f1 s1)); case_eq (choose (filter f2 s2));
[intuition|intros HCN e HCS|intros e HCS HCN|intuition];
apply choose_spec1 in HCS; apply choose_spec2 in HCN;
unfold Equal, Equal_aux in H; [rewrite H in HCS|rewrite <- H in HCS];
apply empty_is_empty_1 in HCN; unfold Equal, Equal_aux in HCN;
rewrite HCN in HCS; rewrite <- (empty_iff e); apply HCS.
Qed.

Definition eqopp (p1 p2 : option ((@elt SS) * (@elt SS))) :=
  match p1,p2 with
    | None   , None    => True
    | Some s1, Some s2 => True
    | _      , _       => False
  end.

Lemma proper_3 :
  Proper (Equal ==> Equal ==> Logic.eq ==> eqopp) pick_varieties_aux.
Proof.
intros x1 y1 HXY1 x2 y2 HXY2 x3 y3 HXY3.
unfold pick_varieties_aux; rewrite HXY3.
assert (eqop (exists_witness (fun s2 => pick_variety (inter x1 s2) y3) x2)
             (exists_witness (fun s2 => pick_variety (inter y1 s2) y3) y2)).
  {
  apply proper_2; auto; try apply proper_1.
  intro; apply proper_0; [apply inter_equal_1|]; trivial.
  }
case_eq (exists_witness (fun s2 => pick_variety (inter y1 s2) y3) y2);
case_eq (exists_witness (fun s2 => pick_variety (inter x1 s2) y3) x2);
[simpl; intuition|intros HCN e HCS|intros e HCS HCN|intuition];
simpl in *; rewrite HCS in H; rewrite HCN in H; simpl in *; intuition.
Qed.

Lemma pick_varieties_ok_1 : forall s1 s2 ss st,
  pick_varieties ss st = Some(s1,s2) -> (@In SS) s1 ss.
Proof.
intros s1 s2 ss st H; unfold pick_varieties in H.
case_eq (exists_witness (fun s =>
                           match pick_varieties_aux s (remove s ss) st with
                           | Some _ => true | None => false end) ss);
[|intro HEW; rewrite HEW in H; discriminate].
intros e1 HEW1; rewrite HEW1 in H; unfold pick_varieties_aux in H.
case_eq (exists_witness (fun s2 => pick_variety (inter e1 s2) st)
                        (remove e1 ss));
[|intro HEW2; rewrite HEW2 in H; discriminate].
intros e2 HEW2; rewrite HEW2 in H.
assert (HEq1 : e1 = s1) by (injection H; intros; assumption); rewrite HEq1 in *.
assert (HEq2 : e2 = s2) by (injection H; intros; assumption); rewrite HEq2 in *.
apply exists_witness_ok with (fun s : (@elt SS) =>
                                match pick_varieties_aux s (remove s ss) st with
                                | Some _ => true | None => false end); [|auto].
intros x y HXY.
assert (Equal ((@remove SS) x ss) ((@remove SS) y ss))
  by (apply remove_m; [auto|apply Equal_refl]).
assert (eqopp (pick_varieties_aux x ((@remove SS) x ss) st)
              (pick_varieties_aux y ((@remove SS) y ss) st))
  by (apply proper_3; auto).
case_eq (pick_varieties_aux x ((@remove SS) x ss) st); intros;
case_eq (pick_varieties_aux y ((@remove SS) y ss) st); intros; auto;
rewrite H2 in H1; rewrite H3 in H1; unfold eqop in H1; simpl in H1; intuition.
Qed.

Lemma pick_varieties_ok_2 : forall s1 s2 ss st,
  pick_varieties ss st = Some(s1,s2) -> (@In SS) s2 ((@remove SS) s1 ss).
Proof.
intros s1 s2 ss st H; unfold pick_varieties in H.
case_eq (exists_witness (fun s =>
                           match pick_varieties_aux s (remove s ss) st with
                           | Some _ => true | None => false end) ss);
[|intro HEW; rewrite HEW in H; discriminate].
intros e1 HEW1; rewrite HEW1 in H; unfold pick_varieties_aux in H.
case_eq (exists_witness (fun s2 => pick_variety (inter e1 s2) st)
                        (remove e1 ss));
[|intro HEW2; rewrite HEW2 in H; discriminate].
intros e2 HEW2; rewrite HEW2 in H.
assert (HEq1 : e1 = s1) by (injection H; intros; assumption); rewrite HEq1 in *.
assert (HEq2 : e2 = s2) by (injection H; intros; assumption); rewrite HEq2 in *.
apply exists_witness_ok with (fun s2 => pick_variety (inter s1 s2) st);
[intros x y HXY; apply proper_1; assumption|assumption].
Qed.

Function identify_varieties ss st {measure cardinal ss} :=
  let varieties := pick_varieties ss st in
  match varieties with
    | None         => ss
    | Some (s1,s2) => let auxsetofsets := remove s2 ((@remove SS) s1 ss) in
                     let auxset := union s1 s2 in
                     let newss := (@add SS) auxset auxsetofsets in
                     identify_varieties newss st
  end.
Proof.
intros; remember ((@remove SS) s1 ss) as ssMs1; rename HeqssMs1 into H.
assert (Datatypes.S (cardinal ssMs1) = cardinal ss)
  by (rewrite H; apply remove_cardinal_1, pick_varieties_ok_1 with s2 st; auto).
assert (Datatypes.S (Datatypes.S (cardinal (remove s2 ssMs1))) =
        Datatypes.S (cardinal ssMs1))
  by (rewrite H; apply eq_S, remove_cardinal_1;
      apply pick_varieties_ok_2 with st; auto).
assert (HR1 : Datatypes.S (Datatypes.S (cardinal (remove s2 ssMs1))) =
              cardinal ss)
  by (transitivity (Datatypes.S (cardinal ssMs1)); assumption).
elim ((@In_dec SS) (union s1 s2) (remove s2 ssMs1)); intro HDec; rewrite <- HR1;
remember (cardinal ((@add SS) (union s1 s2) (remove s2 ssMs1))) as lhs;
[replace lhs with (cardinal (remove s2 ssMs1))|
 replace lhs with (Datatypes.S (cardinal (remove s2 ssMs1)))];
[apply le_S, le_n| |apply le_n| ]; rewrite Heqlhs; apply Logic.eq_sym;
[apply add_cardinal_1|apply add_cardinal_2]; assumption.
Defined.

Definition memCPAux m
           (cp : cartesianPower positive (Datatypes.S (Datatypes.S m)))
           (s : (@elt SS)) : bool.
Proof.
induction m; [exact ((@mem S) (fst cp) s && (@mem S) (snd cp) s)|].
exact ((@mem S) (fst cp) s && (IHm (snd cp))).
Defined.

Lemma memCPAuxHdTl : forall m cp s,
  memCPAux (Datatypes.S m) cp s =
  (@mem S) (fst cp) s && memCPAux m (tailCP cp) s.
Proof.
induction m; unfold memCPAux; unfold nat_rect; reflexivity.
Qed.

Lemma memCPAuxProperOK : forall m,
  Proper (Logic.eq ==> Equal==> Logic.eq) (memCPAux m).
Proof.
intros m cp1 cp2 Hcp s1 s2 Hs.
rewrite Hcp; clear Hcp; clear cp1; rename cp2 into cp.
unfold memCPAux.
assert (H : forall p, mem p s1 = mem p s2)
  by (intro p; apply mem_m; [apply TCSets.eq_refl|auto]).
induction m; [simpl; rewrite !H; reflexivity|].
simpl; rewrite H; rewrite IHm; reflexivity.
Qed.

Lemma memCPAuxOK : forall m cp s e,
  memCPAux m cp s = true -> InCP e cp -> (@mem S) e s = true.
Proof.
induction m.

  {
  intros cp s e Hmem HIn; unfold InCP in HIn; simpl in *.
  rewrite andb_true_iff in Hmem; intuition; subst; auto.
  }

  {
  intros cp s e Hmem HIn; apply InCPOK in HIn.
  elim HIn; clear HIn; intro HIn; [subst|apply IHm with (tailCP cp); auto];
  simpl in Hmem; rewrite andb_true_iff in Hmem; intuition.
  }
Qed.

Lemma memMemCPAuxOK : forall m cp s,
  (forall e, InCP e cp -> (@mem S) e s = true) -> memCPAux m cp s = true.
Proof.
induction m.

  {
  intros cp s H; simpl; rewrite andb_true_iff.
  split; apply H; unfold InCP; simpl; auto.
  }

  {
  intros cp s H; rewrite memCPAuxHdTl, andb_true_iff.
  split; [apply H; unfold InCP; simpl; auto|].
  apply IHm; intros e HIn; apply H, InCPOK; right; assumption.
  }
Qed.

Lemma memCPAuxTlOK : forall m cp s,
  memCPAux (Datatypes.S m) cp s = true ->
  memCPAux m (tailCP cp) s = true.
Proof.
intros m cp s Hmemcp; apply memMemCPAuxOK; intros e HIn.
apply memCPAuxOK with (Datatypes.S m) cp; try assumption.
apply InCPOK; right; assumption.
Qed.

Definition memCP cp s := memCPAux (Datatypes.S n) cp s.

Lemma memCPProper : Proper (Logic.eq ==> Equal==> Logic.eq) memCP.
Proof. apply memCPAuxProperOK. Qed.

Lemma memMemCPOK : forall cp s,
  (forall e, InCP e cp -> (@mem S) e s = true) -> memCP cp s = true.
Proof. apply memMemCPAuxOK. Qed.

Lemma memCPConsHd : forall p s x,
  mem p s = true ->
  memCPAux n x s = true ->
  memCP (consHeadCP p x) s = true.
Proof.
intros p s x Hmem Hmemcp; apply memMemCPOK; intros e HIn.
apply InCPOK in HIn; simpl in HIn; elim HIn; clear HIn; intro HIn;
[subst|apply memCPAuxOK with n x]; assumption.
Qed.

Definition test_coinc ss st cp : bool :=
  let newss := identify_varieties ss st  in
  exists_ (fun s => memCP cp s) newss.

Lemma pick_variety_aux_memCPAux1 :
  forall s1 s2 m cp,
    pick_variety_auxCP (inter s1 s2) cp = true ->
    memCPAux m cp s1 = true.
Proof.
intros s1 s2 m cp; induction m; simpl; rewrite !andb_true_iff; intro Hhtspa;
[rewrite !inter_b, !andb_true_iff in Hhtspa; tauto|].
destruct Hhtspa as [Hmem Hhtspa]; rewrite inter_b, andb_true_iff in Hmem.
split; [intuition|apply IHm; assumption].
Qed.

Lemma pick_variety_aux_memCPAux2 : forall s1 s2 m cp,
  pick_variety_auxCP (inter s1 s2) cp = true ->
  memCPAux m cp s2 = true.
Proof.
intros s1 s2 m cp; induction m; simpl; rewrite !andb_true_iff; intro Hhtspa;
[rewrite !inter_b, !andb_true_iff in Hhtspa; tauto|].
destruct Hhtspa as [Hmem Hhtspa]; rewrite inter_b, andb_true_iff in Hmem.
split; [intuition|apply IHm; assumption].
Qed.

Definition interp_CP {m : nat} (cp : cartesianPower positive (Datatypes.S m))
                               (interp: positive -> COINCpoint) :
  cartesianPower COINCpoint (Datatypes.S m).
Proof.
induction m; [exact (interp cp)|clear IHm].
induction m; [split; [exact (interp (headCP cp))|exact (interp (tailCP cp))]|].
split; [exact (interp (headCP cp))|exact (IHm (tailCP cp))].
Defined.

Lemma interp_CPHdOK {m : nat} :
  forall (cp : cartesianPower positive (Datatypes.S m)) interp,
    interp_CP (headCPbis cp) interp = headCP (interp_CP cp interp).
Proof.
induction m; [unfold interp_CP, nat_rect; simpl; reflexivity|].
induction m; unfold interp_CP, nat_rect; simpl; reflexivity.
Qed.

Lemma interp_CPTlOK {m : nat} :
  forall (cp : cartesianPower positive (Datatypes.S (Datatypes.S m))) interp,
    interp_CP (tailCP cp) interp = tailCP (interp_CP cp interp).
Proof. induction m; unfold interp_CP, nat_rect; simpl; reflexivity. Qed.

Lemma interp_CPOK {m : nat} :
  forall (cp : cartesianPower positive (Datatypes.S m)),
  forall (interp: positive -> COINCpoint),
    CPToList (interp_CP cp interp) = map interp (CPToList cp).
Proof.
induction m; intros cp interp; [simpl; reflexivity|].
induction m; try (clear IHm0); [simpl; reflexivity|].
rewrite CPToListOK, <- interp_CPHdOK, <- interp_CPTlOK, IHm; simpl; reflexivity.
Qed.

Context {COP : Coinc_predicates AR}.

Definition ss_ok ss (interp: positive -> COINCpoint) :=
  forall s, mem s ss = true ->
  forall cp, memCP cp s = true ->
    app coinc (interp_CP cp interp).

Lemma consHdInterpOK : forall (cp : cartesianPower positive 1) (x : tST) interp,
  consHeadCP (interp_CP cp interp) (interp_CP x interp) =
  interp_CP (consHeadCP cp x) interp.
Proof. intros cp x interp; apply CP_ind; simpl; reflexivity. Qed.

Lemma ss_ok_inter_ok1 : forall ss i s1 s2 x (p : cartesianPower positive 1),
  ss_ok ss i ->
  In s1 ss ->
  pick_variety_aux (inter s1 s2) x = true ->
  (@mem S) p s1 = true ->
  app_1_n coinc (interp_CP p i) (interp_CP x i).
Proof.
intros ss interp s1 s2 x p HSSOK HIn HInter Hmem.
apply app_app_1_n with (consHeadCP (interp_CP p interp) (interp_CP x interp));
[|simpl; reflexivity|simpl; reflexivity].
assert (Hmemcp : memCPAux n x s1 = true)
  by (apply pick_variety_aux_memCPAux1 with s2; assumption).
unfold ss_ok in HSSOK; rewrite consHdInterpOK; apply mem_1 in HIn.
apply HSSOK with s1; [|apply memCPConsHd]; assumption.
Qed.

Lemma ss_ok_inter_ok2 : forall ss i s1 s2 x (p : cartesianPower positive 1),
  ss_ok ss i ->
  In s2 ss ->
  pick_variety_aux (inter s1 s2) x = true ->
  (@mem S) p s2 = true ->
  app_1_n coinc (interp_CP p i) (interp_CP x i).
Proof.
intros ss interp s1 s2 x p HSSOK HIn HInter Hmem.
apply app_app_1_n with (consHeadCP (interp_CP p interp) (interp_CP x interp));
[|simpl; reflexivity|simpl; reflexivity].
assert (Hmemcp : memCPAux n x s2 = true)
  by (apply pick_variety_aux_memCPAux2 with s1; assumption).
unfold ss_ok in HSSOK; rewrite consHdInterpOK; apply mem_1 in HIn.
apply HSSOK with s2; [|apply memCPConsHd]; assumption.
Qed.

Lemma mca_pick_variety_aux_pca : forall m cp s1 s2 ss x interp,
  ss_ok ss interp ->
  In s1 ss ->
  In s2 ss ->
  memCPAux (Datatypes.S m) cp (union s1 s2) = true ->
  pick_variety_aux (inter s1 s2) x = true ->
  pred_conj_aux coinc (Datatypes.S (Datatypes.S m))
                      (interp_CP cp interp) (interp_CP x interp).
Proof.
induction m; intros cp s1 s2 ss x interp HSSOK HIn1 HIn2 Hmemcp Hhtspa;
[|rewrite pcaHdTl; split; [|rewrite <- interp_CPTlOK]];
[split; [|split]| |apply IHm with s1 s2 ss; auto; apply memCPAuxTlOK; auto];
[assert (HIn: InCP (headCP cp) cp)|assert (HIn: InCP (headCP (tailCP cp)) cp)|
 assert (HIn: InCP (tailCP (tailCP cp)) cp)|assert (HIn: InCP (headCP cp) cp)];
try solve [unfold InCP; simpl; auto];
[assert (HElim : (@mem S) (headCP cp) (union s1 s2) = true)|
 assert (HElim : (@mem S) (headCP (tailCP cp)) (union s1 s2) = true)|
 assert (HElim : (@mem S) (tailCP (tailCP cp)) (union s1 s2) = true)|
 assert (HElim : (@mem S) (headCP cp) (union s1 s2) = true)];
try solve [apply memCPAuxOK with 1 cp; assumption];
try solve [apply memCPAuxOK with (Datatypes.S (Datatypes.S m)) cp; assumption];
rewrite union_b in HElim; apply orb_true_iff in HElim;
elim HElim; clear HElim; intro HElim;
try solve [apply ss_ok_inter_ok1 with ss s1 s2; assumption];
apply ss_ok_inter_ok2 with ss s1 s2; assumption.
Qed.

Definition st_ok st (interp: positive -> COINCpoint) :=
  forall t, (@mem ST) t st = true -> app wd (interp_CP t interp).

Context {COT : Coinc_theory AR COP}.

Lemma identify_varieties_ok : forall ss st interp,
  ss_ok ss interp -> st_ok st interp ->
  ss_ok (identify_varieties ss st) interp.
Proof.
intros ss st interp HSS HST.
apply (let P interp ss st newss :=
       ss_ok ss interp -> st_ok st interp -> ss_ok newss interp in
         identify_varieties_ind (P interp)); try assumption;
[intros; assumption|].
clear HSS; clear HST; clear ss; clear st.
intros ss st varieties s1 s2 Hs1s2 auxsetofsets auxset newss H HSS HST.
assert (Hs1 := Hs1s2); assert (Hs2 := Hs1s2).
apply pick_varieties_ok_1 in Hs1; apply pick_varieties_ok_2 in Hs2.
apply remove_3 in Hs2; apply H; try assumption; clear H.
intros s Hmem cp Hmemcp; unfold newss in Hmem; clear newss.
assert (HEq : Equal auxset s \/ ~ Equal auxset s)
  by (rewrite <- equal_Equal; elim (equal auxset s); auto).
destruct HEq as [HEq|HEq];
[|rewrite add_neq_b in Hmem; [apply HSS with s; [|auto]|auto];
 apply mem_2 in Hmem; do 2 (apply remove_3 in Hmem); apply mem_1; auto].
assert (HEq' : memCP cp auxset = memCP cp s) by (apply memCPProper; trivial).
rewrite <- HEq' in *; clear HEq HEq' Hmem s.
unfold varieties in Hs1s2; clear varieties; unfold pick_varieties in Hs1s2.
case_eq (exists_witness
           (fun s => match pick_varieties_aux s (remove s ss) st with
                      | Some _ => true
                      | None => false
                     end) ss);
[|intro HEW; rewrite HEW in *; discriminate].
intros e1 HEW; rewrite HEW in *; clear HEW; unfold pick_varieties_aux in *.
case_eq (exists_witness
           (fun s2 : elt => pick_variety (inter e1 s2) st) (remove e1 ss));
[|intro HEW; rewrite HEW in *; discriminate].
intros e2 HEW; rewrite HEW in *; injection Hs1s2; intros He2s2 He1s1.
rewrite He2s2 in *; rewrite He1s1 in *; clear He1s1 He2s2 Hs1s2 e1 e2.
case_eq (pick_variety (inter s1 s2) st);
[|intro HEW2; apply choose_spec1, filter_2 in HEW;
  [rewrite HEW2 in *; discriminate|apply proper_1]].
clear HEW; intro HEW; unfold pick_variety in HEW; apply exists_mem_4 in HEW;
[destruct HEW as [x [HmemST1 HmemST2]]|apply proper_00].
apply HST in HmemST1; apply coinc_n with (interp_CP x interp); [|auto].
apply mca_pick_variety_aux_pca with s1 s2 ss; assumption.
Qed.

Lemma test_coinc_ok : forall ss st interp cp,
  ss_ok ss interp -> st_ok st interp ->
  test_coinc ss st cp = true ->
  app coinc (interp_CP cp interp).
Proof.
intros ss st interp cp HSS HST HTC; unfold test_coinc in *.
assert (HSS2 : ss_ok (identify_varieties ss st) interp)
  by (apply identify_varieties_ok; assumption).
unfold ss_ok in HSS2; apply exists_2 in HTC;
[|intros x y Hxy; apply memCPProper; trivial].
destruct HTC as [s [HIn Hmem]]; apply HSS2 with s; [apply mem_1|]; auto.
Qed.

Lemma ss_ok_empty : forall interp,
  ss_ok empty interp.
Proof.
intros interp ss Hmem1 cp Hmem2; rewrite empty_b in Hmem1; discriminate.
Qed.

Lemma st_ok_empty : forall interp,
  st_ok empty interp.
Proof. intros; intros t Ht; rewrite empty_b in Ht; discriminate. Qed.

Definition CPToSS {m : nat} (cp : cartesianPower positive m) : (@elt SS).
Proof.
induction m; [exact (@empty S)|induction m; [exact ((@add S) cp (@empty S))|]].
exact ((@add S) (headCP cp) (IHm (tailCP cp))).
Defined.

Lemma CPToSSHdTl {m : nat} :
  forall (cp : cartesianPower positive (Datatypes.S (Datatypes.S m))),
    CPToSS cp = (@add S) (headCP cp) (CPToSS (tailCP cp)).
Proof. simpl; reflexivity. Qed.

Lemma memCPToSSOK {m : nat} :
  forall e (cp : cartesianPower positive (Datatypes.S m)),
    mem e (CPToSS cp) = true -> InCP e cp.
Proof.
induction m; intros e cp Hmem;
[left; apply mem_2 in Hmem; unfold In in *; rewrite In_alt in Hmem;
 destruct Hmem as [y [HE1 HE2]]; simpl in *; transitivity y; intuition|].
apply InCPOK; rewrite CPToSSHdTl, add_b in Hmem.
apply orb_true_iff in Hmem; elim Hmem; clear Hmem; intro Hmem;
[left; apply TCSets.eqb_eq in Hmem|right; apply IHm]; auto.
Qed.

Lemma CPToSSOKAux {m m' : nat} :
  forall (cp : cartesianPower positive (Datatypes.S (Datatypes.S m))),
  forall (cp' : cartesianPower positive (Datatypes.S (Datatypes.S m'))) e s,
  Equal (CPToSS cp) s ->
  memCPAux m' cp' s = true ->
  InCP e cp' ->
  InCP e cp.
Proof.
induction m'.

  {
  induction m; intros cp cp' e s HEq Hmem HIn.

    {
    unfold InCP in *; simpl in *.
    apply andb_true_iff in Hmem; destruct Hmem as [Hmem1 Hmem2].
    assert ((@mem S) (fst cp') ((@add S) (fst cp) ((@add S) (snd cp) empty)) =
            (@mem S) (fst cp') s);
    [apply mem_m; [apply TCSets.eq_refl|auto]|rewrite <- H in Hmem1; clear H].
    assert ((@mem S) (snd cp') ((@add S) (fst cp) ((@add S) (snd cp) empty)) =
            (@mem S) (snd cp') s);
    [apply mem_m; [apply TCSets.eq_refl|auto]|rewrite <- H in Hmem2; clear H].
    rewrite !add_b, empty_b in Hmem1; rewrite !add_b, empty_b in Hmem2.
    rewrite !orb_true_iff in Hmem1; rewrite !orb_true_iff in Hmem2.
    destruct HIn as [HIn|[HIn|]]; [..|intuition]; subst;
    [destruct Hmem1 as [HE|[HE|]]; [..|intuition]|
     destruct Hmem2 as [HE|[HE|]]; [..|intuition]];
    apply TCSets.eqb_eq in HE; auto.
    }

    {
    assert (HmemEq : memCPAux 0 cp' (CPToSS cp) = memCPAux 0 cp' s)
        by (apply memCPAuxProperOK; trivial).
    rewrite <- HmemEq in Hmem; clear HmemEq; clear HEq; clear IHm.
    destruct HIn as [HIn|[HIn|]]; [..|intuition]; subst;
    [assert (HIn : InCP (headCP cp') cp')|assert (HIn : InCP (tailCP cp') cp')];
    try solve [unfold InCP; simpl; auto];
    apply memCPToSSOK; apply memCPAuxOK with 0 cp'; auto.
    }
  }

  {
  intros cp cp' e s HEq Hmem HIn; apply InCPOK in HIn.
  elim HIn; clear HIn; intro HIn;
  [subst|apply IHm' with (tailCP cp') s; [|apply memCPAuxTlOK|]; auto].
  assert (HmemEq : memCPAux (Datatypes.S m') cp' (CPToSS cp) =
                   memCPAux (Datatypes.S m') cp' s)
    by (apply memCPAuxProperOK; trivial).
    rewrite <- HmemEq in Hmem.
    assert (HIn : InCP (headCP cp') cp') by (unfold InCP; simpl; auto).
    apply memCPToSSOK; apply memCPAuxOK with (Datatypes.S m') cp'; auto.
  }
Qed.

Lemma CPToSSOK :
  forall (cp cp': cartesianPower positive
                                 (Datatypes.S (Datatypes.S (Datatypes.S n)))) s,
    Equal (CPToSS cp) s ->
    memCP cp' s = true ->
    incl (CPToList cp') (CPToList cp).
Proof. intros cp cp' s HEq Hmem e HIn; apply CPToSSOKAux with cp' s; auto. Qed.

Lemma CoappDupPerm {m : nat} :
  forall (cp : cartesianPower positive m),
  ~ List.NoDup (CPToList cp) ->
  exists e, exists l,
    Permutation.Permutation (CPToList (ListToCP (e :: e :: l) e)) (CPToList cp).
Proof.
intros cp HDup; apply NotNoDupDup in HDup; [|apply Pos.eq_dec].
destruct HDup as [e [l1 [l2 [HEq HIn]]]]; apply in_split in HIn.
destruct HIn as [l3 [l4 HEq']].
assert (HPerm := Permutation.Permutation_middle l1 l2 e).
rewrite <- HEq in HPerm; clear HEq.
rewrite HEq' in HPerm; clear HEq' l1 l2; rename l3 into l1; rename l4 into l2.
assert (HPerm' := Permutation.Permutation_middle l1 l2 e).
apply (Permutation.perm_skip e) in HPerm'.
assert (HPerm'' := Permutation.perm_trans HPerm' HPerm).
clear HPerm HPerm'; rename HPerm'' into HPerm.
rewrite <- CPLOK with (e :: e :: l1 ++ l2) e in HPerm.
exists e; exists (l1 ++ l2); assumption.
Qed.

Lemma CoappDupAux {m : nat} :
  forall (cp : cartesianPower positive
                              (Datatypes.S (Datatypes.S (Datatypes.S m)))),
  ~ List.NoDup (CPToList cp) ->
  exists e (l : list positive) m',
  exists (cp' : cartesianPower positive
                               (Datatypes.S (Datatypes.S (Datatypes.S m')))),
  Permutation.Permutation (CPToList cp') (CPToList cp) /\
  headCP cp' = e /\ headCP (tailCP cp') = e.
Proof.
intros cp H; apply CoappDupPerm in H; destruct H as [e [l HPerm]].
assert (Hl := Permutation.Permutation_length HPerm); rewrite CPLOK in Hl.
rewrite <- lengthOfCPToList in Hl.
induction l; try (simpl in Hl; discriminate); clear IHl.
exists e, (a :: l), (length l), (ListToCP (e :: e :: a :: l) e).
split; [auto|simpl; split; reflexivity].
Qed.

Lemma CoappDup : forall cp interp,
  ~ List.NoDup (CPToList cp) ->
  app coinc (interp_CP cp interp).
Proof.
intros cp interp H; apply CoappDupAux in H.
destruct H as [e [l [m' [cp' [HPerm [Hfst Hsnd]]]]]].
assert (Hmn := Permutation.Permutation_length HPerm).
apply Permutation.Permutation_map with
  positive COINCpoint interp (CPToList cp') (CPToList cp) in HPerm.
rewrite <- !interp_CPOK in HPerm; rewrite <- !lengthOfCPToList in Hmn.
do 3 (apply eq_add_S in Hmn); subst.
apply PermCoincOK with (interp_CP cp' interp); [|auto; clear HPerm].
apply app_2_n_app with (interp (headCP cp')) (interp (headCP (tailCP cp')))
                       (interp_CP (tailCP (tailCP cp')) interp);
rewrite <- ?interp_CPTlOK, <- ?interp_CPHdOK; [|reflexivity..].
rewrite Hsnd; apply coinc_bd.
Qed.

Lemma collect_coincs :
forall cp ss interp,
  app coinc (interp_CP cp interp) ->
  ss_ok ss interp -> ss_ok (add (CPToSS cp) ss) interp.
Proof.
intros cp ss interp HCoapp HSS s Hs cp' Hmem.
apply mem_2, add_iff in Hs.
elim Hs; clear Hs; intro Hs; [|apply HSS with s; [apply mem_1|]; auto].
assert (HDup := NoDup_dec (CPToList cp') Pos.eq_dec).
elim HDup; clear HDup; intro HDup; [|apply CoappDup; auto].
assert (Hincl := CPToSSOK cp cp' s Hs Hmem).
assert (Hlength : length (CPToList cp') = length (CPToList cp))
  by (rewrite <- !lengthOfCPToList; reflexivity).
assert (HPerm := NoDupOK (CPToList cp') (CPToList cp) Hincl Hlength HDup).
apply Permutation.Permutation_map with
  positive COINCpoint interp (CPToList cp') (CPToList cp) in HPerm.
rewrite <- !interp_CPOK in HPerm; clear HDup Hincl Hlength.
apply Permutation.Permutation_sym in HPerm.
apply PermCoincOK with (interp_CP cp interp); assumption.
Qed.

Lemma collect_wds :
  forall cp st interp,
  app wd (interp_CP cp interp) ->
  st_ok st interp -> st_ok ((@add ST) cp st) interp.
Proof.
intros cp st interp HWd HST cp' Hmem. apply mem_2, add_iff in Hmem.
elim Hmem; clear Hmem; intro Hmem; [|apply HST, mem_1, Hmem].
assert (Hcp := Permuted_sort (CPToList cp)).
assert (Hcp' := Permuted_sort (CPToList cp')).
apply eqListOK in Hmem; rewrite Hmem in Hcp.
apply PermWdOK with (interp_CP cp interp); [assumption|].
rewrite !interp_CPOK; apply Permutation.Permutation_map.
transitivity (sort (CPToList cp')); [assumption|].
apply Permutation.Permutation_sym; assumption.
Qed.

Definition list_assoc_inv :=
  (fix list_assoc_inv_rec (A:Type) (B:Set)
                          (eq_dec:forall e1 e2:B, {e1 = e2} + {e1 <> e2})
                          (lst : list (prodT A B)) {struct lst} : B -> A -> A :=
  fun (key:B) (default:A) =>
    match lst with
      | nil => default
      | cons (pairT v e) l =>
        match eq_dec e key with
          | left _ => v
          | right _ => list_assoc_inv_rec A B eq_dec l key default
        end
    end).

Lemma positive_dec : forall (p1 p2:positive), {p1=p2}+{~p1=p2}.
Proof.
decide equality.
Defined.

Definition interp (lvar : list (COINCpoint * positive)) (Default : COINCpoint) :
  positive -> COINCpoint :=
    fun p => list_assoc_inv COINCpoint positive positive_dec lvar p Default.

End Coinc_refl.

Ltac add_to_distinct_list x xs :=
  match xs with
    | nil     => constr:(x::xs)
    | x::_    => fail 1
    | ?y::?ys => let zs := add_to_distinct_list x ys in constr:(y::zs)
  end.

Ltac collect_points_list Tpoint xs :=
  match goal with
    | N : Tpoint |- _ => let ys := add_to_distinct_list N xs in
                           collect_points_list Tpoint ys
    | _               => xs
  end.

Ltac collect_points Tpoint := collect_points_list Tpoint (@nil Tpoint).

Ltac number_aux Tpoint lvar cpt :=
  match constr:(lvar) with
    | nil          => constr:(@nil (prodT Tpoint positive))
    | cons ?H ?T => let scpt := eval vm_compute in (Pos.succ cpt) in
                    let lvar2 := number_aux Tpoint T scpt in
                      constr:(cons (@pairT  Tpoint positive H cpt) lvar2)
  end.

Ltac number Tpoint lvar := number_aux Tpoint lvar (1%positive).

Ltac build_numbered_points_list Tpoint := let lvar := collect_points Tpoint in number Tpoint lvar.

Ltac List_assoc Tpoint elt lst :=
  match constr:(lst) with
    | nil => fail
    | (cons (@pairT Tpoint positive ?X1 ?X2) ?X3) =>
      match constr:(elt = X1) with
        | (?X1 = ?X1) => constr:(X2)
        | _ => List_assoc Tpoint elt X3
      end
  end.

Definition Tagged P : Prop := P.

Lemma PropToTagged : forall P : Prop, P -> Tagged P.
Proof. trivial. Qed.