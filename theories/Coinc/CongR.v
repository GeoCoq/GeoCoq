Require Import Recdef.
Require Import NArith.
Require Import GeoCoq.Coinc.Utils.sets.

Module SSPWP := WPropertiesOn SetOfSetsOfPairsOfPositiveOrderedType SSP.

Module SSPWEqP := WEqPropertiesOn SetOfSetsOfPairsOfPositiveOrderedType SSP.

Lemma proper_0 : Proper (SP.Equal ==> eq) (fun s => negb (SP.is_empty s)).
Proof.
intros x y Hxy.
f_equal.
apply SPWP.Dec.F.is_empty_m.
assumption.
Qed.

Lemma proper_1 : forall s1,
  Proper (SP.Equal ==> eq)
  (fun s2 : SSP.elt => negb (SP.is_empty (SP.inter s1 s2))).
Proof.
intros s1 x y HXY.
assert (HEqI : SP.Equal (SP.inter s1 x) (SP.inter s1 y))
  by (apply SPWP.inter_equal_2; assumption).
apply proper_0; auto.
Qed.

Definition exists_witness (f : SSP.elt -> bool) (s : SSP.t) : option SSP.elt :=
  SSP.choose (SSP.filter f s).

Lemma exists_witness_ok : forall e f s,
  Proper (SP.Equal ==> eq) f ->
  exists_witness f s = Some e -> SSP.In e s.
Proof.
intros e f s HP H.
unfold exists_witness in H.
apply SSPWEqP.MP.Dec.F.mem_2.
apply SSPWEqP.choose_mem_1 in H.
rewrite SSPWEqP.filter_mem in H; try assumption.
apply andb_true_iff in H.
induction H.
assumption.
Qed.

Definition pick_lengths_aux (s1 : SSP.elt) (ss : SSP.t) : (option (SSP.elt * SSP.elt)) :=
  match (exists_witness (fun s2 => negb (SP.is_empty (SP.inter s1 s2))) ss) with
    | None => None
    | Some s2 => Some(s1,s2)
  end.

Definition pick_lengths (ss : SSP.t) : (option (SSP.elt * SSP.elt)) :=
  match (exists_witness (fun s =>
                           match (pick_lengths_aux s (SSP.remove s ss)) with
                             | None => false
                             | _ => true
                           end) ss) with
    | None => None
    | Some s1 => pick_lengths_aux s1 (SSP.remove s1 ss)
  end.

Definition eqop (p1 p2 : option SSP.elt) :=
  match p1,p2 with
    | None, None => True
    | Some s1, Some s2 => True
    | _, _ => False
  end.

Lemma proper_2_aux : Proper (SSP.Equal ==> eqop) SSP.choose.
Proof.
intros x y H.
unfold eqop.
case_eq (SSP.choose x); case_eq (SSP.choose y).

  intuition.

  intros HCN e HCS.
  apply SSP.choose_spec1 in HCS.
  apply SSP.choose_spec2 in HCN.
  rewrite H in HCS.
  apply SSPWEqP.MP.empty_is_empty_1 in HCN.
  rewrite HCN in HCS.
  apply SSPWEqP.MP.Dec.F.empty_iff in HCS.
  assumption.

  intros e HCS HCN.
  apply SSP.choose_spec1 in HCS.
  apply SSP.choose_spec2 in HCN.
  rewrite H in HCN.
  apply SSPWEqP.MP.empty_is_empty_1 in HCN.
  rewrite HCN in HCS.
  apply SSPWEqP.MP.Dec.F.empty_iff in HCS.
  assumption.

  intuition.
Qed.

Lemma proper_2 : forall (f1 f2 : SSP.elt -> bool) (s1 s2 : SSP.t),
  Proper (SP.Equal ==> eq) f1 ->
  (forall x, f1 x = f2 x) ->
  SSP.Equal s1 s2 ->
  eqop (exists_witness f1 s1) (exists_witness f2 s2).
Proof.
intros.
apply proper_2_aux.
apply SSPWEqP.MP.Dec.F.filter_ext; assumption.
Qed.

Definition eqopp (p1 p2 : option (SSP.elt * SSP.elt)) :=
  match p1,p2 with
    | None, None => True
    | Some s1, Some s2 => True
    | _, _ => False
  end.

Lemma proper_3 : Proper (SP.Equal ==> SSP.Equal ==> eqopp) pick_lengths_aux.
Proof.
intros x1 y1 HXY1.
intros x2 y2 HXY2.
unfold pick_lengths_aux.
assert (H : eqop (exists_witness (fun s2 : SSP.elt => negb (SP.is_empty (SP.inter x1 s2))) x2)
             (exists_witness (fun s2 : SSP.elt => negb (SP.is_empty (SP.inter y1 s2))) y2)).

  apply proper_2.

    apply proper_1.

    intro; apply proper_0.

      apply SPWP.inter_equal_1; assumption.

      assumption.

case_eq (exists_witness (fun s2 : SSP.elt => negb (SP.is_empty (SP.inter y1 s2))) y2);
case_eq (exists_witness (fun s2 : SSP.elt => negb (SP.is_empty (SP.inter x1 s2))) x2).

  simpl; intuition.

  intros HCN e HCS.
  simpl.
  rewrite HCS in H; rewrite HCN in H.
  simpl in H.
  assumption.

  intros e HCS HCN.
  simpl.
  rewrite HCS in H; rewrite HCN in H.
  simpl in H.
  assumption.

  intuition auto with crelations.
Qed.

Lemma pick_lengths_ok_1 : forall s1 s2 ss,
  pick_lengths ss = Some(s1,s2) ->
  SSP.In s1 ss.
Proof.
intros s1 s2 ss H.
unfold pick_lengths in H.
case_eq (exists_witness (fun s : SSP.elt => match pick_lengths_aux s (SSP.remove s ss) with
                          | Some _ => true | None => false end) ss).

  intros e1 HEW1.
  rewrite HEW1 in H.
  unfold pick_lengths_aux in H.
  case_eq (exists_witness (fun s2 : SSP.elt => negb (SP.is_empty (SP.inter e1 s2))) (SSP.remove e1 ss)).

    intros e2 HEW2.
    rewrite HEW2 in H.
    assert (HEq1 : e1 = s1) by (injection H; intros; assumption).
    rewrite HEq1 in *.
    assert (HEq2 : e2 = s2) by (injection H; intros; assumption).
    rewrite HEq2 in *.
    eapply exists_witness_ok; [|exact HEW1].
    intros x y HXY.
    assert (SSP.Equal (SSP.remove x ss) (SSP.remove y ss))
      by (apply SSPWP.Dec.F.remove_m; try assumption; reflexivity).
    assert (eqopp (pick_lengths_aux x (SSP.remove x ss)) (pick_lengths_aux y (SSP.remove y ss))).
    apply proper_3; auto.
    case_eq (pick_lengths_aux x (SSP.remove x ss));
      intros;
      case_eq (pick_lengths_aux y (SSP.remove y ss));
      intros.

      reflexivity.

      rewrite H2 in H1; rewrite H3 in H1.
      unfold eqop in H1; simpl in H1.
      contradiction.

      rewrite H2 in H1; rewrite H3 in H1.
      unfold eqop in H1; simpl in H1.
      contradiction.

      reflexivity.

    intro HEW2.
    rewrite HEW2 in H.
    discriminate H.

  intro HEW.
  rewrite HEW in H.
  discriminate H.
Qed.

Lemma pick_lengths_ok_2 : forall s1 s2 ss,
  pick_lengths ss = Some(s1,s2) ->
  SSP.In s2 (SSP.remove s1 ss).
Proof.
intros s1 s2 ss H.
unfold pick_lengths in H.
case_eq (exists_witness (fun s : SSP.elt => match pick_lengths_aux s (SSP.remove s ss) with
                          | Some _ => true | None => false end) ss).

  intros e1 HEW1.
  rewrite HEW1 in H.
  unfold pick_lengths_aux in H.
  case_eq (exists_witness (fun s2 : SSP.elt => negb (SP.is_empty (SP.inter e1 s2))) (SSP.remove e1 ss)).

    intros e2 HEW2.
    rewrite HEW2 in H.
    assert (HEq1 : e1 = s1) by (injection H; intros; assumption).
    rewrite HEq1 in *.
    assert (HEq2 : e2 = s2) by (injection H; intros; assumption).
    rewrite HEq2 in *.
    apply exists_witness_ok with (fun s2 : SSP.elt => negb (SP.is_empty (SP.inter s1 s2))).
    apply proper_1.
    assumption.

    intro HEW2.
    rewrite HEW2 in H.
    discriminate H.

  intro HEW.
  rewrite HEW in H.
  discriminate H.
Qed.

Function identify_lengths (ss : SSP.t) {measure SSP.cardinal ss}
                        : SSP.t :=
  let lengths := pick_lengths ss in
    match lengths with
      |None => ss
      |Some (s1,s2) => let auxsetofsets := SSP.remove s2 (SSP.remove s1 ss) in
                       let auxset := SP.union s1 s2 in
                       let newss := SSP.add auxset auxsetofsets in
                         identify_lengths newss
    end.
Proof.
intros.
assert (S(SSP.cardinal (SSP.remove s1 ss)) = SSP.cardinal ss).
apply SSPWP.remove_cardinal_1.
apply pick_lengths_ok_1 with s2.
assumption.
assert (S(S(SSP.cardinal (SSP.remove s2 (SSP.remove s1 ss)))) = S(SSP.cardinal (SSP.remove s1 ss))).
apply eq_S.
apply SSPWP.remove_cardinal_1.
apply pick_lengths_ok_2.
assumption.
assert (HR1 : S(S(SSP.cardinal (SSP.remove s2 (SSP.remove s1 ss)))) = SSP.cardinal ss).
transitivity (S(SSP.cardinal (SSP.remove s1 ss))); assumption.
elim (SSPWP.In_dec (SP.union s1 s2) (SSP.remove s2 (SSP.remove s1 ss))); intro HDec.

  assert (HR2 : SSP.cardinal (SSP.add (SP.union s1 s2) (SSP.remove s2 (SSP.remove s1 ss))) = SSP.cardinal (SSP.remove s2 (SSP.remove s1 ss))).
  apply SSPWP.add_cardinal_1; assumption.
  rewrite HR2.
  rewrite <- HR1.
  apply le_S, le_n.

  assert (HR2 : SSP.cardinal (SSP.add (SP.union s1 s2) (SSP.remove s2 (SSP.remove s1 ss))) = S(SSP.cardinal (SSP.remove s2 (SSP.remove s1 ss)))).
  apply SSPWP.add_cardinal_2; assumption.
  rewrite HR2.
  rewrite <- HR1.
  apply le_n.
Defined.

Definition test_cong (ss : SSP.t) p1 p2 p3 p4 : bool :=
  let newss := identify_lengths ss in
    SSP.exists_ (fun s => SP.mem (p1,p2) s && SP.mem (p3,p4) s) newss.

Section Cong_refl.

Context `{CT:Cong_theory}.

Lemma CTcong_right_comm : forall A B C D, CTCong A B C D -> CTCong A B D C.
Proof.
intros.
apply CTcong_sym, CTcong_left_comm, CTcong_sym.
assumption.
Qed.

Lemma CTcong_comm : forall A B C D, CTCong A B C D -> CTCong B A D C.
Proof.
intros.
apply CTcong_left_comm, CTcong_right_comm.
assumption.
Qed.

Lemma CTcong_pseudo_refl : forall A B, CTCong A B B A.
Proof.
intros.
apply CTcong_left_comm, CTcong_refl.
Qed.

Definition ss_ok (ss : SSP.t) (interp: positive -> CONGpoint) :=
  forall s, SSP.mem s ss = true ->
  forall p1 p2 p3 p4, SP.mem (p1,p2) s && SP.mem (p3,p4) s = true ->
    CTCong (interp p1) (interp p2) (interp p3) (interp p4).

Lemma identify_lengths_ok : forall ss interp,
  ss_ok ss interp -> ss_ok (identify_lengths ss) interp.
Proof.
intros ss interp HSS.
apply (let P ss newss :=
       ss_ok ss interp -> ss_ok newss interp in
         identify_lengths_ind P); try assumption.

  intros.
  assumption.

  clear HSS ss.
  intros ss suitablepairofsets s1 s2 Hs1s2 auxsetofsets auxset newss H HSS.
  assert (Hs1 := Hs1s2).
  assert (Hs2 := Hs1s2).
  apply pick_lengths_ok_1 in Hs1.
  apply pick_lengths_ok_2 in Hs2.
  apply SSPWEqP.MP.Dec.F.remove_3 in Hs2.
  apply H; clear H.
  intros s Hmem p1 p2 p3 p4 Hmemp.
  unfold newss in Hmem; clear newss.
  elim (SSP.E.eq_dec auxset s); intro HEq.

    rewrite <- HEq in *; clear HEq Hmem s.
    unfold suitablepairofsets in Hs1s2; clear suitablepairofsets.
    unfold pick_lengths in Hs1s2.
    case_eq (exists_witness
            (fun s : SSP.elt =>
             match pick_lengths_aux s (SSP.remove s ss) with
             | Some _ => true
             | None => false
             end) ss); [|intro HEW; rewrite HEW in Hs1s2; discriminate Hs1s2].
    intros e1 HEW; rewrite HEW in *; clear HEW.
    unfold pick_lengths_aux in *.
    case_eq (exists_witness
            (fun s2 : SSP.elt => negb (SP.is_empty (SP.inter e1 s2)))
            (SSP.remove e1 ss)); [|intro HEW; rewrite HEW in Hs1s2; discriminate Hs1s2].
    intros e2 HEW; rewrite HEW in *.
    injection Hs1s2; intros He2s2 He1s1.
    rewrite He2s2, He1s1 in *; clear He2s2 He1s1 Hs1s2 e2 e1.
    apply SSP.choose_spec1, SSPWEqP.MP.Dec.F.filter_2 in HEW; [|apply proper_1].
    apply eq_sym, negb_sym, not_true_iff_false in HEW.
    rewrite SP.is_empty_spec, SPWP.cardinal_Empty in HEW.
    apply SPWP.cardinal_inv_2b in HEW.
    destruct HEW as [(e1,e2) He].
    apply SP.inter_spec in He.
    destruct He as [Hes1 Hes2].
    rewrite andb_true_iff in Hmemp.
    destruct Hmemp as [Hmemp1 Hmemp2].
    cut (forall p q, SP.mem (p, q) auxset = true ->
              CTCong (interp e1) (interp e2) (interp p) (interp q)).

      intro Haux.
      apply CTcong_trans with (interp e1) (interp e2); [apply CTcong_sym|]; apply Haux; assumption.

    intros p q Hmemp.
    apply SPWP.Dec.F.mem_2, SPWP.Dec.F.union_1 in Hmemp.
    rewrite SSPWP.Dec.F.mem_iff in *.
    rewrite 2 SPWP.Dec.F.mem_iff in *.
    destruct Hmemp; [apply (HSS s1 Hs1)|apply (HSS s2 Hs2)]; apply andb_true_iff; split; assumption.

    rewrite SSPWP.Dec.F.add_neq_b in Hmem; [|assumption].
    apply SSPWEqP.MP.Dec.F.mem_2 in Hmem.
    do 2 (apply SSPWEqP.MP.Dec.F.remove_3 in Hmem).
    apply SSPWEqP.MP.Dec.F.mem_1 in Hmem.
    apply (HSS s); assumption.
Qed.

Lemma test_cong_ok : forall ss interp p1 p2 p3 p4,
  ss_ok ss interp ->
  test_cong ss p1 p2 p3 p4 = true ->
  CTCong (interp p1) (interp p2) (interp p3) (interp p4).
Proof.
intros ss interp p1 p2 p3 p4 HSS HTC.
unfold test_cong in HTC.
assert (HSS2 : ss_ok (identify_lengths ss) interp)
  by (apply identify_lengths_ok; assumption).

unfold ss_ok in HSS2.
apply SSPWEqP.MP.Dec.F.exists_2 in HTC.
unfold SSP.Exists in HTC.
destruct HTC as [s [HIn Hmem]].
apply HSS2 with s.
apply SSPWEqP.MP.Dec.F.mem_1.
assumption.
assumption.

intros x y Hxy.
assert (HmemEq : forall p q, SP.mem (p,q) x = SP.mem (p,q) y)
  by (intros; apply SPWP.Dec.F.mem_m; [unfold Pos.eq|]; auto).
rewrite 2 HmemEq; reflexivity.
Qed.

Lemma ss_ok_empty : forall interp,
  ss_ok SSP.empty interp.
Proof.
intros interp ss Hmem1.
rewrite SSPWEqP.MP.Dec.F.empty_b in Hmem1.
discriminate.
Qed.

Lemma eq_le2__eq2 : forall p1 p2 p3 p4, Pos.le p1 p2 -> Pos.le p3 p4 ->
  (Pos.eq (fstpp (p1, p2)) (fstpp (p3, p4)) /\ Pos.eq (sndpp (p1, p2)) (sndpp (p3, p4))) ->
  (p1 = p3 /\ p2 = p4).
Proof.
intros p1 p2 p3 p4 Hle Hle'.
unfold fstpp, sndpp, Pos.eq.
rewrite 2 Pos.min_l; [rewrite 2 Pos.max_r|..]; trivial.
Qed.

Lemma eq_pseudo_refl : forall p q,
  Pos.eq (fstpp (p, q)) (fstpp (q, p)) /\ Pos.eq (sndpp (p, q)) (sndpp (q, p)).
Proof.
cut (forall p q, Pos.le p q ->
  Pos.eq (fstpp (p, q)) (fstpp (q, p)) /\ Pos.eq (sndpp (p, q)) (sndpp (q, p))).

  intros Haux p q.
  case_eq (Pos.leb p q); intro Hpq.

    apply Haux, Pos.leb_le, Hpq.

    apply SP.Raw.MX.eq_sym, Haux, Pos.lt_le_incl, Pos.leb_gt, Hpq.

intros p q Hle.
unfold fstpp, sndpp.
rewrite Pos.min_l; trivial.
rewrite Pos.min_r; trivial.
rewrite Pos.max_r; trivial.
rewrite Pos.max_l; trivial.
split; reflexivity.
Qed.

Lemma collect_congs :
  forall (A B C D : CONGpoint) (HCong : CTCong A B C D) pa pb pc pd ss (interp :  positive -> CONGpoint),
  interp pa = A ->
  interp pb = B ->
  interp pc = C ->
  interp pd = D ->
  ss_ok ss interp -> ss_ok (SSP.add (SP.add (pa,pb) (SP.add (pc,pd) SP.empty)) ss) interp.
Proof.
intros A B C D HCong pa pb pc pd ss interp HA HB HC HD HSS.
revert A B C D pa pb pc pd HA HB HC HD HCong.
cut (forall A B C D pa pb pc pd, interp pa = A -> interp pb = B -> interp pc = C -> interp pd = D ->
      CTCong A B C D -> Pos.le pa pb -> Pos.le pc pd ->
      ss_ok (SSP.add (SP.add (pa, pb) (SP.add (pc, pd) SP.empty)) ss) interp).

  intros Haux A B C D pa pb pc pd HA HB HC HD HCong.
  revert C D pc pd HC HD HCong.
  cut (forall C D pc pd, interp pc = C -> interp pd = D -> CTCong A B C D -> Pos.le pc pd ->
      ss_ok (SSP.add (SP.add (pa, pb) (SP.add (pc, pd) SP.empty)) ss) interp).

    intros Haux' C D pc pd HC HD HCong.
    case_eq (Pos.leb pc pd); intro Hpcpd.

      apply Pos.leb_le in Hpcpd.
      apply Haux' with C D; assumption.

      apply Pos.leb_gt, Pos.lt_le_incl in Hpcpd.
      assert (Heq : SP.Equal (SP.add (pc, pd) SP.empty) (SP.add (pd, pc) SP.empty))
        by (apply SPWP.Dec.F.add_m; [apply eq_pseudo_refl|apply SPWP.equal_refl]).
      intro s.
      rewrite Heq.
      apply Haux' with D C; trivial.
      apply CTcong_right_comm, HCong.

  intros C D pc pd HC HD HCong Hpcpd.
  case_eq (Pos.leb pa pb); intro Hpapb.

    apply Pos.leb_le in Hpapb.
    apply Haux with A B C D; assumption.

    apply Pos.leb_gt, Pos.lt_le_incl in Hpapb.
    assert (Heq : SP.Equal (SP.add (pa, pb) (SP.add (pc, pd) SP.empty))
                           (SP.add (pb, pa) (SP.add (pc, pd) SP.empty)))
      by (apply SPWP.Dec.F.add_m; [apply eq_pseudo_refl|apply SPWP.equal_refl]).
    intro s.
    rewrite Heq.
    apply Haux with B A C D; trivial.
    apply CTcong_left_comm, HCong.

intros A B C D pa pb pc pd HA HB HC HD HCong Hpapb Hpcpd s Hs.
cut (forall p1 p2 p3 p4, SP.mem (p1, p2) s && SP.mem (p3, p4) s = true ->
      Pos.le p1 p2 -> Pos.le p3 p4 -> CTCong (interp p1) (interp p2) (interp p3) (interp p4)).

  intros Haux p1 p2.
  cut (forall p3 p4, SP.mem (p1, p2) s && SP.mem (p3, p4) s = true ->
        Pos.le p3 p4 -> CTCong (interp p1) (interp p2) (interp p3) (interp p4)).

    intros Haux' p3 p4 Hmem.
    case_eq (Pos.leb p3 p4); intro Hp3p4.

      apply Pos.leb_le in Hp3p4.
      apply Haux'; assumption.

      apply Pos.leb_gt, Pos.lt_le_incl in Hp3p4.
      apply CTcong_right_comm, Haux'; trivial.
      assert (Heq : SP.mem (p4, p3) s = SP.mem (p3, p4) s)
        by (apply SPWP.Dec.F.mem_m; [apply eq_pseudo_refl|apply SPWP.equal_refl]).
      rewrite Heq.
      assumption.

  intros p3 p4 Hmem Hp3p4.
  case_eq (Pos.leb p1 p2); intro Hp1p2.

    apply Pos.leb_le in Hp1p2.
    apply Haux; assumption.

    apply Pos.leb_gt, Pos.lt_le_incl in Hp1p2.
    apply CTcong_left_comm, Haux; trivial.
    assert (Heq : SP.mem (p2, p1) s = SP.mem (p1, p2) s)
      by (apply SPWP.Dec.F.mem_m; [apply eq_pseudo_refl|apply SPWP.equal_refl]).
    rewrite Heq.
    assumption.

intros p1 p2 p3 p4 Hmem Hp1p2 Hp3p4.
elim (SPWP.Dec.F.eq_dec (p1,p2) (p3,p4)); intro Hp1p3.

  apply eq_le2__eq2 in Hp1p3; trivial.
  destruct Hp1p3.
  subst.
  apply CTcong_refl.

  apply SSPWEqP.MP.Dec.F.mem_2 in Hs.
  apply SSPWEqP.MP.Dec.F.add_iff in Hs.
  rewrite andb_true_iff in Hmem.
  destruct Hmem as [Hmem1 Hmem2].
  elim Hs; intro HsE.

    assert (HmemR : forall p q, SP.mem (p,q) (SP.add (pa, pb) (SP.add (pc, pd) SP.empty)) = SP.mem (p,q) s)
      by (intros; apply SPWP.Dec.F.mem_m; [unfold Pos.eq|]; auto).
    rewrite <- HmemR in Hmem1.
    rewrite <- HmemR in Hmem2.
    clear HmemR.
    elim (SPWP.Dec.F.eq_dec (pa,pb) (p1,p2)); intro Hpap1.

      apply eq_le2__eq2 in Hpap1; trivial.
      destruct Hpap1 as [Hpap1 Hpbp2].
      rewrite Hpap1, Hpbp2 in *.
      rewrite SPWP.Dec.F.add_neq_b in Hmem2; trivial.
      rewrite <- SPWP.singleton_equal_add in Hmem2.
      apply SPWP.Dec.F.mem_iff in Hmem2.
      apply SPWP.Dec.F.singleton_1 in Hmem2.
      apply eq_le2__eq2 in Hmem2; trivial.
      destruct Hmem2 as [Hpcp3 Hpdp4].
      rewrite Hpcp3, Hpdp4 in *; rewrite HA, HB, HC, HD.
      assumption.

    rewrite SPWP.Dec.F.add_neq_b in Hmem1; trivial.
    rewrite <- SPWP.singleton_equal_add in Hmem1.
    apply SPWP.Dec.F.mem_iff in Hmem1.
    apply SPWP.Dec.F.singleton_1 in Hmem1.
    apply eq_le2__eq2 in Hmem1; trivial.
    destruct Hmem1 as [Hpcp1 Hpdp2].
    rewrite Hpcp1, Hpdp2 in *.
    rewrite SPWP.add_add in Hmem2.
    rewrite SPWP.Dec.F.add_neq_b in Hmem2; trivial.
    rewrite <- SPWP.singleton_equal_add in Hmem2.
    apply SPWP.Dec.F.mem_iff in Hmem2.
    apply SPWP.Dec.F.singleton_1 in Hmem2.
    apply eq_le2__eq2 in Hmem2; trivial.
    destruct Hmem2 as [Hpap3 Hpbp4].
    rewrite Hpap3, Hpbp4 in *; rewrite HA, HB, HC, HD.
    apply CTcong_sym, HCong.

  apply HSS with s.
  apply SSPWEqP.MP.Dec.F.mem_1.
  assumption.
  rewrite Hmem1; rewrite Hmem2; reflexivity.
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

Definition interp (lvar : list (CONGpoint * positive)) (Default : CONGpoint) : positive -> CONGpoint :=
  fun p => list_assoc_inv CONGpoint positive positive_dec lvar p Default.

End Cong_refl.
