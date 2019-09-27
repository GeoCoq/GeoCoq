Require Import Bool.
Require Import Morphisms.
Require Import NArith.
Require Import Recdef.
Require Import GeoCoq.Utils.sets.

Lemma proper_0 :
  Proper ((@Equal SP) ==> Logic.eq) (fun s => negb ((@is_empty SP) s)).
Proof. intros x y Hxy; f_equal; apply (@is_empty_m SP); assumption. Qed.

Lemma proper_1 : forall s1,
  Proper ((@Equal SP) ==> Logic.eq)
         (fun s2 : (@elt SSP) => negb ((@is_empty SP) ((@inter SP) s1 s2))).
Proof.
intros s1 x y HXY.
assert (HEqI : (@Equal SP) ((@inter SP) s1 x) ((@inter SP) s1 y))
  by (apply inter_equal_2; assumption).
apply proper_0; auto.
Qed.

Definition exists_witness (f : (@elt SSP) -> bool) s : option (@elt SSP) :=
  (@choose SSP) ((@filter SSP) f s).

Lemma exists_witness_ok : forall e f s,
  Proper ((@Equal SP) ==> Logic.eq) f ->
  exists_witness f s = Some e -> (@In SSP) e s.
Proof.
intros e f s HP H; unfold exists_witness in H.
apply mem_2; apply choose_mem_1 in H.
rewrite filter_mem in H; try assumption.
apply andb_true_iff in H; intuition.
Qed.

Definition pick_lengths_aux (s1 : (@elt SSP))
                            (ss : (@TCSets.t SSP))
                            : (option ((@elt SSP) * (@elt SSP))) :=
  match (exists_witness
           (fun s2 => negb ((@is_empty SP) ((@inter SP) s1 s2))) ss) with
    | None    => None
    | Some s2 => Some(s1,s2)
  end.

Definition pick_lengths (ss : (@TCSets.t SSP))
                        : (option ((@elt SSP) * (@elt SSP))) :=
  match (exists_witness (fun s =>
                           match (pick_lengths_aux s ((@remove SSP) s ss)) with
                             | None => false
                             | _    => true
                           end) ss) with
    | None    => None
    | Some s1 => pick_lengths_aux s1 ((@remove SSP) s1 ss)
  end.

Definition eqop (p1 p2 : option (@elt SSP)) :=
  match p1,p2 with
    | None   , None    => True
    | Some s1, Some s2 => True
    | _      , _       => False
  end.

Lemma proper_2_aux : Proper ((@Equal SSP) ==> eqop) (@choose SSP).
Proof.
intros x y H; unfold eqop; case_eq (choose x); case_eq (choose y);
[intuition|intros HCN e HCS|intros e HCS HCN|intuition];
apply choose_spec1 in HCS; apply choose_spec2 in HCN;
unfold Equal, Equal_aux in H; [rewrite H in HCS|rewrite <- H in HCS];
apply empty_is_empty_1 in HCN; unfold Equal, Equal_aux in HCN;
rewrite HCN in HCS; apply empty_iff in HCS; assumption.
Qed.

Lemma proper_2 : forall (f1 f2 : (@elt SSP) -> bool) (s1 s2 : (@TCSets.t SSP)),
  Proper ((@Equal SP) ==> Logic.eq) f1 ->
  (forall x, f1 x = f2 x) ->
  (@Equal SSP) s1 s2 ->
  eqop (exists_witness f1 s1) (exists_witness f2 s2).
Proof. intros; apply proper_2_aux, filter_ext; assumption. Qed.

Definition eqopp (p1 p2 : option ((@elt SSP) * (@elt SSP))) :=
  match p1,p2 with
    | None   , None    => True
    | Some s1, Some s2 => True
    | _      , _       => False
  end.

Lemma proper_3 :
  Proper ((@Equal SP) ==> (@Equal SSP) ==> eqopp) pick_lengths_aux.
Proof.
intros x1 y1 HXY1 x2 y2 HXY2; unfold pick_lengths_aux.
assert (H : eqop (exists_witness
                    (fun s2 : (@elt SSP)
                       => negb ((@is_empty SP) ((@inter SP) x1 s2))) x2)
                 (exists_witness
                    (fun s2 : (@elt SSP)
                       => negb ((@is_empty SP) ((@inter SP) y1 s2))) y2)).
  {
  apply proper_2; [apply proper_1| |assumption].
  intro; apply proper_0; apply inter_equal_1; assumption.
  }
case_eq (exists_witness (fun s2 => negb (is_empty (inter y1 s2))) y2);
case_eq (exists_witness (fun s2 => negb (is_empty (inter x1 s2))) x2);
[simpl; intuition|intros HCN e HCS|intros e HCS HCN|intuition];
simpl; rewrite HCS in H; rewrite HCN in H; simpl in H; assumption.
Qed.

Lemma pick_lengths_ok_1 : forall s1 s2 ss,
  pick_lengths ss = Some (s1,s2) ->
  In s1 ss.
Proof.
intros s1 s2 ss H; unfold pick_lengths in H.
case_eq (exists_witness (fun s => match pick_lengths_aux s (remove s ss) with
                          | Some _ => true | None => false end) ss);
[|intro HEW; rewrite HEW in H; discriminate H].
intros e1 HEW1; rewrite HEW1 in H; unfold pick_lengths_aux in H.
case_eq (exists_witness (fun s2
                           => negb (is_empty (inter e1 s2))) (remove e1 ss));
[|intro HEW2; rewrite HEW2 in H; discriminate H].
intros e2 HEW2; rewrite HEW2 in H.
assert (HEq1 : e1 = s1) by (injection H; intros; assumption).
rewrite HEq1 in *.
assert (HEq2 : e2 = s2) by (injection H; intros; assumption).
rewrite HEq2 in *; eapply exists_witness_ok; [|exact HEW1].
intros x y HXY.
assert (H1 : eqopp (pick_lengths_aux x (remove x ss))
                   (pick_lengths_aux y (remove y ss))).
  {
  assert (Equal (remove x ss) (remove y ss));
  [apply remove_m; [assumption|apply Equal_refl]|apply proper_3; auto].
  }
case_eq (pick_lengths_aux x (remove x ss)); [intro p|]; intro H2;
case_eq (pick_lengths_aux y (remove y ss));
[reflexivity| |intro p|reflexivity]; intro H3; rewrite H2 in H1;
rewrite H3 in H1; unfold eqop in H1; simpl in H1; contradiction.
Qed.

Lemma pick_lengths_ok_2 : forall s1 s2 ss,
  pick_lengths ss = Some (s1,s2) ->
  In s2 (remove s1 ss).
Proof.
intros s1 s2 ss H; unfold pick_lengths in H.
case_eq (exists_witness (fun s => match pick_lengths_aux s (remove s ss) with
                          | Some _ => true | None => false end) ss);
[|intro HEW; rewrite HEW in H; discriminate H].
intros e1 HEW1; rewrite HEW1 in H; unfold pick_lengths_aux in H.
case_eq (exists_witness (fun s2 => negb (is_empty (inter e1 s2)))
                        (remove e1 ss)); [intro e2|];
intro HEW2; rewrite HEW2 in H; [|discriminate H].
assert (HEq1 : e1 = s1) by (injection H; intros; assumption).
rewrite HEq1 in *.
assert (HEq2 : e2 = s2) by (injection H; intros; assumption).
rewrite HEq2 in *.
apply exists_witness_ok with (fun s2 => negb (is_empty (inter s1 s2)));
[apply proper_1|assumption].
Qed.

Function identify_lengths (ss : (@TCSets.t SSP))
         {measure cardinal ss} : (@TCSets.t SSP) :=
  let lengths := pick_lengths ss in
    match lengths with
      | None         => ss
      | Some (s1,s2) =>
         let auxsetofsets := remove s2 (remove s1 ss) in
         let auxset := union s1 s2 in
         let newss := add auxset auxsetofsets in
         identify_lengths newss
    end.
Proof.
intros.
assert (Datatypes.S(cardinal (remove s1 ss)) = cardinal ss)
  by (apply remove_cardinal_1; apply pick_lengths_ok_1 with s2; assumption).
assert (Datatypes.S(Datatypes.S(cardinal (remove s2 (remove s1 ss)))) =
        Datatypes.S(cardinal (remove s1 ss))).
  {
  apply eq_S; apply remove_cardinal_1;
  apply pick_lengths_ok_2; assumption.
  }
assert (HR1 : Datatypes.S(Datatypes.S(cardinal (remove s2 (remove s1 ss)))) =
              cardinal ss)
  by (transitivity (Datatypes.S(cardinal (remove s1 ss))); assumption).
elim ((@In_dec SSP) (union s1 s2) (remove s2 (remove s1 ss))); intro HDec.

  {
  assert (HR2 : cardinal (add (union s1 s2) (remove s2 (remove s1 ss))) =
                cardinal (remove s2 (remove s1 ss)))
    by (apply add_cardinal_1; assumption).
  rewrite HR2, <- HR1; apply le_S, le_n.
  }

  {
  assert (HR2 : cardinal (add (union s1 s2) (remove s2 (remove s1 ss))) =
                Datatypes.S(cardinal (remove s2 (remove s1 ss))))
    by (apply add_cardinal_2; assumption).
  rewrite HR2, <- HR1; apply le_n.
  }
Defined.

Definition test_cong (ss : (@TCSets.t SSP)) p1 p2 p3 p4 : bool :=
  let newss := identify_lengths ss in
    exists_ (fun s => (@mem SP) (p1,p2) s && (@mem SP) (p3,p4) s) newss.

Section Cong_refl.

Context `{CT:Cong_theory}.

Lemma CTcong_right_comm : forall A B C D, CTCong A B C D -> CTCong A B D C.
Proof. intros; apply CTcong_sym, CTcong_left_comm, CTcong_sym; assumption. Qed.

Lemma CTcong_comm : forall A B C D, CTCong A B C D -> CTCong B A D C.
Proof. intros; apply CTcong_left_comm, CTcong_right_comm; assumption. Qed.

Lemma CTcong_pseudo_refl : forall A B, CTCong A B B A.
Proof. intros; apply CTcong_left_comm, CTcong_refl. Qed.

Definition ss_ok (ss : (@TCSets.t SSP)) (interp: positive -> CONGpoint) :=
  forall s, mem s ss = true ->
  forall p1 p2 p3 p4, (@mem SP) (p1,p2) s && (@mem SP) (p3,p4) s = true ->
    CTCong (interp p1) (interp p2) (interp p3) (interp p4).

Lemma identify_lengths_ok : forall ss interp,
  ss_ok ss interp -> ss_ok (identify_lengths ss) interp.
Proof.
intros ss interp HSS.
apply (let P ss newss :=
       ss_ok ss interp -> ss_ok newss interp in
         identify_lengths_ind P); try assumption; [intros; assumption|].
clear HSS ss.
intros ss suitablepairofsets s1 s2 Hs1s2 auxsetofsets auxset newss H HSS.
assert (Hs1 := Hs1s2); assert (Hs2 := Hs1s2).
apply pick_lengths_ok_1 in Hs1; apply pick_lengths_ok_2 in Hs2.
apply remove_3 in Hs2.
apply H; clear H; intros s Hmem p1 p2 p3 p4 Hmemp.
unfold newss in Hmem; clear newss.
assert (HEq : Equal auxset s \/ ~ Equal auxset s)
  by (rewrite <- equal_Equal; elim (equal auxset s); auto).
destruct HEq as [HEq|HEq];
[|rewrite add_neq_b in Hmem; try assumption; apply HSS with s; [|assumption];
  unfold auxsetofsets in *; apply mem_2 in Hmem;
  do 2 (apply remove_3 in Hmem); apply mem_1; assumption].
rewrite andb_true_iff in Hmemp; destruct Hmemp as [Hmemp12 Hmemp34].
rewrite <- ((@mem_m SP) _ _ ((@TCSets.eq_refl SP) (p1,p2)) _ _ HEq) in Hmemp12.
rewrite <- ((@mem_m SP) _ _ ((@TCSets.eq_refl SP) (p3,p4)) _ _ HEq) in Hmemp34.
clear HEq Hmem s.
unfold suitablepairofsets in Hs1s2; clear suitablepairofsets.
unfold pick_lengths in Hs1s2.
case_eq (exists_witness
           (fun s : elt =>
              match pick_lengths_aux s (remove s ss) with
                | Some _ => true
                | None   => false
              end) ss); [|intro HEW; rewrite HEW in Hs1s2; discriminate Hs1s2].
intros e1 HEW; rewrite HEW in *; clear HEW.
unfold pick_lengths_aux in *.
case_eq (exists_witness
           (fun s2 => negb (is_empty (inter e1 s2))) (remove e1 ss));
[|intro HEW; rewrite HEW in Hs1s2; discriminate Hs1s2].
intros e2 HEW; rewrite HEW in *.
injection Hs1s2; intros He2s2 He1s1.
rewrite He2s2, He1s1 in *; clear He2s2 He1s1 Hs1s2 e2 e1.
apply choose_spec1, filter_2 in HEW; [|apply proper_1].
apply Logic.eq_sym, negb_sym, not_true_iff_false in HEW.
rewrite <- is_empty_iff, cardinal_Empty in HEW.
apply cardinal_inv_2b in HEW; destruct HEW as [(e1,e2) He].
apply inter_spec in He; destruct He as [Hes1 Hes2].
cut (forall p q, (@mem SP) (p, q) auxset = true ->
                 CTCong (interp e1) (interp e2) (interp p) (interp q));
[intro Haux; apply CTcong_trans with (interp e1) (interp e2);
[apply CTcong_sym|]; apply Haux; assumption|].
intros p q Hmemp; apply mem_2, union_1 in Hmemp.
rewrite mem_iff in Hs1; rewrite mem_iff in Hs2.
rewrite mem_iff in Hes1; rewrite mem_iff in Hes2.
rewrite 2 mem_iff in Hmemp; destruct Hmemp;
[apply (HSS s1 Hs1)|apply (HSS s2 Hs2)];
apply andb_true_iff; split; assumption.
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
unfold ss_ok in HSS2; apply exists_2 in HTC.

  {
  destruct HTC as [s [HIn Hmem]].
  apply HSS2 with s; [apply mem_1|]; assumption.
  }

  {
  intros x y Hxy.
  assert (HmemEq : forall p q, (@mem SP) (p,q) x = (@mem SP) (p,q) y)
    by (intros; apply mem_m; [apply eq_refl|auto]).
  rewrite 2 HmemEq; reflexivity.
  }
Qed.

Lemma ss_ok_empty : forall interp,
  ss_ok empty interp.
Proof. intros interp ss Hmem1; rewrite empty_b in Hmem1; discriminate. Qed.

Lemma eq_le2__eq2 : forall p1 p2 p3 p4,
  Pos.le p1 p2 -> Pos.le p3 p4 ->
  (Pos.eq (fstpp (p1, p2)) (fstpp (p3, p4)) /\
   Pos.eq (sndpp (p1, p2)) (sndpp (p3, p4))) ->
  (p1 = p3 /\ p2 = p4).
Proof.
intros p1 p2 p3 p4 Hle Hle'; unfold fstpp, sndpp, Pos.eq.
rewrite 2 Pos.min_l; [rewrite 2 Pos.max_r|..]; trivial.
Qed.

Lemma eq_pseudo_refl : forall p q,
  Pos.eq (fstpp (p, q)) (fstpp (q, p)) /\ Pos.eq (sndpp (p, q)) (sndpp (q, p)).
Proof.
cut (forall p q, Pos.le p q ->
  Pos.eq (fstpp (p, q)) (fstpp (q, p)) /\ Pos.eq (sndpp (p, q)) (sndpp (q, p))).

  {
  intros Haux p q; case_eq (Pos.leb p q); intro Hpq;
  [apply Haux, Pos.leb_le, Hpq|].
  apply sets.eq_sym, Haux, Pos.lt_le_incl, Pos.leb_gt, Hpq.
  }

  {
  intros p q Hle; unfold fstpp, sndpp.
  rewrite Pos.min_l; trivial.
  rewrite Pos.min_r; trivial.
  rewrite Pos.max_r; trivial.
  rewrite Pos.max_l; trivial.
  split; reflexivity.
  }
Qed.

Lemma collect_congs :
  forall (A B C D : CONGpoint) (HCong : CTCong A B C D),
  forall pa pb pc pd ss (interp :  positive -> CONGpoint),
  interp pa = A -> interp pb = B ->
  interp pc = C -> interp pd = D ->
  ss_ok ss interp ->
  ss_ok (add ((@add SP) (pa,pb) ((@add SP) (pc,pd) (@empty SP))) ss) interp.
Proof.
intros A B C D HCong pa pb pc pd ss interp HA HB HC HD HSS.
revert A B C D pa pb pc pd HA HB HC HD HCong.
cut (forall A B C D pa pb pc pd,
       interp pa = A -> interp pb = B -> interp pc = C -> interp pd = D ->
       CTCong A B C D -> Pos.le pa pb -> Pos.le pc pd ->
       ss_ok (add ((@add SP) (pa,pb) ((@add SP) (pc,pd) empty)) ss) interp).

  {
  intros Haux A B C D pa pb pc pd HA HB; revert C D pc pd.
  cut (forall C D pc pd,
         interp pc = C -> interp pd = D ->
         CTCong A B C D -> Pos.le pc pd ->
         ss_ok (add ((@add SP) (pa,pb) ((@add SP) (pc,pd) empty)) ss) interp).

    {
    intros Haux' C D pc pd HC HD HCong; case_eq (Pos.leb pc pd); intro Hpcpd;
    [apply Pos.leb_le in Hpcpd; apply Haux' with C D; assumption|].
    apply Pos.leb_gt, Pos.lt_le_incl in Hpcpd.
    assert (H : Equal (add ((@add SP) (pa,pb) ((@add SP) (pc,pd) empty)) ss)
                      (add ((@add SP) (pa,pb) ((@add SP) (pd,pc) empty)) ss)).
      {
      assert (H : Equal ((@add SP) (pa,pb) ((@add SP) (pc,pd) empty))
                        ((@add SP) (pa,pb) ((@add SP) (pd,pc) empty))).
        {
        intro a; rewrite <- !elements_iff, !add_iff; intuition; right; left;
        [apply TCSets.eq_trans with (pc,pd)|apply TCSets.eq_trans with (pd,pc)];
        auto; apply eq_pseudo_refl.
        }
      intro a; rewrite <- !elements_iff, !add_iff.
      split; intros [HE|HIn]; auto; left;
      [apply TCSets.eq_trans with ((@add SP)(pa,pb)((@add SP)(pc,pd) empty))|
       apply TCSets.eq_trans with ((@add SP)(pa,pb)((@add SP)(pd,pc) empty))];
      auto; apply TCSets.eq_sym; auto.
      }
    intros s Hs; rewrite (mem_m _ _ (TCSets.eq_refl s) H) in Hs.
    revert Hs; apply Haux' with D C; trivial.
    apply CTcong_right_comm, HCong.
    }

    {
    intros C D pc pd HC HD HCong Hpcpd; case_eq (Pos.leb pa pb); intro Hpapb;
    [apply Pos.leb_le in Hpapb; apply Haux with A B C D; assumption|].
    apply Pos.leb_gt, Pos.lt_le_incl in Hpapb.
    assert (H : Equal (add ((@add SP) (pa,pb) ((@add SP) (pc,pd) empty)) ss)
                      (add ((@add SP) (pb,pa) ((@add SP) (pc,pd) empty)) ss)).
      {
      assert (H : Equal ((@add SP) (pa,pb) ((@add SP) (pc,pd) empty))
                        ((@add SP) (pb,pa) ((@add SP) (pc,pd) empty))).
        {
        intro a; rewrite <- !elements_iff, !add_iff; intuition; left;
        [apply TCSets.eq_trans with (pa,pb)|
         apply TCSets.eq_trans with (pb,pa)]; auto; apply eq_pseudo_refl.
        }
      intro a; rewrite <- !elements_iff, !add_iff.
      split; intros [HE|HIn]; auto; left;
      [apply TCSets.eq_trans with ((@add SP)(pa,pb)((@add SP)(pc,pd) empty))|
       apply TCSets.eq_trans with ((@add SP)(pb,pa)((@add SP)(pc,pd) empty))];
      auto; apply TCSets.eq_sym; auto.
      }
    intros s Hs; rewrite (mem_m _ _ (TCSets.eq_refl s) H) in Hs.
    revert Hs; apply Haux with B A C D; trivial.
    apply CTcong_left_comm, HCong.
    }
  }

  {
  intros A B C D pa pb pc pd HA HB HC HD HCong Hpapb Hpcpd s Hs.
  cut (forall p1 p2 p3 p4,
         (@mem SP) (p1,p2) s && (@mem SP) (p3,p4) s = true ->
         Pos.le p1 p2 -> Pos.le p3 p4 ->
         CTCong (interp p1) (interp p2) (interp p3) (interp p4)).

    {
    intros Haux p1 p2.
    cut (forall p3 p4,
           (@mem SP) (p1,p2) s && (@mem SP) (p3,p4) s = true ->
           Pos.le p3 p4 ->
           CTCong (interp p1) (interp p2) (interp p3) (interp p4)).

      {
      intros Haux' p3 p4 Hmem; case_eq (Pos.leb p3 p4); intro Hp3p4;
      [apply Pos.leb_le in Hp3p4; apply Haux'; assumption|].
      apply Pos.leb_gt, Pos.lt_le_incl in Hp3p4.
      apply CTcong_right_comm, Haux'; trivial.
      assert (Heq : (@mem SP) (p4,p3) s = (@mem SP) (p3, p4) s)
        by (apply mem_m; [apply eq_pseudo_refl|apply Equal_refl]).
      rewrite Heq; assumption.
      }

      {
      intros p3 p4 Hmem Hp3p4; case_eq (Pos.leb p1 p2); intro Hp1p2;
      [apply Pos.leb_le in Hp1p2; apply Haux; assumption|].
      apply Pos.leb_gt, Pos.lt_le_incl in Hp1p2.
      apply CTcong_left_comm, Haux; trivial.
      assert (Heq : (@mem SP) (p2,p1) s = (@mem SP) (p1,p2) s)
        by (apply mem_m; [apply eq_pseudo_refl|apply Equal_refl]).
      rewrite Heq; assumption.
      }
    }

    {
    intros p1 p2 p3 p4 Hmem Hp1p2 Hp3p4.
    assert (HE : eq (p1,p2) (p3,p4) \/ ~ eq (p1,p2) (p3,p4))
      by (rewrite <- eqb_eq; case (eqb (p1,p2) (p3,p4)); intuition).
    elim HE; clear HE; intro Hp1p3;
    [apply eq_le2__eq2 in Hp1p3; trivial;
     destruct Hp1p3; subst; apply CTcong_refl|].
    apply mem_2, add_iff in Hs.
    rewrite andb_true_iff in Hmem.
    destruct Hmem as [Hmem1 Hmem2].
    elim Hs; intro HsE;
    [|apply HSS with s; [apply mem_1; assumption|];
     rewrite Hmem1; rewrite Hmem2; reflexivity].
    assert (HmemR : forall p q,
               (@mem SP) (p,q) ((@add SP) (pa, pb) ((@add SP) (pc, pd) empty)) =
               (@mem SP) (p,q) s)
      by (intros; apply mem_m; auto; apply TCSets.eq_refl).
    rewrite <- HmemR in Hmem1; rewrite <- HmemR in Hmem2.
    assert (HE : eq (pa,pb) (p1,p2) \/ ~ eq (pa,pb) (p1,p2))
      by (rewrite <- eqb_eq; case (eqb (pa,pb) (p1,p2)); intuition).
    clear HmemR; elim HE; clear HE; intro Hpap1.

      {
      apply eq_le2__eq2 in Hpap1; trivial.
      destruct Hpap1 as [Hpap1 Hpbp2].
      rewrite Hpap1, Hpbp2 in *.
      rewrite add_neq_b in Hmem2; trivial.
      apply mem_iff, singleton_1 in Hmem2.
      apply eq_le2__eq2 in Hmem2; trivial.
      destruct Hmem2 as [Hpcp3 Hpdp4].
      rewrite Hpcp3, Hpdp4 in *; rewrite HA, HB, HC, HD.
      assumption.
      }

      {
      rewrite add_neq_b in Hmem1; trivial.
      apply mem_iff, singleton_1 in Hmem1.
      apply eq_le2__eq2 in Hmem1; trivial.
      destruct Hmem1 as [Hpcp1 Hpdp2].
      rewrite Hpcp1, Hpdp2 in *.
      rewrite <- mem_iff, !add_iff in Hmem2.
      destruct Hmem2 as [Hmem2|[|]]; [|exfalso; apply Hp1p3; auto|];
      [|exfalso; apply ((@empty_iff SP) (p3,p4)); auto].
      apply eq_le2__eq2 in Hmem2; trivial.
      destruct Hmem2 as [Hpap3 Hpbp4].
      rewrite Hpap3, Hpbp4 in *; rewrite HA, HB, HC, HD.
      apply CTcong_sym, HCong.
      }
    }
  }
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

Definition interp (lvar : list (CONGpoint * positive)) (Default : CONGpoint) :
  positive -> CONGpoint :=
    fun p => list_assoc_inv CONGpoint positive positive_dec lvar p Default.

End Cong_refl.

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

Ltac build_numbered_points_list Tpoint :=
  let lvar := collect_points Tpoint in number Tpoint lvar.

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