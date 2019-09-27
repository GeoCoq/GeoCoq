Require Import Bool.
Require Import Morphisms.
Require Import NArith.
Require Import Recdef.
Require Import GeoCoq.Utils.sets.

Definition pick_line (s : (@elt SS)) (sp : (@TCSets.t SP)) :=
  (@exists_ SP) (fun p => ((@mem S) (fstpp p) s) && ((@mem S) (sndpp p) s)) sp.

Lemma proper_00 : forall (s : (@TCSets.t S)),
  Proper
  ((fun t1 t2 : t =>
    Pos.eq (fstpp t1) (fstpp t2) /\ Pos.eq (sndpp t1) (sndpp t2)) ==> Logic.eq)
  (fun p : (@elt SP) =>
   (@mem S) (fstpp p) s && (@mem S) (sndpp p) s).
Proof.
intros s x y Hxy.
destruct Hxy as [Hxyfst Hxysnd].
rewrite Hxyfst.
rewrite Hxysnd.
reflexivity.
Qed.

Lemma proper_0 :
  Proper ((@Equal S) ==> Logic.eq ==> Logic.eq) pick_line.
Proof.
intros x1 y1 HXY1.
intros x2 y2 HXY2.
unfold pick_line, exists_, exists_aux; rewrite HXY2.
induction (this y2); try intuition.
assert (HEqMem : forall e, (@mem S) e x1 = (@mem S) e y1)
  by (intro; apply mem_m; intuition).
assert (HEqAI : ((@mem S) (fstpp a) x1 && (@mem S) (sndpp a) x1) =
                ((@mem S) (fstpp a) y1 && (@mem S) (sndpp a) y1))
  by (rewrite HEqMem; rewrite HEqMem; intuition).
rewrite HEqAI.
induction ((@mem S) (fstpp a) y1 && (@mem S) (sndpp a) y1); intuition.
Qed.

Lemma proper_1 : forall s1 sp,
  Proper ((@Equal S) ==> Logic.eq)
  (fun s2 : (@elt SS) => pick_line ((@inter S) s1 s2) sp).
Proof.
intros s1 sp.
intros x y HXY.
assert (HEqI : (@Equal S) ((@inter S) s1 x) ((@inter S) s1 y))
  by (apply inter_equal_2; assumption).
apply proper_0; auto.
Qed.

Definition exists_witness (f : (@elt SS) -> bool) s : option (@elt SS) :=
  (@choose SS) ((@filter SS) f s).

Lemma exists_witness_ok : forall e f s,
  Proper ((@Equal S) ==> Logic.eq) f ->
  exists_witness f s = Some e -> (@In SS) e s.
Proof.
intros e f s HP H; unfold exists_witness in H.
apply mem_2; apply choose_mem_1 in H.
rewrite filter_mem in H; try assumption.
apply andb_true_iff in H; intuition.
Qed.

Definition pick_lines_aux (s1 : (@elt SS))
                          (ss : (@TCSets.t SS))
                          (sp : (@TCSets.t SP))
                          : (option ((@elt SS) * (@elt SS))) :=
  match ((exists_witness (fun s2 => let i := (@inter S) s1 s2 in
                                    pick_line i sp)) ss) with
    | None    => None
    | Some s2 => Some(s1,s2)
  end.

Definition pick_lines (ss : (@TCSets.t SS)) (sp : (@TCSets.t SP))
                      : (option ((@elt SS) * (@elt SS))) :=
  match (exists_witness (fun s =>
                           match (pick_lines_aux s ((@remove SS) s ss) sp) with
                             | None => false
                             | _    => true
                           end) ss) with
    | None    => None
    | Some s1 => pick_lines_aux s1 ((@remove SS) s1 ss) sp
  end.

Definition eqop (p1 p2 : option (@elt SS)) :=
  match p1,p2 with
    | None   , None    => True
    | Some s1, Some s2 => True
    | _      , _       => False
  end.

Lemma proper_2 : forall (f1 f2 : (@elt SS) -> bool) (s1 s2 : (@TCSets.t SS)),
  Proper ((@Equal S) ==> Logic.eq) f1 ->
  Proper ((@Equal S) ==> Logic.eq) f2 ->
  (forall x, f1 x = f2 x) ->
  (@Equal SS) s1 s2 ->
  eqop (exists_witness f1 s1) (exists_witness f2 s2).
Proof.
intros f1 f2 s1 s2  H1 H2 H3 H4; unfold eqop; unfold exists_witness in *.
assert (Equal (filter f1 s1) (filter f2 s2))
  by (apply filter_ext; assumption).
case_eq (choose (filter f1 s1));
case_eq (choose (filter f2 s2)); try solve [intuition];
[intros HCN e HCS|intros e HCS HCN]; apply choose_spec1 in HCS;
apply choose_spec2 in HCN; unfold Equal, Equal_aux in H;
[rewrite H in HCS|rewrite <- H in HCS]; apply empty_is_empty_1 in HCN;
unfold Equal, Equal_aux in HCN; rewrite HCN in HCS;
apply empty_iff with e; unfold In; apply HCS.
Qed.

Definition eqopp (p1 p2 : option ((@elt SS) * (@elt SS))) :=
  match p1,p2 with
    | None, None => True
    | Some s1, Some s2 => True
    | _, _ => False
  end.

Lemma proper_3 :
  Proper ((@Equal S) ==> (@Equal SS) ==> Logic.eq ==> eqopp) pick_lines_aux.
Proof.
intros x1 y1 HXY1.
intros x2 y2 HXY2.
intros x3 y3 HXY3.
unfold pick_lines_aux.
rewrite HXY3.
assert (eqop (exists_witness (fun s2 => pick_line (inter x1 s2) y3) x2)
             (exists_witness (fun s2 => pick_line (inter y1 s2) y3) y2)).
  {
  apply proper_2; auto; try apply proper_1.
  intro; apply proper_0; try reflexivity.
  apply inter_equal_1; assumption.
  }

case_eq (exists_witness
           (fun s2 : (@elt SS) => pick_line ((@inter S) y1 s2) y3) y2);
case_eq (exists_witness
           (fun s2 : (@elt SS) => pick_line ((@inter S) x1 s2) y3) x2);
try solve [simpl; intuition]; [intros HCN e HCS|intros e HCS HCN];
simpl in *; rewrite HCS in H; rewrite HCN in H; simpl in *; intuition.
Qed.

Lemma pick_lines_ok_1 : forall s1 s2 ss sp,
  pick_lines ss sp = Some (s1,s2) ->
  In s1 ss.
Proof.
intros s1 s2 ss sp H.
unfold pick_lines in H.
case_eq (exists_witness
           (fun s : (@elt SS) =>
              match pick_lines_aux s ((@remove SS) s ss) sp with
                | Some _ => true | None => false
              end) ss);
[intros e1 HEW1; rewrite HEW1 in H|intro HEW; rewrite HEW in H; discriminate].
unfold pick_lines_aux in H.
case_eq (exists_witness
           (fun s2 : (@elt SS) =>
              pick_line ((@inter S) e1 s2) sp) ((@remove SS) e1 ss));
[intros e2 HEW2; rewrite HEW2 in H|intro HEW2; rewrite HEW2 in H; discriminate].
assert (HEq1 : e1 = s1) by (injection H; intros; assumption).
assert (HEq2 : e2 = s2) by (injection H; intros; assumption).
rewrite HEq1 in *; rewrite HEq2 in *.
apply exists_witness_ok with
    (fun s : (@elt SS) => match pick_lines_aux s ((@remove SS) s ss) sp with
                         | Some _ => true | None => false
                       end); [|assumption].
intros x y HXY.
assert ((@Equal SS) ((@remove SS) x ss) ((@remove SS) y ss))
  by (apply remove_m; [apply HXY|apply Equal_refl]).
assert (E' : eqopp (pick_lines_aux x ((@remove SS) x ss) sp)
                   (pick_lines_aux y ((@remove SS) y ss) sp))
  by (apply proper_3; auto).
case_eq (pick_lines_aux x ((@remove SS) x ss) sp); [intros p Hp|intro HF];
case_eq (pick_lines_aux y ((@remove SS) y ss) sp); auto; [intro HF|intros p Hp];
rewrite Hp, HF in E'; unfold eqopp in E'; intuition.
Qed.

Lemma pick_lines_ok_2 : forall s1 s2 ss sp,
  pick_lines ss sp = Some (s1,s2) ->
  (@In SS) s2 ((@remove SS) s1 ss).
Proof.
intros s1 s2 ss sp H.
unfold pick_lines in H.
case_eq (exists_witness (fun s : (@elt SS) =>
                           match pick_lines_aux s ((@remove SS) s ss) sp with
                             | Some _ => true | None => false
                           end) ss);
[intros e1 HEW1; rewrite HEW1 in H|intro HEW; rewrite HEW in H; discriminate].
unfold pick_lines_aux in H.
case_eq (exists_witness (fun s2 : (@elt SS) => pick_line ((@inter S) e1 s2) sp)
                        ((@remove SS) e1 ss));
[intros e2 HEW2; rewrite HEW2 in H|intro HEW2; rewrite HEW2 in H; discriminate].
assert (HEq1 : e1 = s1) by (injection H; intros; assumption).
assert (HEq2 : e2 = s2) by (injection H; intros; assumption).
rewrite HEq1 in *; rewrite HEq2 in *.
apply exists_witness_ok with
    (fun s2 : (@elt SS) => pick_line ((@inter S) s1 s2) sp);
[intros x y HXY; apply proper_1; assumption|assumption].
Qed.

Function identify_lines (ss : (@TCSets.t SS)) (sp : (@TCSets.t SP))
         {measure cardinal ss} : (@TCSets.t SS) :=
  let lines := pick_lines ss sp in
    match lines with
      | None         => ss
      | Some (s1,s2) =>
         let auxsetofsets := (@remove SS) s2 ((@remove SS) s1 ss) in
         let auxset := (@union S) s1 s2 in
         let newss := (@add SS) auxset auxsetofsets in
         identify_lines newss sp
    end.
Proof.
intros.
assert (Datatypes.S(cardinal (remove s1 ss)) = cardinal ss)
  by (apply remove_cardinal_1; apply pick_lines_ok_1 with s2 sp; assumption).
assert (Datatypes.S(Datatypes.S(cardinal (remove s2 (remove s1 ss)))) =
        Datatypes.S(cardinal (remove s1 ss))).
  {
  apply eq_S; apply remove_cardinal_1;
  apply pick_lines_ok_2 with sp; assumption.
  }
assert (HR1 : Datatypes.S(Datatypes.S(cardinal (remove s2 (remove s1 ss)))) =
              cardinal ss)
  by (transitivity (Datatypes.S(cardinal (remove s1 ss))); assumption).
elim ((@In_dec SS) (union s1 s2) (remove s2 (remove s1 ss))); intro HDec.

  {
  assert (HR2 : cardinal ((@add SS) (union s1 s2) (remove s2 (remove s1 ss))) =
                cardinal (remove s2 (remove s1 ss)))
    by (apply add_cardinal_1; assumption).
  rewrite HR2, <- HR1; apply le_S, le_n.
  }

  {
  assert (HR2 : cardinal ((@add SS) (union s1 s2) (remove s2 (remove s1 ss))) =
                Datatypes.S(cardinal (remove s2 (remove s1 ss))))
    by (apply add_cardinal_2; assumption).
  rewrite HR2, <- HR1; apply le_n.
  }
Defined.

Definition test_col ss sp p1 p2 p3 : bool :=
  let newss := identify_lines ss sp  in
    (@exists_ SS) (fun s => mem p1 s && mem p2 s && mem p3 s) newss.

Section Col_refl.

Context `{CT:Col_theory}.

Lemma CTcol_permutation_5 : forall A B C : COLTpoint,
  CTCol A B C -> CTCol A C B.
Proof.
apply CTcol_permutation_2.
Qed.

Lemma CTcol_permutation_2 : forall A B C : COLTpoint,
  CTCol A B C -> CTCol C A B.
Proof.
intros.
apply CTcol_permutation_1.
apply CTcol_permutation_1.
assumption.
Qed.

Lemma CTcol_permutation_3 : forall A B C : COLTpoint,
  CTCol A B C -> CTCol C B A.
Proof.
intros.
apply CTcol_permutation_5.
apply CTcol_permutation_2.
assumption.
Qed.

Lemma CTcol_permutation_4 : forall A B C : COLTpoint,
  CTCol A B C -> CTCol B A C.
Proof.
intros.
apply CTcol_permutation_5.
apply CTcol_permutation_1.
assumption.
Qed.

Lemma CTcol_trivial_1 : forall A B : COLTpoint, CTCol A A B.
Proof.
apply CTcol_trivial.
Qed.

Lemma CTcol_trivial_2 : forall A B : COLTpoint, CTCol A B B.
Proof.
intros.
apply CTcol_permutation_2.
apply CTcol_trivial_1.
Qed.

Definition ss_ok (ss : (@TCSets.t SS)) (interp: positive -> COLTpoint) :=
  forall s, (@mem SS) s ss = true ->
  forall p1 p2 p3, mem p1 s && mem p2 s && mem p3 s = true ->
    CTCol (interp p1) (interp p2) (interp p3).

Definition sp_ok (sp : (@TCSets.t SP)) (interp: positive -> COLTpoint) :=
  forall p, mem p sp = true -> interp (fstpp p) <> interp (sndpp p).

Lemma identify_lines_ok : forall ss sp interp,
  ss_ok ss interp -> sp_ok sp interp ->
  ss_ok (identify_lines ss sp) interp.
Proof.
intros ss sp interp HSS HSP.
apply (let P interp ss sp newss :=
       ss_ok ss interp -> sp_ok sp interp -> ss_ok newss interp in
         identify_lines_ind (P interp)); try assumption; [intros; assumption|].
clear HSS; clear HSP; clear ss; clear sp.
intros ss sp suitablepairofsets s1 s2 Hs1s2 auxsetofsets auxset newss H HSS HSP.
assert (Hs1 := Hs1s2); assert (Hs2 := Hs1s2).
apply pick_lines_ok_1 in Hs1; apply pick_lines_ok_2 in Hs2.
apply remove_3 in Hs2.
apply H; try assumption; clear H.
intros s Hmem p1 p2 p3 Hmemp.
do 2 (rewrite andb_true_iff in Hmemp).
destruct Hmemp as [[Hmemp1 Hmemp2] Hmemp3].
unfold newss in Hmem; clear newss.
assert (HEq : Equal auxset s \/ ~ Equal auxset s)
  by (rewrite <- equal_Equal; elim (equal auxset s); auto).
destruct HEq as [HEq|HEq];
[|rewrite add_neq_b in Hmem; try assumption;
 apply HSS with s; [|do 2 (rewrite andb_true_iff); repeat split; assumption];
 unfold auxsetofsets in *; apply mem_2 in Hmem;
 do 2 (apply remove_3 in Hmem); apply mem_1; assumption].
rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p1) _ _ HEq) in Hmemp1.
rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p2) _ _ HEq) in Hmemp2.
rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p3) _ _ HEq) in Hmemp3.
clear HEq; clear Hmem; clear s.
unfold suitablepairofsets in Hs1s2; clear suitablepairofsets.
unfold pick_lines in Hs1s2.
case_eq (exists_witness
           (fun s : elt =>
              match pick_lines_aux s (remove s ss) sp with
                | Some _ => true
                | None   => false
              end) ss); [|intro HEW; rewrite HEW in *; discriminate].
intros e1 HEW; rewrite HEW in *; clear HEW.
unfold pick_lines_aux in *.
case_eq (exists_witness
           (fun s2 : elt => pick_line (inter e1 s2) sp)
           (remove e1 ss)); try (intro HEW; rewrite HEW in *; discriminate).
intros e2 HEW; rewrite HEW in *.
injection Hs1s2; intros He2s2 He1s1.
rewrite He2s2 in *; rewrite He1s1 in *.
clear He2s2; clear He1s1; clear Hs1s2; clear e2; clear e1.
case_eq (pick_line (inter s1 s2) sp);
[|intro HEW2; unfold exists_witness in *; apply choose_spec1 in HEW;
 apply filter_2 in HEW; try apply proper_1;
 rewrite HEW2 in *; discriminate].
clear HEW; intro HEW; unfold pick_line in HEW.
apply exists_mem_4 in HEW; try (apply proper_00).
destruct HEW as [x [HmemSP HmemS]].
rewrite andb_true_iff in HmemS; destruct HmemS as [Hmemfsts Hmemsnds].
apply HSP in HmemSP.
apply mem_2 in Hmemfsts; apply mem_2 in Hmemsnds.
apply inter_spec in Hmemfsts; destruct Hmemfsts as [Hfss1 Hfss2].
apply inter_spec in Hmemsnds; destruct Hmemsnds as [Hsss1 Hsss2].
unfold auxset in *.
apply mem_2, union_1 in Hmemp1.
apply mem_2, union_1 in Hmemp2.
apply mem_2, union_1 in Hmemp3.
apply CTcol3 with (interp (fstpp(x))) (interp (sndpp(x))); try assumption.

  {
  elim (Hmemp1); intro HInp1; [apply HSS with s1|apply HSS with s2];
  try (apply mem_1; assumption);
  do 2 (rewrite andb_true_iff);
  repeat split; apply mem_1; assumption.
  }

  {
  elim (Hmemp2); intro HInp2; [apply HSS with s1|apply HSS with s2];
  try (apply mem_1; assumption);
  do 2 (rewrite andb_true_iff);
  repeat split; apply mem_1; assumption.
  }

  {
  elim (Hmemp3); intro HInp3; [apply HSS with s1|apply HSS with s2];
  try (apply mem_1; assumption);
  do 2 (rewrite andb_true_iff);
  repeat split; apply mem_1; assumption.
  }
Qed.

Lemma test_col_ok : forall ss sp interp p1 p2 p3,
  ss_ok ss interp -> sp_ok sp interp ->
  test_col ss sp p1 p2 p3 = true ->
  CTCol (interp p1) (interp p2) (interp p3).
Proof.
intros ss sp interp p1 p2 p3 HSS HSP HTC.
unfold test_col in *.
assert (HSS2 : ss_ok (identify_lines ss sp) interp)
  by (apply identify_lines_ok; assumption).
unfold ss_ok in HSS2.
apply exists_2 in HTC;
[destruct HTC as [s [HIn Hmem]];
 apply HSS2 with s; [apply mem_1; assumption|assumption]|].
intros x y Hxy.
assert (HmemEq : forall p, mem p x = mem p y)
  by (intro; apply mem_m; auto; apply TCSets.eq_refl).
do 3 (rewrite HmemEq); reflexivity.
Qed.

Lemma ss_ok_empty : forall interp,
  ss_ok empty interp.
Proof.
intros interp ss Hmem1 p1 p2 p3 Hmem2; rewrite empty_b in Hmem1; discriminate.
Qed.

Lemma sp_ok_empty : forall interp,
  sp_ok empty interp.
Proof. intros; intros p Hp; rewrite empty_b in Hp; discriminate. Qed.

Lemma collect_cols :
  forall (A B C : COLTpoint) (HCol : CTCol A B C),
  forall pa pb pc ss (interp :  positive -> COLTpoint),
  interp pa = A ->
  interp pb = B ->
  interp pc = C ->
  ss_ok ss interp ->
  ss_ok ((@add SS) ((@add S) pa ((@add S) pb ((@add S) pc empty))) ss) interp.
Proof.
intros A B C HCol pa pb pc ss interp HA HB HC HSS.
intros s Hs p1 p2 p3 Hmem.
apply mem_2, add_iff in Hs.
do 2 (rewrite andb_true_iff in Hmem).
destruct Hmem as [[Hmem1 Hmem2] Hmem3].
elim Hs; intro HsE;
[|apply HSS with s; [apply mem_1; assumption|];
 rewrite Hmem1; rewrite Hmem2; rewrite Hmem3; reflexivity].
assert (HmemR : forall p,
           mem p ((@add S) pa ((@add S) pb ((@add S) pc empty))) = mem p s)
  by (intros; apply mem_m; auto; apply TCSets.eq_refl).
rewrite <- HmemR in Hmem1.
rewrite <- HmemR in Hmem2.
rewrite <- HmemR in Hmem3.
clear HmemR.
elim (Pos.eq_dec pa p1); intro Hpap1.

  {
  rewrite Hpap1 in *; rewrite HA.
  elim (Pos.eq_dec p1 p2); intro Hp1p2.

    {
    rewrite Hp1p2 in *; rewrite HA.
    apply CTcol_trivial_1.
    }

    {
    rewrite add_neq_b in Hmem2; auto.
    elim (Pos.eq_dec pb p2); intro Hpbp2.

      {
      rewrite Hpbp2 in *; rewrite HB.
      elim (Pos.eq_dec p3 p1); intro Hp3p1;
      elim (Pos.eq_dec p3 p2); intro Hp3p2.

        {
        rewrite Hp3p2; rewrite HB; apply CTcol_trivial_2.
        }

        {
        rewrite Hp3p1; rewrite HA; apply CTcol_permutation_1.
        apply CTcol_trivial_1.
        }

        {
        rewrite Hp3p2; rewrite HB; apply CTcol_trivial_2.
        }

        {
        do 2 (rewrite add_neq_b in Hmem3); auto.
        rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p3)
                            _ _ ((@singleton_equal_add S) pc)) in Hmem3.
        apply mem_iff, singleton_1 in Hmem3.
        rewrite <- Hmem3; rewrite HC; assumption.
        }
      }

      {
      rewrite add_neq_b in Hmem2; auto.
      rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p2)
                             _ _ ((@singleton_equal_add S) pc)) in Hmem2.
      apply mem_iff, singleton_1 in Hmem2.
      rewrite <- Hmem2 in *; rewrite HC.
      elim (Pos.eq_dec p3 p1); intro Hp3p1;
      elim (Pos.eq_dec p3 p2); intro Hp3p2.

        {
        rewrite Hp3p2 in *; rewrite Hmem2 in *; rewrite HC.
        apply CTcol_trivial_2.
        }

        {
        rewrite Hp3p1 in *; rewrite HA; apply CTcol_permutation_1.
        apply CTcol_trivial_1.
        }

        {
        rewrite Hp3p2 in *; rewrite Hmem2 in *; rewrite HC.
        apply CTcol_trivial_2.
        }

        {
        rewrite add_neq_b in Hmem3; auto.
        elim (Pos.eq_dec p3 pb); intro Hp3pb;
        [rewrite Hp3pb in *; rewrite HB;
         apply CTcol_permutation_5; assumption|].
        rewrite add_neq_b in Hmem3; auto.
        rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p3)
                               _ _ ((@singleton_equal_add S) pc)) in Hmem3.
        apply mem_iff, singleton_1 in Hmem3.
        rewrite <- Hmem3, HC; apply CTcol_trivial_2.
        }
      }
    }
  }

  {
  rewrite add_neq_b in Hmem1; auto.
  elim (Pos.eq_dec p1 pb); intro Hp1pb.

    {
    rewrite Hp1pb in *; rewrite HB.
    elim (Pos.eq_dec pa p2); intro Hpap2.

      {
      rewrite Hpap2 in *; rewrite HA.
      elim (Pos.eq_dec p3 p2); intro Hp3p2;
      elim (Pos.eq_dec p3 pb); intro Hp3pb.

        {
        rewrite Hp3pb; rewrite HB; apply CTcol_permutation_1.
        apply CTcol_trivial_1.
        }

        {
        rewrite Hp3p2; rewrite HA; apply CTcol_trivial_2.
        }

        {
        rewrite Hp3pb; rewrite HB; apply CTcol_permutation_1.
        apply CTcol_trivial_1.
        }

        {
        do 2 (rewrite add_neq_b in Hmem3; auto).
        rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p3)
                            _ _ ((@singleton_equal_add S) pc)) in Hmem3.
        apply mem_iff, singleton_1 in Hmem3.
        rewrite <- Hmem3; rewrite HC; apply CTcol_permutation_4; assumption.
        }
      }

      {
      rewrite add_neq_b in Hmem2; auto.
      elim (Pos.eq_dec p2 pb); intro Hp2pb.

        {
        rewrite Hp2pb; rewrite HB; apply CTcol_trivial_1.
        }

        {
        rewrite add_neq_b in Hmem2; auto.
        rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p2)
                               _ _ ((@singleton_equal_add S) pc)) in Hmem2.
        apply mem_iff, singleton_1 in Hmem2.
        rewrite <- Hmem2 in *; rewrite HC.
        elim (Pos.eq_dec p3 p1); intro Hp3p1;
        elim (Pos.eq_dec p3 p2); intro Hp3p2.

          {
          rewrite Hp3p2 in *; rewrite Hmem2 in *; rewrite HC.
          apply CTcol_trivial_2.
          }

          {
          rewrite Hp3p1 in *; rewrite Hp1pb; rewrite HB.
          apply CTcol_permutation_1; apply CTcol_trivial_1.
          }

          {
          rewrite Hp3p2 in *; rewrite Hmem2 in *; rewrite HC.
          apply CTcol_trivial_2.
          }

          {
          elim (Pos.eq_dec p3 pa); intro Hp3pa.

            {
            rewrite Hp3pa; rewrite HA; apply CTcol_permutation_1; assumption.
            }

            {
            rewrite add_neq_b in Hmem3; auto.
            elim (Pos.eq_dec p3 pb); intro Hp3pb.

              {
              rewrite Hp3pb in *; rewrite HB; apply CTcol_permutation_5.
              apply CTcol_trivial_1.
              }

              {
              rewrite add_neq_b in Hmem3; auto.
              rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p3)
                                     _ _ ((@singleton_equal_add S) pc))
                in Hmem3.
              apply mem_iff, singleton_1 in Hmem3.
              rewrite Hmem3 in *; contradiction.
              }
            }
          }
        }
      }
    }

    {
    rewrite add_neq_b in Hmem1; auto.
    rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p1)
                           _ _ ((@singleton_equal_add S) pc)) in Hmem1.
    apply mem_iff, singleton_1 in Hmem1.
    rewrite <- Hmem1 in *; rewrite HC.
    elim (Pos.eq_dec pa p2); intro Hpap2.

      {
      rewrite Hpap2 in *; rewrite HA.
      elim (Pos.eq_dec p3 p2); intro Hp3p2;
      elim (Pos.eq_dec p3 pb); intro Hp3pb.

        {
        rewrite Hp3pb; rewrite HB; apply CTcol_permutation_2; assumption.
        }

        {
        rewrite Hp3p2; rewrite HA; apply CTcol_trivial_2.
        }

        {
        rewrite Hp3pb; rewrite HB; apply CTcol_permutation_2; assumption.
        }

        {
        do 2 (rewrite add_neq_b in Hmem3; auto).
        rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p3)
                               _ _ ((@singleton_equal_add S) pc)) in Hmem3.
        apply mem_iff, singleton_1 in Hmem3.
        rewrite <- Hmem3 in *; rewrite HC.
        apply CTcol_permutation_1; apply CTcol_trivial_1.
        }
      }

      {
      rewrite add_neq_b in Hmem2; auto.
      elim (Pos.eq_dec p2 pb); intro Hp2pb.

        {
        rewrite Hp2pb; rewrite HB.
        elim (Pos.eq_dec p3 pa); intro Hp3pa;
        elim (Pos.eq_dec p3 pb); intro Hp3pb.

          {
          rewrite Hp3pa; rewrite HA; apply CTcol_permutation_3; assumption.
          }

          {
          rewrite Hp3pa; rewrite HA; apply CTcol_permutation_3; assumption.
          }

          {
          rewrite Hp3pb; rewrite HB; apply CTcol_trivial_2.
          }

          {
          do 2 (rewrite add_neq_b in Hmem3; auto).
          rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p3)
                                 _ _ ((@singleton_equal_add S) pc)) in Hmem3.
          apply mem_iff, singleton_1 in Hmem3.
          rewrite <- Hmem3 in *; rewrite HC.
          apply CTcol_permutation_1; apply CTcol_trivial_1.
          }
        }

        {
        rewrite add_neq_b in Hmem2; auto.
        rewrite <- ((@mem_m S) _ _ (TCSets.eq_refl p2)
                               _ _ ((@singleton_equal_add S) pc)) in Hmem2.
        apply mem_iff, singleton_1 in Hmem2.
          rewrite <- Hmem2 in *; rewrite HC; apply CTcol_trivial_1.
        }
      }
    }
  }
Qed.

Lemma collect_diffs :
  forall (A B : COLTpoint) (H : A <> B),
  forall pa pb sp (interp :  positive -> COLTpoint),
  interp pa = A ->
  interp pb = B ->
  sp_ok sp interp -> sp_ok ((@add SP) (pa, pb) sp) interp.
Proof.
intros A B HDiff pa pb sp interp HA HB HSP p Hp.
apply mem_2, add_iff in Hp.
elim Hp; intro HpE; [|apply HSP, mem_1; assumption].
destruct HpE as [HEq1 HEq2].
destruct p as [fstp sndp].
simpl in *.
elim (Pos.min_spec pa pb); intro Hmin1;
elim (Pos.min_spec fstp sndp); intro Hmin2;
destruct Hmin1 as [Hpapb1 Hmin1]; destruct Hmin2 as [Hfpsp1 Hmin2];
elim (Pos.max_spec pa pb); intro Hmax1;
elim (Pos.max_spec fstp sndp); intro Hmax2;
destruct Hmax1 as [Hpapb2 Hmax1]; destruct Hmax2 as [Hfpsp2 Hmax2].

  {
  rewrite Hmin1 in *; rewrite Hmin2 in *; rewrite Hmax1 in *;rewrite Hmax2 in *.
  rewrite <- HEq1; rewrite <- HEq2; rewrite HA in *; rewrite HB in *.
  assumption.
  }

  {
  rewrite <- Pos.ltb_lt in Hfpsp1; rewrite Pos.ltb_antisym in Hfpsp1.
  rewrite negb_true_iff in Hfpsp1; rewrite Pos.leb_nle in Hfpsp1; contradiction.
  }

  {
  rewrite <- Pos.ltb_lt in Hpapb1; rewrite Pos.ltb_antisym in Hpapb1.
  rewrite negb_true_iff in Hpapb1; rewrite Pos.leb_nle in Hpapb1; contradiction.
  }

  {
  rewrite <- Pos.ltb_lt in Hfpsp1; rewrite Pos.ltb_antisym in Hfpsp1.
  rewrite negb_true_iff in Hfpsp1; rewrite Pos.leb_nle in Hfpsp1; contradiction.
  }

  {
  rewrite <- Pos.ltb_lt in Hfpsp2; rewrite Pos.ltb_antisym in Hfpsp2.
  rewrite negb_true_iff in Hfpsp2; rewrite Pos.leb_nle in Hfpsp2; contradiction.
  }

  {
  rewrite Hmin1 in *; rewrite Hmin2 in *; rewrite Hmax1 in *;rewrite Hmax2 in *.
  rewrite <- HEq1; rewrite <- HEq2; rewrite HA in *; rewrite HB in *.
  assumption.
  }

  {
  rewrite <- Pos.ltb_lt in Hfpsp2; rewrite Pos.ltb_antisym in Hfpsp2.
  rewrite negb_true_iff in Hfpsp2; rewrite Pos.leb_nle in Hfpsp2; contradiction.
  }

  {
  rewrite <- Pos.ltb_lt in Hpapb1; rewrite Pos.ltb_antisym in Hpapb1.
  rewrite negb_true_iff in Hpapb1; rewrite Pos.leb_nle in Hpapb1; contradiction.
  }

  {
  rewrite <- Pos.ltb_lt in Hpapb2; rewrite Pos.ltb_antisym in Hpapb2.
  rewrite negb_true_iff in Hpapb2; rewrite Pos.leb_nle in Hpapb2; contradiction.
  }

  {
  rewrite <- Pos.ltb_lt in Hpapb2; rewrite Pos.ltb_antisym in Hpapb2.
  rewrite negb_true_iff in Hpapb2; rewrite Pos.leb_nle in Hpapb2; contradiction.
  }

  {
  rewrite Hmin1 in *; rewrite Hmin2 in *; rewrite Hmax1 in *;rewrite Hmax2 in *.
  rewrite <- HEq1; rewrite <- HEq2; rewrite HA in *; rewrite HB in *; intuition.
  }

  {
  rewrite <- Pos.ltb_lt in Hfpsp1; rewrite Pos.ltb_antisym in Hfpsp1.
  rewrite negb_true_iff in Hfpsp1; rewrite Pos.leb_nle in Hfpsp1; contradiction.
  }

  {
  rewrite <- Pos.ltb_lt in Hpapb2; rewrite Pos.ltb_antisym in Hpapb2.
  rewrite negb_true_iff in Hpapb2; rewrite Pos.leb_nle in Hpapb2; contradiction.
  }

  {
  rewrite <- Pos.ltb_lt in Hpapb2; rewrite Pos.ltb_antisym in Hpapb2.
  rewrite negb_true_iff in Hpapb2; rewrite Pos.leb_nle in Hpapb2; contradiction.
  }

  {
  rewrite <- Pos.ltb_lt in Hfpsp2; rewrite Pos.ltb_antisym in Hfpsp2.
  rewrite negb_true_iff in Hfpsp2; rewrite Pos.leb_nle in Hfpsp2; contradiction.
  }

  {
  rewrite Hmin1 in *; rewrite Hmin2 in *; rewrite Hmax1 in *;rewrite Hmax2 in *.
  rewrite <- HEq1; rewrite <- HEq2; rewrite HA in *; rewrite HB in *; intuition.
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

Definition interp (lvar : list (COLTpoint * positive)) (Default : COLTpoint) : positive -> COLTpoint := 
  fun p => list_assoc_inv COLTpoint positive positive_dec lvar p Default.

(*
Definition eq_tagged (lvar : list (COLTpoint * positive)) := lvar = lvar.

Lemma eq_eq_tagged : forall lvar, lvar = lvar -> eq_tagged lvar.
Proof.
trivial.
Qed.

Definition partition_ss e ss :=
  SS.partition (fun s => S.mem e s) ss.

Definition fst_ss (pair : SS.t * SS.t) :=
 match pair with
    |(a,b) => a
  end.

Definition snd_ss (pair : SS.t * SS.t) :=
 match pair with
    |(a,b) => b
  end.

Definition subst_in_set p1 p2 s := S.add p1 (S.remove p2 s).

Definition subst_in_ss_aux p1 p2 := (fun s ss => SS.add (subst_in_set p1 p2 s) ss).

Definition subst_in_ss p1 p2 ss :=
  let pair := partition_ss p2 ss in
  let fss := fst_ss(pair) in
  let sss := snd_ss(pair) in
  let newfss := SS.fold (subst_in_ss_aux p1 p2) fss SS.empty in
  SS.union newfss sss.

Lemma proper_4 : forall p, Proper (S.Equal ==> eq) (fun s : SS.elt => S.mem p s).
Proof.
intros p x y Hxy.
apply SWP.Dec.F.mem_m; intuition.
Qed.

Lemma proper_5 : forall p, Proper (S.Equal ==> eq) (fun s : SS.elt => negb (S.mem p s)).
Proof.
intros p x y Hxy.
f_equal.
apply SWP.Dec.F.mem_m; intuition.
Qed.

Lemma subst_ss_ok :
  forall (A B : COLTpoint) (H : A = B) pa pb ss (interp :  positive -> COLTpoint),
  interp pa = A ->
  interp pb = B ->
  ss_ok ss interp -> ss_ok (subst_in_ss pa pb ss) interp.
Proof.
intros A B H pa pb ss interp HA HB HSS.
unfold subst_in_ss.
unfold ss_ok.
intros s Hs.
intros p1 p2 p3 Hmem.
apply SSWEqP.MP.Dec.F.mem_2 in Hs.
rewrite SS.union_spec in Hs.
elim Hs; intro HIn; clear Hs.

  assert (HSSF : ss_ok (fst_ss (partition_ss pb ss)) interp).

    clear Hmem; clear p1; clear p2; clear p3.
    intros s' Hs'.
    intros.
    apply SSWEqP.MP.Dec.F.mem_2 in Hs'.
    unfold partition in Hs'.
    apply SS.partition_spec1 in Hs'; try apply proper_4.
    apply SSWEqP.MP.Dec.F.filter_1 in Hs'; try apply proper_4.
    unfold ss_ok in HSS.
    apply HSS with s'; try assumption.
    apply SSWEqP.MP.Dec.F.mem_1; assumption.

  assert (HSSF' : ss_ok (SS.fold (subst_in_ss_aux pa pb) (fst_ss (partition_ss pb ss)) SS.empty) interp).

    apply SSWEqP.MP.fold_rec_nodep; try apply ss_ok_empty.
    intros x a HIn1 HSSa.
    clear Hmem; clear p1; clear p2; clear p3.
    intros s' Hs'.
    intros p1 p2 p3 Hmem.
    unfold subst_in_ss_aux in *.
    apply SSWEqP.MP.Dec.F.mem_2 in Hs'.
    rewrite SSWEqP.MP.Dec.F.add_iff in Hs'.
    elim Hs'; intro HIn2; clear Hs'.

      unfold subst_in_set in HIn2.
      clear HIn; clear s; assert (HEq := HIn2); clear HIn2; assert (HIn := HIn1); clear HIn1.
      elim (Pos.eq_dec pb p1); intro Hp1; elim (Pos.eq_dec pb p2); intro Hp2; elim (Pos.eq_dec pb p3); intro Hp3.

        subst.
        apply CTcol_trivial_1.

        subst.
        apply CTcol_trivial_1.

        subst.
        apply CTcol_permutation_4; apply CTcol_trivial_2.

        subst.
        do 2 (rewrite andb_true_iff in Hmem).
        destruct Hmem as [[Hmem1' Hmem2'] Hmem3'].
        assert (Hmem1 : S.mem p1 x = true).

          unfold partition in HIn.
          apply SS.partition_spec1 in HIn; try apply proper_4.
          apply SSWEqP.MP.Dec.F.filter_2 in HIn; try assumption; apply proper_4.

        elim (Pos.eq_dec pa p2); intro Hpap2.

          subst; rewrite HB; apply CTcol_trivial_1.

          assert (Hmem2 : S.mem p2 x = true).

            rewrite <- HEq in Hmem2'.
            rewrite SWP.Dec.F.add_neq_b in Hmem2'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem2'; assumption.

          elim (Pos.eq_dec pa p3); intro Hpap3.

            subst; rewrite HB; apply CTcol_permutation_4; apply CTcol_trivial_2.

            assert (Hmem3 : S.mem p3 x = true).

              rewrite <- HEq in Hmem3'.
              rewrite SWP.Dec.F.add_neq_b in Hmem3'; try assumption.
              rewrite SWP.Dec.F.remove_neq_b in Hmem3'; assumption.

            unfold ss_ok in HSSF.
            apply HSSF with x.

              apply SSWEqP.MP.Dec.F.mem_1; assumption.

              do 2 (rewrite andb_true_iff); repeat split; assumption.

        subst.
        apply CTcol_trivial_2.

        subst.
        do 2 (rewrite andb_true_iff in Hmem).
        destruct Hmem as [[Hmem1' Hmem2'] Hmem3'].
        assert (Hmem2 : S.mem p2 x = true).

          unfold partition in HIn.
          apply SS.partition_spec1 in HIn; try apply proper_4.
          apply SSWEqP.MP.Dec.F.filter_2 in HIn; try assumption; apply proper_4.

        elim (Pos.eq_dec pa p1); intro Hpap1.

          subst; rewrite HB; apply CTcol_trivial_1.

          assert (Hmem1 : S.mem p1 x = true).

            rewrite <- HEq in Hmem1'.
            rewrite SWP.Dec.F.add_neq_b in Hmem1'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem1'; assumption.

          elim (Pos.eq_dec pa p3); intro Hpap3.

            subst; rewrite HB; apply CTcol_trivial_2.

            assert (Hmem3 : S.mem p3 x = true).

              rewrite <- HEq in Hmem3'.
              rewrite SWP.Dec.F.add_neq_b in Hmem3'; try assumption.
              rewrite SWP.Dec.F.remove_neq_b in Hmem3'; assumption.

            unfold ss_ok in HSSF.
            apply HSSF with x.

              apply SSWEqP.MP.Dec.F.mem_1; assumption.

              do 2 (rewrite andb_true_iff); repeat split; assumption.

        subst.
        do 2 (rewrite andb_true_iff in Hmem).
        destruct Hmem as [[Hmem1' Hmem2'] Hmem3'].
        assert (Hmem3 : S.mem p3 x = true).

          unfold partition in HIn.
          apply SS.partition_spec1 in HIn; try apply proper_4.
          apply SSWEqP.MP.Dec.F.filter_2 in HIn; try assumption; apply proper_4.

        elim (Pos.eq_dec pa p1); intro Hpap1.

          subst; rewrite HB; apply CTcol_permutation_4; apply CTcol_trivial_2.

          assert (Hmem1 : S.mem p1 x = true).

            rewrite <- HEq in Hmem1'.
            rewrite SWP.Dec.F.add_neq_b in Hmem1'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem1'; assumption.

          elim (Pos.eq_dec pa p2); intro Hpap2.

            subst; rewrite HB; apply CTcol_trivial_2.

            assert (Hmem2 : S.mem p2 x = true).

              rewrite <- HEq in Hmem2'.
              rewrite SWP.Dec.F.add_neq_b in Hmem2'; try assumption.
              rewrite SWP.Dec.F.remove_neq_b in Hmem2'; assumption.

            unfold ss_ok in HSSF.
            apply HSSF with x.

              apply SSWEqP.MP.Dec.F.mem_1; assumption.

              do 2 (rewrite andb_true_iff); repeat split; assumption.

        do 2 (rewrite andb_true_iff in Hmem).
        destruct Hmem as [[Hmem1' Hmem2'] Hmem3'].

        elim (Pos.eq_dec pa p1); intro Hpap1;
        elim (Pos.eq_dec pa p2); intro Hpap2;
        elim (Pos.eq_dec pa p3); intro Hpap3.

          subst; apply CTcol_trivial_1.

          subst; apply CTcol_trivial_1.

          subst; apply CTcol_permutation_4; apply CTcol_trivial_2.

          subst.
          assert (Hmem1 : S.mem pb x = true).

            unfold partition in HIn.
            apply SS.partition_spec1 in HIn; try apply proper_4.
            apply SSWEqP.MP.Dec.F.filter_2 in HIn; try assumption; apply proper_4.

          assert (Hmem2 : S.mem p2 x = true).

            rewrite <- HEq in Hmem2'.
            rewrite SWP.Dec.F.add_neq_b in Hmem2'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem2'; assumption.

          assert (Hmem3 : S.mem p3 x = true).

            rewrite <- HEq in Hmem3'.
            rewrite SWP.Dec.F.add_neq_b in Hmem3'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem3'; assumption.

          rewrite <- HB.
          unfold ss_ok in HSSF.
          apply HSSF with x.

            apply SSWEqP.MP.Dec.F.mem_1; assumption.

            do 2 (rewrite andb_true_iff); repeat split; assumption.

          subst; apply CTcol_trivial_2.

          subst.
          assert (Hmem2 : S.mem pb x = true).

            unfold partition in HIn.
            apply SS.partition_spec1 in HIn; try apply proper_4.
            apply SSWEqP.MP.Dec.F.filter_2 in HIn; try assumption; apply proper_4.

          assert (Hmem1 : S.mem p1 x = true).

            rewrite <- HEq in Hmem1'.
            rewrite SWP.Dec.F.add_neq_b in Hmem1'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem1'; assumption.

          assert (Hmem3 : S.mem p3 x = true).

            rewrite <- HEq in Hmem3'.
            rewrite SWP.Dec.F.add_neq_b in Hmem3'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem3'; assumption.

          rewrite <- HB.
          unfold ss_ok in HSSF.
          apply HSSF with x.

            apply SSWEqP.MP.Dec.F.mem_1; assumption.

            do 2 (rewrite andb_true_iff); repeat split; assumption.

          subst.
          assert (Hmem3 : S.mem pb x = true).

            unfold partition in HIn.
            apply SS.partition_spec1 in HIn; try apply proper_4.
            apply SSWEqP.MP.Dec.F.filter_2 in HIn; try assumption; apply proper_4.

          assert (Hmem1 : S.mem p1 x = true).

            rewrite <- HEq in Hmem1'.
            rewrite SWP.Dec.F.add_neq_b in Hmem1'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem1'; assumption.

          assert (Hmem2 : S.mem p2 x = true).

            rewrite <- HEq in Hmem2'.
            rewrite SWP.Dec.F.add_neq_b in Hmem2'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem2'; assumption.

          rewrite <- HB.
          unfold ss_ok in HSSF.
          apply HSSF with x.

            apply SSWEqP.MP.Dec.F.mem_1; assumption.

            do 2 (rewrite andb_true_iff); repeat split; assumption.

         assert (Hmem1 : S.mem p1 x = true).

            rewrite <- HEq in Hmem1'.
            rewrite SWP.Dec.F.add_neq_b in Hmem1'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem1'; assumption.

          assert (Hmem2 : S.mem p2 x = true).

            rewrite <- HEq in Hmem2'.
            rewrite SWP.Dec.F.add_neq_b in Hmem2'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem2'; assumption.

          assert (Hmem3 : S.mem p3 x = true).

            rewrite <- HEq in Hmem3'.
            rewrite SWP.Dec.F.add_neq_b in Hmem3'; try assumption.
            rewrite SWP.Dec.F.remove_neq_b in Hmem3'; assumption.

          unfold ss_ok in HSSF.
          apply HSSF with x.

            apply SSWEqP.MP.Dec.F.mem_1; assumption.

            do 2 (rewrite andb_true_iff); repeat split; assumption.

      unfold ss_ok in HSSa.
      apply HSSa with s'; try assumption.
      apply SSWEqP.MP.Dec.F.mem_1; assumption.

  clear HSSF; assert (HSSF := HSSF'); clear HSSF'.

  unfold ss_ok in HSSF.
  apply HSSF with s; try assumption.
  apply SSWEqP.MP.Dec.F.mem_1; assumption.

  assert (HSSS : ss_ok (snd_ss (partition_ss pb ss)) interp).

    clear Hmem; clear p1; clear p2; clear p3.
    intros s' Hs'.
    intros.
    apply SSWEqP.MP.Dec.F.mem_2 in Hs'.
    unfold partition in Hs'.
    apply SS.partition_spec2 in Hs'; try apply proper_4.
    apply SSWEqP.MP.Dec.F.filter_1 in Hs'; try apply proper_5.
    unfold ss_ok in HSS.
    apply HSS with s'; try assumption.
    apply SSWEqP.MP.Dec.F.mem_1; assumption.

  unfold ss_ok in HSSS.
  apply HSSS with s; try assumption.
  apply SSWEqP.MP.Dec.F.mem_1; assumption.
Qed.

Definition partition_sp_1 p sp :=
  SP.partition (fun e => Pos.eqb (fstpp e) p || Pos.eqb (sndpp e) p) sp.

Definition partition_sp_2 p sp :=
  SP.partition (fun e => Pos.eqb (fstpp e) p) sp.

Definition fst_sp (pair : SP.t * SP.t) :=
 match pair with
    |(a,b) => a
  end.

Definition snd_sp (pair : SP.t * SP.t) :=
 match pair with
    |(a,b) => b
  end.

Definition new_pair_1 pair (pos : positive) := (pos, sndpp(pair)).

Definition new_pair_2 pair (pos : positive) := (fstpp(pair), pos).

Definition subst_in_sp_aux_1 := (fun pos pair sp => SP.add (new_pair_1 pair pos) sp).

Definition subst_in_sp_aux_2 := (fun pos pair sp => SP.add (new_pair_2 pair pos) sp).

Definition subst_in_sp p1 p2 sp :=
  let pair_1 := partition_sp_1 p2 sp in
  let sp_to_modify := fst_sp(pair_1) in
  let sp_to_keep := snd_sp(pair_1) in
  let pair_2 := partition_sp_2 p2 sp_to_modify in
  let sp_to_modify_f := fst_sp(pair_2) in
  let sp_to_modify_s := snd_sp(pair_2) in
  let newsp_to_modify_f := SP.fold (subst_in_sp_aux_1 p1) sp_to_modify_f SP.empty in
  let newsp_to_modify_s := SP.fold (subst_in_sp_aux_2 p1) sp_to_modify_s SP.empty in
  SP.union (SP.union newsp_to_modify_f newsp_to_modify_s) sp_to_keep.

Lemma proper_6 : forall p, Proper ((fun t1 t2 : SetOfPairsOfPositiveOrderedType.t =>
                                  Pos.eq (fstpp t1) (fstpp t2) /\ Pos.eq (sndpp t1) (sndpp t2)) ==> eq)
                                  (fun e : SP.elt => (fstpp e =? p)%positive || (sndpp e =? p)%positive).
Proof.
intros p x y Hxy.
destruct Hxy as [Hxyf Hxys].
rewrite Hxyf; rewrite Hxys.
reflexivity.
Qed.

Lemma proper_7 : forall p, Proper ((fun t1 t2 : SetOfPairsOfPositiveOrderedType.t =>
                                  Pos.eq (fstpp t1) (fstpp t2) /\ Pos.eq (sndpp t1) (sndpp t2)) ==> eq)
                                  (fun x : SP.elt => negb ((fstpp x =? p)%positive || (sndpp x =? p)%positive)).
Proof.
intros p x y Hxy.
destruct Hxy as [Hxyf Hxys].
rewrite Hxyf; rewrite Hxys.
reflexivity.
Qed.

Lemma proper_8 : forall p, Proper ((fun t1 t2 : SetOfPairsOfPositiveOrderedType.t =>
                                  Pos.eq (fstpp t1) (fstpp t2) /\ Pos.eq (sndpp t1) (sndpp t2)) ==> eq)
                                  (fun e : SP.elt => (fstpp e =? p)%positive).
Proof.
intros p x y Hxy.
destruct Hxy as [Hxyf Hxys].
rewrite Hxyf.
reflexivity.
Qed.

Lemma proper_9 : forall p, Proper ((fun t1 t2 : SetOfPairsOfPositiveOrderedType.t =>
                                  Pos.eq (fstpp t1) (fstpp t2) /\ Pos.eq (sndpp t1) (sndpp t2)) ==> eq)
                                  (fun x : SP.elt => negb (fstpp x =? p)%positive).
Proof.
intros p x y Hxy.
destruct Hxy as [Hxyf Hxys].
rewrite Hxyf.
reflexivity.
Qed.

Lemma subst_sp_ok :
  forall (A B : COLTpoint) (H : A = B) pa pb sp (interp :  positive -> COLTpoint),
  interp pa = A ->
  interp pb = B ->
  sp_ok sp interp -> sp_ok (subst_in_sp pa pb sp) interp.
Proof.
intros A B H pa pb sp interp HA HB HSP.
unfold subst_in_sp.
unfold sp_ok.
intros p Hp.
apply SPWEqP.MP.Dec.F.mem_2 in Hp.
do 2 rewrite SPWEqP.MP.Dec.F.union_iff in Hp.
elim Hp; intro HInAux; clear Hp.

  assert (HSPM : sp_ok (fst_sp (partition_sp_1 pb sp)) interp).

    intros p' Hp'.
    apply SPWEqP.MP.Dec.F.mem_2 in Hp'.
    unfold partition_sp_1 in Hp'.
    apply SP.partition_spec1 in Hp'; try apply proper_6.
    apply SPWEqP.MP.Dec.F.filter_1 in Hp'; try apply proper_6.
    unfold sp_ok in HSP.
    apply HSP; try assumption.
    apply SPWEqP.MP.Dec.F.mem_1; assumption.

  clear HSP.
  elim HInAux; intro HIn; clear HInAux.

    assert (HSPF : sp_ok (fst_sp (partition_sp_2 pb (fst_sp (partition_sp_1 pb sp)))) interp).

      intros p' Hp'.
      apply SPWEqP.MP.Dec.F.mem_2 in Hp'.
      unfold partition_sp_1 in Hp'.
      apply SP.partition_spec1 in Hp'; try apply proper_8.
      apply SPWEqP.MP.Dec.F.filter_1 in Hp'; try apply proper_8.
      unfold sp_ok in HSPM.
      apply HSPM; try assumption.
      apply SPWEqP.MP.Dec.F.mem_1; assumption.

    clear HSPM.

    assert (HSPF' : sp_ok (SP.fold (subst_in_sp_aux_1 pa)
                         (fst_sp (partition_sp_2 pb (fst_sp (partition_sp_1 pb sp))))
                         SP.empty) interp).
    apply SPWEqP.MP.fold_rec_nodep; try apply sp_ok_empty.
    clear HIn.
    intros x a HInRec HSPRec.
    intros p' Hp'.
    unfold subst_in_sp_aux_1 in *.
    apply SPWEqP.MP.Dec.F.mem_2 in Hp'.
    rewrite SPWEqP.MP.Dec.F.add_iff in Hp'.
    elim Hp'; intro HIn; clear Hp'.

      destruct HIn as [HEq1 HEq2].
      rewrite <- HEq1; rewrite <- HEq2.
      unfold new_pair_1.
      clear HSPRec; clear a.
      elim (Pos.min_spec pa (sndpp(x))); intro Hmin.

        destruct Hmin as [HLt Hmin].
        assert (Hmax : Pos.max pa (sndpp(x)) = (sndpp(x))) by (apply Pos.max_r; apply Pos.lt_le_incl; assumption).
        assert (HF : fstpp(pa, sndpp(x)) = pa) by (unfold fstpp; assumption).
        assert (HS : sndpp(pa, sndpp(x)) = sndpp(x)) by (unfold sndpp; assumption).
        rewrite HF; rewrite HS.

        assert (Hpb : fstpp(x) = pb).

          unfold partition_sp_2 in HInRec.
          apply SP.partition_spec1 in HInRec; try apply proper_8.
          apply SPWEqP.MP.Dec.F.filter_2 in HInRec; try apply proper_8.
          apply Ndec.Peqb_complete.
          assumption.

        intro HEq4.
        unfold sp_ok in HSPF.
        apply SPWEqP.MP.Dec.F.mem_1 in HInRec.
        apply (HSPF x) in HInRec.
        apply HInRec.
        rewrite Hpb; rewrite <- HEq4; rewrite HA; rewrite HB; rewrite H; reflexivity.

        destruct Hmin as [HLe Hmin].
        assert (Hmax : Pos.max pa (sndpp(x)) = pa) by (apply Pos.max_l; assumption).
        assert (HF : fstpp(pa, sndpp(x)) = sndpp(x)) by (unfold fstpp; assumption).
        assert (HS : sndpp(pa, sndpp(x)) = pa) by (unfold sndpp; assumption).
        rewrite HF; rewrite HS.

        assert (Hpb : fstpp(x) = pb).

          unfold partition_sp_2 in HInRec.
          apply SP.partition_spec1 in HInRec; try apply proper_8.
          apply SPWEqP.MP.Dec.F.filter_2 in HInRec; try apply proper_8.
          apply Ndec.Peqb_complete.
          assumption.

        intro HEq4.
        unfold sp_ok in HSPF.
        apply SPWEqP.MP.Dec.F.mem_1 in HInRec.
        apply (HSPF x) in HInRec.
        apply HInRec.
        rewrite Hpb; rewrite HEq4; rewrite HA; rewrite HB; rewrite H; reflexivity.

      unfold sp_ok in HSPRec.
      apply HSPRec.
      apply SPWEqP.MP.Dec.F.mem_1; assumption.

    clear HSPF; assert (HSPF := HSPF'); clear HSPF'.
    unfold sp_ok in HSPF.
    apply HSPF.
    apply SPWEqP.MP.Dec.F.mem_1; assumption.

    assert (HSPS : sp_ok (snd_sp (partition_sp_2 pb (fst_sp (partition_sp_1 pb sp)))) interp).

      intros p' Hp'.
      apply SPWEqP.MP.Dec.F.mem_2 in Hp'.
      unfold partition_sp_1 in Hp'.
      apply SP.partition_spec2 in Hp'; try apply proper_8.
      apply SPWEqP.MP.Dec.F.filter_1 in Hp'; try apply proper_9.
      unfold sp_ok in HSPM.
      apply HSPM; try assumption.
      apply SPWEqP.MP.Dec.F.mem_1; assumption.

    clear HSPM.

    assert (HSPS' : sp_ok (SP.fold (subst_in_sp_aux_2 pa)
                         (snd_sp (partition_sp_2 pb (fst_sp (partition_sp_1 pb sp))))
                         SP.empty) interp).
    apply SPWEqP.MP.fold_rec_nodep; try apply sp_ok_empty.
    clear HIn.
    intros x a HInRec HSPRec.
    intros p' Hp'.
    unfold subst_in_sp_aux_2 in *.
    apply SPWEqP.MP.Dec.F.mem_2 in Hp'.
    rewrite SPWEqP.MP.Dec.F.add_iff in Hp'.
    elim Hp'; intro HIn; clear Hp'.

      destruct HIn as [HEq1 HEq2].
      rewrite <- HEq1; rewrite <- HEq2.
      unfold new_pair_2.
      clear HSPRec; clear a.
      elim (Pos.min_spec (fstpp(x)) pa); intro Hmin.

        destruct Hmin as [HLt Hmin].
        assert (Hmax : Pos.max (fstpp(x)) pa = pa) by (apply Pos.max_r; apply Pos.lt_le_incl; assumption).
        assert (HF : fstpp(fstpp(x), pa) = fstpp(x)) by (unfold fstpp; assumption).
        assert (HS : sndpp(fstpp(x), pa) = pa) by (unfold sndpp; assumption).
        rewrite HF; rewrite HS.

        assert (Hpb : sndpp(x) = pb).

          assert (HIn : SP.In x (fst_sp (partition_sp_1 pb sp))).

            unfold partition_sp_2 in HInRec.
            apply SP.partition_spec2 in HInRec; try apply proper_8.
            apply SPWEqP.MP.Dec.F.filter_1 in HInRec; try apply proper_9.
            assumption.

          unfold partition_sp_2 in HInRec.
          apply SP.partition_spec2 in HInRec; try apply proper_8.
          apply SPWEqP.MP.Dec.F.filter_2 in HInRec; try apply proper_9.
          unfold partition_sp_1 in HIn.
          apply SP.partition_spec1 in HIn; try apply proper_6.
          apply SPWEqP.MP.Dec.F.filter_2 in HIn; try apply proper_6.
          apply orb_true_iff in HIn.
          elim HIn; intro HEqb; clear HIn.

            apply Peqb_true_eq in HEqb.
            apply negb_true_iff in HInRec.
            apply Pos.eqb_neq in HInRec.
            rewrite HEqb in HInRec.
            intuition.

            apply Peqb_true_eq in HEqb.
            assumption.

        intro HEq4.
        unfold sp_ok in HSPS.
        apply SPWEqP.MP.Dec.F.mem_1 in HInRec.
        apply (HSPS x) in HInRec.
        apply HInRec.
        rewrite Hpb; rewrite HEq4; rewrite HA; rewrite HB; rewrite H; reflexivity.

        destruct Hmin as [HLe Hmin].
        assert (Hmax : Pos.max (fstpp(x)) pa = fstpp(x)) by (apply Pos.max_l; assumption).
        assert (HF : fstpp(fstpp(x), pa) = pa) by (unfold fstpp; assumption).
        assert (HS : sndpp(fstpp(x), pa) = fstpp(x)) by (unfold sndpp; assumption).
        rewrite HF; rewrite HS.

        assert (Hpb : sndpp(x) = pb).

          assert (HIn : SP.In x (fst_sp (partition_sp_1 pb sp))).

            unfold partition_sp_2 in HInRec.
            apply SP.partition_spec2 in HInRec; try apply proper_8.
            apply SPWEqP.MP.Dec.F.filter_1 in HInRec; try apply proper_9.
            assumption.

          unfold partition_sp_2 in HInRec.
          apply SP.partition_spec2 in HInRec; try apply proper_8.
          apply SPWEqP.MP.Dec.F.filter_2 in HInRec; try apply proper_9.
          unfold partition_sp_1 in HIn.
          apply SP.partition_spec1 in HIn; try apply proper_6.
          apply SPWEqP.MP.Dec.F.filter_2 in HIn; try apply proper_6.
          apply orb_true_iff in HIn.
          elim HIn; intro HEqb; clear HIn.

            apply Peqb_true_eq in HEqb.
            apply negb_true_iff in HInRec.
            apply Pos.eqb_neq in HInRec.
            rewrite HEqb in HInRec.
            intuition.

            apply Peqb_true_eq in HEqb.
            assumption.

        intro HEq4.
        unfold sp_ok in HSPS.
        apply SPWEqP.MP.Dec.F.mem_1 in HInRec.
        apply (HSPS x) in HInRec.
        apply HInRec.
        rewrite Hpb; rewrite <- HEq4; rewrite HA; rewrite HB; rewrite H; reflexivity.

      unfold sp_ok in HSPRec.
      apply HSPRec.
      apply SPWEqP.MP.Dec.F.mem_1; assumption.

    clear HSPS; assert (HSPS := HSPS'); clear HSPS'.
    unfold sp_ok in HSPS.
    apply HSPS.
    apply SPWEqP.MP.Dec.F.mem_1; assumption.

  assert (HIn := HInAux); clear HInAux.
  assert (HSPK : sp_ok (snd_sp (partition_sp_1 pb sp)) interp).

    intros p' Hp'.
    apply SPWEqP.MP.Dec.F.mem_2 in Hp'.
    unfold partition_sp_1 in Hp'.
    apply SP.partition_spec2 in Hp'; try apply proper_6.
    apply SPWEqP.MP.Dec.F.filter_1 in Hp'; try apply proper_7.
    unfold sp_ok in HSP.
    apply HSP; try assumption.
    apply SPWEqP.MP.Dec.F.mem_1; assumption.

  unfold sp_ok in HSPK.
  apply HSPK; try assumption.
  apply SPWEqP.MP.Dec.F.mem_1; assumption.
Qed.
*)

End Col_refl.