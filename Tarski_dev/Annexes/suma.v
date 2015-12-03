Require Export GeoCoq.Tarski_dev.Ch11_angles.

Section Sec.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

(** Definition of the sum of angles.
    Suma A B C D E F G H I means that ABC+DEF = GHI. *)

Definition Suma A B C D E F G H I:=
   exists J, Conga C B J D E F /\ ~ one_side B C A J /\ Conga A B J G H I.

(** The Isi predicate describes the fact that the sum of the two angles is "interior", 
i.e doesn't exceed a flat angle. *)

Definition Isi A B C D E F:=
   A<>B /\ (out E D F \/ ~ Bet A B C) /\
   exists J, Conga C B J D E F /\ ~ one_side B C A J /\ ~ two_sides A B C J.


Lemma suma_distincts : forall A B C D E F G H I, Suma A B C D E F G H I ->
   A<>B /\ B<>C /\ D<>E /\ E<>F /\ G<>H /\ H<>I.
Proof.
  intros A B C D E F G H I Hsuma.
  destruct Hsuma as [J HJ].
  spliter.
  assert_diffs.
  repeat split; auto.
Qed.

Lemma ex_suma : forall A B C D E F, A<>B -> B<>C -> D<>E -> E<>F ->
   exists G H I, Suma A B C D E F G H I.
Proof.
  intros A B C D E F HAB HBC HDE HEF.
  exists A.
  exists B.
  elim (Col_dec A B C).
  { intro HColB.
    assert (HJ : exists J, Conga D E F C B J) by (apply angle_construction_3; auto).
    destruct HJ as [J HConga].
    assert_diffs.
    exists J.
    exists J.
    repeat (split; Conga).
    apply (col123__nos); Col.
  }
  intro HNColB.
  elim (Col_dec D E F).
  { intro HColE.
    elim (Bet_dec D E F).
    { intro HEBet.
      assert (HJ : exists J, is_midpoint B C J) by (apply symmetric_point_construction).
      destruct HJ as [J HMid].
      assert_diffs.
      destruct HMid as [HJBet HCong].
      exists J.
      exists J.
      split.
      apply conga_line; Between; repeat split; auto; intro; treat_equalities; absurde.
      split; Conga.
      apply col124__nos; Col.
    }
    intro HENBet.
    assert (HEOut : out E D F) by (apply l6_4_2; auto).
    exists C.
    exists C.
    split.
    apply (out_conga C B C D E D); auto; try (apply out_trivial); Conga.
    split; Conga.
    apply col124__nos; Col.
  }
  intro HNColE.
  assert (HJ : exists J, Conga D E F C B J /\ two_sides C B J A) by (apply ex_conga_ts; Col).
  destruct HJ as [J [HConga HTwo]].
  assert_diffs.
  exists J.
  exists J.
  repeat (split; Conga).
  apply l9_9; apply l9_2; apply invert_two_sides; auto.
Qed.

(** Unicity of the sum. *)

Lemma suma2__conga : forall A B C D E F G H I G' H' I',
   Suma A B C D E F G H I -> Suma A B C D E F G' H' I' -> Conga G H I G' H' I'.
Proof.
  intros A B C D E F G H I G' H' I' Hsuma Hsuma'.
  destruct Hsuma as [J [HJ1 [HJ2 HJ3]]].
  destruct Hsuma' as [J' [HJ'1 [HJ'2 HJ'3]]].
  assert_diffs.
  assert (HcongaC : Conga C B J C B J') by (apply (conga_trans C B J D E F); auto; apply conga_sym; auto).
  assert (HcongaA : Conga A B J A B J').
  { elim (Col_dec A B C).
    { intro HColB.
      elim (Bet_dec A B C).
      { intro HBBet.
        apply (l11_13 C B J C B J'); Between.
      }
      intro HBNBet.
      assert (HBOut : out B A C) by (apply l6_4_2; auto).
      apply (l11_10 C B J C B J'); try (apply out_trivial); auto.
    }
    intro HNColB.
    elim (Col_dec D E F).
    { intro HColE.
      apply (out_conga A B J A B J); try (apply out_trivial); Conga.
      elim (Bet_dec D E F).
      { intro HEBet.
        apply l6_3_2; repeat split; auto.
        exists C.
        split; auto; split; apply (bet_conga_bet D E F); Conga.
      }
      intro HENBet.
      assert (HEOut : out E D F) by (apply l6_4_2; auto).
      apply (l6_7 B J C); apply (out_conga_out D E F); Conga.
    }
    intro HNColE.
    apply (l11_22a A B J C A B J' C); auto.
    repeat (split; try (apply not_one_side_two_sides); Conga); apply (ncol_conga_ncol D E F); Conga.
  }
  apply (conga_trans G H I A B J).
  Conga.
  apply (conga_trans A B J A B J'); auto.
Qed.

(** Commutativity of the sum. *)

Lemma suma__suma456123 : forall A B C D E F G H I, Suma A B C D E F G H I -> Suma D E F A B C G H I.
Proof.
  intros A B C D E F G H I Hsuma.
  destruct Hsuma as [J [HCongaBCJ [HNOne HCongaABJ]]].
  assert_diffs.
  elim (Col_dec A B C).
  { intro HColB.
    elim (Bet_dec A B C).
    { intro HBBet.
      assert (HK : exists K, is_midpoint E F K) by (apply symmetric_point_construction).
      destruct HK as [K [HKBet HCong]].
      assert_diffs.
      exists K.
      split; try (apply conga_line; auto).
      split.
      intro HOne; assert (~ Col E F K) by (apply (one_side_not_col E F K D); apply one_side_symmetry; auto); assert_cols; Col.
      apply (conga_trans D E K A B J); auto.
      apply conga_left_comm; apply (l11_13 F E D C B J); Between; Conga.
    }
    intro HBNBet.
    assert (HBOut : out B A C) by (apply l6_4_2; auto).
    exists F.
    split.
    apply (l11_10 F E F C B C); try (apply out_trivial); Conga.
    split.
    apply col124__nos; Col.
    apply (conga_trans D E F A B J); auto.
    apply conga_sym.
    apply (l11_10 C B J D E F); try (apply out_trivial); auto.
  }

  intro HNColB.
  elim (Col_dec D E F).
  { intro HColE.
    assert (HK : exists K, Conga A B C F E K) by (apply angle_construction_3; auto).
    destruct HK as [K HConga].
    assert_diffs.
    exists K.
    split; Conga.
    split.
    intro HOne; assert (~ Col E F D) by (apply (one_side_not_col E F D K); auto); Col.
    apply (conga_trans D E K A B J); auto.
    elim (Bet_dec D E F).
    { intro HEBet.
      apply conga_sym; apply conga_left_comm.
      apply (l11_13 C B A F); Conga; Between.
      apply (bet_conga_bet D E F); Conga.
    }
    intro HENBet.
    assert (HEOut : out E D F) by (apply l6_4_2; auto).
    apply conga_sym.
    apply (l11_10 A B C F E K); try (apply out_trivial); auto.
    apply (out_conga_out D E F); Conga.
  }

  intro HNColE.
  assert (HK : exists K, Conga A B C F E K /\ two_sides F E K D) by (apply ex_conga_ts; Col).
  destruct HK as [K [HConga HTwo]].
  exists K.
  split; Conga.
  split.
  apply l9_9; apply l9_2; apply invert_two_sides; auto.
  apply (conga_trans D E K A B J); auto.
  apply conga_sym; apply conga_right_comm.
  apply (l11_22a A B J C K E D F).
  split.
  apply not_one_side_two_sides; Col.
  intro; assert (Col D E F) by (apply (col_conga_col C B J D E F); Col); Col.
  split.
  apply invert_two_sides; auto.
  split; Conga.
Qed.

(** ABC + 0 =  ABC *)

Lemma out546_suma__conga : forall A B C D E F G H I, Suma A B C D E F G H I ->
   out E D F -> Conga A B C G H I.
Proof.
  intros A B C D E F G H I Hsuma Hout.
  assert(A<>B/\B<>C/\D<>E/\E<>F/\G<>H/\H<>I) by (apply suma_distincts; auto).
  spliter.
  apply (suma2__conga A B C D E F A B C); auto.
  exists C.
  split.
  apply (out_conga C B C D E D); try (apply out_trivial); Conga.
  split; Conga.
  apply col124__nos; Col.
Qed.

(** 0 + DEF = DEF *)

Lemma out213_suma__conga : forall A B C D E F G H I, Suma A B C D E F G H I ->
   out B A C -> Conga D E F G H I.
Proof.
  intros A B C D E F G H I Hsuma Hout.
  apply (out546_suma__conga D E F A B C); auto.
  apply suma__suma456123; auto.
Qed.

(** Conga preserves Suma. *)

Lemma conga3_suma__suma : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   Suma A B C D E F G H I ->
   Conga A B C A' B' C' ->
   Conga D E F D' E' F' ->
   Conga G H I G' H' I' ->
   Suma A' B' C' D' E' F' G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I' Hsuma HCongaB HCongaE HCongaH.
  assert (Hsuma' : Suma D' E' F' A B C G' H' I').
  { apply suma__suma456123.
    destruct Hsuma as [J [HJ1 [HJ2 HJ3]]].
    exists J.
    split.
    apply (conga_trans C B J D E F); auto.
    split; auto.
    apply (conga_trans A B J G H I); auto.
  }
  apply suma__suma456123.
  destruct Hsuma' as [J [HJ1 [HJ2 HJ3]]].
  exists J.
  split.
  apply (conga_trans F' E' J A B C); auto.
  split; auto.
Qed.

(** Out preserves Suma. *)

Lemma out6_suma__suma : forall A B C D E F G H I A' C' D' F' G' I',
   Suma A B C D E F G H I -> out B A A' -> out B C C' -> out E D D' ->
   out E F F' -> out H G G' -> out H I I' -> Suma A' B C' D' E F' G' H I'.
Proof.
  intros.
  assert_diffs.
  apply (conga3_suma__suma A B C D E F G H I); auto.
    apply (out_conga A B C A B C); try (apply out_trivial); Conga.
    apply (out_conga D E F D E F); try (apply out_trivial); Conga.
    apply (out_conga G H I G H I); try (apply out_trivial); Conga.
Qed.

(** Some permutation properties:*)

Lemma suma__suma321456789 : forall A B C D E F G H I,
   Suma A B C D E F G H I -> Suma C B A D E F G H I.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := suma_distincts A B C D E F G H I Hsuma).
  spliter.
  apply (conga3_suma__suma A B C D E F G H I); Conga.
Qed.

Lemma suma__suma123654789 : forall A B C D E F G H I,
   Suma A B C D E F G H I -> Suma A B C F E D G H I.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := suma_distincts A B C D E F G H I Hsuma).
  spliter.
  apply (conga3_suma__suma A B C D E F G H I); Conga.
Qed.

Lemma suma__suma123456987 : forall A B C D E F G H I,
   Suma A B C D E F G H I -> Suma A B C D E F I H G.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := suma_distincts A B C D E F G H I Hsuma).
  spliter.
  apply (conga3_suma__suma A B C D E F G H I); Conga.
Qed.

Lemma suma__suma321654987 : forall A B C D E F G H I,
   Suma A B C D E F G H I -> Suma C B A F E D I H G.
Proof.
  intros A B C D E F G H I Hsuma.
  assert(Hd := suma_distincts A B C D E F G H I Hsuma).
  spliter.
  apply (conga3_suma__suma A B C D E F G H I); Conga.
Qed.

(** Characterization of Isi using lea. *)

Lemma isi_chara : forall A B C D E F A', A<>B -> A'<>B -> Bet A B A' ->
   (Isi A B C D E F <-> lea D E F C B A').
Proof.
  intros A B C D E F A' HAB HA'B HABA'.
  split.
  - intro Hint.
    destruct Hint as [_ [HUn [J [HJ1 [HJ2 HJ3]]]]].
    assert_diffs.
    destruct HUn as [HEOut | HBNBet].
    apply l11_31_1; auto.
    elim (Col_dec A B C).
    { intro HColB.
      apply l11_31_2; auto.
      apply (bet_out_out_bet A B A'); try (apply out_trivial); auto.
      apply l6_4_2; auto.
    }
    intro HNColB.
    elim (Col_dec D E F).
    { intro HColE.
      elim (Bet_dec D E F).
      { intro HDEF.
        exfalso.
        apply HJ3.
        assert (HCBJ : Bet C B J) by (apply (bet_conga_bet D E F); Conga; Between); assert_cols.
        repeat split; Col.
        intro; apply HNColB; apply (l6_16_1 B J C A); Col.
        exists B.
        split; Col; Between.
      }
      intro; apply l11_31_1; auto; apply l6_4_2; auto.
    }
    intro HNColE.
    apply (l11_30 C B J C B A'); try (apply conga_refl); auto.
    exists J.
    split; Conga.
    apply l11_24; apply (in_angle_reverse A); auto.
    assert (HTwo : two_sides B C A J).
    { apply not_one_side_two_sides; auto.
      apply (ncol_conga_ncol D E F); Conga.
    }
    destruct HTwo as [_ [_ [_ [X [HXCol HXBet]]]]].
    repeat split; auto.
    exists X.
    split; auto.
    elim (eq_dec_points B X); auto.
    intro HBX.
    right.
    apply (col_one_side_out B A X C); Col.
    apply invert_one_side.
    apply (one_side_transitivity A B X J).
    { apply out_one_side.
      left; intro; apply HNColB; apply (l6_16_1 B X); Col.
      assert (HAX : A<>X) by (intro; treat_equalities; Col).
      repeat split; auto.
      intro; treat_equalities; auto.
    }
    apply one_side_symmetry.
    apply not_two_sides_one_side; Col.
    intro; apply HNColB. apply (l6_16_1 B X); Col. apply (col_transitivity_2 J); Col.
    intro; treat_equalities; auto.

  - intro Hlea.
    assert_diffs.
    split; auto.
    elim (Col_dec A B C).
    { intro HColB.
      elim (Bet_dec A B C).
      { intro HBBet.
        assert (HEOut : out E D F).
        { assert (out B C A') by (apply (l6_3_2); repeat split; auto; exists A; repeat split; Between).
          apply (out_conga_out C B A'); auto.
          apply lea_asym; auto.
          apply l11_31_1; auto.
        }
        split; try left; auto.
        exists C.
        split.
        apply (out_conga C B C D E D); try (apply out_trivial); Conga.
        split.
        apply col124__nos; Col.
        apply not_two_sides_id.
      }
      intro HBNBet.
      assert (HBOut : out B A C) by (apply not_bet_out; auto).
      split.
      right; auto.
      assert (HJ : exists J : Tpoint, Conga D E F C B J) by (apply (angle_construction_3 D E F C B); auto).
      destruct HJ as [J HJ].
      exists J.
      split; Conga.
      split.
      apply col123__nos; Col.
      intro HTwo; destruct HTwo as [HBA [HNCol _]]; Col.
    }
    intro HNColB.
    assert (HNColB' : ~ Col A' B C) by (intro; apply HNColB; apply (l6_16_1 B A'); Col).
    elim (Col_dec D E F).
    { intro HNColE.
      assert (HEOut : out E D F).
      { apply not_bet_out; auto.
        intro HEBet.
        apply HNColB'.
        apply bet_col; apply between_symmetry.
        apply (bet_lea__bet D E F); auto.
      }
      split.
      left; auto.
      exists C.
      split.
      apply (out_conga C B C D E D); try (apply out_trivial); Conga.
      split.
      apply col124__nos; Col.
      apply not_two_sides_id.
    }
    intro HNColE.
    split.
    right; intro; Col.
    assert (HJ : exists J, Conga D E F C B J /\ two_sides C B J A) by (apply ex_conga_ts; Col).
    destruct HJ as [J [HCongaJ HTwo]].
    assert_diffs.
    exists J.
    split; Conga.
    split.
    apply l9_9; apply l9_2; apply invert_two_sides; auto.
    elim (Col_dec A B J).
    { intro HColJ.
      intro HTwo'.
      destruct HTwo' as [HBA [HNColC [HNColJ _]]].
      Col.
    }
    intro HNColJ.
    assert (HF : ~ two_sides A' B C J).
    { apply l9_9_bis.
      apply one_side_symmetry.
      apply (in_angle_one_side); auto.
      intro; apply HNColJ; apply (l6_16_1 B A'); Col.
      apply l11_24.
      destruct Hlea as [K [HInAngle HCongaK]].
      apply (conga_preserves_in_angle C B A' K C B A' J); Conga.
      apply (conga_trans C B K D E F); Conga.
      exists A; split; auto.
      repeat (split; Col).
      exists B; split; Between; Col.
    }
    intro; apply HF.
    apply (col_preserves_two_sides A B); Col.
Qed.

Lemma isi_distincts : forall A B C D E F, Isi A B C D E F ->
   A<>B /\ B<>C /\ D<>E /\ E<>F.
Proof.
  intros A B C D E F Hisi.
  destruct Hisi as [HP1 [HP2 [J HJ]]]. 
  spliter.
  assert_diffs.
  repeat split; auto.
Qed.

Lemma isi__isi456123 : forall A B C D E F, Isi A B C D E F ->
   Isi D E F A B C.
Proof.
  intros A B C D E F Hisi.
  assert(A<>B/\B<>C/\D<>E/\E<>F) by (apply isi_distincts; auto).
  spliter.
  assert(HD' : exists D', is_midpoint E D D') by apply symmetric_point_construction.
  destruct HD' as [D'].
  assert(HA' : exists A', is_midpoint B A A') by apply symmetric_point_construction.
  destruct HA' as [A'].
  assert_diffs.
  apply (isi_chara D E F A B C D'); Between.
  apply lea_right_comm.
  apply (l11_36 D _ _ A'); Between.
  apply lea_right_comm.
  apply (isi_chara A); Between.
Qed.

Lemma isi__isi123654 : forall A B C D E F, Isi A B C D E F ->
   Isi A B C F E D.
Proof.
  intros A B C D E F Hisi.
  destruct Hisi as [HAB [HUn [J [HJ1 [HJ2 HJ3]]]]].
  split; auto.
  split.
  { destruct HUn.
    left; apply l6_6; auto.
    right; auto.
  }
  exists J.
  split.
  apply conga_right_comm; auto.
  split; auto.
Qed.

Lemma isi__isi321456 : forall A B C D E F, Isi A B C D E F ->
   Isi C B A D E F.
Proof.
  intros.
  apply isi__isi456123.
  apply isi__isi123654.
  apply isi__isi456123.
  assumption.
Qed.

Lemma isi__isi321654 : forall A B C D E F, Isi A B C D E F ->
   Isi C B A F E D.
Proof.
  intros.
  apply isi__isi321456.
  apply isi__isi123654.
  assumption.
Qed.

Lemma conga2_isi__isi : forall A B C D E F A' B' C' D' E' F',
   Conga A B C A' B' C' -> Conga D E F D' E' F' ->
   Isi A B C D E F -> Isi A' B' C' D' E' F'.
Proof.
  intros A B C D E F A' B' C' D' E' F' HCongaB HCongaE Hisi.
  assert(HA0 : exists A0, is_midpoint B A A0) by apply symmetric_point_construction.
  destruct HA0 as [A0].
  assert(HA'0 : exists A'0, is_midpoint B' A' A'0) by apply symmetric_point_construction.
  destruct HA'0 as [A'0].
  assert_diffs.
  apply (isi_chara _ _ _ _ _ _ A'0); Between.
  apply (l11_30 D E F C B A0); try (apply (isi_chara A)); Between.
  apply conga_comm.
  apply (l11_13 A B C A'); Between.
Qed.

End Sec.


Ltac not_exist_hyp6 A B C D E F G H I J K L := first [not_exist_hyp_comm A B | not_exist_hyp_comm C D | not_exist_hyp_comm E F | not_exist_hyp_comm G H | not_exist_hyp_comm I J | not_exist_hyp_comm K L].

Ltac assert_diffs :=
repeat
 match goal with
      | H:(~Col ?X1 ?X2 ?X3) |- _ =>
      let h := fresh in
      not_exist_hyp3 X1 X2 X1 X3 X2 X3;
      assert (h := not_col_distincts X1 X2 X3 H);decompose [and] h;clear h;clean_reap_hyps

      | H:Cong ?A ?B ?C ?D, H2 : ?A <> ?B |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?B <> ?A |-_ =>
      let T:= fresh in (not_exist_hyp_comm C D);
        assert (T:= cong_diff_2 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?C <> ?D |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_3 A B C D H2 H);clean_reap_hyps
      | H:Cong ?A ?B ?C ?D, H2 : ?D <> ?C |-_ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= cong_diff_4 A B C D H2 H);clean_reap_hyps

      | H:is_midpoint ?I ?A ?B, H2 : ?A<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:is_midpoint ?I ?A ?B, H2 : ?B<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B I A);
       assert (T:= midpoint_distinct_1 I A B (swap_diff B A H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:is_midpoint ?I ?A ?B, H2 : ?I<>?A |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:is_midpoint ?I ?A ?B, H2 : ?A<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I B A B);
       assert (T:= midpoint_distinct_2 I A B (swap_diff A I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:is_midpoint ?I ?A ?B, H2 : ?I<>?B |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B H2 H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:is_midpoint ?I ?A ?B, H2 : ?B<>?I |- _ =>
      let T:= fresh in (not_exist_hyp2 I A A B);
       assert (T:= midpoint_distinct_3 I A B (swap_diff B I H2) H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Perp ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_distinct A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:Perp_in ?X ?A ?B ?C ?D |- _ =>
      let T:= fresh in (not_exist_hyp2 A B C D);
       assert (T:= perp_in_distinct X A B C D H);
       decompose [and] T;clear T;clean_reap_hyps
      | H:out ?A ?B ?C |- _ =>
      let T:= fresh in (not_exist_hyp2 A B A C);
       assert (T:= out_distinct A B C H);
       decompose [and] T;clear T;clean_reap_hyps

      | H:Conga ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A B);
        assert (T:= conga_diff1 A B C A' B' C' H);clean_reap_hyps
      | H:Conga ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B C);
        assert (T:= conga_diff2 A B C A' B' C' H);clean_reap_hyps
      | H:Conga ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm A' B');
        assert (T:= conga_diff45 A B C A' B' C' H);clean_reap_hyps
      | H:Conga ?A ?B ?C ?A' ?B' ?C' |- _ =>
      let T:= fresh in (not_exist_hyp_comm B' C');
        assert (T:= conga_diff56 A B C A' B' C' H);clean_reap_hyps

      | H:lea ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := lea_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:lta ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := lta_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
      | H:(acute ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp3 A B A C B C;
      assert (h := acute_distincts A B C H);decompose [and] h;clear h;clean_reap_hyps
      | H:(obtuse ?A ?B ?C) |- _ =>
      let h := fresh in
      not_exist_hyp3 A B A C B C;
      assert (h := obtuse_distincts A B C H);decompose [and] h;clear h;clean_reap_hyps

      | H:Suma ?A ?B ?C ?D ?E ?F ?G ?I ?J |- _ =>
      let h := fresh in
      not_exist_hyp6 A B B C D E E F G I I J;
      assert (h := suma_distincts A B C D E F G I J H);decompose [and] h;clear h;clean_reap_hyps

      | H:Isi ?A ?B ?C ?D ?E ?F |- _ =>
      let h := fresh in
      not_exist_hyp4 A B B C D E E F;
      assert (h := isi_distincts A B C D E F H);decompose [and] h;clear h;clean_reap_hyps
 end.

Hint Resolve suma__suma456123 suma__suma321456789 suma__suma123654789
             suma__suma123456987 suma__suma321654987 isi__isi321654 isi__isi321456
             isi__isi123654 isi__isi456123 : suma.

Ltac Suma := auto with suma.


Section Sec2.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

(** ABC <= ABC + DEF. *)

Lemma isi_suma__lea123789 : forall A B C D E F G H I, Suma A B C D E F G H I ->
   Isi A B C D E F -> lea A B C G H I.
Proof.
  intros A B C D E F G H I Hsuma Hisi.
  assert_diffs.
  spliter.
  elim(Col_dec A B C).
  { intro HColB.
    elim(Bet_dec A B C).
    { intro HBBet.
      destruct Hisi as [_[[HEout|]]]; try solve[exfalso; auto].
      apply conga_lea.
      apply (out546_suma__conga _ _ _ D E F); auto.
    }
    intro HBout.
    apply l11_31_1; auto.
    apply not_bet_out; auto.
  }
  intro HNColB.
  elim(Col_dec D E F).
  { intro HColE.
    elim(Bet_dec D E F).
    { intro HEBet.
      apply isi__isi456123 in Hisi.
      destruct Hisi as [_[[HBout|]]]; try solve[exfalso; auto].
      apply l11_31_1; auto.
    }
    intro HEout.
    apply conga_lea.
    apply (out546_suma__conga _ _ _ D E F); auto.
    apply not_bet_out; auto.
  }
  intro HNColE.
  elim(Col_dec G H I).
  { intro HColH.
    elim(Bet_dec G H I).
      apply l11_31_2; auto.
    intro HHout.
    apply not_bet_out in HHout; auto.
    exfalso.
    destruct Hisi as [_ [HUn _]].
    destruct HUn as [HEout | HBNBet].
      apply HNColE; apply col_permutation_4; apply out_col; auto.
    destruct Hsuma as [J [HJ1 [HJ2 HJ3]]].
    apply HJ2.
    apply conga_sym in HJ3.
    apply out_conga_out in HJ3; auto.
    apply (l9_19 _ _ _ _ B); try split; Col.
  }
  intro HNColH.
  destruct Hisi as [_ [_ [J [HJ1 [HJ2 HJ3]]]]].
  assert_diffs.
  assert(HNColJ : ~ Col J B C).
  { intro HColJ.
    apply HNColE.
    apply (col_conga_col J B C); Conga.
  }
  assert(HCongaJ : Conga A B J G H I).
  { apply (suma2__conga A B C D E F); auto.
    exists J.
    repeat (split; Conga).
  }
  assert(HNColJ2 : ~ Col J B A).
  { intro HColJ.
    apply HNColH.
    apply (col_conga_col A B J); Col.
  }
  apply (l11_30 A B C A B J); Conga.
  exists C.
  split; Conga.
  apply not_one_side_two_sides in HJ2; auto.
  destruct HJ2 as [a [b [c [X [HColX HXBet]]]]].
  repeat split; auto.
  exists X.
  split; auto.
  right.
  assert(HNColX : ~Col X A B).
  { intro.
    apply HNColJ2.
    apply col_permutation_1; apply (col_transitivity_1 A X); Col.
    intro; subst X; Col.
  }
  assert_diffs.
  apply (col_one_side_out _ A); Col.
  apply invert_one_side.
  apply (one_side_transitivity _ _ _ J).
  - apply out_one_side.
    left; Col.
    apply bet_out; auto.
  - apply one_side_symmetry.
    apply not_two_sides_one_side; Col.
Qed.

(** DEF <= ABC + DEF. *)

Lemma isi_suma__lea456789 : forall A B C D E F G H I, Suma A B C D E F G H I ->
   Isi A B C D E F -> lea D E F G H I.
Proof.
  intros A B C D E F G H I Hsuma Hisi.
  apply (isi_suma__lea123789 D E F A B C G H I); Suma.
Qed.

(** lea preserves Isi. *)

Lemma isi_lea2__isi : forall A B C D E F A' B' C' D' E' F',
   Isi A' B' C' D' E' F' -> lea A B C A' B' C' -> lea D E F D' E' F' ->
   Isi A B C D E F.
Proof.
  intros A B C D E F A' B' C' D' E' F' Hisi HleaB HleaE.
  assert(HA0 : exists A0, is_midpoint B A A0) by apply symmetric_point_construction.
  destruct HA0 as [A0].
  assert(HA'0 : exists A'0, is_midpoint B' A' A'0) by apply symmetric_point_construction.
  destruct HA'0 as [A'0].
  assert_diffs.
  apply (isi_chara _ _ _ _ _ _ A0); Between.
  apply (lea_trans D E F D' E' F'); auto.
  apply (lea_trans D' E' F' C' B' A'0).
  - apply (isi_chara A'); Between.
  - apply lea_comm.
    apply (l11_36 A B C A'); Between.
Qed.

Lemma isi_lea456_suma2__lea : forall A B C D E F G H I D' E' F' G' H' I',
   lea D E F D' E' F' -> Isi A B C D' E' F' -> Suma A B C D E F G H I ->
   Suma A B C D' E' F' G' H' I' -> lea G H I G' H' I'.
Proof.
  intros A B C D E F G H I D' E' F' G' H' I' Hlea Hisi' Hsuma Hsuma'.
  assert_diffs.
  elim(out_dec E' D' F').
  { intro HE'out.
    apply conga_lea.
    apply (conga_trans _ _ _ A B C).
    apply conga_sym; apply (out546_suma__conga _ _ _ D E F); auto; apply (out_lea__out _ _ _ D' E' F'); auto.
    apply (out546_suma__conga _ _ _ D' E' F'); auto.
  }
  intro HE'Nout.
  elim(Col_dec A B C).
  { intro HColB.
    destruct Hisi' as [_ [[HE'out|HBNBet]_]].
    exfalso; auto.
    apply not_bet_out in HColB; auto.
    apply (l11_30 D E F D' E' F'); auto; apply (out213_suma__conga A B C); auto.
  }
  intro HNColB.
  elim(Col_dec D' E' F').
  { intro HColE'.
    apply isi__isi456123 in Hisi'.
    destruct Hisi' as [_ [[HBout|HE'NBet]_]]; exfalso.
    apply HNColB; assert_cols; Col.
    apply not_bet_out in HColE'; auto.
  }
  intro HNColE'.
  clear HE'Nout.
  elim(Col_dec D E F).
  { intro HColE.
    assert(~ Bet D E F) by (intro; apply HNColE'; apply bet_col; apply (bet_lea__bet D E F); auto).
    apply (l11_30 A B C G' H' I'); try (apply conga_refl); auto.
    apply (isi_suma__lea123789 _ _ _ D' E' F'); auto.
    apply (out546_suma__conga _ _ _ D E F); auto.
    apply not_bet_out; auto.
  }
  intro HNColE.
  elim(Col_dec G' H' I').
  { intro HColH'.
    elim(Bet_dec G' H' I').
    apply l11_31_2; auto.
    intro HH'out.
    apply not_bet_out in HH'out; auto.
    exfalso.
    apply HNColB.
    apply col_permutation_4.
    apply out_col.
    apply (out_lea__out _ _ _ G' H' I'); auto.
    apply (isi_suma__lea123789 _ _ _ D' E' F'); auto.
  }
  intro HNColH'.
  destruct Hisi' as [_[_[F'1]]].
  spliter.
  apply(l11_30 _ _ _ _ _ _ D E F C B F'1) in Hlea; Conga.
  destruct Hlea as [F1].
  spliter.
  assert_diffs.
  assert(Conga A B F'1 G' H' I').
  apply (suma2__conga A B C D' E' F'); auto; exists F'1; repeat (split; Conga).
  assert(~ Col A B F'1) by (apply (ncol_conga_ncol G' H' I'); Conga).
  assert(~ Col C B F'1) by (apply (ncol_conga_ncol D' E' F'); Conga).
  apply (l11_30 A B F1 A B F'1); auto.
  - exists F1.
    split; Conga.
    apply l11_24.
    apply (in_angle_trans _ _ _ C).
    apply l11_24; auto.
    assert(Hts : two_sides B C A F'1) by (apply not_one_side_two_sides; Col).
    destruct Hts as [_ [_ [_ [X]]]].
    spliter.
    repeat split; auto.
    exists X.
    split; Between.
    right.
    apply (col_one_side_out _ A); Col.
    apply invert_one_side.
    apply (one_side_transitivity _ _ _ F'1); auto.
    2: apply one_side_symmetry; apply not_two_sides_one_side; Col.
    apply out_one_side; Col.
    apply bet_out; auto; intro; subst A; Col.

  - apply (suma2__conga A B C D E F); auto.
    exists F1.
    repeat (split; Conga).
    apply l9_9.
    apply l9_2.
    apply (l9_8_2 _ _ F'1).
    apply l9_2; apply not_one_side_two_sides; Col.
    apply invert_one_side; apply one_side_symmetry.
    apply in_angle_one_side; Col.
    apply not_col_permutation_4; apply (ncol_conga_ncol D E F); auto.
Qed.

Lemma isi_lea123_suma2__lea : forall A B C D E F G H I A' B' C' G' H' I',
   lea A B C A' B' C' -> Isi A' B' C' D E F -> Suma A B C D E F G H I -> 
   Suma A' B' C' D E F G' H' I' -> lea G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C'.
  intros.
  apply (isi_lea456_suma2__lea D E F A B C _ _ _ A' B' C'); Suma.
Qed.

(** Suma preserves lea. *)

Lemma isi_lea2_suma2__lea : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lea A B C A' B' C' -> lea D E F D' E' F' -> Isi A' B' C' D' E' F' ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lea G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I' HleaB HleaD Hisi' Hsuma Hsuma'.
  assert_diffs.
  assert(Haux := ex_suma A B C D' E' F').
  destruct Haux as [G'' [H'' [I'']]]; auto.
  apply (lea_trans _ _ _ G'' H'' I'').
  - apply (isi_lea456_suma2__lea A B C D E F _ _ _ D' E' F'); auto.
    apply (isi_lea2__isi _ _ _ _ _ _ A' B' C' D' E' F'); Lea.
  - apply (isi_lea123_suma2__lea A B C D' E' F' _ _ _ A' B' C'); auto.
Qed.

(** Unicity of the difference of angles. *)

Lemma isi2_suma2__conga456 : forall A B C D E F D' E' F' G H I,
   Isi A B C D E F -> Isi A B C D' E' F' ->
   Suma A B C D E F G H I -> Suma A B C D' E' F' G H I ->
   Conga D E F D' E' F'.
Proof.
  intros A B C D E F D' E' F' G H I Hisi Hisi' Hsuma Hsuma'.
  assert_diffs.
  elim(Col_dec A B C).
  { intro HColB.
    elim(Bet_dec A B C).
    { intro HBBet.
      destruct Hisi as [_ [[HEout|]_]]; try solve [exfalso; Between].
      destruct Hisi' as [_ [[HE'out|]_]]; try solve [exfalso; Between].
      apply l11_21_b; auto.
    }
    intro HBout.
    apply not_bet_out in HBout; auto.
    apply (conga_trans _ _ _ G H I).
    - apply (out213_suma__conga A B C); auto.
    - apply conga_sym.
      apply (out213_suma__conga A B C); auto.
  }
  intro HNColB.
  destruct Hisi as [_[_[J [HJ1 [HJ2 HJ3]]]]].
  destruct Hisi' as [_[_[J' [HJ'1 [HJ'2 HJ'3]]]]].
  assert_diffs.
  apply (conga_trans _ _ _ C B J); try solve [apply conga_sym; auto].
  apply (conga_trans _ _ _ C B J'); auto.
  assert(Conga A B J A B J').
  { apply (conga_trans _ _ _ G H I).
    apply (suma2__conga A B C D E F); auto; exists J; Conga.
    apply (suma2__conga A B C D' E' F'); auto; exists J'; Conga.
  }
  assert(HJJ' : out B J J' \/ two_sides A B J J') by (apply l11_22_aux; auto).
  destruct HJJ' as [Hout|Hts].
  - apply (out_conga C B J C B J); try (apply out_trivial); Conga.
  - exfalso.
    apply HJ'3.
    apply (l9_8_2 _ _ J); auto.
    apply one_side_symmetry.
    apply not_two_sides_one_side; Col.
    apply two_sides_not_col in Hts; Col.
Qed.

(** Unicity of the difference on the left. *)

Lemma isi2_suma2__conga123 : forall A B C A' B' C' D E F G H I,
   Isi A B C D E F -> Isi A' B' C' D E F ->
   Suma A B C D E F G H I -> Suma A' B' C' D E F G H I ->
   Conga A B C A' B' C'.
Proof.
  intros A B C A' B' C' D E F G H I Hisi Hisi' Hsuma Hsuma'.
  apply (isi2_suma2__conga456 D E F _ _ _ _ _ _ G H I); Suma.
Qed.

Lemma suma_assoc_1 : forall A B C D E F G H I K L M A' B' C' D' E' F',
   Isi A B C D E F -> Isi D E F G H I ->
   Suma A B C D E F A' B' C' -> Suma D E F G H I D' E' F' ->
   Suma A' B' C' G H I K L M -> Suma A B C D' E' F' K L M.
Proof.
  intros A B C D E F G H I K L M A' B' C' D' E' F' HisiBE HisiEH HsBE HsEH HsB'H.
  assert(HA0 : exists A0, is_midpoint B A A0) by apply symmetric_point_construction.
  destruct HA0 as [A0].
  assert(HD0 : exists D0, is_midpoint E D D0) by apply symmetric_point_construction.
  destruct HD0 as [D0].
  assert_diffs.
  elim(Col_dec A B C).
  { intro HColB.
    elim(Bet_dec A B C).
    { intro HBBet.
      destruct HisiBE as [_ [[HEout | HBNBet] HJ]]; try solve [exfalso; Between].
      apply (conga3_suma__suma A' B' C' G H I K L M); try (apply conga_refl); auto.
      apply conga_sym; apply (out546_suma__conga _ _ _ D E F); auto.
      apply (out213_suma__conga D E F); auto.
    }
    intro HBout.
    apply not_bet_out in HBout; auto.
    assert(Hexsuma : exists K0 L0 M0, Suma A B C D' E' F' K0 L0 M0) by (apply ex_suma; auto).
    destruct Hexsuma as [K0 [L0 [M0]]].
    apply (conga3_suma__suma A B C D' E' F' K0 L0 M0); try (apply conga_refl); auto.
    apply (conga_trans _ _ _ D' E' F').
    apply conga_sym; apply (out213_suma__conga A B C); auto.
    apply (suma2__conga D E F G H I); auto.
    apply (conga3_suma__suma A' B' C' G H I K L M); try (apply conga_refl); auto.
    apply conga_sym.
    apply (out213_suma__conga A B C); auto.
  }
  intro HNColB.
  assert(~ Col C B A0) by (intro; apply HNColB; apply (l6_16_1 _ A0); Col).
  elim(Col_dec D E F).
  { intro HColE.
    elim(Bet_dec D E F).
    { intro HEBet.
      destruct HisiEH as [_ [[HHout | HENBet] HJ]]; try solve [exfalso; Between].
      apply (conga3_suma__suma A B C D E F A' B' C'); try (apply conga_refl); try (apply (out546_suma__conga _ _ _ G H I)); auto.
    }
    intro HEout.
    apply not_bet_out in HEout; auto.
    apply (conga3_suma__suma A' B' C' G H I K L M); try (apply conga_refl); auto.
    apply conga_sym; apply (out546_suma__conga _ _ _ D E F); auto.
    apply (out213_suma__conga D E F); auto.
  }
  intro HNColE.
  assert(~ Col F E D0) by (intro; apply HNColE; apply (l6_16_1 _ D0); Col).
  elim(Col_dec G H I).
  { intro HColH.
    elim(Bet_dec G H I).
    { intro HHBet.
      apply isi__isi456123 in HisiEH.
      destruct HisiEH as [_ [[HEout | HHNBet] HJ]]; try solve [exfalso; Between].
      exfalso.
      apply HNColE.
      apply col_permutation_4.
      apply out_col; auto.
    }
    intro HHout.
    apply not_bet_out in HHout; auto.
    apply (conga3_suma__suma A B C D E F A' B' C'); try (apply conga_refl); try (apply (out546_suma__conga _ _ _ G H I)); auto.
  }
  intro HNColH.
  assert(~ one_side B C A A0).
  { apply l9_9.
    repeat split; Col.
    exists B.
    split; Col; Between.
  }
  assert(HisiA0: Isi A B C A0 B C).
  { split; auto.
    split.
    right; intro; assert_cols; Col.
    exists A0.
    repeat (split; Conga).
    unfold two_sides.
    intro; spliter; assert_cols; Col.
  }
  assert(~ one_side E F D D0).
  { apply l9_9.
    repeat split; Col.
    exists E.
    split; Col; Between.
  }
  assert(HisiD0: Isi D E F D0 E F).
  { split; auto.
    split.
    right; intro; assert_cols; Col.
    exists D0.
    repeat (split; Conga).
    unfold two_sides.
    intro; spliter; assert_cols; Col.
  }
  elim(Col_dec A' B' C').
  { intro HColB'.
    elim(Bet_dec A' B' C').
    { intro HB'Bet.
      elim(Col_dec D' E' F').
      { intro HColE'.
        elim(Bet_dec D' E' F').
        { intro HE'Bet.
          apply suma__suma456123.
          apply (conga3_suma__suma A' B' C' G H I K L M); try (apply conga_refl); auto; try solve [apply conga_line; auto].
          apply conga_sym.
          apply (conga_trans _ _ _ D0 E F).
          - apply (isi2_suma2__conga123 _ _ _ _ _ _ D E F A' B' C'); Suma.
            apply suma__suma456123.
            exists D0.
            split.
            apply conga_pseudo_refl; auto.
            split; auto.
            apply conga_line; Between.
          - apply (isi2_suma2__conga456 D E F _ _ _ _ _ _ D' E' F'); auto.
            exists D0.
            split.
            apply conga_pseudo_refl; auto.
            split; auto.
            apply conga_line; Between.
        }
        intro HE'out.
        apply not_bet_out in HE'out; auto.
        exfalso.
        apply HNColE.
        apply col_permutation_4.
        apply out_col.
        apply (out_lea__out _ _ _ D' E' F'); auto.
        apply (isi_suma__lea123789 _ _ _ G H I); auto.
      }
      intro HNColE'.
      assert(Conga D E F C B A0).
      { apply (isi2_suma2__conga456 A B C _ _ _ _ _ _ A' B' C'); auto.
        apply (isi_chara _ _ _ _ _ _ A0); try (apply lea_refl); Between.
        apply (conga3_suma__suma A B C C B A0 A B A0); try (apply conga_refl); try (apply conga_line); Between.
        exists A0.
        repeat (split; Conga).
      }
      assert(HJ : Isi C B A0 G H I) by (apply (conga2_isi__isi D E F G H I); try (apply conga_refl); auto).
      destruct HJ as [_ [_ [J]]].
      destruct HisiEH as [_ [_ [F1]]].
      spliter.
      assert_diffs.
      assert(Conga C B J D' E' F').
      { apply (conga_trans _ _ _ D E F1); auto.
        - apply (l11_22 _ _ _ A0 _ _ _ F); auto.
          split.
          left; split; apply not_one_side_two_sides; auto; apply (ncol_conga_ncol G H I); Conga.
          split.
          { apply (isi2_suma2__conga456 A B C _ _ _ _ _ _ A' B' C'); auto.
            apply (isi_chara _ _ _ _ _ _ A0); try (apply lea_refl); Between.
            apply (conga3_suma__suma A B C C B A0 A B A0); try (apply conga_refl); try (apply conga_line); Between.
            exists A0.
            repeat (split; Conga).
          }
          apply (conga_trans _ _ _ G H I); auto.
          apply conga_sym; auto.

        - apply (suma2__conga D E F G H I); auto.
          exists F1.
          repeat (split; Conga).
      }
      apply (conga3_suma__suma A B C D' E' F' A B J); try (apply conga_refl); auto.
      { exists J.
        split.
        { apply (suma2__conga C B A0 G H I).
          exists J; repeat (split; Conga).
          apply (conga3_suma__suma D E F G H I D' E' F'); Conga.
        }
        split; Conga.
        apply l9_9.
        apply invert_two_sides; apply l9_2.
        apply (l9_8_2 _ _ A0).
        repeat split; Col; exists B; split; Col; Between.
        apply not_two_sides_one_side; Col.
        apply not_col_permutation_2.
        apply (ncol_conga_ncol D' E' F'); Conga.
      }
      apply (suma2__conga A' B' C' G H I); auto.
      apply (conga3_suma__suma A B A0 A0 B J A B J); try (apply conga_refl); auto; try (apply conga_line); Between.
      exists J.
      repeat (split; Conga).
      apply col123__nos; Col.
    }
    intro HB'out.
    apply not_bet_out in HB'out; auto.
    exfalso.
    apply HNColB.
    apply col_permutation_4.
    apply out_col.
    apply (out_lea__out _ _ _ A' B' C'); auto.
    apply (isi_suma__lea123789 _ _ _ D E F); auto.
  }
  intro HNColB'.
  clear dependent A0.
  destruct HisiBE as [_ [_ [C1 HC1]]].
  spliter.
  assert_diffs.
  assert(Conga A' B' C' A B C1).
  { apply (suma2__conga A B C D E F); auto.
    apply (conga3_suma__suma A B C C B C1 A B C1); Conga.
    exists C1.
    repeat (split; Conga).
  }
  assert(one_side B C1 C A).
  { apply one_side_symmetry.
    apply os_ts1324__os.
    - apply invert_one_side.
      apply not_two_sides_one_side; Col.
      apply not_col_permutation_2; apply (ncol_conga_ncol A' B' C'); auto.
    - apply not_one_side_two_sides; Col.
      apply (ncol_conga_ncol D E F); Conga.
  }
  elim(Col_dec D' E' F').
  { intro HColE'.
    elim(Bet_dec D' E' F').
    { intro HE'Bet.
      assert(HC0 : exists C0, is_midpoint B C C0) by apply symmetric_point_construction.
      destruct HC0 as [C0].
      spliter.
      assert_diffs.
      assert(two_sides B C1 C C0).
      { repeat split; auto.
        apply (ncol_conga_ncol D E F); Conga.
        intro; apply HNColE; apply (col_conga_col C B C1); Conga; apply (l6_16_1 _ C0); Col.
        exists B.
        split; Col; Between.
      }
      apply (conga3_suma__suma A B C C B C0 A B C0); try (apply conga_refl); auto.
        exists C0; repeat (split; Conga); apply col124__nos; Col.
        apply conga_line; Between.
      apply (suma2__conga A' B' C' G H I); auto.
      apply (conga3_suma__suma A B C1 C1 B C0 A B C0); try (apply conga_refl); try solve [apply conga_sym; auto]; auto.
      exists C0; repeat (split; Conga); apply l9_9; apply (l9_8_2 _ _ C); auto.
      apply (isi2_suma2__conga456 C B C1 _ _ _ _ _ _ C B C0); auto.
        apply (isi_chara _ _ _ _ _ _ C0); try (apply lea_refl); Between.
        apply (conga2_isi__isi D E F G H I); Conga.
        exists C0; repeat (split; Conga); apply l9_9; auto.
      apply (conga3_suma__suma D E F G H I D' E' F'); try (apply conga_refl); try (apply conga_sym); auto.
      apply conga_line; Between.
    }
    intro HE'out.
    apply not_bet_out in HE'out; auto.
    exfalso.
    apply HNColE.
    apply col_permutation_4.
    apply out_col.
    apply (out_lea__out _ _ _ D' E' F'); auto.
    apply (isi_suma__lea123789 _ _ _ G H I); auto.
  }
  intro HNColE'.
  clear dependent D0.
  assert(HJ : Isi C B C1 G H I) by (apply (conga2_isi__isi D E F G H I); Conga).
  destruct HJ as [_ [_ [J]]].
  destruct HisiEH as [_ [_ [F1 HF1]]].
  spliter.
  assert_diffs.
  assert(Conga C B J D' E' F').
  { apply (conga_trans _ _ _ D E F1); auto.
    - apply (l11_22 _ _ _ C1 _ _ _ F); auto.
      split.
      left; split; apply not_one_side_two_sides; auto; try solve [apply (ncol_conga_ncol G H I); Conga]; apply (ncol_conga_ncol D E F); Conga.
      split. 
      Conga.
      apply (conga_trans _ _ _ G H I); Conga.

    - apply (suma2__conga D E F G H I); auto.
      exists F1.
      repeat (split; Conga).
  }
  apply (conga3_suma__suma A B C C B J A B J); try (apply conga_refl); auto.
  - exists J.
    repeat (split; Conga).
    apply l9_9.
    apply l9_2.
    apply (l9_8_2 _ _ C1).
    apply l9_2; apply not_one_side_two_sides; auto; apply (ncol_conga_ncol D E F); Conga.
    apply invert_one_side.
    apply not_two_sides_one_side; auto; apply not_col_permutation_2.
    apply (ncol_conga_ncol D E F); Conga.
    apply (ncol_conga_ncol D' E' F'); Conga.

  - apply (suma2__conga A' B' C' G H I); auto.
    apply (conga3_suma__suma A B C1 C1 B J A B J); Conga.
    exists J.
    repeat (split; Conga).
    apply l9_9.
    apply (l9_8_2 _ _ C); auto.
    apply not_one_side_two_sides; auto.
    apply (ncol_conga_ncol D E F); Conga.
    apply (ncol_conga_ncol G H I); Conga.
Qed.

Lemma suma_assoc_2 : forall A B C D E F G H I K L M A' B' C' D' E' F',
   Isi A B C D E F -> Isi D E F G H I ->
   Suma A B C D E F A' B' C' -> Suma D E F G H I D' E' F' ->
   Suma A B C D' E' F' K L M -> Suma A' B' C' G H I K L M.
Proof.
  intros A B C D E F G H I K L M A' B' C' D' E' F'.
  intros.
  apply suma__suma456123.
  apply (suma_assoc_1 G H I D E F A B C K L M D' E' F'); Suma.
Qed.

(** Associativity of sum of angles. *)

Lemma suma_assoc : forall A B C D E F G H I K L M A' B' C' D' E' F',
   Isi A B C D E F -> Isi D E F G H I ->
   Suma A B C D E F A' B' C' -> Suma D E F G H I D' E' F' ->
   (Suma A' B' C' G H I K L M <-> Suma A B C D' E' F' K L M).
Proof.
  intros A B C D E F G H I K L M A' B' C' D' E' F'.
  intros.
  split.
    apply (suma_assoc_1 _ _ _ D E F); auto.
    apply (suma_assoc_2 _ _ _ D E F); auto.
Qed.

Lemma isi_assoc_1 : forall A B C D E F G H I A' B' C' D' E' F',
   Isi A B C D E F -> Isi D E F G H I ->
   Suma A B C D E F A' B' C' -> Suma D E F G H I D' E' F' ->
   Isi A' B' C' G H I -> Isi A B C D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' Hisi1 Hisi2 Hs1 Hs2 Hisi1'.
  assert_diffs.
  elim(Col_dec A B C).
  { intro HColB.
    destruct Hisi1 as [_ [[HEout|HBout]_]].
    - apply (conga2_isi__isi A' B' C' G H I); auto.
      apply conga_sym; apply (out546_suma__conga _ _ _ D E F); auto.
      apply (out213_suma__conga D E F); auto.

    - apply not_bet_out in HBout; auto.
      apply isi__isi456123.
      repeat split; auto.
      exists F'.
      split.
      apply l11_21_b; try (apply out_trivial); auto.     
      split.
      apply col124__nos; Col.
      apply not_two_sides_id.
  }
  intro HNColB.
  elim(Col_dec D E F).
  { intro HColE.
    destruct Hisi2 as [_ [[HHout|HEout]_]].
    - apply (conga2_isi__isi A B C D E F); try (apply conga_refl); auto.
      apply (out546_suma__conga _ _ _ G H I); auto.

    - apply not_bet_out in HEout; auto.
      apply (conga2_isi__isi A' B' C' G H I); auto.
      apply conga_sym; apply (out546_suma__conga _ _ _ D E F); auto.
      apply (out213_suma__conga D E F); auto.
  }
  intro HNColE.
  elim(Col_dec G H I).
  { intro HColH.
    apply isi__isi456123 in Hisi2.
    destruct Hisi2 as [_ [[HEout|HHout]_]].
    exfalso; assert_cols; Col.
    apply not_bet_out in HHout; auto.
    apply (conga2_isi__isi A B C D E F); try (apply conga_refl); auto.
    apply (out546_suma__conga _ _ _ G H I); auto.
  }
  intro HNColH.
  split; auto.
  split.
  right; intro; assert_cols; Col.
  assert(~ Col A' B' C').
  { intro.
    exfalso.
    destruct Hisi1' as [_ [[|HB'out]_]].
    assert_cols; Col.
    apply not_bet_out in HB'out; auto.
    apply HNColB.
    apply col_permutation_4.
    apply out_col.
    apply (out_lea__out _ _ _ A' B' C'); auto.
    apply (isi_suma__lea123789 _ _ _ D E F); auto.
  }
  assert(HC1 : exists C1, Conga C B C1 D E F /\ ~ one_side B C A C1 /\ ~ two_sides A B C C1) by (destruct Hisi1 as [_ []]; auto).
  destruct HC1 as [C1].
  spliter.
  assert_diffs.
  assert(Conga A B C1 A' B' C') by (apply (suma2__conga A B C D E F); auto; exists C1; repeat (split; Conga)).
  assert(HJ :exists J, Conga C1 B J G H I /\ ~ one_side B C1 C J /\ ~ two_sides C B C1 J).
  { apply (conga2_isi__isi _ _ _ _ _ _ C B C1 G H I) in Hisi2; Conga.
    destruct Hisi2 as [_ [_ HJ]]; auto.
  }
  destruct HJ as [J [HJ1 [HJ2 HJ3]]].
  spliter.
  apply (conga2_isi__isi _ _ _ _ _ _ A B C1 C1 B J) in Hisi1'; Conga.
  destruct Hisi1' as [_ [_ [J']]].
  spliter.
  assert_diffs.
  assert (HUn : out B J' J \/ two_sides C1 B J' J) by (apply l11_22_aux; auto).
  destruct HUn as [HJJ'|Hts].
  { exists J.
    split.
    2:split.
    - apply (suma2__conga D E F G H I); auto.
      apply (conga3_suma__suma C B C1 C1 B J C B J); try (apply conga_refl); auto.
      exists J.
      repeat (split; Conga).

    - elim(Col_dec C B J).
      intro; apply col124__nos; Col.
      intro.
      apply l9_9.
      apply l9_2.
      apply (l9_8_2 _ _ C1).
      apply l9_2; apply not_one_side_two_sides; Col; apply (ncol_conga_ncol D E F); Conga.
      apply invert_one_side.
      apply not_two_sides_one_side; Col.
      apply not_col_permutation_2; apply (ncol_conga_ncol D E F); Conga.

    - elim(Col_dec A B J).
      intro; intro Hts; destruct Hts; spliter; Col.
      intro.
      apply l9_9_bis.
      apply (one_side_transitivity _ _ _ C1).
      apply not_two_sides_one_side; Col; apply not_col_permutation_2; apply (ncol_conga_ncol A' B' C'); Conga.
      apply (one_side_transitivity _ _ _ J').
      2: apply invert_one_side; apply out_one_side; Col.
      apply not_two_sides_one_side; auto.
      apply not_col_permutation_2; apply (ncol_conga_ncol A' B' C'); Conga.
      apply not_col_permutation_2; apply (ncol_conga_ncol A B J); auto.
      apply (out_conga A B J' A B J'); try (apply out_trivial); try (apply conga_refl); auto.
  }
  exfalso.
  apply l9_2 in Hts.
  apply invert_two_sides in Hts.
  apply HJ2.
  exists J'.
  split; auto.
  apply (l9_8_2 _ _ A).
  - apply not_one_side_two_sides; auto.
    apply (ncol_conga_ncol A' B' C'); Conga.
    apply (ncol_conga_ncol G H I); auto.
    apply (conga_trans _ _ _ C1 B J); Conga.
  - apply os_ts1324__os.
    apply invert_one_side; apply not_two_sides_one_side; Col; apply not_col_permutation_2; apply (ncol_conga_ncol A' B' C'); Conga.
    apply not_one_side_two_sides; Col; apply (ncol_conga_ncol D E F); Conga.
Qed.

Lemma isi_assoc_2 : forall A B C D E F G H I A' B' C' D' E' F',
   Isi A B C D E F -> Isi D E F G H I ->
   Suma A B C D E F A' B' C' -> Suma D E F G H I D' E' F' ->
   Isi A B C D' E' F' -> Isi A' B' C' G H I.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F'.
  intros.
  apply isi__isi456123.
  apply (isi_assoc_1 G H I D E F A B C D' E' F'); Suma.
Qed.

Lemma isi_assoc : forall A B C D E F G H I A' B' C' D' E' F',
   Isi A B C D E F -> Isi D E F G H I ->
   Suma A B C D E F A' B' C' -> Suma D E F G H I D' E' F' ->
   (Isi A' B' C' G H I <-> Isi A B C D' E' F').
Proof.
  intros A B C D E F.
  split.
  apply (isi_assoc_1 _ _ _ D E F); auto.
  apply (isi_assoc_2 _ _ _ D E F); auto.
Qed.

Lemma isi_lea2_suma2__conga123 : forall A B C D E F G H I A' B' C' D' E' F',
   lea A B C A' B' C' -> lea D E F D' E' F' -> Isi A' B' C' D' E' F' ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G H I -> Conga A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' HleaB HleaE Hisi' Hsuma Hsuma'.
  assert_diffs.
  apply (isi2_suma2__conga123 _ _ _ _ _ _ D E F G H I); auto.
    apply (isi_lea2__isi _ _ _ _ _ _ A' B' C' D' E' F'); auto.
    apply (isi_lea2__isi _ _ _ _ _ _ A' B' C' D' E' F'); Lea.
  assert (Haux := ex_suma A' B' C' D E F).
  destruct Haux as [G' [H' [I']]]; auto.
  apply (conga3_suma__suma A' B' C' D E F G' H' I'); try (apply conga_refl); auto.
  apply lea_asym.
  apply (isi_lea456_suma2__lea A' B' C' D E F _ _ _ D' E' F'); auto.
  apply (isi_lea123_suma2__lea A B C D E F _ _ _ A' B' C'); auto.
  apply (isi_lea2__isi _ _ _ _ _ _ A' B' C' D' E' F'); Lea.
Qed.

Lemma isi_lea2_suma2__conga456 : forall A B C D E F G H I A' B' C' D' E' F',
   lea A B C A' B' C' -> lea D E F D' E' F' -> Isi A' B' C' D' E' F' ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G H I -> Conga D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F'.
  intros.
  apply (isi_lea2_suma2__conga123 _ _ _ A B C G H I _ _ _ A' B' C'); Suma.
Qed.

Lemma isi_lea_lta123_suma2__lta : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lta A B C A' B' C' -> lea D E F D' E' F' -> Isi A' B' C' D' E' F' ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lta G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I' HltaB HleaE Hisi' Hsuma Hsuma'.
  assert_diffs.
  split.
  apply (isi_lea2_suma2__lea A B C D E F _ _ _ A' B' C' D' E' F'); Lea.
  intro.
  destruct HltaB as [HleaB HNConga].
  apply HNConga.
  apply (isi_lea2_suma2__conga123 _ _ _ D E F G H I _ _ _ D' E' F'); auto.
  apply (conga3_suma__suma A' B' C' D' E' F' G' H' I'); Conga.
Qed.

Lemma isi_lea_lta456_suma2__lta : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lea A B C A' B' C' -> lta D E F D' E' F' -> Isi A' B' C' D' E' F' ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lta G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (isi_lea_lta123_suma2__lta D E F A B C _ _ _ D' E' F' A' B' C'); Suma.
Qed.

Lemma isi_lta2_suma2__lta : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lta A B C A' B' C' -> lta D E F D' E' F' -> Isi A' B' C' D' E' F' ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lta G H I G' H' I'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (isi_lea_lta123_suma2__lta A B C D E F _ _ _ A' B' C' D' E' F'); auto.
  apply lta__lea; auto.
Qed.

Lemma isi_lea2_suma2__lea123 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lea D' E' F' D E F -> lea G H I G' H' I' -> Isi A B C D E F ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lea A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  assert_diffs.
  elim(lta_dec A' B' C' A B C).
  2: intro; apply nlta__lea; auto.
  intro Hlta.
  exfalso.
  assert(~ lea G H I G' H' I'); auto.
  apply lta__nlea.
  apply(isi_lea_lta123_suma2__lta A' B' C' D' E' F' _ _ _ A B C D E F); auto.
Qed.

Lemma isi_lea2_suma2__lea456 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lea A' B' C' A B C -> lea G H I G' H' I' -> Isi A B C D E F ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lea D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (isi_lea2_suma2__lea123 _ _ _ A B C G H I _ _ _ A' B' C' G' H' I'); try (apply suma__suma456123); auto.
  apply isi__isi456123; assumption.
Qed.

Lemma isi_lea_lta456_suma2__lta123 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lta D' E' F' D E F -> lea G H I G' H' I' -> Isi A B C D E F ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lta A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  assert_diffs.
  elim(lea_dec A' B' C' A B C).
  2: intro; apply nlea__lta; auto.
  intro Hlea.
  exfalso.
  assert(~ lea G H I G' H' I'); auto.
  apply lta__nlea.
  apply(isi_lea_lta456_suma2__lta A' B' C' D' E' F' _ _ _ A B C D E F); auto.
Qed.

Lemma isi_lea_lta123_suma2__lta456 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lta A' B' C' A B C -> lea G H I G' H' I' -> Isi A B C D E F ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lta D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (isi_lea_lta456_suma2__lta123 _ _ _ A B C G H I _ _ _ A' B' C' G' H' I'); try (apply suma__suma456123); auto.
  apply isi__isi456123; assumption.
Qed.

Lemma isi_lea_lta789_suma2__lta123 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lea D' E' F' D E F -> lta G H I G' H' I' -> Isi A B C D E F ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lta A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  assert_diffs.
  elim(lea_dec A' B' C' A B C).
  2: intro; apply nlea__lta; auto.
  intro Hlta.
  exfalso.
  assert(~ lta G H I G' H' I'); auto.
  apply lea__nlta.
  apply(isi_lea2_suma2__lea A' B' C' D' E' F' _ _ _ A B C D E F); auto.
Qed.

Lemma isi_lea_lta789_suma2__lta456 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lea A' B' C' A B C -> lta G H I G' H' I' -> Isi A B C D E F ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lta D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (isi_lea_lta789_suma2__lta123 _ _ _ A B C G H I _ _ _ A' B' C' G' H' I'); try (apply suma__suma456123); auto.
  apply isi__isi456123; assumption.
Qed.

Lemma isi_lta2_suma2__lta123 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lta D' E' F' D E F -> lta G H I G' H' I' -> Isi A B C D E F ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lta A B C A' B' C'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (isi_lea_lta789_suma2__lta123 _ _ _ D E F G H I _ _ _ D' E' F' G' H' I'); auto.
  apply lta__lea; assumption.
Qed.

Lemma isi_lta2_suma2__lta456 : forall A B C D E F G H I A' B' C' D' E' F' G' H' I',
   lta A' B' C' A B C -> lta G H I G' H' I' -> Isi A B C D E F ->
   Suma A B C D E F G H I -> Suma A' B' C' D' E' F' G' H' I' -> lta D E F D' E' F'.
Proof.
  intros A B C D E F G H I A' B' C' D' E' F' G' H' I'.
  intros.
  apply (isi_lea_lta789_suma2__lta456 A B C _ _ _ G H I A' B' C' _ _ _ G' H' I'); auto.
  apply lta__lea; assumption.
Qed.


Lemma isi123231 : forall A B C, A <> B -> A <> C -> B <> C -> Isi A B C B C A.
Proof.
  intros A B C.
  intros.
  assert(HA' := symmetric_point_construction A B).
  destruct HA' as [A'].
  assert_diffs.
  apply (isi_chara _ _ _ _ _ _ A'); Between.
  elim(Col_dec A B C).
  { intro HCol.
    elim(Bet_dec A C B).
    { intro HCBet.
      apply conga_lea.
      apply conga_line; Between.
      apply (between_exchange3 A); Between.
    }
    intro.
    apply l11_31_1; auto.
    apply l6_6.
    apply not_bet_out; Col.
  }
  intro.
  apply lta__lea.
  apply l11_41_aux; Col; Between.
Qed.

(** Sum of two right angles is a flat angle:
  90+90=180.
 *)

Lemma per2_suma__bet : forall A B C D E F G H I, Per A B C -> Per D E F ->
   Suma A B C D E F G H I -> Bet G H I.
Proof.
  intros A B C D E F G H I HBRight HERight HSuma.
  destruct HSuma as [A1 [HConga1 [HNos HConga2]]].
  assert_diffs.
  assert(Per A1 B C) by (apply (l11_17 D E F); Conga).
  apply (bet_conga_bet A B A1); auto.
  apply (col_two_sides_bet _ C).
  apply col_permutation_2; apply (per_per_col _ _ C); auto.
  apply not_one_side_two_sides; auto; apply per_not_col; auto.
Qed.

(** If 90+x=180 then x=90. *)

Lemma bet_per_suma__per456 : forall A B C D E F G H I, Per A B C -> Bet G H I ->
   Suma A B C D E F G H I -> Per D E F.
Proof.
  intros A B C D E F G H I HPer HBet HSuma.
  assert(HA1 := symmetric_point_construction A B).
  destruct HA1 as [A1].
  assert_diffs.
  assert(~ Col A B C) by (apply per_not_col; auto).
  apply (l11_17 A B C); auto.
  apply (isi2_suma2__conga456 A B C _ _ _ _ _ _ G H I); auto.
  - apply (isi_chara _ _ _ _ _ _ A1); Between.
    apply conga_lea.
    apply conga_left_comm.
    apply l11_18_1; Between; Perp.

  - destruct HSuma as [F1 [HConga1 [HNos HConga2]]].
    repeat split; auto.
    right; intro; assert_cols; Col.
    exists F1.
    repeat (split; auto).
    intro Habs.
    destruct Habs as [_ [_ [Habs _]]].
    apply Habs.
    apply col_permutation_2.
    apply bet_col.
    apply (bet_conga_bet G H I); Conga.

  - assert(HSuma' := ex_suma A B C A B C).
    destruct HSuma' as [G' [H' [I']]]; auto.
    assert_diffs.
    apply (conga3_suma__suma A B C A B C G' H' I'); try (apply conga_refl); auto.
    apply conga_line; auto.
    apply (per2_suma__bet A B C A B C); auto.
Qed.

(** If x+90=180 then x=90. *)

Lemma bet_per_suma__per123 : forall A B C D E F G H I, Per D E F -> Bet G H I ->
   Suma A B C D E F G H I -> Per A B C.
Proof.
  intros A B C D E F G H I HPer HBet HSuma.
  apply (bet_per_suma__per456 D E F _ _ _ G H I); Suma.
Qed.

(** If x+x=180 then x=90. *)

Lemma bet_suma__per : forall A B C D E F, Bet D E F -> Suma A B C A B C D E F ->
   Per A B C.
Proof.
  intros A B C D E F HBet HSuma.
  assert_diffs.
  destruct HSuma as [A' [HConga1 [_ HConga2]]].
  apply l8_2.
  apply (l11_18_2 _ _ _ A'); Conga.
  apply (bet_conga_bet D E F); Conga.
Qed.

(** If x<90 then x+x<180 (two lemmas). *)

Lemma acute__isi : forall A B C, acute A B C -> Isi A B C A B C.
Proof.
  intros A B C Hacute.
  assert(HA' := symmetric_point_construction A B).
  destruct HA' as [A'].
  assert_diffs.
  apply (isi_chara _ _ _ _ _ _ A'); Between.
  apply lea_acute_obtuse; auto.
  apply obtuse_sym.
  apply (bet_acute__obtuse A); Between.
Qed.

Lemma acute_suma__nbet : forall A B C D E F, acute A B C -> Suma A B C A B C D E F -> ~ Bet D E F.
Proof.
  intros A B C D E F Hacute HSuma.
  assert_diffs.
  intro.
  apply (nlta A B C).
  apply acute_per__lta; auto.
  apply (bet_suma__per _ _ _ D E F); auto.
Qed.

(** If x>90 then x+x>180. *)

Lemma obtuse__nisi : forall A B C, obtuse A B C -> ~ Isi A B C A B C.
Proof.
  intros A B C Hobtuse.
  assert(HA' := symmetric_point_construction A B).
  destruct HA' as [A'].
  assert_diffs.
  intro.
  apply (nlta A B C).
  apply (lea123456_lta__lta _ _ _ A' B C).
  - apply lea_right_comm.
    apply (isi_chara A); Between.
  - apply acute_obtuse__lta; auto.
    apply (bet_obtuse__acute A); Between.
Qed.

(** If x+x<180 then x<90. *)

Lemma nbet_isi_suma__acute : forall A B C D E F, ~ Bet D E F -> Isi A B C A B C ->
   Suma A B C A B C D E F -> acute A B C.
Proof.
  intros A B C D E F HNBet HIsi HSuma.
  assert_diffs.
  elim(angle_partition A B C); auto.
  intro HUn.
  exfalso.
  destruct HUn.
  - apply HNBet.
    apply (per2_suma__bet A B C A B C); auto.
  - assert(~ Isi A B C A B C); auto.
    apply obtuse__nisi; auto.
Qed.

(** If x+x>180 then x>90. *)

Lemma nisi__obtuse : forall A B C, A <> B -> B <> C -> ~ Isi A B C A B C -> obtuse A B C.
Proof.
  intros A B C HAB HBC HNIsi.
  elim(angle_partition A B C); auto.
  - intro.
    exfalso.
    apply HNIsi.
    apply acute__isi; auto.

  - intro HUn.
    destruct HUn; auto.
    exfalso.
    apply HNIsi.
    assert(HA' := symmetric_point_construction A B).
    assert(HNCol : ~ Col A B C) by (apply per_not_col; auto).
    destruct HA' as [A'].
    assert_diffs.
    repeat split; auto.
    right; intro; Col.
    exists A'.
    split.
      apply conga_right_comm; apply conga_sym; apply l11_18_1; Between; Perp.
    split.
    2: intro Hts; destruct Hts as [_ [_ []]]; assert_cols; Col.
    apply l9_9.
    repeat split; Col.
    intro; apply HNCol; ColR.
    exists B; Col; Between.
Qed.


(** The sum of angles of a triangle.*)

Definition Trisuma A B C D E F:= exists G H I, Suma A B C B C A G H I /\ Suma G H I C A B D E F.

Lemma trisuma_perm_231 : forall A B C D E F, Trisuma A B C D E F -> Trisuma B C A D E F.
Proof.
  intros A B C D E F HT.
  destruct HT as [A1 [B1 [C1 [HT1 HT2]]]].
  assert_diffs.
  assert(Hex:= ex_suma B C A C A B).
  destruct Hex as [B2 [C2 [A2 Hex]]]; auto.
  exists B2.
  exists C2.
  exists A2.
  split; auto.
  apply suma__suma456123.
  apply (suma_assoc A B C B C A C A B D E F A1 B1 C1 B2 C2 A2); try (apply isi123231); auto.
Qed.

Lemma trisuma_perm_312 : forall A B C D E F, Trisuma A B C D E F -> Trisuma C A B D E F.
Proof.
  intros.
  do 2 apply trisuma_perm_231.
  assumption.
Qed.

Lemma trisuma_perm_321 : forall A B C D E F, Trisuma A B C D E F -> Trisuma C B A D E F.
Proof.
  intros A B C D E F HT.
  destruct HT as [A1 [B1 [C1 [HT1 HT2]]]].
  apply suma__suma456123 in HT2.
  assert_diffs.
  assert(Hex:= ex_suma C A B A B C).
  destruct Hex as [C2 [A2 [B2 Hex]]]; auto.
  exists C2.
  exists A2.
  exists B2.
  split.
  Suma.
  apply suma__suma123654789.
  apply (suma_assoc C A B A B C B C A D E F C2 A2 B2 A1 B1 C1); try (apply isi123231); auto.
Qed.

Lemma trisuma_perm_213 : forall A B C D E F, Trisuma A B C D E F -> Trisuma B A C D E F.
Proof.
  intros.
  apply trisuma_perm_321.
  apply trisuma_perm_312.
  assumption.
Qed.

Lemma trisuma_perm_132 : forall A B C D E F, Trisuma A B C D E F -> Trisuma A C B D E F.
Proof.
  intros.
  apply trisuma_perm_321.
  apply trisuma_perm_231.
  assumption.
Qed.

Lemma col_trisuma__bet : forall A B C P Q R, Col A B C -> Trisuma A B C P Q R -> Bet P Q R.
Proof.
  intros A B C P Q R HCol HTri.
  destruct HTri as [D [E [F []]]].
  assert_diffs.
  destruct HCol as [|[|]].
  - apply (bet_conga_bet A B C); auto.
    apply (conga_trans _ _ _ D E F).
    apply (out546_suma__conga _ _ _ B C A); try (apply bet_out); Between.
    apply (out546_suma__conga _ _ _ C A B); try (apply l6_6; apply bet_out); auto.
  - apply (bet_conga_bet B C A); auto.
    apply (conga_trans _ _ _ D E F).
    apply (out213_suma__conga A B C); try (apply l6_6; apply bet_out); auto.
    apply (out546_suma__conga _ _ _ C A B); try (apply bet_out); Between.
  - apply (bet_conga_bet C A B); auto.
    apply (out213_suma__conga D E F); auto.
    apply (out_conga_out B C A); try (apply l6_6; apply bet_out); auto.
    apply (out213_suma__conga A B C); try (apply bet_out); Between.
Qed.

Lemma suma_dec : forall A B C D E F G H I, Suma A B C D E F G H I \/ ~ Suma A B C D E F G H I.
Proof.
  intros A B C D E F G H I.
  elim(eq_dec_points A B).
    intro; subst; right; intro; assert_diffs; auto.
  intro.
  elim(eq_dec_points C B).
    intro; subst; right; intro; assert_diffs; auto.
  intro.
  elim(eq_dec_points D E).
    intro; subst; right; intro; assert_diffs; auto.
  intro.
  elim(eq_dec_points F E).
    intro; subst; right; intro; assert_diffs; auto.
  intro.
  assert(HSuma := ex_suma A B C D E F).
  destruct HSuma as [G' [H' [I']]]; auto.
  elim(conga_dec G H I G' H' I').
  - intro.
    left.
    apply (conga3_suma__suma A B C D E F G' H' I'); Conga.
  - intro HNConga.
    right.
    intro.
    apply HNConga.
    apply (suma2__conga A B C D E F); auto.
Qed.

Lemma isi_dec : forall A B C D E F, Isi A B C D E F \/ ~ Isi A B C D E F.
Proof.
  intros A B C D E F.
  elim(eq_dec_points A B).
    intro; subst; right; intro; assert_diffs; auto.
  intro.
  assert(HA' := symmetric_point_construction A B).
  destruct HA' as [A'].
  assert_diffs.
  elim(lea_dec D E F C B A').
  - intro.
    left.
    apply (isi_chara _ _ _ _ _ _ A'); Between.
  - intro HNlea.
    right.
    intro.
    apply HNlea.
    apply (isi_chara A); Between.
Qed.

End Sec2.

Hint Resolve isi123231 : suma.