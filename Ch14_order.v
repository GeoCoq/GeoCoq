Require Export Ch14_prod.

Section Order.

Context `{MT:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

Definition Ps O E A := out O A E.

Lemma l14_36_a :
 forall O E E' A B C,
 sum O E E' A B C ->
 out O A B ->
 Bet O A C.
Proof.
    intros.
    assert(HS:=H).
    unfold sum in H.
    spliter.
    unfold Ar2 in H.
    unfold out in H0.
    spliter.
    assert(Parallelogram_flat O A C B).
      apply(sum_cong O E E' H A B C HS).
      tauto.
    assert(Parallelogram O A C B).
      right.
      auto.
    induction(eq_dec_points A B).
      subst B.
      unfold Parallelogram_flat in H7.
      spliter.
      assert(O = C \/ is_midpoint A O C).
        apply(l7_20 A O C).
          ColR.
        Cong.
      induction H13.
        subst C.
        apply False_ind.
        apply HS.
        apply (double_null_null O E E') in HS; auto.
        tauto.
      unfold is_midpoint in H13.
      tauto.
    induction H3.
      apply plg_permut in H8.
      apply plg_permut in H8.
      apply plg_permut in H8.
      assert(Bet A B C).
        apply between_symmetry.
        apply(plg_bet1 B O A C).
          assumption.
        apply between_symmetry.
        assumption.
      apply (outer_transitivity_between O A B C); auto.
    assert(Bet B A C).
      apply between_symmetry.
      apply(plg_bet1 A O B C).
        apply plg_comm2.
        assumption.
      apply between_symmetry.
      assumption.
    apply (outer_transitivity_between2 O B A C); auto.
Qed.



Lemma l14_36_b :
 forall O E E' A B C,
 sum O E E' A B C ->
 out O A B -> O <> A /\ O <> C /\ A <> C.
Proof.
    intros.
    assert(HH:= l14_36_a O E E' A B C H H0).
    unfold out in H0.
    spliter.
    split; auto.
    split.
      intro.
      subst C.
      apply between_identity in HH.
      subst A.
      tauto.
    intro.
    subst C.
    assert(HS:= H).
    unfold sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    assert(is_sum O E E' A O A).
      apply (sum_0_r); Col.
    unfold is_sum in H7.
    spliter.
    induction H7.
      assert(B = O).
        apply (sum_unicityB O E E' H A B O A); auto.
      contradiction.
    spliter.
    contradiction.
Qed.

(** Lemma 14.37 *)

Lemma O_not_positive :
 forall O E,
 ~ Ps O E O.
Proof.
    intros.
    unfold Ps.
    unfold out.
    intuition.
Qed.

Lemma opp_midpoint :
 forall O E E' A MA,
 opp O E E' A MA ->
 is_midpoint O A MA.
Proof.
    intros.
    unfold opp in H.
    assert(HS:=H).
    unfold sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    induction (eq_dec_points A O).
      subst A.
      assert(HH:= sum_A_O_eq O E E' H MA O HS).
      subst MA.
      unfold is_midpoint.
      split; Cong.
      apply between_trivial.
    assert(Parallelogram_flat O MA O A).
      apply(sum_cong O E E' H MA A O HS).
      tauto.
    unfold Parallelogram_flat in H5.
    spliter.
    assert(A = MA \/ is_midpoint O A MA).
      apply(l7_20 O A MA).
        Col.
      Cong.
    induction H10.
      subst MA.
      tauto.
    assumption.
Qed.

Lemma pos_null_neg :
 forall O E E' A MA,
 opp O E E' A MA ->
 Ps O E A \/ O = A \/ Ps O E MA.
Proof.
    intros.
    unfold opp in H.
    induction (eq_dec_points A O).
      right; left; auto.
    assert(HS:= H).
    unfold sum in H.
    spliter.
    unfold Ar2 in H.
    spliter.
    assert(Parallelogram_flat O MA O A).
      apply(sum_cong O E E' H MA A O HS); tauto.
    unfold Parallelogram_flat in H5.
    spliter.
    assert(HG:=grid_not_par O E E' H).
    spliter.
    assert(A = MA \/ is_midpoint O A MA).
      apply(l7_20 O A MA); try ColR.
      Cong.
    induction H16.
      subst MA.
      tauto.
    induction(out_dec O E A).
      left.
      unfold Ps.
      apply l6_6.
      assumption.
    right; right.
    assert(MA <> O).
      intro.
      subst MA.
      apply is_midpoint_id_2 in H16.
      subst A.
      tauto.
    unfold is_midpoint in H16.
    spliter.
    unfold Ps.
    unfold Col in H2.
    induction H2.
      unfold out.
      repeat split; auto.
    induction H2.
      unfold out.
      repeat split; Col.
      left.
      apply between_symmetry.
      auto.
    apply False_ind.
    apply H17.
    unfold out.
    repeat split; auto.
    apply between_symmetry in H16.
    assert(HH:= l5_2 MA O A E H18 H16 H2).
    tauto.
Qed.


Lemma sum_pos_pos :
 forall O E E' A B AB,
 Ps O E A ->
 Ps O E B ->
 sum O E E' A B AB ->
 Ps O E AB.
Proof.
    intros.
    unfold Ps in *.
    assert(out O A B).
      apply l6_6 in H0.
      apply(l6_7 O A E B); auto.
    assert(HH:=l14_36_b O E E' A B AB H1 H2).
    spliter.
    assert(HH:=l14_36_a O E E' A B AB H1 H2).
    apply l6_6 in H.
    assert(out O A AB).
      apply bet_out; auto.
    assert(HP:=l6_7 O E A AB H H6).
    apply l6_6.
    assumption.
Qed.

Lemma prod_pos_pos :
 forall O E E' A B AB,
 Ps O E A ->
 Ps O E B ->
 prod O E E' A B AB ->
 Ps O E AB.
Proof.
    intros.
    assert(HP:= H1).
    unfold prod in H1.
    spliter.
    unfold Ar2 in H1.
    spliter.
    ex_and H2 B'.
    assert(HG:= grid_not_par O E E' H1).
    spliter.
    unfold Ps in H.
    unfold Ps in H0.
    unfold out in *.
    spliter.
    assert(E' <> A).
      intro.
      subst A.
      contradiction.
    assert(~Col O E' A).
      intro.
      apply H1.
      ColR.
    assert(~Par O E E' A).
      intro.
      induction H20.
        apply H20.
        exists A.
        split; Col.
      spliter.
      contradiction.
    assert(project E E' O E' E E').
      apply(pj_col_project); Col.
      left; right.
      repeat split; Col.
    assert(project B B' O E' E E').
      apply(pj_col_project); Col.
    assert(project O O O E' E E').
      apply(pj_col_project); Col.
      right.
      auto.
    assert(project E' A O E E' A).
      apply(pj_col_project); Col.
      left; right.
      repeat split; Col.
    assert(project B' AB O E E' A).
      apply(pj_col_project); Col.
    assert(project O O O E E' A).
      apply(pj_col_project); Col.
      right.
      auto.
    assert(AB <> O).
      intro.
      subst AB.
      apply prod_null in HP.
      induction HP; contradiction.
    unfold Ps.
    repeat split; auto.
    induction H15.
      assert(Bet O B' E').
        apply(project_preserves_bet O E' E E' O B E O B' E'); auto.
      assert(Bet O AB A).
        apply(project_preserves_bet O E E' A O B' E' O AB A); auto.
      induction H17.
        left.
        apply(between_exchange4 _ _ A); auto.
      apply(l5_3 O AB E A); auto.
    assert(Bet O E' B').
      apply(project_preserves_bet O E' E E' O E B O E' B'); auto.
    assert(Bet O A AB).
      apply(project_preserves_bet O E E' A O E' B' O A AB); auto.
    induction H17.
      assert(Bet O E AB \/ Bet O AB E).
        apply(l5_1 O A E AB); auto.
      tauto.
    right.
    apply (between_exchange4 O E A AB); auto.
Qed.


Definition Ng O E A := A <> O /\ E <> O /\ Bet A O E .

Lemma pos_not_neg : forall O E A, Ps O E A -> ~Ng O E A.
Proof.
    intros.
    intro.
    unfold Ps in H.
    unfold Ng in H0.
    unfold out in H.
    spliter.
    induction H4.
      apply H.
      apply (between_egality _ _ E); Between.
    apply H1.
    apply (between_egality _ _ A); Between.
Qed.

Lemma neg_not_pos : forall O E A, Ng O E A -> ~Ps O E A.
Proof.
    intros.
    intro.
    unfold Ps in H0.
    unfold Ng in H.
    unfold out in H0.
    spliter.
    induction H2.
      apply H0.
      apply (between_egality _ _ E); Between.
    apply H1.
    apply (between_egality _ _ A); Between.
Qed.

Lemma opp_pos_neg : forall O E E' A MA, Ps O E A ->  opp O E E' A MA -> Ng O E MA.
Proof.
    intros.
    assert(HH:=opp_midpoint O E E' A MA H0).
    unfold Ng.
    unfold Ps in H.
    unfold out in H.
    unfold is_midpoint in HH.
    spliter.
    repeat split; auto.
      intro.
      subst MA.
      apply cong_identity in H2.
      contradiction.
    induction H4.
      apply(outer_transitivity_between MA O A E); Between.
    apply(between_inner_transitivity MA O E A); Between.
Qed.

Lemma opp_neg_pos : forall O E E' A MA, Ng O E A ->  opp O E E' A MA -> Ps O E MA.
Proof.
    intros.
    assert(HH:=opp_midpoint O E E' A MA H0).
    unfold Ng in H.
    unfold Ps.
    unfold is_midpoint in HH.
    spliter.
    apply l6_6.
    unfold out.
    repeat split; auto.
      intro.
      subst MA.
      apply cong_identity in H2.
      contradiction.
    apply (l5_2 A O E MA); auto.
Qed.



(** Definition 14.38. *)
(** Definition of the substraction. *)


Definition diff O E E' A B AMB :=
  exists MB, opp O E E' B MB /\ sum O E E' A MB AMB.

Lemma diff_ar2 : forall O E E' A B AMB, diff O E E' A B AMB -> Ar2 O E E' A B AMB.
Proof.
    intros.
    unfold diff in H.
    ex_and H MA.
    unfold opp in H.
    unfold sum in *.
    spliter.
    unfold Ar2 in *.
    spliter.
    repeat split; auto.
Qed.


Lemma diff_null : forall O E E' A, ~Col O E E' -> Col O E A -> diff O E E' A A O.
Proof.
    intros.
    unfold diff.
    assert(Hop:=opp_exists O E E' H A H0).
    ex_and Hop MB.
    exists MB.
    split; auto.
    unfold opp in H1.
    apply sum_comm; auto.
Qed.

Lemma diff_exists : forall O E E' A B, ~Col O E E' -> Col O E A -> Col O E B ->  exists D, diff O E E' A B D.
Proof.
    intros.
    assert(Hop:=opp_exists O E E' H B H1).
    ex_and Hop MB.
    assert(Col O E MB).
      unfold opp in H2.
      unfold sum in H2.
      spliter.
      unfold Ar2 in H2.
      tauto.
    assert(HS:=sum_exists O E E' H A MB H0 H3).
    ex_and HS C.
    exists C.
    unfold diff.
    exists MB.
    split; assumption.
Qed.


Lemma diff_unicity : forall O E E' A B D1 D2, diff O E E' A B D1 -> diff O E E' A B D2 -> D1 = D2.
Proof.
    intros.
    assert(Ar2 O E E' A B D1).
      apply (diff_ar2); assumption.
    unfold Ar2 in H1.
    spliter.
    unfold diff in *.
    ex_and H MB1.
    ex_and H0 MB2.
    assert(MB1 = MB2).
      apply (opp_unicity O E E' H1 B); assumption.
    subst MB2.
    apply(sum_unicity O E E'  A MB1); assumption.
Qed.

(*
Definition ltP O E E' A B :=
 forall D, diff O E E' B A D -> Ps O E D.
*)

Definition ltP O E E' A B :=
 exists D, diff O E E' B A D /\ Ps O E D.

Lemma ltP_ar2 : forall O E E' A B, ltP O E E' A B -> Ar2 O E E' A B A.
Proof.
    intros.
    unfold ltP in H.
    ex_and H D.
    apply diff_ar2 in H.
    unfold Ar2 in H.
    spliter.
    repeat split; auto.
Qed.

Lemma ltP_neq : forall O E E' A B, ltP O E E' A B -> A <> B.
Proof.
    intros.
    assert(HH:=ltP_ar2 O E E' A B H).
    unfold Ar2 in HH.
    spliter.
    unfold ltP in H.
    intro.
    subst B.
    ex_and H OO.
    assert(OO=O).
      apply (diff_unicity O E E' A A).
        assumption.
      apply diff_null; Col.
    subst OO.
    unfold Ps in H4.
    unfold out in H4.
    tauto.
Qed.

Lemma sum_ar2 : forall O E E' A B C, sum O E E' A B C -> Ar2 O E E' A B C.
Proof.
    intros.
    unfold sum in H.
    tauto.
Qed.

Definition leP O E E' A B :=
 ltP O E E' A B \/ A=B.


Lemma leP_refl : forall O E E' A, leP O E E' A A.
Proof.
    intros.
    right.
    tauto.
Qed.

Lemma diff_A_O : forall O E E' A, ~Col O E E' -> Col O E A ->  diff O E E' A O A.
Proof.
    intros.
    unfold diff.
    exists O.
    split.
      unfold opp.
      apply sum_O_O; auto.
    apply sum_A_O;auto.
Qed.

Lemma diff_O_A : forall O E E' A mA, ~Col O E E' -> Col O E A -> Col O E mA
                                     -> opp O E E' A mA -> diff O E E' O A mA.
Proof.
    intros.
    unfold diff.
    exists mA.
    split.
      assumption.
    apply sum_O_B; auto.
Qed.

Lemma diff_O_A_opp : forall O E E' A mA, diff O E E' O A mA -> opp O E E' A mA.
Proof.
    intros.
    assert(Ar2 O E E' O A mA).
      apply diff_ar2;auto.
    unfold diff in H.
    ex_and H A'.
    assert(Ar2 O E E' O A' mA).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    assert(sum O E E' O A' A').
      apply (sum_O_B); auto.
    assert(mA = A').
      apply(sum_unicity O E E' O A'); auto.
    subst A'.
    assumption.
Qed.

Lemma diff_unicityA : forall O E E' A A' B C, diff O E E' A B C -> diff O E E' A' B C -> A = A'.
Proof.
    intros.
    assert(Ar2 O E E' A B C).
      apply diff_ar2; auto.
    assert(Ar2 O E E' A' B C).
      apply diff_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    unfold diff in *.
    ex_and H mB.
    ex_and H0 mB'.
    assert(mB = mB').
      apply(opp_unicity O E E' H1 B); auto.
    subst mB'.
    apply (sum_unicityA O E E' H1 mB A A' C); auto.
Qed.

Lemma diff_unicityB : forall O E E' A B B' C, diff O E E' A B C -> diff O E E' A B' C -> B = B'.
Proof.
    intros.
    assert(Ar2 O E E' A B C).
      apply diff_ar2; auto.
    assert(Ar2 O E E' A B' C).
      apply diff_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    unfold diff in *.
    ex_and H mB.
    ex_and H0 mB'.
    assert(mB = mB').
      apply (sum_unicityA O E E' H1 A mB mB' C); apply sum_comm; auto.
    subst mB'.
    apply (opp_unicity O E E' H1 mB); apply opp_comm; auto.
Qed.


Lemma diff_null_eq : forall O E E' A B, diff O E E' A B O -> A = B.
Proof.
    intros.
    assert(Ar2 O E E' A B O).
      apply diff_ar2; auto.
    unfold Ar2 in H0.
    spliter.
    clear H3.
    assert(diff O E E' A A O).
      apply diff_null; Col.
    apply (diff_unicityB O E E' A _ _ O); auto.
Qed.

Lemma midpoint_opp: forall O E E' A B, Ar2 O E E' O A B -> is_midpoint O A B -> opp O E E' A B.
Proof.
    intros.
    unfold Ar2.
    unfold Ar2 in H.
    spliter.
    clear H1.
    unfold is_midpoint in H0.
    spliter.
    induction (eq_dec_points A B).
      subst B.
      apply between_identity in H0.
      subst A.
      apply opp0; auto.
    unfold opp.
    apply cong_sum; auto.
      unfold Ar2.
      repeat split; Col.
      Cong.
    Cong.
Qed.

Lemma sum_diff : forall O E E' A B S, sum O E E' A B S -> diff O E E' S A B.
Proof.
    intros.
    assert(Ar2 O E E' A B S).
      apply sum_ar2; auto.
    unfold Ar2 in H0.
    spliter.
    assert(HH:=opp_exists O E E' H0 A H1).
    ex_and HH mA.
    exists mA.
    split; auto.
    unfold opp in H4.
    assert(Ar2 O E E' mA A O).
      apply sum_ar2; auto.
    unfold Ar2 in H5.
    spliter.
    clean_duplicated_hyps.
    clear H8.
    induction(eq_dec_points A O).
      subst A.
      assert(B = S).
        apply (sum_unicity O E E' O B); auto.
        apply sum_O_B; auto.
      subst S.
      assert(mA = O).
        apply (sum_unicity O E E' mA O); auto.
        apply sum_A_O; auto.
      subst mA.
      apply sum_A_O; auto.
    induction(eq_dec_points B O).
      subst B.
      assert(A = S).
        apply (sum_unicity O E E' A O); auto.
        apply sum_A_O; auto.
      subst S.
      apply sum_comm; auto.
    apply sum_cong in H; auto.
    apply sum_cong in H4; auto.
    assert(E <> O).
      intro.
      subst E.
      apply H0.
      Col.
    assert(Parallelogram O mA B S \/ O = mA /\ O = A /\ S = B /\ O = S).
      apply(plg_pseudo_trans O mA O A S B); auto.
        right; auto.
      right; auto.
    induction H9.
      induction H9.
        apply False_ind.
        unfold Parallelogram_strict in H9.
        spliter.
        unfold two_sides in H9.
        spliter.
        apply H13.
        ColR.
      unfold Parallelogram_flat in H.
      unfold Parallelogram_flat in H4.
      unfold Parallelogram_flat in H9.
      spliter.
      apply cong_sum; auto.
        repeat split; Col.
        eCong.
      Cong.
    spliter.
    subst A.
    tauto.
Qed.


Lemma diff_sum : forall O E E' A B S, diff O E E' S A B -> sum O E E' A B S.
Proof.
    intros.
    assert(Ar2 O E E' S A B).
      apply diff_ar2; auto.
    unfold Ar2 in H0.
    spliter.
    induction(eq_dec_points A O).
      subst A.
      assert(HH:=diff_A_O O E E' S H0 H1).
      assert(S = B).
        apply (diff_unicity O E E' S O); auto.
      subst B.
      apply sum_O_B; auto.
    unfold diff in H.
    ex_and H mA.
    assert(mA <> O).
      intro.
      subst mA.
      assert(HH:=opp0 O E E' H0).
      apply H4.
      apply (opp_unicity O E E' H0 O); auto.
      apply opp_comm; auto.
    unfold opp in H.
    induction(eq_dec_points S O).
      subst S.
      assert(mA = B).
        apply (sum_O_B_eq O E E'); auto.
      subst mA.
      apply sum_comm; auto.
    apply sum_cong in H; auto.
    apply sum_cong in H5; auto.
    assert(E <> O).
      intro.
      subst E.
      apply H0.
      Col.
    assert(Parallelogram O A S B \/ O = A /\ O = mA /\ B = S /\ O = B).
      apply(plg_pseudo_trans O A O mA B S).
        apply plg_permut.
        apply plg_permut.
        right.
        assumption.
      apply plg_comm2.
      apply plg_permut.
      apply plg_permut.
      apply plg_permut.
      right.
      auto.
    induction H9.
      induction H9.
        apply False_ind.
        unfold Parallelogram_strict in H9.
        spliter.
        unfold two_sides in H9.
        spliter.
        apply H12.
        ColR.
      unfold Parallelogram_flat in H.
      unfold Parallelogram_flat in H5.
      unfold Parallelogram_flat in H9.
      spliter.
      apply cong_sum; Cong.
      repeat split; Col.
    spliter.
    subst A.
    tauto.
Qed.

Lemma ltP_sum_pos : forall O E E' A B C , Ps O E B -> sum O E E' A B C -> ltP O E E' A C.
Proof.
    intros.
    unfold ltP.
    exists B.
    split; auto.
    apply sum_diff in H0.
    assumption.
Qed.


Lemma diff_opp : forall O E E' A B AmB BmA, diff O E E' A B AmB -> diff O E E' B A BmA
                                            -> opp O E E' AmB BmA.
Proof.
    intros.
    assert(Ar2 O E E' A B AmB).
      apply diff_ar2; auto.
    assert(Ar2 O E E' B A BmA).
      apply diff_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    apply diff_sum in H.
    apply diff_sum in H0.
    induction(eq_dec_points A O).
      subst A.
      assert(BmA = B).
        apply(sum_O_B_eq O E E'); auto.
      subst BmA.
      unfold opp.
      assumption.
    induction(eq_dec_points B O).
      subst B.
      assert(AmB = A).
        apply(sum_O_B_eq O E E'); auto.
      subst AmB.
      unfold opp.
      apply sum_comm; auto.
    apply sum_cong in H0; auto.
    apply sum_cong in H; auto.
    assert(Parallelogram A O BmA B).
      apply plg_comm2.
      right.
      assumption.
    apply plg_permut in H4.
    apply plg_permut in H4.
    apply plg_permut in H4.
    assert(Parallelogram AmB O BmA O \/ AmB = O /\ B = A /\ O = BmA /\ AmB = O).
      apply(plg_pseudo_trans AmB O  B A O BmA).
        apply plg_permut.
        apply plg_permut.
        apply plg_permut.
        right; assumption.
      assumption.
    assert(E <> O).
      intro.
      subst E.
      apply H1.
      Col.
    induction H9.
      induction H9.
        apply False_ind.
        unfold Parallelogram_strict in H9.
        unfold two_sides in H9.
        spliter.
        apply H13.
        ColR.
      unfold Parallelogram_flat in H.
      unfold Parallelogram_flat in H0.
      unfold Parallelogram_flat in H9.
      spliter.
      unfold opp.
      apply cong_sum; Cong.
        right.
        intro.
        subst BmA.
        tauto.
      repeat split; Col.
    spliter.
    subst AmB.
    subst BmA.
    unfold opp.
    apply sum_O_O; auto.
Qed.

Lemma pos_opp_neg : forall O E E' A mA, Ps O E A -> opp O E E' A mA -> Ng O E mA.
Proof.
    intros.
    assert(Ar2 O E E' mA A O).
      unfold opp in H0.
      apply sum_ar2; auto.
    unfold Ar2 in H1.
    apply opp_midpoint in H0.
    unfold is_midpoint in H0.
    unfold Ps in H.
    unfold out in H.
    spliter.
    unfold Ng.
    repeat split.
      intro.
      subst mA.
      apply H.
      apply cong_identity in H5.
      assumption.
      auto.
    induction H7.
      apply(outer_transitivity_between mA O A E); Between.
    apply between_symmetry.
    apply(between_exchange3 A E O mA); Between.
Qed.


Lemma diff_pos_diff_neg : forall O E E' A B AmB BmA,
                                     diff O E E' A B AmB
                                  -> diff O E E' B A BmA
                                  -> Ps O E AmB
                                  -> Ng O E BmA.
Proof.
    intros.
    assert(opp O E E' AmB BmA).
      apply (diff_opp O E E' A B); auto.
    eapply (pos_opp_neg O E E' AmB); auto.
Qed.


Lemma not_pos_and_neg : forall O E A, ~(Ps O E A /\ Ng O E A).
Proof.
    intros.
    intro.
    spliter.
    unfold Ps in H.
    unfold Ng in H0.
    unfold out in H.
    spliter.
    clean_duplicated_hyps.
    induction H4.
      apply H.
      apply (between_egality _  _ E); Between.
    apply H3.
    apply (between_egality _  _ A); Between.
Qed.

Lemma leP_asym : forall O E E' A B, leP O E E' A B -> leP O E E' B A -> A = B.
Proof.
    intros.
    unfold leP in *.
    induction H; induction H0.
      unfold ltP in *.
      ex_and H BmA.
      ex_and H0 AmB.
      assert(HH:=diff_pos_diff_neg O E E' A B AmB BmA H0 H H2).
      assert(HT:=diff_pos_diff_neg O E E' B A BmA AmB  H H0 H1).
      apply False_ind.
      assert(HN:=not_pos_and_neg O E AmB).
      apply HN.
      split; auto.
      auto.
      auto.
    auto.
Qed.

Lemma sum_stable : forall O E E' A B C S1 S2 , A = B -> sum O E E' A C S1 -> sum O E E' B C S2 -> S1 = S2.
Proof.
    intros.
    subst B.
    apply (sum_unicity O E E' A C); auto.
Qed.

Lemma diff_stable : forall O E E' A B C D1 D2 , A = B -> diff O E E' A C D1 -> diff O E E' B C D2 -> D1 = D2.
Proof.
    intros.
    subst B.
    apply(diff_unicity O E E' A C); auto.
Qed.

Lemma plg_to_sum : forall O E E' A B C, Ar2 O E E' A B C ->Parallelogram_flat O A C B -> sum O E E' A B C.
Proof.
    intros.
    induction(eq_dec_points A B).
      subst B.
      unfold Parallelogram_flat in H0.
      spliter.
      assert(O = C \/ is_midpoint A O C).
        apply(l7_20 A O C H0).
        Cong.
      induction H5.
        subst C.
        tauto.
      apply cong_sum; auto.
        unfold Ar2 in H.
        tauto.
        unfold is_midpoint in H5.
        tauto.
      unfold is_midpoint in H5.
      tauto.
    unfold Ar2 in H.
    unfold Parallelogram_flat in H0.
    spliter.
    apply cong_sum; auto.
      repeat split; auto.
      Cong.
    Cong.
Qed.

Lemma diff_to_plg : forall O E E' A B dBA, A <> O \/ B <> O -> diff O E E' B A dBA -> Parallelogram_flat O A B dBA.
Proof.
    intros.
    assert(Ar2 O E E' B A dBA).
      apply diff_ar2; auto.
    unfold Ar2 in H1.
    spliter.
    apply diff_sum in H0.
    induction(eq_dec_points A O).
      subst A.
      assert(dBA = B).
        apply(sum_O_B_eq O E E'); auto.
      subst dBA.
      apply plgf_permut.
      apply plgf_trivial.
      induction H; tauto.
    assert(E <> O).
      intro.
      subst E.
      apply H1.
      Col.
    induction(eq_dec_points B O).
      subst B.
      assert(opp O E E' dBA A).
        unfold opp.
        auto.
      apply opp_midpoint in H7.
      unfold is_midpoint in H7.
      spliter.
      unfold Parallelogram_flat.
      repeat split; try ColR.
        Cong.
        Cong.
      right.
      intro.
      subst dBA.
      apply between_identity in H7.
      contradiction.
    apply sum_cong in H0; auto.
Qed.

Definition sum3 O E E' A B C S := exists AB, sum O E E' A B AB /\ sum O E E' AB C S.

Lemma sum3_col : forall O E E' A B C S, sum3 O E E' A B C S -> ~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E S.
Proof.
    intros.
    unfold sum3 in H.
    ex_and H AB.
    assert(Ar2 O E E' A B AB).
      apply sum_ar2; auto.
    assert(Ar2 O E E' AB C S).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    repeat split; auto.
Qed.

Lemma sum3_permut : forall O E E' A B C S, sum3 O E E' A B C S -> sum3 O E E' C A B S.
Proof.
    intros.
    assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E S).
      apply sum3_col; auto.
    spliter.
    unfold sum3 in H.
    ex_and H AB.
    assert(HH:= sum_exists O E E' H0 A C H1 H3).
    ex_and HH AC.
    unfold sum3.
    exists AC.
    split.
      apply sum_comm; auto.
    apply sum_comm in H5; auto.
    apply sum_comm in H6; auto.
    assert(HH:=sum_assoc O E E' C A B AC AB S H6 H).
    destruct HH.
    apply H7; auto.
Qed.

Lemma sum3_comm_1_2 : forall O E E' A B C S, sum3 O E E' A B C S -> sum3 O E E' B A C S.
Proof.
    intros.
    assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E S).
      apply sum3_col; auto.
    spliter.
    unfold sum3 in H.
    ex_and H AB.
    unfold sum3.
    exists AB.
    split.
      apply sum_comm; auto.
    auto.
Qed.

Lemma sum3_comm_2_3 : forall O E E' A B C S, sum3 O E E' A B C S -> sum3 O E E' A C B S.
Proof.
    intros.
    apply sum3_permut in H.
    apply sum3_comm_1_2 in H.
    assumption.
Qed.

Lemma sum3_exists : forall O E E' A B C, Ar2 O E E' A B C -> exists S, sum3 O E E' A B C S.
Proof.
    intros.
    unfold Ar2 in *.
    spliter.
    assert(HH:=sum_exists O E E' H A B H0 H1).
    ex_and HH AB.
    assert(Ar2 O E E' A B AB).
      apply sum_ar2; auto.
    unfold Ar2 in H4.
    spliter.
    clean_duplicated_hyps.
    assert(HH:=sum_exists O E E' H AB C H7 H2).
    ex_and HH ABC.
    exists ABC.
    unfold sum3.
    exists AB.
    split; auto.
Qed.

Lemma sum3_unicity : forall O E E' A B C S1 S2, sum3 O E E' A B C S1 -> sum3 O E E' A B C S2 -> S1 = S2.
Proof.
    intros.
    unfold sum3 in H.
    unfold sum3 in H0.
    ex_and H AB1.
    ex_and H0 AB2.
    assert(AB1 = AB2).
      apply(sum_unicity O E E' A B); auto.
    subst AB2.
    apply (sum_unicity O E E' AB1 C); auto.
Qed.


Definition sum4 O E E' A B C D S := exists ABC, sum3 O E E' A B C ABC /\ sum O E E' ABC D S.

Definition sum22 O E E' A B C D S := exists AB, exists CD, sum O E E' A B AB /\ sum O E E' C D CD /\ sum O E E' AB CD S.

Lemma sum4_col : forall O E E' A B C D S, sum4 O E E' A B C D S ->  ~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S.
Proof.
    intros.
    unfold sum4 in H.
    ex_and H ABC.
    assert(HH:=sum3_col O E E' A B C ABC H).
    assert(Ar2 O E E' ABC D S).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    repeat split; auto.
Qed.

Lemma sum22_col : forall O E E' A B C D S, sum22 O E E' A B C D S ->  ~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S.
Proof.
    intros.
    unfold sum22 in H.
    ex_and H AB.
    ex_and H0 CD.
    assert(Ar2 O E E' A B AB).
      apply sum_ar2; auto.
    assert(Ar2 O E E' C D CD).
      apply sum_ar2; auto.
    assert(Ar2 O E E' AB CD S).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    repeat split; auto.
Qed.


Lemma sum_to_sum3 : forall O E E' A B AB X S, sum O E E' A B AB -> sum O E E' AB X S -> sum3 O E E' A B X S.
Proof.
    intros.
    unfold sum3.
    exists AB.
    split; auto.
Qed.

Lemma sum3_to_sum4 : forall O E E' A B C X ABC S , sum3 O E E' A B C ABC -> sum O E E' ABC X S -> sum4 O E E' A B C X S.
Proof.
    intros.
    assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E ABC).
      apply sum3_col; auto.
    assert(Ar2 O E E' ABC X S).
      apply sum_ar2; auto.
    unfold Ar2 in H2.
    spliter.
    clean_duplicated_hyps.
    unfold sum4.
    exists ABC.
    split; auto.
Qed.

Lemma sum_A_exists : forall O E E' A AB, Ar2 O E E' A AB O -> exists B, sum O E E' A B AB.
Proof.
    intros.
    unfold Ar2 in *.
    spliter.
    assert(HH:=diff_exists O E E' AB A H H1 H0).
    ex_and HH B.
    exists B.
    apply diff_sum in H3.
    assumption.
Qed.

Lemma sum_B_exists : forall O E E' B AB, Ar2 O E E' B AB O -> exists A, sum O E E' A B AB.
Proof.
    intros.
    unfold Ar2 in *.
    spliter.
    assert(HH:=diff_exists O E E' AB B H H1 H0).
    ex_and HH A.
    exists A.
    apply diff_sum in H3.
    apply sum_comm; auto.
Qed.

Lemma sum4_equiv : forall O E E' A B C D S, sum4 O E E' A B C D S <-> sum22 O E E' A B C D S.
Proof.
    intros.
    split.
      intro.
      assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S).
        apply sum4_col; auto.
      spliter.
      assert(HS1:= sum_exists O E E' H0 A B H1 H2).
      assert(HS2:= sum_exists O E E' H0 C D H3 H4).
      ex_and HS1 AB.
      ex_and HS2 CD.
      unfold sum22.
      exists AB.
      exists CD.
      assert(Ar2 O E E' A B AB).
        apply sum_ar2; auto.
      assert(Ar2 O E E' C D CD).
        apply sum_ar2; auto.
      unfold Ar2 in *.
      spliter.
      clean_duplicated_hyps.
      split; auto.
      split; auto.
      unfold sum4 in H.
      ex_and H ABC.
      unfold sum3 in H.
      ex_and H AB'.
      assert(AB' = AB).
        apply(sum_unicity O E E' A B); auto.
      subst AB'.
      assert(HH:= sum_assoc O E E' AB C D ABC CD S H9 H7).
      destruct HH.
      apply H11.
      assumption.
    intro.
    unfold sum22 in H.
    ex_and H AB.
    ex_and H0 CD.
    assert(Ar2 O E E' A B AB).
      apply sum_ar2; auto.
    assert(Ar2 O E E' C D CD).
      apply sum_ar2; auto.
    assert(Ar2 O E E' AB CD S).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    unfold sum4.
    assert(HS:=sum_exists O E E' H2 AB C H13 H8).
    ex_and HS ABC.
    exists ABC.
    split.
      unfold sum3.
      exists AB.
      split; auto.
    assert(HH:= sum_assoc O E E' AB C D ABC CD S H3 H0).
    destruct HH.
    apply H4.
    assumption.
Qed.

Lemma sum4_permut: forall O E E' A B C D S, sum4 O E E' A B C D S -> sum4 O E E' D A B C S.
Proof.
    intros.
    assert( ~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S).
      apply sum4_col; auto.
    spliter.
    assert(HH:=sum4_equiv O E E' A B C D S).
    destruct HH.
    assert(sum22 O E E' A B C D S).
      apply H6; auto.
    unfold sum22 in H8.
    ex_and H8 AB.
    ex_and H9 CD.
    apply sum_comm in H9; auto.
    apply sum_comm in H10; auto.
    unfold sum4 in H.
    ex_and H ABC.
    assert(HH:= sum_assoc O E E' D C AB CD ABC S H9).
    assert(HP:=sum3_permut O E E' A B C ABC H).
    unfold sum3 in HP.
    ex_and HP AC.
    assert(HP:= sum_assoc O E E' C A B AC AB ABC H12 H8).
    destruct HP.
    assert(sum O E E' C AB ABC).
      apply H15; auto.
    apply HH in H16.
    destruct H16.
    assert(sum O E E' D ABC S).
      apply H17; auto.
    assert(HP:= sum_exists O E E' H0 D A H4 H1); auto.
    ex_and HP AD.
    assert(Ar2 O E E' D A AD).
      apply sum_ar2; auto.
    unfold Ar2 in H20.
    spliter.
    clean_trivial_hyps.
    assert(HP:= sum_exists O E E' H0 AD B H23 H2); auto.
    ex_and HP ABD.
    assert(HP:= sum_assoc O E E' D A B  AD AB ABD H19 H8).
    destruct HP.
    apply H26 in H24.
    unfold sum4.
    exists ABD.
    split.
      unfold sum3.
      exists AD.
      split; auto.
    unfold sum3 in H.
    ex_and H AB'.
    assert(AB'=AB).
      apply (sum_unicity O E E' A B); auto.
    subst AB'.
    assert(HP:= sum_assoc O E E' D AB C ABD ABC S H24 H27).
    destruct HP.
    apply H28.
    auto.
Qed.

(* a + b + c + d = d + a + b + c *)

Lemma sum22_permut : forall O E E' A B C D S, sum22 O E E' A B C D S -> sum22 O E E' D A B C S.
Proof.
    intros.
    assert(HH:= sum4_equiv O E E' A B C D S).
    destruct HH.
    assert(sum4 O E E' A B C D S).
      apply H1; auto.
    assert(sum4 O E E' D A B C S).
      apply sum4_permut; auto.
    assert(HH:= sum4_equiv O E E' D A B C S).
    destruct HH.
    apply H4.
    auto.
Qed.

Lemma sum4_comm : forall O E E' A B C D S, sum4 O E E' A B C D S -> sum4 O E E' B A C D S.
Proof.
    intros.
    assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S).
      apply sum4_col; auto.
    spliter.
    assert(HH:= sum4_equiv O E E' A B C D S).
    destruct HH.
    apply H6 in H.
    unfold sum22 in H.
    ex_and H AB.
    ex_and H8 CD.
    apply sum_comm in H; auto.
    assert(sum22 O E E' B A C D S).
      unfold sum22.
      exists AB.
      exists CD.
      split; auto.
    assert(HH:= sum4_equiv O E E'  B A C D S).
    destruct HH.
    apply H12; auto.
Qed.

(* a + b + c + d = b + a + c + d *)

Lemma sum22_comm : forall O E E' A B C D S, sum22 O E E' A B C D S -> sum22 O E E' B A C D S.
Proof.
    intros.
    assert(~Col O E E' /\ Col O E A /\ Col O E B /\ Col O E C /\ Col O E D /\ Col O E S).
      apply sum22_col; auto.
    spliter.
    unfold sum22 in H.
    ex_and H AB.
    ex_and H6 CD.
    unfold sum22.
    exists AB.
    exists CD.
    split; auto.
    apply sum_comm; auto.
Qed.

(* a + b + c + d = b  c + a + d *)

Lemma sum_abcd : forall O E E' A B C D AB CD BC AD S, sum O E E' A B AB -> sum O E E' C D CD
                                                   -> sum O E E' B C BC -> sum O E E' A D AD
                                                   -> sum O E E' AB CD S -> sum O E E' BC AD S.
Proof.
    intros.
    assert(Ar2 O E E' A B AB).
      apply sum_ar2;auto.
    assert(Ar2 O E E' C D CD).
      apply sum_ar2;auto.
    assert(Ar2 O E E' B C BC).
      apply sum_ar2;auto.
    assert(Ar2 O E E' A D AD).
      apply sum_ar2;auto.
    assert(Ar2 O E E' AB CD S).
      apply sum_ar2;auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    assert(sum22 O E E' A B C D S).
      unfold sum22.
      exists AB.
      exists CD.
      split; auto.
    apply sum22_permut in H5.
    unfold sum22 in H5.
    ex_and H5 AD'.
    ex_and H6 BC'.
    assert(AD' = AD).
      apply sum_comm in H2; auto.
      apply (sum_unicity O E E' D A); auto.
    subst AD'.
    assert(BC' = BC).
      apply (sum_unicity O E E' B C); auto.
    subst BC'.
    apply sum_comm; auto.
Qed.

(* (b - a) + (c - b) = (c - a) *)

Lemma sum_diff_diff_a : forall O E E' A B C dBA dCB dCA,
                         diff O E E' B A dBA
                      -> diff O E E' C B dCB
                      -> diff O E E' C A dCA
                      -> sum O E E' dCB dBA dCA.
Proof.
    intros.
    assert(Ar2 O E E' B A dBA).
      apply diff_ar2; auto.
    assert(Ar2 O E E' C B dCB).
      apply diff_ar2; auto.
    assert(Ar2 O E E' C A dCA).
      apply diff_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    unfold diff in H.
    ex_and H mA.
    unfold diff in H0.
    ex_and H0 mB.
    unfold diff in H1.
    ex_and H1 mA'.
    assert(mA' = mA).
      apply (opp_unicity O E E' H2 A); auto.
    subst mA'.
    assert(HH:=sum_exists O E E' H2 dBA dCB H13 H10).
    ex_and HH Sd.
    assert(sum22 O E E' B mA C mB Sd).
      unfold sum22.
      exists dBA.
      exists dCB.
      split; auto.
    apply sum22_permut in H9.
    unfold sum22 in H9.
    ex_and H9 O'.
    ex_and H14 dCA'.
    assert(O' = O).
      apply (sum_unicity O E E' mB B); auto.
    subst O'.
    assert(dCA'=dCA).
      apply (sum_unicity O E E' C mA); auto.
      apply sum_comm; auto.
    subst dCA'.
    assert(dCA=Sd).
      apply (sum_O_B_eq O E E'); auto.
    subst Sd.
    apply sum_comm; auto.
Qed.

Lemma sum_diff_diff_b : forall O E E' A B C dBA dCB dCA,
                         diff O E E' B A dBA
                      -> diff O E E' C B dCB
                      -> sum O E E' dCB dBA dCA
                      -> diff O E E' C A dCA.
Proof.
    intros.
    assert(Ar2 O E E' B A dBA).
      apply diff_ar2; auto.
    assert(Ar2 O E E' C B dCB).
      apply diff_ar2; auto.
    assert(Ar2 O E E' dCB dBA dCA).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    unfold diff in H.
    ex_and H mA.
    unfold diff in H0.
    ex_and H0 mB.
    assert(sum22 O E E' B mA C mB dCA).
      unfold sum22.
      exists dBA.
      exists dCB.
      split; auto.
      split; auto.
      apply sum_comm; auto.
    apply sum22_permut in H5.
    unfold sum22 in H5.
    ex_and H5 O'.
    ex_and H6 dCA'.
    assert(O'=O).
      apply (sum_unicity O E E' mB B); auto.
    subst O'.
    assert(dCA' = dCA).
      apply(sum_O_B_eq O E E'); auto.
    subst dCA'.
    unfold diff.
    exists mA.
    split; auto.
    apply sum_comm; auto.
Qed.


Lemma leP_trans : forall O E E' A B C, leP O E E' A B -> leP O E E' B C -> leP O E E' A C.
Proof.
    intros.
    unfold leP in *.
    induction H; induction H0.
      left.
      unfold ltP in *.
      ex_and H dBA.
      ex_and H0 dCB.
      assert(Ar2 O E E' B A dBA).
        apply diff_ar2; auto.
      assert(Ar2 O E E' C B dCB).
        apply diff_ar2; auto.
      unfold Ar2 in *.
      spliter.
      clean_duplicated_hyps.
      assert(HH:= sum_exists O E E' H3 dBA dCB H10 H7).
      ex_and HH dCA.
      exists dCA.
      assert(HH:= sum_diff_diff_b O E E' A B C dBA dCB dCA H H0).
      split.
        apply HH.
        apply sum_comm; auto.
      apply(sum_pos_pos O E E' dBA dCB); auto.
      subst C.
      left; auto.
      subst B.
      left; auto.
    subst C.
    subst B.
    right; auto.
Qed.

(* (x + y) - (a + b) = (x - a) + (y - b) *)

Lemma sum_diff2_diff_sum2_a : forall O E E' A B C X Y Z dXA dYB dZC, sum O E E' A B C -> sum O E E' X Y Z
                                                            -> diff O E E' X A dXA -> diff O E E' Y B dYB
                                                            -> sum O E E' dXA dYB dZC -> diff O E E' Z C dZC.
Proof.
    intros.
    assert(Ar2 O E E' A B C).
      apply sum_ar2; auto.
    assert(Ar2 O E E' X Y Z).
      apply sum_ar2; auto.
    assert(Ar2 O E E' dXA dYB dZC).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    apply diff_sum in H1.
    apply diff_sum in H2.
    apply sum_diff.
    assert(HH:=sum_exists O E E' H4 C dZC H15 H9); auto.
    ex_and HH Z'.
    assert(sum22 O E E' A B dXA dYB Z').
      unfold sum22.
      exists C.
      exists dZC.
      auto.
    apply sum22_comm in H6.
    apply sum22_permut in H6.
    apply sum22_comm in H6.
    unfold sum22 in H6.
    ex_and H6 Y'.
    ex_and H16 X'.
    assert(X' = X).
      apply(sum_unicity O E E' A dXA); auto.
    subst X'.
    assert(Y'=Y).
      apply(sum_unicity O E E' B dYB); auto.
    subst Y'.
    assert( Z'= Z).
      apply(sum_unicity O E E' X Y); auto.
      apply sum_comm; auto.
    subst Z'.
    assumption.
Qed.

Lemma sum_diff2_diff_sum2_b : forall O E E' A B C X Y Z dXA dYB dZC, sum O E E' A B C -> sum O E E' X Y Z
                                                            -> diff O E E' X A dXA -> diff O E E' Y B dYB
                                                            -> diff O E E' Z C dZC -> sum O E E' dXA dYB dZC .
Proof.
    intros.
    assert(Ar2 O E E' A B C).
      apply sum_ar2; auto.
    assert(Ar2 O E E' X Y Z).
      apply sum_ar2; auto.
    assert(Ar2 O E E' X A dXA).
      apply diff_ar2; auto.
    assert(Ar2 O E E' Y B dYB).
      apply diff_ar2; auto.
    assert(Ar2 O E E' Z C dZC).
      apply diff_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    assert(HH:=sum_exists O E E' H4 dXA dYB H17 H14).
    ex_and HH dZC'.
    assert(HH:=sum_diff2_diff_sum2_a O E E' A B C X Y Z dXA dYB dZC' H H0 H1 H2 H5).
    assert( dZC' = dZC).
      apply(diff_unicity O E E' Z C); auto.
    subst dZC'.
    assumption.
Qed.

(* sum_preserves leP : a <= x /\ b <= y => a + b <= x + y *)

Lemma leP_sum_leP : forall O E E' A B C X Y Z, leP O E E' A X -> leP O E E' B Y -> sum O E E' A B C -> sum O E E' X Y Z -> leP O E E' C Z.
Proof.
    intros.
    unfold leP in *.
    assert(Ar2 O E E' A B C).
      apply sum_ar2; auto.
    assert(Ar2 O E E' X Y Z).
      apply sum_ar2; auto.
    unfold Ar2 in *.
    spliter.
    clean_duplicated_hyps.
    induction H; induction H0.
      unfold ltP in *.
      ex_and H dXA.
      ex_and H0 dYB.
      assert(HH:= diff_exists O E E' Z C  H3 H7 H10).
      ex_and HH dZC.
      left.
      exists dZC.
      split; auto.
      assert(sum O E E' dXA dYB dZC).
        apply(sum_diff2_diff_sum2_b O E E' A B C X Y Z dXA dYB dZC H1 H2 H H0); auto.
      apply(sum_pos_pos O E E' dXA dYB); auto.
      subst Y.
      left.
      unfold ltP in *.
      ex_and H dXA.
      assert(HH:=diff_exists O E E' Z C H3 H7 H10).
      ex_and HH dZC.
      exists dZC.
      split; auto.
      assert( sum O E E' dXA O dZC).
        apply(sum_diff2_diff_sum2_b O E E' A B C X B Z dXA O dZC); auto.
        apply diff_null; auto.
      assert(dXA = dZC).
        apply(sum_A_O_eq O E E'); auto.
      subst dXA.
      assumption.
      subst X.
      left.
      unfold ltP in *.
      ex_and H0 dYB.
      assert(HH:=diff_exists O E E' Z C H3 H7 H10).
      ex_and HH dZC.
      exists dZC.
      split; auto.
      assert(sum O E E' O dYB dZC).
        apply(sum_diff2_diff_sum2_b O E E' A B C A Y Z O dYB dZC); auto.
        apply diff_null; auto.
      assert(dYB = dZC).
        apply(sum_O_B_eq O E E'); auto.
      subst dYB.
      assumption.
    subst X.
    subst Y.
    right.
    apply(sum_unicity O E E' A B); auto.
Qed.


(** Lemma 14.40 states that we have an ordered field. *)

End Order.
