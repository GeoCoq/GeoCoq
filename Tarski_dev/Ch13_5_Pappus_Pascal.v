(* Gabriel Braun April 2013 *)

Require Export GeoCoq.Tarski_dev.Ch13_4_cos.
Require Export GeoCoq.Tarski_dev.Annexes.project.

Section Pappus_Pascal.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.



Lemma l13_10_aux1 : forall O A B P Q la lb lp lq,
 Col O A B -> Col O P Q -> Perp O P P A -> Perp O Q Q B ->
 lg la -> lg lb -> lg lp -> lg lq -> la O A -> lb O B -> lp O P -> lq O Q ->
 exists a, anga a /\ lcos lp la a /\ lcos lq lb a.
Proof.
    intros.
    assert(acute A O P).
      eapply (perp_acute _ _ P);finish.
    assert(P <> O).
      intro.
      subst P.
      apply perp_not_eq_1 in H1.
      tauto.
    assert(A <> O).
      intro.
      subst A.
      apply perp_not_col in H1.
      apply H1.
      Col.
    assert(Q <> O).
      intro.
      subst Q.
      apply perp_not_eq_1 in H2.
      tauto.
    assert(B <> O).
      intro.
      subst B.
      apply perp_not_col in H2.
      apply H2.
      Col.
    assert(HH:= anga_exists A O P H13 H12 H11).
    ex_and HH a.
    assert(a B O Q).
      assert(~ Par O P A P).
        intro.
        unfold Par in H18.
        induction H18.
          unfold Par_strict in H18.
          spliter.
          apply H21.
          exists P.
          split; Col.
        spliter.
        apply perp_comm in H1.
        apply perp_not_col in H1.
        apply H1.
        Col.
      assert(A <> P).
        apply perp_not_eq_2 in H1.
        auto.
      assert(project O O O P A P).
        unfold project.
        repeat split; Col.
      assert(project A P O P A P).
        unfold project.
        repeat split; Col.
        left.
        apply par_reflexivity.
        auto.
      assert(project B Q O P A P).
        unfold project.
        repeat split; Col.
        left.
        eapply (l12_9 _ _ _ _ O P).
          apply perp_sym.
          eapply (perp_col _ Q); Col.
          Perp.
        Perp.
      induction H.
        assert(Bet O P Q).

        apply(per23_preserves_bet O A B P Q); auto.
        apply perp_in_per.
apply perp_comm in H1.
apply perp_perp_in in H1.
Perp.
apply perp_in_per.
apply perp_comm in H2.
apply perp_perp_in in H2.
Perp.

   (*       apply(project_preserves_bet O P A P O A B O P Q); auto. *)
        assert(Conga A O P B O Q).
          eapply (out_conga B _ Q B _ Q).
            apply conga_refl; auto.
            unfold out.
            repeat split; auto.
            unfold out.
            repeat split; auto.
            apply out_trivial; auto.
          apply out_trivial; auto.
        apply (anga_conga_anga _ A O P); auto.
      induction H.
        assert(Bet P Q O).

apply between_symmetry.
apply(per23_preserves_bet O B A Q P); Between.
Col.

apply perp_in_per.
apply perp_comm in H2.
apply perp_perp_in in H2.
Perp.
apply perp_comm in H1.
apply perp_perp_in in H1.
Perp.

 (*         apply(project_preserves_bet O P A P A B O P Q O); auto.*)
        assert(Conga A O P B O Q).
          eapply (out_conga B _ Q B _ Q).
            apply conga_refl; auto.
            unfold out.
            repeat split; auto.
            left.
            Between.
            unfold out.
            repeat split; auto.
            left.
            Between.
            apply out_trivial; auto.
          apply out_trivial; auto.
        apply (anga_conga_anga _ A O P); auto.
      assert(Bet Q O P).

apply(per13_preserves_bet B O A Q P); auto.
Col.
apply perp_in_per.
apply perp_comm in H2.
apply perp_perp_in in H2.
Perp.
apply perp_comm in H1.
apply perp_perp_in in H1.
Perp.

 (*       apply(project_preserves_bet O P A P B O A Q O P); auto. *)
      assert(Conga A O P B O Q).
        eapply (l11_14 ); Between.
      apply (anga_conga_anga _ A O P); auto.
    exists a.
    repeat split; auto.
      exists O.
      exists P.
      exists A.
      repeat split; auto.
        apply perp_in_per.
        Perp.
      apply anga_sym; auto.
    exists O.
    exists Q.
    exists B.
    repeat split; auto.
      apply perp_in_per.
      Perp.
    apply anga_sym; auto.
Qed.

Lemma acute_trivial : forall A B, A <> B -> acute A B A.
Proof.
    intros.
    assert(HH:= not_col_exists A B H).
    ex_and HH P.
    assert(exists C : Tpoint, Per C B A /\ Cong C B A B /\ one_side A B C P).
      apply(ex_per_cong A B B P A B H H); Col; exists A.
    ex_and H1 C.
    assert_diffs.
    unfold acute.
    exists A.
    exists B.
    exists C.
    split.
      apply l8_2.
      auto.
    unfold lta.
    split.
      unfold lea.
      exists A.
      split.
        apply in_angle_trivial_1; auto.
      apply conga_refl; auto.
    intro.
    assert(out B A C).
      apply(out_conga_out A B A A B C).
        apply out_trivial; auto.
      auto.
    assert(Perp C B B A).
      apply per_perp_in in H1; auto.
      apply perp_in_perp in H1.
      induction H1.
        apply perp_not_eq_1 in H1.
        tauto.
      auto.
    apply perp_comm in H8.
    apply perp_not_col in H8.
    apply out_col in H7.
    Col.
Qed.


Lemma lcos_eqa_lcos : forall lp l a b, lcos lp l a -> eqA a b -> lcos lp l b.
Proof.
    intros.
    assert(HH:=lcos_lg_anga l lp a H).
    spliter.
    clear H1.
    assert(HH:= H0).
    unfold eqA in HH.
    assert (ang a) by (apply anga_is_ang;auto).
    assert (ang b) by (apply eqA_preserves_ang with a;auto).
    assert (anga b).
      apply (eqA_preserves_anga a b); auto.
    unfold lcos in *.
    spliter.
    repeat split; auto.
    ex_and H9 A.
    ex_and H10 B.
    ex_and H9 C.
    exists A.
    exists B.
    exists C.
    repeat split; auto.
    apply HH;auto.
Qed.

Lemma l13_10_aux2 : forall O A B la lla lb llb,
 Col O A B  -> lg la -> lg lla -> lg lb -> lg llb -> la O A -> lla O A -> lb O B -> llb O B ->
 A <> O -> B <> O -> exists a, anga a /\ lcos lla la a /\ lcos llb lb a.
Proof.
    intros.
    assert(HH:=anga_exists A O A H8 H8 (acute_trivial A O H8)).
    ex_and HH a.
    exists a.
    split; auto.
    assert(is_null_anga a).
      assert(out O A A /\ is_null_anga a).
        apply(anga_col_null a A O A); auto.
        Col.
      tauto.
    split.
      assert(eqL la lla).
        apply ex_eql.
        exists O.
        exists A.
        repeat split; auto.
      rewrite <- H13.
      apply null_lcos; auto.
      intro.
      unfold lg_null in H14.
      spliter.
      ex_and H15 X.
      assert(HH:= lg_cong la O A X X H0 H4 H16).
      treat_equalities.
      tauto.
    assert(HH:=anga_exists B O B H9 H9 (acute_trivial B O H9)).
    ex_and HH b.
    assert(eqA a b).
      assert(HH:=null_anga A O B O a b).
      apply HH; split; auto.
    assert(eqL lb llb).
      apply ex_eql.
      exists O.
      exists B.
      repeat split; auto.
    rewrite <- H16.
    apply null_lcos; auto.
    intro.
    unfold lg_null in H17.
    spliter.
    ex_and H18 X.
    assert(HH:= lg_cong lb O B X X H2 H6 H19).
    treat_equalities.
    tauto.
Qed.


Lemma acute_not_per : forall A B C, acute A B C -> ~ Per A B C.
Proof.
    intros.
    unfold acute in H.
    ex_and H A'.
    ex_and H0 B'.
    ex_and H C'.
    unfold lta in H0.
    spliter.
    intro.
    apply H1.
    assert(A <> B /\ C <> B /\ A' <> B' /\ C' <> B').
      unfold lea in H0.
      ex_and H0 X.
      apply conga_distinct in H3.
      spliter.
      repeat split; auto.
      unfold InAngle in H0.
      spliter; auto.
    spliter.
    apply(l11_16 A B C A' B' C'); auto.
Qed.



Lemma lcos_exists : forall l a, anga a -> lg l -> ~lg_null l -> exists lp, lcos lp l a.
Proof.
    intros.
    lg_instance l A B.
    induction(is_null_anga_dec a).
      exists l.
      apply null_lcos; auto.
      anga_instance1 a A B C.
        assert(~ Col B C A).
          intro.
          assert(out B A C /\ is_null_anga a).
            apply(anga_col_null a A B C H H4).
            Col.
          apply H3.
          tauto.
        assert(HH:= l8_18_existence B C A H5).
        ex_and HH P.
        assert(HH:=lg_exists B P).
        ex_and HH lp.
        exists lp.
        assert(acute A B C).
          unfold anga in H.
          ex_and H A'.
          ex_and H10 B'.
          ex_and H C'.
          assert(HH:=H10 A B C).
          destruct HH.
          assert(HP:= H12 H4).
          apply (acute_lea_acute _ _ _ A' B' C'); auto.
          unfold lea.
          exists C'.
          split.
            apply in_angle_trivial_2.
              apply conga_distinct in HP.
              tauto.
            apply conga_distinct in HP.
            tauto.
          apply conga_sym.
          auto.
        unfold lcos.
        repeat split; auto.
        exists B.
        exists P.
        exists A.
        repeat split; auto.
          apply perp_in_per.
          apply perp_in_comm.
          apply perp_perp_in.
          apply perp_sym.
          apply (perp_col _ C).
            intro.
            subst P.
            assert(Per A B C).
              apply perp_in_per.
              apply perp_in_comm.
              apply perp_perp_in.
              Perp.
            apply acute_not_per in H10.
            contradiction.
            Perp.
          Col.
          apply (lg_sym l); auto.
        assert(HH:=H10).
        unfold acute in HH.
        apply(anga_sym a); auto.
        apply(anga_out_anga a A B C A P); auto.
          apply out_trivial.
          intro.
          subst B.
          apply H5.
          Col.
        eapply (perp_acute_out _ _ A).
          apply acute_sym.
          auto.
          Perp.
        Col.
      intro.
      apply H1.
      unfold lg_null.
      split; auto.
      subst B.
      exists A.
      auto.
    assumption.
Qed.

Definition lcos_eq := fun la a lb b => exists lp, lcos lp la a /\ lcos lp lb b.

Lemma lcos_eq_refl : forall la a, lg la -> ~lg_null la -> anga a -> lcos_eq la a la a.
Proof.
    intros.
    unfold lcos_eq.
    assert(HH:=lcos_exists la a H1 H H0).
    ex_and HH lp.
    exists lp.
    split; auto.
Qed.

Lemma lcos_eq_sym : forall la a lb b, lcos_eq la a lb b -> lcos_eq lb b la a.
Proof.
    intros.
    unfold lcos_eq in *.
    ex_and H lp.
    exists lp.
    split; auto.
Qed.

Lemma lcos_eq_trans : forall la a lb b lc c, lcos_eq la a lb b -> lcos_eq lb b lc c -> lcos_eq la a lc c.
Proof.
    intros.
    unfold lcos_eq in *.
    ex_and H lab.
    ex_and H0 lbc.
    assert(HH:= l13_6 b lab lbc lb H1 H0).
    assert(lcos lbc la a).
      rewrite <- HH.
      apply lcos_lg_anga in H.
      tauto.
    exists lbc.
    split; auto.
Qed.


Definition lcos2 := fun lp l a b => exists la, lcos la l a /\ lcos lp la b.

Lemma lcos2_comm : forall lp l a b, lcos2 lp l a b -> lcos2 lp l b a.
Proof.
    intros.
    unfold lcos2 in *.
    ex_and H la.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    spliter.
    assert(exists lb, lcos lb l b).
      apply(lcos_exists l b); auto.
      assert(HH:= lcos_lg_not_null la l a H).
      tauto.
    ex_and H7 lb.
    apply lcos_lg_anga in H8.
    spliter.
    exists lb.
    split.
      auto.
    assert(exists lp', lcos lp' lb a).
      apply(lcos_exists lb a); auto.
      assert(HH:= lcos_lg_not_null lb l b H7).
      tauto.
    ex_and H11 lp'.
    assert(eqL lp lp').
      apply(l13_7 a b l la lb lp lp'); auto.
    apply lcos_lg_anga in H12.
    rewrite H11. tauto.
Qed.

Lemma lcos2_exists : forall l a b, lg l -> ~lg_null l -> anga a -> anga b -> 
 exists lp, lcos2 lp l a b.
Proof.
    intros.
    assert(HH:= lcos_exists l a H1 H H0).
    ex_and HH la.
    apply lcos_lg_anga in H3.
    spliter.
    assert(~ lg_null la /\ ~ lg_null l).
      apply (lcos_lg_not_null _ _ a).
      auto.
    spliter.
    clear H8.
    assert(HH:= lcos_exists la b H2 H5 H7).
    ex_and HH lab.
    exists lab.
    unfold lcos2.
    exists la.
    split; auto.
Qed.

Lemma lcos2_exists' : forall l a b, lg l -> ~lg_null l -> anga a -> anga b ->
 exists la, exists lab, lcos la l a /\ lcos lab la b.
Proof.
    intros.
    assert(HH:=lcos_exists l a H1 H H0).
    ex_and HH la.
    exists la.
    apply lcos_lg_anga in H3.
    spliter.
    assert(HP:=lcos_not_lg_null la l a H3).
    assert(HH:=lcos_exists la b H2 H5 HP).
    ex_and HH lab.
    exists lab.
    split; auto.
Qed.

Definition lcos2_eq := fun l1 a b l2 c d => exists lp, lcos2 lp l1 a b /\ lcos2 lp l2 c d.

Lemma lcos2_eq_refl : forall l a b, lg l -> ~lg_null l -> anga a -> anga b -> lcos2_eq l a b l a b.
Proof.
    intros.
    assert(HH:= lcos2_exists l a b H H0 H1 H2).
    ex_and HH lab.
    unfold lcos2_eq.
    exists lab.
    split; auto.
Qed.

Lemma lcos2_eq_sym : forall l1 a b l2 c d, lcos2_eq l1 a b l2 c d -> lcos2_eq l2 c d l1 a b.
Proof.
    intros.
    unfold lcos2_eq in *.
    ex_and H lp.
    exists lp.
    auto.
Qed.

Lemma lcos2_unicity: forall l l1 l2 a b, lcos2 l1 l a b -> lcos2 l2 l a b -> eqL l1 l2.
Proof.
    intros.
    unfold lcos2 in *.
    ex_and H la.
    ex_and H0 lb.
    assert(eqL la lb).
      apply (l13_6 a _ _ l); auto.
    apply lcos_lg_anga in H2.
    apply lcos_lg_anga in H1.
    spliter.
    assert(lcos l2 la b).
      rewrite H3;auto.
    apply (l13_6 b _ _ la); auto.
Qed.

Lemma lcos2_eql_lcos2 : forall lla llb la lb a b, lcos2 la lla a b -> eqL lla llb -> eqL la lb -> lcos2 lb llb a b.
Proof.
    intros.
    unfold lcos2 in *.
    ex_and H l.
    exists l.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H2.
    spliter.
    split.
    rewrite <- H0;auto.
    rewrite <- H1;auto.
Qed.

Lemma lcos2_lg_anga : forall lp l a b, lcos2 lp l a b -> lcos2 lp l a b /\ lg lp /\ lg l /\ anga a /\ anga b.
Proof.
    intros.
    split; auto.
    unfold lcos2 in H.
    ex_and H ll.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    spliter.
    split; auto.
Qed.

Lemma lcos2_eq_trans : forall l1 a b l2 c d l3 e f, lcos2_eq l1 a b l2 c d -> lcos2_eq l2 c d l3 e f
                                   -> lcos2_eq l1 a b l3 e f.
Proof.
    intros.
    unfold lcos2_eq in *.
    ex_and H lp.
    ex_and H0 lq.
    exists lp.
    split; auto.
    assert(eqL lp lq).
      eapply (lcos2_unicity l2 _ _ c d); auto.
    apply lcos2_lg_anga in H2.
    apply lcos2_lg_anga in H1.
    spliter.
    eapply (lcos2_eql_lcos2 l3 _ lq); auto.
      reflexivity.
    symmetry; auto.
Qed.

Lemma lcos_eq_lcos2_eq : forall la lb a b c, anga c -> lcos_eq la a lb b -> lcos2_eq la a c lb b c.
Proof.
    intros.
    assert(HH0:=H0).
    unfold lcos_eq in HH0.
    ex_and HH0 lp.
    apply lcos_lg_anga in H1.
    apply lcos_lg_anga in H2.
    spliter.
    clear H7.
    assert(~ lg_null lp /\ ~ lg_null la).
      apply (lcos_lg_not_null _ _ a).
      auto.
    spliter.
    unfold lcos2_eq.
    assert(HH:= lcos_exists lp c H H4 H7).
    ex_and HH lq.
    exists lq.
    split.
      unfold lcos2.
      exists lp.
      split; auto.
    unfold lcos2.
    exists lp.
    split; auto.
Qed.

Lemma lcos2_lg_not_null: forall lp l a b, lcos2 lp l a b -> ~lg_null l /\ ~lg_null lp.
Proof.
    intros.
    unfold lcos2 in H.
    ex_and H la.
    apply lcos_lg_not_null in H.
    apply lcos_lg_not_null in H0.
    spliter.
    split; auto.
Qed.

Definition lcos3 := fun lp l a b c => exists la, exists lab, lcos la l a /\ lcos lab la b /\ lcos lp lab c.

Lemma lcos3_lcos_1_2 : forall lp l a b c, lcos3 lp l a b c <-> exists la, lcos la l a /\ lcos2 lp la b c.
Proof.
    intros.
    split.
      intro.
      unfold lcos3 in H.
      ex_and H la.
      ex_and H0 lab.
      exists la.
      split; auto.
      unfold lcos2.
      exists lab.
      split; auto.
    intro.
    ex_and H la.
    unfold lcos2 in H0.
    ex_and H0 lab.
    unfold lcos3.
    exists la.
    exists lab.
    apply lcos_lg_anga in H0.
    apply lcos_lg_anga in H1.
    spliter.
    split; auto.
Qed.

Lemma lcos3_lcos_2_1 : forall lp l a b c, lcos3 lp l a b c <-> exists lab, lcos2 lab l a b /\ lcos lp lab c.
Proof.
    intros.
    split.
      intro.
      unfold lcos3 in H.
      ex_and H la.
      ex_and H0 lab.
      exists lab.
      split.
        unfold lcos2.
        exists la.
        split; assumption.
      assumption.
    intro.
    ex_and H lab.
    unfold lcos3.
    unfold lcos2 in H.
    ex_and H la.
    exists la.
    exists lab.
    split; auto.
Qed.


Lemma lcos3_permut3 : forall lp l a b c, lcos3 lp l a b c -> lcos3 lp l b a c.
Proof.
    intros.
    assert(HH:= lcos3_lcos_2_1 lp l a b c).
    destruct HH.
    assert(exists lab : Tpoint -> Tpoint -> Prop, lcos2 lab l a b /\ lcos lp lab c).
      apply lcos3_lcos_2_1; auto.
    ex_and H2 lab.
    apply lcos2_comm in H2.
    apply lcos3_lcos_2_1.
    exists lab.
    split; auto.
Qed.


Lemma lcos3_permut1 : forall lp l a b c, lcos3 lp l a b c -> lcos3 lp l a c b.
Proof.
    intros.
    assert(HH:= lcos3_lcos_1_2 lp l a b c).
    destruct HH.
    assert(exists la : Tpoint -> Tpoint -> Prop, lcos la l a /\ lcos2 lp la b c).
      apply lcos3_lcos_1_2; auto.
    ex_and H2 la.
    apply lcos2_comm in H3.
    apply lcos3_lcos_1_2.
    exists la.
    split; auto.
Qed.

Lemma lcos3_permut2 : forall lp l a b c, lcos3 lp l a b c -> lcos3 lp l c b a.
Proof.
    intros.
    apply lcos3_permut3.
    apply lcos3_permut1.
    apply lcos3_permut3.
    auto.
Qed.

Lemma lcos3_exists : forall l a b c, lg l -> ~lg_null l -> anga a -> anga b -> anga c ->
 exists lp, lcos3 lp l a b c.
Proof.
    intros.
    assert(HH:= lcos_exists l a H1 H H0).
    ex_and HH la.
    apply lcos_lg_anga in H4.
    spliter.
    assert(~ lg_null la /\ ~ lg_null l).
      apply (lcos_lg_not_null _ _ a).
      auto.
    spliter.
    clear H9.
    clear H7.
    assert(HH:= lcos_exists la b H2 H6 H8).
    ex_and HH lab.
    apply lcos_lg_anga in H7.
    spliter.
    assert(~ lg_null lab /\ ~ lg_null la).
      apply (lcos_lg_not_null _ _ b).
      auto.
    spliter.
    assert(HH:= lcos_exists lab c H3 H10 H12).
    ex_and HH lp.
    exists lp.
    unfold lcos3.
    exists la.
    exists lab.
    split;auto.
Qed.

(*----------------------------------------*)


Definition lcos3_eq := fun l1 a b c l2 d e f => exists lp, lcos3 lp l1 a b c /\ lcos3 lp l2 d e f.

Lemma lcos3_eq_refl : forall l a b c, lg l -> ~lg_null l -> anga a -> anga b -> anga c -> lcos3_eq l a b c l a b c.
Proof.
    intros.
    assert(HH:= lcos3_exists l a b c H H0 H1 H2 H3).
    ex_and HH lp.
    unfold lcos3_eq.
    exists lp.
    split; auto.
Qed.

Lemma lcos3_eq_sym : forall l1 a b c l2 d e f, lcos3_eq l1 a b c l2 d e f -> lcos3_eq l2 d e f l1 a b c.
Proof.
    intros.
    unfold lcos3_eq in *.
    ex_and H lp.
    exists lp.
    auto.
Qed.

Lemma lcos3_unicity: forall l l1 l2 a b c, lcos3 l1 l a b c -> lcos3 l2 l a b c -> eqL l1 l2.
Proof.
    intros.
    unfold lcos3 in *.
    ex_and H la.
    ex_and H1 lab.
    ex_and H0 la'.
    ex_and H3 lab'.
    assert(eqL la la').
      apply (l13_6 a _ _ l); auto.
    apply lcos_lg_anga in H2.
    apply lcos_lg_anga in H3.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H4.
    spliter.
    assert(lcos lab' la b).
      rewrite H5;auto.
    assert(eqL lab lab') by
      (apply (l13_6 b _ _ la); auto).
    assert(lcos l2 lab c).
      rewrite H19. auto.
    apply (l13_6 c _ _ lab); auto.
Qed.


Lemma lcos3_eql_lcos3 : forall lla llb la lb a b c, lcos3 la lla a b c -> eqL lla llb -> eqL la lb -> lcos3 lb llb a b c.
Proof.
    intros.
    unfold lcos3 in *.
    ex_and H lpa.
    exists lpa.
    ex_and H2 lpab.
    exists lpab.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H2.
    apply lcos_lg_anga in H3.
    spliter.
    split.
    rewrite <- H0;auto.
    split.
      auto.
    rewrite <- H1;auto.
Qed.

Lemma lcos3_lg_anga : forall lp l a b c, lcos3 lp l a b c -> lcos3 lp l a b c /\ lg lp /\ lg l /\ anga a /\ anga b /\ anga c.
Proof.
    intros.
    split; auto.
    unfold lcos3 in H.
    ex_and H la.
    ex_and H0 lab.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    apply lcos_lg_anga in H1.
    spliter.
    split; auto.
Qed.

Lemma lcos3_lg_not_null: forall lp l a b c, lcos3 lp l a b c -> ~lg_null l /\ ~lg_null lp.
Proof.
    intros.
    unfold lcos3 in H.
    ex_and H la.
    ex_and H0 lab.
    apply lcos_lg_not_null in H.
    apply lcos_lg_not_null in H1.
    spliter.
    split; auto.
Qed.

Lemma lcos3_eq_trans : forall l1 a b c l2 d e f l3 g h i,
 lcos3_eq l1 a b c l2 d e f -> lcos3_eq l2 d e f l3 g h i -> lcos3_eq l1 a b c l3 g h i.
Proof.
    intros.
    unfold lcos3_eq in *.
    ex_and H lp.
    ex_and H0 lq.
    exists lp.
    split; auto.
    assert(eqL lp lq).
      eapply (lcos3_unicity l2 _ _ d e f); auto.
    apply lcos3_lg_anga in H2.
    apply lcos3_lg_anga in H1.
    spliter.
    eapply (lcos3_eql_lcos3 l3 _ lq); auto.
      reflexivity.
    symmetry; auto.
Qed.

Lemma lcos_eq_lcos3_eq : forall la lb a b c d, anga c -> anga d -> lcos_eq la a lb b -> lcos3_eq la a c d lb b c d.
Proof.
    intros.
    assert(HH1:=H1).
    unfold lcos_eq in HH1.
    ex_and HH1 lp.
    apply lcos_lg_anga in H2.
    apply lcos_lg_anga in H3.
    spliter.
    assert(~ lg_null lp /\ ~ lg_null la).
      apply (lcos_lg_not_null _ _ a).
      auto.
    spliter.
    assert(HH:= lcos_exists lp c H H5 H10).
    ex_and HH lq.
    apply lcos_lg_anga in H12.
    spliter.
    assert(~ lg_null lq /\ ~ lg_null lp).
      apply (lcos_lg_not_null _ _ c); auto.
    spliter.
    assert(HH:= lcos_exists lq d H0 H14 H16).
    ex_and HH lm.
    unfold lcos3_eq.
    exists lm.
    split; unfold lcos3.
      exists lp.
      exists lq.
      split; auto.
    exists lp.
    exists lq.
    split; auto.
Qed.

Lemma lcos2_eq_lcos3_eq : forall la lb a b c d e, anga e -> lcos2_eq la a b lb c d -> lcos3_eq la a b e lb c d e.
Proof.
    intros.
    assert(HH0:=H0).
    unfold lcos2_eq in HH0.
    ex_and HH0 lp.
    apply lcos2_lg_anga in H1.
    apply lcos2_lg_anga in H2.
    spliter.
    assert(~ lg_null la /\ ~ lg_null lp).
      eapply (lcos2_lg_not_null _ _ a b).
      auto.
    spliter.
    assert(HH:= lcos_exists lp e H H3 H12).
    ex_and HH lq.
    apply lcos_lg_anga in H13.
    spliter.
    assert(~ lg_null lq /\ ~ lg_null lp).
      apply (lcos_lg_not_null _ _ e); auto.
    spliter.
    unfold lcos3_eq.
    exists lq.
    split; apply lcos3_lcos_2_1; exists lp; split; auto.
Qed.

Lemma l13_6_bis : forall lp l1 l2 a, lcos lp l1 a -> lcos lp l2 a -> eqL l1 l2.
Proof.
    intros.
    induction(is_null_anga_dec a).
      apply lcos_lg_anga in H.
      apply lcos_lg_anga in H0.
      spliter.
      assert(HH:= null_lcos_eql lp l1 a H H1).
      assert(HP:= null_lcos_eql lp l2 a H0 H1).
      transitivity lp; auto.
      symmetry; auto.
      apply lcos_lg_anga in H.
      apply lcos_lg_anga in H0.
      spliter.
      assert (HH:= H).
      assert(HH0:= H0).
      unfold lcos in HH.
      unfold lcos in HH0.
      spliter.
      ex_and H11 A.
      ex_and H16 B.
      ex_and H11 C.
      ex_and H15 A'.
      ex_and H19 B'.
      ex_and H15 C'.
      assert(HH:=not_null_not_col a B A C H4 H1 H18).
      assert(HP:=not_null_not_col a B' A' C' H4 H1 H21).
      assert(B <> C).
        intro.
        subst C.
        apply HH.
        Col.
      assert(B' <> C').
        intro.
        subst C'.
        apply HP.
        Col.
      assert(HQ:= anga_distincts a B A C H4  H18).
      assert(HR:= anga_distincts a B' A' C' H4 H21).
      spliter.
      assert(Cong A B A' B').
        apply (lg_cong lp); auto.
      assert(Conga B A C B' A' C').
        apply (anga_conga a); auto.
      assert(Conga C B A C' B' A').
        apply l11_16; auto.
      assert(Cong A C A' C' /\ Cong B C B' C' /\ Conga A C B A' C' B').
        apply(l11_50_1 A B C A' B' C'); auto.
          intro.
          apply HH.
          Col.
        apply conga_comm.
        auto.
      spliter.
      apply (all_eql A' C').
        split; auto.
      split; auto.
      eapply (lg_cong_lg _ A C); auto.
    unfold lcos in *;intuition.
Qed.


Lemma lcos3_lcos2 : forall l1 l2 a b c d n, lcos3_eq l1 a b n l2 c d n -> lcos2_eq l1 a b l2 c d.
Proof.
    intros.
    unfold lcos3_eq in H.
    ex_and H lp.
    unfold lcos2_eq.
    apply lcos3_lcos_2_1 in H.
    apply lcos3_lcos_2_1 in H0.
    ex_and H ll1.
    ex_and H0 ll2.
    assert (eqL ll1 ll2).
      eapply(l13_6_bis lp _ _ n); auto.
    exists ll1.
    split; auto.
    apply lcos2_lg_anga in H.
    apply lcos2_lg_anga in H0.
    spliter.
    apply(lcos2_eql_lcos2 l2 l2 ll2 ll1 c d); auto.
      reflexivity.
    symmetry; auto.
Qed.

Lemma lcos2_lcos : forall l1 l2 a b c, lcos2_eq l1 a c l2 b c -> lcos_eq l1 a l2 b.
Proof.
    intros.
    unfold lcos2_eq in H.
    ex_and H lp.
    unfold lcos2 in H.
    unfold lcos2 in H0.
    ex_and H lx.
    ex_and H0 ly.
    unfold lcos_eq.
    assert(eqL lx ly).
      eapply(l13_6_bis lp _ _ c); auto.
    exists lx.
    split; auto.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    spliter.
    rewrite H3;auto.
Qed.

Lemma lcos_per_anga : forall O A P la lp a, lcos lp la a -> la O A -> lp O P -> Per A P O -> a A O P.
Proof.
    intros.
    assert(HH:= H).
    unfold lcos in HH.
    spliter.
    ex_and H6 O'.
    ex_and H7 P'.
    ex_and H6 A'.
    assert(Cong O A O' A').
      apply (lg_cong la); auto.
    assert(Cong O P O' P').
      apply (lg_cong lp); auto.
    assert(HH:= lcos_lg_not_null lp la a H).
    spliter.
    induction(eq_dec_points A P).
      subst A.
      assert(Cong O' A' O' P').
        apply (cong_transitivity _ _ O P); Cong.
      assert(A' = P').
        induction(Col_dec A' P' O').
          assert(A' = P' \/ O' = P').
            apply l8_9; auto.
          induction H16.
            auto.
          subst P'.
          eapply (cong_identity _  O' O'); Cong.
        assert(lt P' A' A' O' /\ lt P' O' A' O').
          apply(l11_46 A' P' O' H15).
          left.
          auto.
        spliter.
        unfold lt in H17.
        spliter.
        apply False_ind.
        apply H18.
        Cong.
      subst A'.
      assert(is_null_anga a).
        apply(out_null_anga a P' O' P'); auto.
        apply out_trivial.
        intro.
        subst P'.
        apply H12.
        unfold lg_null.
        split.
          auto.
        exists O'.
        auto.
      apply(is_null_all a P O).
        intro.
        subst P.
        apply H12.
        unfold lg_null.
        split.
          auto.
        exists O.
        auto.
      auto.
    assert(O <> P).
      intro.
      subst P.
      apply H12.
      split.
        auto.
      exists O.
      auto.
    induction(Col_dec A P O).
      assert (HH:=anga_distincts a P' O' A' H5 H9).
      spliter.
      assert(A' <> P').
        intro.
        subst A'.
        assert(A = P \/ O = P).
          apply l8_9; auto.
        induction H19.
          auto.
        contradiction.
      assert(~ Col A P O).
        apply(per_not_col A P O); auto.
      contradiction.
    assert (HH:=anga_distincts a P' O' A' H5 H9).
    spliter.
    assert(A' <> P').
      intro.
      subst A'.
      assert(Cong O P O A).
        apply (cong_transitivity _ _ O' P'); Cong.
      assert(lt P A A O /\ lt P O A O).
        apply(l11_46 A P O H16).
        left.
        auto.
      spliter.
      unfold lt in H21.
      spliter.
      apply H22.
      Cong.
    assert(Conga A P O A' P' O').
      apply l11_16; auto.
    assert(Cong P A P' A' /\ Conga P A O P' A' O' /\ Conga P O A P' O' A').
      assert(lt P A A O /\ lt P O A O).
        apply(l11_46 A P O H16).
        left.
        auto.
      spliter.
      unfold lt in H22.
      spliter.
      apply(l11_52 A P O A' P' O' ); Cong.
    spliter.
    apply conga_comm in H23.
    apply (anga_conga_anga a A' O' P'); auto.
      apply (anga_sym a); auto.
    apply conga_sym.
    auto.
Qed.

Lemma lcos_lcos_col : forall la lb lp a b O A B P,
 lcos lp la a -> lcos lp lb b -> la O A -> lb O B -> lp O P -> a A O P -> b B O P -> Col A B P.
Proof.
    intros.
    apply lcos_lg_anga in H.
    apply lcos_lg_anga in H0.
    spliter.
    assert(Per O P A).
      apply (lcos_per O P A lp la a); auto.
      apply anga_sym; auto.
    assert(Per O P B).
      apply (lcos_per O P B lp lb b); auto.
      apply anga_sym; auto.
    eapply (per_per_col _ _ O); Perp.
    intro.
    subst P.
    assert(HH:=lcos_lg_not_null lp la a H).
    spliter.
    apply H14.
    unfold lg_null.
    split; auto.
    exists O.
    auto.
Qed.

(*****strange ****)

Lemma per13_preserves_bet_inv : forall A B C A' C', Bet A' B C' -> B <> A' -> B <> C' ->  Col A B C  -> Per B A' A -> Per B C' C -> Bet A B C.
Proof.
intros.
assert(Col A' B C').
apply bet_col in H.
Col.

induction(eq_dec_points A A').
subst A'.
assert(Col B C' C).
ColR.
assert(HH:=l8_9 B C' C H4 H6 ).
induction HH.
contradiction.
subst C'.
assumption.

assert(C <> C').
intro.
subst C'.
assert(Col B A' A).
ColR.
assert(HH:=l8_9 B A' A H3 H7).
induction HH;
contradiction.

assert(Perp B A' A' A).
apply per_perp_in in H3; auto.
apply perp_in_comm in H3.
apply perp_in_perp in H3.
induction H3.
Perp.
apply perp_distinct in H3.
tauto.

assert(Perp B C' C' C).
apply per_perp_in in H4; auto.
apply perp_in_comm in H4.
apply perp_in_perp in H4.
induction H4.
Perp.
apply perp_distinct in H4.
tauto.

assert(Par A A' C C').
apply(l12_9 A A' C C' B A');Perp.
apply perp_sym.
apply(perp_col _ C'); Perp.
ColR.

induction H10.
assert(HH:=par_strict_symmetry A A' C C' H10).
apply l12_6 in H10.
apply l12_6 in HH.

assert(~Col A' A B).
apply per_not_col in H3; auto.
intro.
apply H3.
Col.

assert(~Col C' C B).
apply per_not_col in H4; auto.
intro.
apply H4.
Col.

assert(one_side A' A B C').
apply out_one_side.
left; auto.
repeat split.
intro.
subst A'.
apply H11.
Col.
intro.
subst C'.
apply one_side_symmetry in H10.
unfold one_side in H10.
ex_and H10 X.
unfold two_sides in H10.
spliter.
apply H14.
Col.
left.
assumption.

assert(one_side C' C B A').
apply out_one_side.
left; auto.
repeat split.
intro.
subst C'.
apply H12.
Col.
intro.
subst C'.
apply one_side_symmetry in H10.
unfold one_side in H10.
ex_and H10 X.
unfold two_sides in H10.
spliter.
apply H15.
Col.
left.
Between.

assert(one_side A' A B C).
apply(one_side_transitivity _ _ _ C'); auto.
apply invert_one_side.
apply one_side_symmetry.
assumption.

assert(one_side C C' B A).
apply(one_side_transitivity _ _ _ A'); auto.
apply invert_one_side.
assumption.
apply one_side_symmetry.
assumption.

apply invert_one_side in H15.

assert(HP:= col_one_side_out A A' B C H2 H15).

assert(out C B A).
apply(col_one_side_out C C' B A); Col.

unfold out in *.
spliter.

induction H19.
Between.
induction H22.
Between.
apply False_ind.
apply H18.
apply (between_equality _ _ B); Between.

(****************************)

spliter.
assert(Perp A' C' A A').
apply (perp_col _ B); Perp.
intro.
subst C'.
apply between_identity in H.
subst A'.
apply perp_distinct in H9.
tauto.
apply perp_not_col in H14.

apply False_ind.
apply H14.
ColR.
Qed.

Lemma l13_10_aux3 : forall A B C A' B' C' O,
  ~ Col O A A' ->
  B <> O -> C <> O -> Col O A B -> Col O B C ->
  B' <> O -> C' <> O ->
  Col O A' B' -> Col O B' C' -> Perp2 B C' C B' O -> Perp2 C A' A C' O ->
  Bet A O B -> Bet A' O B'.
Proof.
    intros.
    assert(A <> O).
      intro.
      subst A.
      apply H.
      Col.
    assert(A' <> O).
      intro.
      subst A'.
      apply H.
      Col.
    assert(Col O A C).
      apply (col_transitivity_1 _ B); Col.
    assert(Col O A' C').
      apply (col_transitivity_1 _ B'); Col.
    assert(Bet C A O \/ Bet A C O \/ Bet O C B \/ Bet O B C).
      apply(fourth_point A O B C); auto.
      ColR.
    induction H15.
      assert(Bet O C' A').
        apply(perp2_preserves_bet23 O A C C' A'); Between.
          Col.
          intro.
          apply H.
               ColR.
               apply perp2_sym.
        auto.

      assert(Bet B' O C').
        apply(perp2_preserves_bet13 O B C B' C'); eBetween.
          intro.
          apply H.
          ColR.
          eBetween.

    (***************)
    induction H15.
      assert(Bet C O B).
        eBetween.
      assert(Bet O A' C').
        apply(perp2_preserves_bet23 O C A A' C'); Between.
        intro.
        apply H.
ColR.

      assert(Bet B' O C').
        apply(perp2_preserves_bet13 O B C B' C'); Between.
          intro.
          apply H.
ColR.
eBetween.
    induction H15.
      assert(Bet A O C).
        eBetween.
      assert(Bet O B' C').
        apply(perp2_preserves_bet23 O C B B' C'); Between.
          intro.
          apply H.
ColR.
        apply perp2_sym.
        auto.
      assert(Bet C' O A').
        apply(perp2_preserves_bet13 O C A C' A'); Col.
Between.
          intro.
          apply H.
ColR.
eBetween.
    assert(Bet A O C).
      eBetween.
    assert(Bet O C' B').
      apply(perp2_preserves_bet23 O B C C' B'); Col.
      intro.
      apply H.
ColR.
    assert(Bet C' O A').
      apply(perp2_preserves_bet13 O C A C' A'); Col.
Between.
        intro.
        apply H.
ColR.
    eBetween.
Qed.

Lemma l13_10_aux4 : forall A B C A' B' C' O,
  ~ Col O A A' -> B <> O -> C <> O -> Col O A B -> Col O B C -> B' <> O -> C' <> O ->
  Col O A' B' -> Col O B' C' -> Perp2 B C' C B' O -> Perp2 C A' A C' O -> Bet O A B ->
  out O A' B'.
Proof.
    intros.
    assert(A <> O).
      intro.
      subst A.
      apply H.
      Col.
    assert(A' <> O).
      intro.
      subst A'.
      apply H.
      Col.
    assert(Col O A C).
    ColR.
    induction(eq_dec_points A B).
      subst B.
assert(HH:= perp2_trans C A' A C' C B' O H9 H8).
      assert(A' = B').
      apply perp2_par in HH.

        assert(Col A' B' C).
          induction HH.
            apply False_ind.
            apply H14.
            exists C.
            split; Col.
          spliter.
          Col.
        apply (l6_21 O C' C B'); Col.
          intro.
          apply H.
ColR.
        intro.
        subst B'.
apply par_distinct in HH.
tauto.
ColR.
      subst B'.
      apply out_trivial.
      auto.


    assert(Bet C O A \/ Bet O C A \/ Bet A C B \/ Bet A B C).
      apply(fourth_point O A B C); auto.

    induction H15.
      assert(Bet B' O C').
        assert(Bet C O B).
        eBetween.
        apply(perp2_preserves_bet13 O B C B' C'); Between.
          intro.
          apply H.
ColR.
  (*        assert(Col O A B').

            apply (col_transitivity_1 _ C); Col.
          apply (col_transitivity_1 _ B'); Col.
        apply perp2_sym.
        auto.*)
      assert(Bet A' O C').
        apply(perp2_preserves_bet13 O A C A' C');Between.
        ColR.
apply perp2_sym.
assumption.
repeat split; auto.
apply(l5_2 C' O A' B'); Between.

    induction H15.
      assert(Bet O C B).
eBetween.
      assert(Bet O B' C').
        apply(perp2_preserves_bet23 O C B B' C'); Col.
          intro.
          apply H.
ColR.
        apply perp2_sym.
        auto.
      assert(Bet O A' C').
        apply(perp2_preserves_bet23 O C A A' C'); Between.
 ColR.
        intro.
        apply H.
ColR.
      repeat split; auto.
apply(l5_3 O A' B' C'); auto.

    induction H15.
      assert(Bet O A C).
eBetween.
      assert(Bet O C' A').
        apply(perp2_preserves_bet23 O A C C' A'); auto.
ColR.
          intro.
          apply H.
ColR.
        apply perp2_sym.
        auto.
      assert(Bet O C B).
eBetween.
      assert(Bet O B' C').
        apply(perp2_preserves_bet23 O C B B' C'); auto.
          intro.
          apply H.
ColR.
        apply perp2_sym.
        auto.
repeat split; auto.
right.
eBetween.

(*      assert(Bet O B' A').
eBetween.
*)
    assert(Bet O A C).
eBetween.
    assert( Bet O B C).
eBetween.

    assert(Bet O C' B').
      apply(perp2_preserves_bet23  O B C C' B'); Col.
      intro.
      apply H.
ColR.
    assert(Bet O C' A').
      apply(perp2_preserves_bet23  O A C C' A'); auto.
ColR.
        intro.
        apply H.
ColR.
      apply perp2_sym.
      auto.
    repeat split; auto.
    apply (l5_1 _ C'); auto.
Qed.

Lemma l13_10_aux5 : forall A B C A' B' C' O,
 ~ Col O A A' -> B <> O -> C <> O -> Col O A B -> Col O B C ->
 B' <> O -> C' <> O -> Col O A' B' -> Col O B' C'->
 Perp2 B C' C B' O -> Perp2 C A' A C' O -> out O A B ->
 out O A' B'.
Proof.
    intros.
    assert(A' <> O).
      intro.
      subst A'.
      apply H.
      Col.
    induction H10.
    spliter.
    induction H13.
      eapply (l13_10_aux4 A B C _ _ C'); auto.
    apply l6_6.
    apply(l13_10_aux4 B A C B' A' C'); try assumption.
      intro.
      apply H.
      ColR.
      Col.
      ColR.
      Col.
      ColR.
      apply perp2_sym.
      assumption.
    apply perp2_sym.
    auto.
Qed.

Lemma per_per_perp : forall A B X Y,
 A <> B -> X <> Y ->
 (B <> X \/ B <> Y) -> Per A B X -> Per A B Y ->
 Perp A B X Y.
Proof.
    intros.
    induction H1.
      assert(HH:=H2).
      apply per_perp_in in H2; auto.
      apply perp_in_perp in H2.
      induction H2.
        apply perp_not_eq_1 in H2.
        tauto.
      apply perp_sym.
      apply (perp_col _ B); auto.
        Perp.
      apply col_permutation_5.
      eapply (per_per_col _ _ A); Perp.
    assert(HH:=H3).
    apply per_perp_in in H3; auto.
    apply perp_in_perp in H3.
    induction H3.
      apply perp_not_eq_1 in H3.
      tauto.
    apply perp_sym.
    apply perp_left_comm.
    apply (perp_col _ B); auto.
      Perp.
    apply col_permutation_5.
    eapply (per_per_col _ _ A); Perp.
Qed.

Lemma l13_10 : forall A B C A' B' C' O,
  ~ Col O A A' -> B <> O -> C <> O ->
  Col O A B -> Col O B C ->
  B' <> O -> C' <> O ->
  Col O A' B' -> Col O B' C' ->
  Perp2 B C' C B' O -> Perp2 C A' A C' O ->
  Perp2 A B' B A' O.
Proof.
    intros.
    assert(HH8:= H8).
    assert(HH9:= H9).
    assert(Col O A C).
      apply (col_transitivity_1 _ B); Col.
    assert(Col O A' C').
      apply (col_transitivity_1 _ B'); Col.
    assert(A <> O).
      intro.
      subst A.
      apply H.
      Col.
    assert(~ Col A B' O).
      intro.
      apply H.
      apply (col_transitivity_1 _ B'); Col.
    apply perp2_perp_in in HH8.
      ex_and HH8 L.
      ex_and H14 L'.
      apply perp2_perp_in in HH9.
        ex_and HH9 M.
        ex_and H19 M'.
        assert(HH:=l8_18_existence A B' O H13).
        ex_and HH N.
        unfold Perp2.
        exists O.
        exists N.
        repeat split.
          Col.
          Perp.
        assert(HH:=lg_exists O A).
        ex_and HH la.
        assert(HH:=lg_exists O B).
        ex_and HH lb.
        assert(HH:=lg_exists O C).
        ex_and HH lc.
        assert(HH:=lg_exists O A').
        ex_and HH la'.
        assert(HH:=lg_exists O B').
        ex_and HH lb'.
        assert(HH:=lg_exists O C').
        ex_and HH lc'.
        assert(HH:=lg_exists O L).
        ex_and HH ll.
        assert(HH:=lg_exists O L').
        ex_and HH ll'.
        assert(HH:=lg_exists O M).
        ex_and HH lm.
        assert(HH:=lg_exists O M').
        ex_and HH lm'.
        assert(HH:=lg_exists O N).
        ex_and HH ln.
        assert(O <> L).
          apply perp_in_perp in H17.
          induction H17.
            apply perp_not_eq_1 in H17.
            tauto.
          apply perp_not_eq_1 in H17.
          auto.
        assert(O <> L').
          apply perp_in_perp in H18.
          induction H18.
            apply perp_not_eq_1 in H18.
            tauto.
          apply perp_not_eq_1 in H18.
          auto.
        assert(~ Col O B B').
          intro.
          apply H.
          assert(Col O A B').
            eapply (col_transitivity_1 _ B); Col.
          eapply (col_transitivity_1 _ B'); Col.
        assert(~ Col O C C').
          intro.
          apply H.
          assert(Col O A C').
            eapply (col_transitivity_1 _ C); Col.
          eapply (col_transitivity_1 _ C'); Col.
        assert(exists a, anga a /\ lcos ll lb a /\ lcos ll' lc a).
          induction(eq_dec_points B L).
            subst L.
            assert(C = L').
              eapply (l6_21 O B B' L'); Col.
              intro.
              subst L'.
              contradiction.
            subst L'.
            apply (l13_10_aux2 O B C); Col.
          apply (l13_10_aux1 O B C L L'); Col.
            apply perp_in_perp in H17.
            induction H17.
              apply perp_not_eq_1 in H17.
              tauto.
            apply perp_sym.
            apply perp_comm.
            eapply (perp_col _ C');auto.
            Perp.
          apply perp_in_perp in H18.
          induction H18.
            apply perp_not_eq_1 in H18.
            tauto.
          apply perp_sym.
          apply perp_comm.
          eapply (perp_col _ B'); auto.
            intro.
            subst L'.
            assert(Col O B L).
              eapply (col_transitivity_1 _ C); Col.
            apply H52.
            apply(l6_21 O C C' B B L); Col.
            intro.
            subst C'.
            unfold Perp_in in H17.
            tauto.
          Perp.
        ex_and H52 l'.
        assert(exists a, anga a /\ lcos ll lc' a /\ lcos ll' lb' a).
          induction(eq_dec_points C' L).
            subst L.
            assert(B' = L').
              eapply (l6_21 O C' C L'); Col.
              intro.
              subst L'.
              apply H51.
              Col.
            subst L'.
            eapply (l13_10_aux2 O C' B'); Col.
          apply (l13_10_aux1 O C' B' L L'); Col.
            apply perp_in_perp in H17.
            induction H17.
              apply perp_not_eq_1 in H17.
              tauto.
            apply perp_sym.
            apply perp_comm.
            eapply (perp_col _ B); Col.
            Perp.
          apply perp_in_perp in H18.
          induction H18.
            apply perp_not_eq_1 in H18.
            tauto.
          apply perp_sym.
          apply perp_comm.
          eapply (perp_col _ C);Col.
            intro.
            subst L'.
            assert(Col O C' L).
              eapply (col_transitivity_1 _ B'); Col.
            apply H55.
            apply(l6_21 O B' B C' C' L); Col.
            intro.
            subst C'.
            unfold Perp_in in H17.
            tauto.
          Perp.
        ex_and H55 l.
        assert(exists a, anga a /\ lcos lm lc a /\ lcos lm' la a).
          induction (eq_dec_points C M).
            subst M.
            assert(A = M').
              eapply (l6_21 O C C' M'); Col.
              intro.
              subst M'.
              contradiction.
            subst M'.
            apply (l13_10_aux2 O C A); Col.
          apply (l13_10_aux1 O C A M M'); Col.
            apply perp_in_perp in H22.
            induction H22.
              apply perp_not_eq_1 in H22.
              tauto.
            apply perp_sym.
            apply perp_comm.
            eapply (perp_col _ A');auto.
            Perp.
          apply perp_in_perp in H23.
          induction H23.
            apply perp_not_eq_1 in H23.
            tauto.
          apply perp_sym.
          apply perp_comm.
          eapply (perp_col _ C'); auto.
            intro.
            subst M'.
            assert(Col O C M).
              eapply (col_transitivity_1 _ A); Col.
            apply H58.
            apply(l6_21 O A A' C C M); Col.
            intro.
            subst A'.
            unfold Perp_in in H22.
            tauto.
          Perp.
        ex_and H58 m'.
        assert(exists a, anga a /\ lcos lm la' a /\ lcos lm' lc' a).
          induction(eq_dec_points A' M).
            subst M.
            assert(C' = M').
              eapply (l6_21 O A' A M'); Col.
              intro.
              subst M'.
              apply H.
              Col.
            subst M'.
            eapply (l13_10_aux2 O A' C'); Col.
            intro.
            subst A'.
            apply H.
            Col.
          apply (l13_10_aux1 O A' C' M M'); Col.
            apply perp_in_perp in H22.
            induction H22.
              apply perp_not_eq_1 in H22.
              tauto.
            apply perp_sym.
            apply perp_comm.
            eapply (perp_col _ C);Col.
            Perp.
          apply perp_in_perp in H23.
          induction H23.
            apply perp_not_eq_1 in H23.
            tauto.
          apply perp_sym.
          apply perp_comm.
          eapply (perp_col _ A);Col.
            intro.
            subst M'.
            assert(Col O A' M).
              eapply (col_transitivity_1 _ C'); Col.
            apply H61.
            apply(l6_21 O C' C A' A' M); Col.
            intro.
            subst A'.
            unfold Perp_in in H22.
            tauto.
          Perp.
        ex_and H61 m.
        assert(exists a, anga a /\ lcos ln la a).
          assert(exists a, anga a /\ a A O N).
            apply(anga_exists A O N).
              intro.
              subst A.
              apply H.
              Col.
              apply perp_not_eq_2 in H25.
              auto.
            induction(eq_dec_points A N).
              subst N.
              apply acute_trivial.
              intro.
              subst A.
              apply H.
              Col.
            eapply (perp_acute _ _ N).
              Col.
            apply perp_in_left_comm.
            apply perp_perp_in.
            apply perp_sym.
            apply (perp_col _ B').
              auto.
              Perp.
            Col.
          ex_and H64 n'.
          exists n'.
          split.
            auto.
          unfold lcos.
          repeat split; auto.
          exists O.
          exists N.
          exists A.
          repeat split; auto.
            induction(eq_dec_points A N).
              subst N.
              apply l8_2.
              apply l8_5.
            apply perp_in_per.
            apply perp_in_comm.
            apply perp_perp_in.
            apply perp_left_comm.
            apply (perp_col _ B').
              auto.
              Perp.
            Col.
          apply anga_sym; auto.
        ex_and H64 n'.
        assert(exists a, anga a /\ lcos ln lb' a).
          assert(exists a, anga a /\ a B' O N).
            apply(anga_exists B' O N).
              intro.
              subst B'.
              apply H50.
              Col.
              apply perp_not_eq_2 in H25.
              auto.
            induction(eq_dec_points B' N).
              subst N.
              apply acute_trivial.
              auto.
            eapply (perp_acute _ _ N).
              Col.
            apply perp_in_left_comm.
            apply perp_perp_in.
            apply perp_sym.
            apply (perp_col _ A).
              auto.
              Perp.
            Col.
          ex_and H66 n.
          exists n.
          split.
            auto.
          unfold lcos.
          repeat split; auto.
          exists O.
          exists N.
          exists B'.
          repeat split; auto.
            induction(eq_dec_points B' N).
              subst N.
              apply l8_2.
              apply l8_5.
            apply perp_in_per.
            apply perp_in_comm.
            apply perp_perp_in.
            apply perp_left_comm.
            apply (perp_col _ A).
              auto.
              Perp.
            Col.
          apply anga_sym; auto.
        ex_and H66 n.
        assert(lcos_eq lc l' lb' l).
          unfold lcos_eq.
          exists ll'.
          split; auto.
        assert(lcos_eq lb l' lc' l).
          unfold lcos_eq.
          exists ll.
          split; auto.
        assert(lcos_eq lc m' la' m).
          unfold lcos_eq.
          exists lm.
          split; auto.
        assert(lcos_eq la m' lc' m).
          unfold lcos_eq.
          exists lm'.
          split; auto.
        assert(lcos_eq la n' lb' n).
          unfold lcos_eq.
          exists ln.
          split; auto.
        assert(exists lp, lcos lp lb n').
          apply(lcos_exists lb n'); auto.
          intro.
          unfold lg_null in H73.
          spliter.
          ex_and H74 X.
          apply H0.
          eapply (cong_identity _ _ X).
          apply (lg_cong lb); auto.
          apply (lg_sym lb); auto.
        ex_and H73 bn'.
        assert(exists lp, lcos lp ll n').
          apply(lcos_exists ll n'); auto.
          intro.
          unfold lg_null in H73.
          spliter.
          ex_and H75 X.
          apply H48.
          apply (cong_identity _ _ X).
          apply (lg_cong ll); auto.
        ex_and H73 bl'n'.
        assert(exists lp, lcos lp bn' l').
          apply(lcos_exists bn' l'); auto.
            apply lcos_lg_anga in H74.
            spliter.
            auto.
          assert(HH:= lcos_lg_not_null bn' lb n' H74 ).
          tauto.
        ex_and H73 bn'l'.
        assert(lcos2 bl'n' lb l' n').
          unfold lcos2.
          exists ll.
          split; auto.
        assert(lcos2 bn'l' lb n' l').
          unfold lcos2.
          exists bn'.
          split; auto.
        assert(eqL bl'n' bn'l').
          apply lcos2_comm in H77.
          apply (lcos2_unicity lb _ _ l' n'); auto.
        apply lcos_lg_anga in H75.
        apply lcos_lg_anga in H76.
        spliter.
        assert(lcos2_eq lb l' n' lb n' l').
          unfold lcos2_eq.
          exists bl'n'.
          split; auto.
          eapply (lcos2_eql_lcos2 lb _ bn'l').
            auto.
            reflexivity.
          symmetry; auto.
        assert(lcos2_eq lb l' n' lc' l n').
          apply lcos_eq_lcos2_eq; auto.
        assert(lcos3_eq lb l' n' m lc' l n' m).
          apply lcos2_eq_lcos3_eq; auto.
        assert(lcos3_eq lb l' n' m lc' m l n').
          unfold lcos3_eq in H87.
          ex_and H87 lp.
          unfold lcos3_eq.
          exists lp.
          split; auto.
          apply lcos3_permut1.
          apply lcos3_permut2.
          auto.
        assert(lcos3_eq la m' l n' lc' m l n').
          apply lcos_eq_lcos3_eq; auto.
        assert(lcos3_eq lb l' n' m la m' l n').
          apply (lcos3_eq_trans _ _ _ _ lc' m l n'); auto.
          apply lcos3_eq_sym; auto.
        assert(lcos3_eq lb l' n' m la n' m' l).
          unfold lcos3_eq in H90.
          ex_and H90 lp.
          unfold lcos3_eq.
          exists lp.
          split; auto.
          apply lcos3_permut1.
          apply lcos3_permut2.
          auto.
        assert(lcos3_eq la n' m' l lb' n m' l).
          apply lcos_eq_lcos3_eq; auto.
        assert(lcos3_eq lb l' n' m lb' n m' l).
          apply (lcos3_eq_trans _ _ _ _ la n' m' l); auto.
        assert(lcos3_eq lb l' n' m lb' l n m').
          unfold lcos3_eq in H93.
          ex_and H93 lp.
          unfold lcos3_eq.
          exists lp.
          split; auto.
          apply lcos3_permut1.
          apply lcos3_permut2.
          auto.
        assert(lcos3_eq lb' l n m' lc l' n m').
          apply lcos_eq_lcos3_eq; auto.
          apply lcos_eq_sym; auto.
        assert(lcos3_eq lb l' n' m lc l' n m').
          apply (lcos3_eq_trans _ _ _ _ lb' l n m'); auto.
        assert(lcos3_eq lb l' n' m lc m' l' n).
          unfold lcos3_eq in H96.
          ex_and H96 lp.
          unfold lcos3_eq.
          exists lp.
          split; auto.
          apply lcos3_permut1.
          apply lcos3_permut2.
          auto.
        assert(lcos3_eq la' m l' n lc m' l' n).
          apply lcos_eq_lcos3_eq; auto.
          apply lcos_eq_sym; auto.
        assert(lcos3_eq lb l' n' m la' m l' n).
          apply (lcos3_eq_trans _ _ _ _ lc m' l' n); auto.
          apply lcos3_eq_sym; auto.
        assert(lcos3_eq lb l' n' m la' n l' m).
          unfold lcos3_eq in H99.
          ex_and H99 lp.
          unfold lcos3_eq.
          exists lp.
          split; auto.
          apply lcos3_permut2.
          auto.
        assert(lcos2_eq lb l' n' la' n l').
          apply (lcos3_lcos2 _ _ _ _ _ _ m); auto.
        assert(lcos2_eq lb n' l' la' n l').
          unfold lcos2_eq in H101.
          ex_and H101 lp.
          unfold lcos2_eq.
          exists lp.
          split; auto.
          apply lcos2_comm.
          auto.
        assert(lcos_eq lb n' la' n).
          apply (lcos2_lcos) in H102.
          auto.
        clear H85 H86 H87 H88 H89 H90 H91 H92 H93 H94 H95 H96 H97 H98 H99 H100 H101 H102.
(*************** we construct the length ln'  ********************)
        unfold lcos_eq in H103.
        ex_and H103 ln'.
        assert(O <> N).
          apply perp_not_eq_2 in H25; auto.
        apply lcos_lg_anga in H85.
        spliter.
(*************** we prove : n' A O N  ********************)
        assert(n' A O N).
          apply(lcos_per_anga _ _ _ la ln); auto.
          induction(eq_dec_points A N).
            subst N.
            apply l8_2.
            apply l8_5.
          apply perp_in_per.
          apply perp_in_comm.
          apply perp_perp_in.
          apply perp_left_comm.
          apply (perp_col _ B'); Col.
(*************** we prove : n B O N  ********************)
        assert(n B' O N).
          apply(lcos_per_anga _ _ _ lb' ln); auto.
          induction(eq_dec_points B' N).
            subst N.
            apply l8_2.
            apply l8_5.
          apply perp_in_per.
          apply perp_in_comm.
          apply perp_perp_in.
          apply perp_left_comm.
          apply (perp_col _ A); Col.
          Perp.
(*************** two cases  ********************)
        assert(Bet A O B \/ out O A B \/ ~ Col A O B).
          apply(or_bet_out A O B); auto.
(*************** case : Bet A O B  ********************)
        induction H93.
(*************** we extend NO with N' such as ln' O N' ********************)         
          assert(HH:=ex_point_lg_bet ln' N O H89).
          ex_and HH N'.
          assert(O <> N').
            intro.
            subst N'.
            assert(HH:=lcos_lg_not_null ln' lb n' H85).
            spliter.
            apply H96.
            unfold lg_null.
            split; auto.
            exists O.
            auto.
          assert(A' <> B).
            intro.
            subst A'.
            contradiction.
(*************** we prove (Per O N' B) using lcos ln' lb n'  ********************)        
            assert(Per O N' B).
            apply(lcos_per O N' B ln' lb n'); auto.
            assert(Conga N O A B O N').
(*************** pair of vertical angles (angles opposés par le sommet) ********************)  
              apply(l11_13 N' O A A O N' N B ); Between.
              apply conga_left_comm.
              apply conga_refl; auto.
            apply (anga_conga_anga n' A O N); auto.
            apply conga_comm.
            auto.
(*************** we prove (Per O N' A') usinglcos ln' la' n  ********************) 
          assert(Per O N' A').
            apply(lcos_per O N' A' ln' la' n); auto.
            assert(Conga N O B' A' O N').
              apply(l11_13 N' O B' B' O N' N A' ); Between.
                apply conga_left_comm.
                apply conga_refl; auto.
                apply between_symmetry.
                apply(l13_10_aux3 A B C A' B' C' O); auto.
              intro.
              subst A'.
              apply H.
              Col.
            eapply (anga_conga_anga  n B' O N); auto.
            apply conga_comm.
            auto.
(*************** we prove (Perp O N B A')  ********************) 
          apply (perp_col _ N'); Col.
          apply per_per_perp; auto.
          induction(eq_dec_points N' B).
            right.
            subst N'.
            auto.
          left.
          auto.
        induction H93.
(*************** case : out O A B  ********************)
(*************** we construct N' on the half-line ON such as ln' O N' /\ out O N' N  ********************)        
          assert(exists N' : Tpoint, ln' O N' /\ out O N' N).
            apply(ex_point_lg_out ln' O N H87 H89).
            assert(HH:=lcos_lg_not_null ln' la' n H86).
            spliter.
            auto.
          ex_and H94 N'.
(*************** we prove (Per O N' B) using lcos ln' lb n'  ********************)
          assert(Per O N' B).
            apply(lcos_per O N' B ln' lb n'); auto.
            assert(Conga A O N B O N').
              apply(out_conga A O N A O N A N B N').
                apply conga_refl ; auto.
                apply out_trivial; auto.
                apply out_trivial; auto.
                auto.
              apply l6_6.
              auto.
            apply (anga_conga_anga n' A O N); auto.
            apply conga_right_comm.
            auto.
(*************** we prove (Per O N' A) using lcos ln' la' n  ********************)
          assert(Per O N' A').
            apply(lcos_per O N' A' ln' la' n); auto.
            assert(Conga B' O N A' O N').
              apply(out_conga B' O N B' O N B' N A' N').
                apply conga_refl; auto.
                apply out_trivial; auto.
                apply out_trivial; auto.
                eapply (l13_10_aux5 B A C B' A' C'); Col.
                  intro.
                  subst A'.
                  apply H.
                  Col.
                  apply perp2_sym.
                  auto.
                  apply perp2_sym.
                  auto.
                apply l6_6.
                auto.
              apply l6_6.
              auto.
            apply (anga_conga_anga n B' O N); auto.
            apply conga_right_comm.
            auto.
          apply(perp_col _ N').
            auto.
            eapply (per_per_perp); auto.
              intro.
              subst N'.
              unfold out in H95.
              tauto.
              intro.
              subst A'.
              contradiction.
            induction(eq_dec_points N' B).
              subst N'.
              right.
              intro.
              subst A'.
              contradiction.
            left.
            auto.
          apply out_col in H95.
          Col.
        apply False_ind.
        apply H93.
        Col.
      split; intro; apply H; ColR.
      split; intro; apply H; ColR.
Qed.

End Pappus_Pascal.

Section Pappus_Pascal_2.

Context `{MT:Tarski_2D_euclidean}.
  Context `{EqDec:EqDecidability Tpoint}.

Lemma par_perp2 : forall A B C D P, Par A B C D -> Perp2 A B C D P.
Proof.
    intros.
    apply par_distincts in H.
    spliter.
    unfold Perp2.
    assert(HH:= perp_exists P A B H0).
    ex_and HH Q.
    exists P.
    exists Q.
    repeat split.
      Col.
      Perp.
    apply perp_sym.
    apply (par_perp_perp A B); auto.
    apply perp_sym; auto.
Qed.

Lemma l13_11 : forall A B C A' B' C' O,
  ~ Col O A A' ->
  B <> O -> C <> O ->
  Col O A B -> Col O B C ->
  B' <> O -> C' <> O ->
  Col O A' B' -> Col O B' C' -> Par B C' C B' -> Par C A' A C' ->
  Par A B' B A'.
Proof.
    intros.
    assert(HH:=par_perp2 B C' C B' O H8).
    assert(HP:=par_perp2 C A' A C' O H9).
    assert(HQ:=perp2_par A B' B A' O).
    apply HQ.
    apply(l13_10 A B C A' B' C' O); auto.
Qed.


Lemma l13_14 : forall O A B C O' A' B' C',
  Par_strict O A O' A' -> Col O A B -> Col O B C -> Col O A C ->
  Col O' A' B' -> Col O' B' C' -> Col O' A' C' ->
  Par A C' A' C -> Par B C' B' C -> Par A B' A' B.
Proof.
    intros.
    assert(HP:= H).
    unfold Par_strict in HP.
    spliter.
    assert(~Col O A A').
      intro.
      apply H11.
      exists A'.
      split; Col.
    induction(eq_dec_points A C).
      subst C.
      induction H6.
        apply False_ind.
        apply H6.
        exists A.
        split; Col.
      spliter.
      assert(A' =  C').
        eapply (l6_21 A C' O' A'); Col.
        intro.
        apply H11.
        exists A.
        split.
          Col.
        eapply (col_transitivity_1 _ C').
          intro.
          subst C'.
          apply H11.
          exists A.
          Col.
          Col.
        Col.
      subst C'.
      Par.
    assert(A' <> C').
      intro.
      subst C'.
      induction H6.
        apply H6.
        exists A'.
        split; Col.
      spliter.
      apply H13.
      eapply (l6_21 A A' O A); Col.
    assert(Par_strict A C A' C').
      unfold Par_strict.
      repeat split; auto; try apply all_coplanar.
      intro.
      apply H11.
      ex_and H15 X.
      exists X.
      split.
        ColR.
      ColR.
    assert(Plg A C A' C').
      apply(pars_par_plg A C A' C').
        auto.
      apply par_right_comm.
      auto.
    induction(eq_dec_points B C).
      subst C.
      assert(B' = C').
        eapply (l6_21 B C' A' C').
          intro.
          apply H11.
          exists B.
          split.
            Col.
          ColR.
          auto.
          induction H7.
            apply False_ind.
            apply H7.
            exists B.
            split; Col.
          spliter.
          Col.
          Col.
          ColR.
          Col.
      subst.
      Par.
    assert(B' <> C').
      intro.
      subst C'.
      induction H7.
        apply H7.
        exists B'.
        split; Col.
      spliter.
      apply H17.
      eapply (l6_21 A C B' B).
        intro.
        induction H6.
          apply H6.
          exists C.
          split; Col.
        spliter.
        apply H15.
        exists B'.
        split; Col.
        auto.
        ColR.
        Col.
        Col.
        Col.
    assert(Par_strict B C B' C').
      unfold Par_strict.
      repeat split; auto; try apply all_coplanar.
      intro.
      apply H11.
      ex_and H19 X.
      exists X.
      split.
        assert(Col X O B).
          ColR.
        induction(eq_dec_points O B).
          subst O.
          ColR.
        ColR.
      assert(Col X O' B').
        ColR.
      induction(eq_dec_points O' B').
        subst O'.
        ColR.
      ColR.
    assert(Plg B C B' C').
      apply(pars_par_plg B C B' C').
        auto.
      apply par_right_comm.
      auto.
    assert(Parallelogram A C A' C').
      apply plg_to_parallelogram.
      auto.
    assert(Parallelogram B C B' C').
      apply plg_to_parallelogram.
      auto.
    apply plg_mid in H21.
    apply plg_mid in H22.
    ex_and H21 M.
    ex_and H22 N.
    assert(M = N).
      eapply (l7_17 C C'); auto.
    subst N.
    assert(Parallelogram A B A' B').
      apply(mid_plg A B A' B' M).
        left.
        intro.
        subst A'.
        apply H12.
        Col.
        assumption.
      assumption.
    apply par_right_comm.
    induction(eq_dec_points A B).
      subst B.
      assert(B' = A').
        eapply (symmetric_point_unicity A M); auto.
      subst B'.
      apply par_reflexivity.
      intro.
      subst A'.
      apply H12.
      Col.
    apply plg_par; auto.
    intro.
    subst A'.
    apply H11.
    exists B.
    split; Col.
Qed.

End Pappus_Pascal_2.