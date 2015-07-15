 (* Gabriel Braun April 2013 *)

Require Export Ch13_2_length.

Section Angles_1.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

(************************************* angle *****************************)


Definition ang (A : Tpoint -> Tpoint -> Tpoint -> Prop) := exists a, exists b, exists c, a <> b /\ c <> b /\
                                                            forall x y z, Conga a b c x y z <-> A x y z.

Definition angle  A B C := fun x y z => Conga A B C x y z.


Lemma ang_exists : forall A B C, A <> B -> C <> B -> exists a, ang a /\ a A B C.
Proof.
    intros.
    exists (angle A B C).
    split.
      unfold ang.
      exists A.
      exists B.
      exists C.
      split; auto.
      split; auto.
      intros.
      split.
        auto.
      auto.
    unfold angle.
    apply conga_refl; auto.
Qed.

Lemma ex_points_ang : forall a , ang a ->  exists A, exists B, exists C, a A B C.
Proof.
    intros.
    unfold ang in H.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    assert(HH:= H1 A B C).
    destruct HH.
    exists A.
    exists B.
    exists C.
    apply H2.
    apply conga_refl; auto.
Qed.

End Angles_1.

Ltac ang_instance a A B C :=
  assert(tempo_ang:= ex_points_ang a);
  match goal with
    |H: ang a |-  _ => assert(tempo_H:=H); apply tempo_ang in tempo_H;
                       elim tempo_H; intros A ; intro tempo_HP; clear tempo_H;
                       elim tempo_HP; intro B; intro tempo_HQ ; clear tempo_HP ;
                       elim tempo_HQ; intro C; intro;  clear tempo_HQ
  end;
  clear tempo_ang.

Section Angles_2.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma ang_conga : forall a A B C A' B' C', ang a -> a A B C -> a A' B' C' -> Conga A B C A' B' C'.
Proof.
    intros.
    unfold ang in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH:=H3 A B C).
    assert(HH1:= H3 A' B' C').
    destruct HH.
    destruct HH1.
    apply H5 in H0.
    apply H7 in H1.
    eapply conga_trans.
      apply conga_sym.
      apply H0.
    auto.
Qed.

Definition is_ang := fun A B C a => ang a /\ a A B C.

Lemma is_ang_conga : forall A B C A' B' C' a, is_ang A B C a -> is_ang A' B' C' a -> Conga A B C A' B' C'.
Proof.
    intros.
    unfold is_ang in *.
    spliter.
    eapply (ang_conga a); auto.
Qed.

Lemma is_ang_conga_is_ang : forall A B C A' B' C' a, is_ang A B C a -> Conga A B C A' B' C' -> is_ang A' B' C' a.
Proof.
    intros.
    unfold is_ang in *.
    spliter.
    split.
      auto.
    unfold ang in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH:= H3 A B C).
    destruct HH.
    assert(HH1:= H3 A' B' C').
    destruct HH1.
    apply H5 in H1.
    apply H6.
    eapply conga_trans.
      apply H1.
    auto.
Qed.

Lemma not_conga_not_ang : forall A B C A' B' C' a , ang a -> ~(Conga A B C A' B' C') -> a A B C -> ~(a A' B' C').
Proof.
    intros.
    intro.
    assert(HH:=ang_conga a A B C A' B' C' H H1 H2).
    contradiction.
Qed.

Lemma not_conga_is_ang : forall A B C A' B' C' a , ~(Conga A B C A' B' C') -> is_ang A B C a -> ~(a A' B' C').
Proof.
    intros.
    unfold is_ang in H0.
    spliter.
    intro.
    apply H.
    apply (ang_conga a); auto.
Qed.

Lemma not_cong_is_ang1 : forall A B C A' B' C' a , ~(Conga A B C A' B' C') -> is_ang A B C a -> ~(is_ang A' B' C' a).
Proof.
    intros.
    intro.
    unfold is_ang in *.
    spliter.
    apply H.
    apply (ang_conga a); auto.
Qed.

Definition eqA (a1 a2 : Tpoint -> Tpoint -> Tpoint -> Prop) := forall A B C, a1 A B C <-> a2 A B C.

Lemma ex_eqa : forall a1 a2, (exists A , exists B, exists C, is_ang A B C a1 /\ is_ang A B C a2)  -> eqA a1 a2.
Proof.
    intros.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    assert(HH:=H).
    assert(HH0:=H0).
    unfold is_ang in HH.
    unfold is_ang in HH0.
    spliter.
    unfold eqA.
    repeat split; auto; intro.
      assert(Conga A B C A0 B0 C0).
        eapply (is_ang_conga _ _ _ _ _ _ a1); auto.
        split; auto.
      assert(is_ang A0 B0 C0 a2).
        apply (is_ang_conga_is_ang A B C); auto.
      unfold is_ang in H7.
      tauto.
    assert(Conga A B C A0 B0 C0).
      eapply (is_ang_conga _ _ _ _ _ _ a2); auto.
      split; auto.
    assert(is_ang A0 B0 C0 a1).
      apply (is_ang_conga_is_ang A B C); auto.
    unfold is_ang in H7.
    tauto.
Qed.

Lemma all_eqa : forall A B C a1 a2, is_ang A B C a1 -> is_ang A B C a2 -> eqA a1 a2.
Proof.
    intros.
    apply ex_eqa.
    exists A.
    exists B.
    exists C.
    split; auto.
Qed.

Lemma is_ang_distinct : forall A B C a , is_ang A B C a -> A <> B /\ C <> B.
Proof.
    intros.
    unfold is_ang in H.
    spliter.
    unfold ang in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= H2 A B C).
    destruct HH.
    apply H4 in H0.
    unfold Conga in H0.
    spliter.
    tauto.
Qed.


Lemma null_ang : forall A B C D a1 a2, is_ang A B A a1 -> is_ang C D C a2 -> eqA a1 a2.
Proof.
    intros.
    eapply (all_eqa A B A).
      apply H.
    eapply (is_ang_conga_is_ang C D C).
      auto.
    eapply l11_21_b.
      apply out_trivial.
      apply is_ang_distinct in H0.
      tauto.
    apply out_trivial.
    apply is_ang_distinct in H.
    tauto.
Qed.

Lemma flat_ang : forall A B C A' B' C' a1 a2, Bet A B C -> Bet A' B' C' -> is_ang A B C a1 -> is_ang A' B' C' a2  -> eqA a1 a2.
Proof.
    intros.
    eapply (all_eqa A B C).
      apply H1.
    eapply (is_ang_conga_is_ang A' B' C').
      apply H2.
    apply is_ang_distinct in H1.
    apply is_ang_distinct in H2.
    spliter.
    eapply conga_line; auto.
      unfold Distincts.
      repeat split; auto.
      intro.
      subst C'.
      apply between_identity in H0.
      contradiction.
    unfold Distincts.
    repeat split; auto.
    intro.
    subst C.
    apply between_identity in H.
    contradiction.
Qed.

Lemma ang_distinct: forall a A B C, ang a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(is_ang A B C a).
      split; auto.
    apply (is_ang_distinct _ _ _ a); auto.
Qed.

Lemma ex_ang : forall A B C, B <> A -> B <> C -> exists a, ang a /\ a A B C.
Proof.
    intros.
    exists (fun X Y Z => Conga A B C X Y Z).
    unfold ang.
    split.
      exists A.
      exists B.
      exists C.
      split.
        auto.
      split.
        auto.
      intros.
      split.
        intro.
        auto.
      intro.
      auto.
    apply conga_refl; auto.
Qed.

(************************************* acute angle *****************************************)

Definition anga (A : Tpoint -> Tpoint -> Tpoint -> Prop) := exists a, exists b, exists c, acute a b c /\
                                                            forall x y z, Conga a b c x y z <-> A x y z.
Definition anglea  A B C := fun x y z => Conga A B C x y z.

Lemma anga_exists : forall A B C, A <> B -> C <> B -> acute A B C -> exists a, anga a /\ a A B C.
Proof.
    intros.
    exists (angle A B C).
    split.
      unfold ang.
      exists A.
      exists B.
      exists C.
      split.
        auto.
      intros.
      split; auto.
    unfold angle.
    apply conga_refl; auto.
Qed.

Lemma anga_is_ang : forall a, anga a -> ang a.
Proof.
    intros.
    unfold anga in H.
    unfold ang.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    exists A.
    exists B.
    exists C.
    apply acute_distinct in H.
    spliter.
    split.
      auto.
    split.
      auto.
    intros.
    split.
      intro.
      assert(is_ang x y z a).
        unfold is_ang.
        split.
          unfold ang.
          exists A.
          exists B.
          exists C.
          split.
            eapply conga_diff1.
            apply H3.
          split.
            eapply conga_diff2.
            apply H3.
          auto.
        assert(HH:= H0 x y z).
        destruct HH.
        apply H4.
        auto.
      unfold is_ang in H4.
      spliter.
      auto.
    intro.
    assert(HH:= H0 x y z).
    destruct HH.
    apply H5.
    auto.
Qed.

Lemma ex_points_anga : forall a , anga a ->  exists A, exists B, exists C, a A B C.
Proof.
    intros.
    assert(HH:=H).
    apply anga_is_ang in H.
    ang_instance a A B C.
    exists A.
    exists B.
    exists C.
    assumption.
Qed.

End Angles_2.

Ltac anga_instance a A B C :=
  assert(tempo_anga:= ex_points_anga a);
  match goal with
    |H: anga a |-  _ => assert(tempo_H:=H); apply tempo_anga in tempo_H;
                        elim tempo_H; intros A ; intro tempo_HP; clear tempo_H;
                        elim tempo_HP; intro B; intro tempo_HQ ; clear tempo_HP ;
                        elim tempo_HQ; intro C; intro;  clear tempo_HQ
  end;
  clear tempo_anga.

Section Angles_3.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.


Lemma anga_conga : forall a A B C A' B' C', anga a -> a A B C -> a A' B' C' -> Conga A B C A' B' C'.
Proof.
    intros.
    apply (ang_conga a); auto.
    apply anga_is_ang.
    auto.
Qed.

Definition is_anga := fun A B C a => anga a /\ a A B C.

Lemma is_anga_to_is_ang : forall A B C a, is_anga A B C a -> is_ang A B C a.
Proof.
    intros.
    unfold is_anga in H.
    unfold is_ang.
    spliter.
    split.
      apply anga_is_ang.
      auto.
    auto.
Qed.

Lemma is_anga_conga : forall A B C A' B' C' a, is_anga A B C a -> is_anga A' B' C' a -> Conga A B C A' B' C'.
Proof.
    intros.
    unfold is_anga in *.
    spliter.
    apply (anga_conga a); auto.
Qed.

Lemma is_anga_conga_is_anga : forall A B C A' B' C' a, is_anga A B C a -> Conga A B C A' B' C' -> is_anga A' B' C' a.
Proof.
    intros.
    unfold is_anga in *.
    spliter.
    split.
      auto.
    apply anga_is_ang in H.
    unfold ang in H.
    ex_and H A0.
    ex_and H2 B0.
    ex_and H C0.
    assert(HH:= H3 A B C).
    destruct HH.
    assert(HH1:= H3 A' B' C').
    destruct HH1.
    apply H5 in H1.
    apply H6.
    eapply conga_trans.
      apply H1.
    auto.
Qed.

Lemma not_conga_is_anga : forall A B C A' B' C' a , ~ Conga A B C A' B' C' -> is_anga A B C a -> ~(a A' B' C').
Proof.
    intros.
    unfold is_anga in H0.
    spliter.
    intro.
    apply H.
    apply (anga_conga a); auto.
Qed.

Lemma not_cong_is_anga1 : forall A B C A' B' C' a , ~Conga A B C A' B' C' -> is_anga A B C a -> ~ is_anga A' B' C' a.
Proof.
    intros.
    intro.
    unfold is_anga in *.
    spliter.
    apply H.
    apply (anga_conga a); auto.
Qed.

Lemma ex_eqaa : forall a1 a2, (exists A , exists B, exists C, is_anga A B C a1 /\ is_anga A B C a2)  -> eqA a1 a2.
Proof.
    intros.
    apply ex_eqa.
    ex_and H A.
    ex_and H0 B.
    ex_and H C.
    exists A.
    exists B.
    exists C.
    split; apply is_anga_to_is_ang; auto.
Qed.

Lemma all_eqaa : forall A B C a1 a2, is_anga A B C a1 -> is_anga A B C a2 -> eqA a1 a2.
Proof.
    intros.
    apply ex_eqaa.
    exists A.
    exists B.
    exists C.
    split; auto.
Qed.

Lemma is_anga_distinct : forall A B C a , is_anga A B C a -> A <> B /\ C <> B.
Proof.
    intros.
    apply (is_ang_distinct A B C a).
    apply is_anga_to_is_ang.
    auto.
Qed.

Global Instance eqA_equivalence : Equivalence eqA.
Proof.
split.
unfold Reflexive.
intros.
unfold eqA.
intros;tauto.
unfold Symmetric, eqA.
intros.
firstorder.
unfold Transitive, eqA.
intros.
rewrite H.
apply H0.
Qed.

Lemma null_anga : forall A B C D a1 a2, is_anga A B A a1 -> is_anga C D C a2 -> eqA a1 a2.
Proof.
    intros.
    eapply (all_eqaa A B A).
      apply H.
    eapply (is_anga_conga_is_anga C D C).
      auto.
    eapply l11_21_b.
      apply out_trivial.
      apply is_anga_distinct in H0.
      tauto.
    apply out_trivial.
    apply is_anga_distinct in H.
    tauto.
Qed.

Lemma anga_distinct: forall a A B C, anga a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(is_anga A B C a).
      split; auto.
    apply (is_anga_distinct _ _ _ a); auto.
Qed.

Lemma out_is_len_eq : forall A B C l, out A B C -> is_len A B l -> is_len A C l -> B = C.
Proof.
    intros.
    assert(Cong A B A C).
      apply (is_len_cong _ _ _ _ l); auto.
    assert(A <> C).
      unfold out in H.
      spliter.
      auto.
    eapply (l6_11_unicity A A C C ); Cong.
    apply out_trivial.
    auto.
Qed.

Lemma out_len_eq : forall A B C l, lg l -> out A B C -> l A B -> l A C -> B = C.
Proof.
    intros.
    apply (out_is_len_eq A _ _ l).
      auto.
      split; auto.
    split; auto.
Qed.

Lemma ex_anga : forall A B C, acute A B C -> exists a, anga a /\ a A B C.
Proof.
    intros.
    exists (fun X Y Z => Conga A B C X Y Z).
    unfold anga.
    apply acute_distinct in H.
    spliter.
    split.
      exists A.
      exists B.
      exists C.
      split; auto.
      intros.
      intros.
      split.
        intro.
        auto.
      intro.
      auto.
    apply conga_refl; auto.
Qed.

Definition not_null_ang := fun a => ang a /\ forall A B C, a A B C -> ~out B A C.
Definition not_flat_ang := fun a => ang a /\ forall A B C, a A B C -> ~Bet A B C.

Definition not_null_ang' := fun a => ang a /\ exists A, exists B, exists C, a A B C /\  ~out B A C.
Definition not_flat_ang' := fun a => ang a /\ exists A, exists B, exists C, a A B C /\  ~Bet A B C.

Definition is_null_ang := fun a => ang a /\ forall A B C, a A B C -> out B A C.
Definition is_flat_ang := fun a => ang a /\ forall A B C, a A B C -> Bet A B C.

Definition is_null_ang' := fun a => ang a /\ exists A, exists B, exists C, a A B C /\ out B A C.
Definition is_flat_ang' := fun a => ang a /\ exists A, exists B, exists C, a A B C /\ Bet A B C.

Lemma not_null_ang_ang : forall a, not_null_ang a -> ang a.
Proof.
    intros.
    unfold not_null_ang  in H.
    spliter; auto.
Qed.

Lemma not_null_ang_def_equiv : forall a, not_null_ang a <-> not_null_ang' a.
Proof.
    intros.
    split.
      intro.
      unfold not_null_ang in H.
      spliter.
      assert(HH:= H).
      unfold ang in HH.
      ex_and HH A.
      ex_and H1 B.
      ex_and H2 C.
      unfold not_null_ang'.
      split.
        auto.
      exists A.
      exists B.
      exists C.
      assert(HH:= H3 A B C).
      destruct HH.
      assert(a A B C).
        apply H4.
        apply conga_refl; auto.
      split.
        auto.
      apply (H0 A B C).
      auto.
    intros.
    unfold not_null_ang' in H.
    spliter.
    ex_and H0 A.
    ex_and H1 B.
    ex_and H0 C.
    unfold not_null_ang.
    split; auto.
    intros.
    assert(Conga A0 B0 C0 A B C).
      apply (ang_conga a); auto.
    intro.
    apply H1.
    apply (out_conga_out A0 B0 C0); auto.
Qed.

Lemma not_flat_ang_def_equiv : forall a, not_flat_ang a <-> not_flat_ang' a.
Proof.
    intros.
    split.
      intro.
      unfold not_flat_ang in H.
      spliter.
      assert(HH:= H).
      unfold ang in HH.
      ex_and HH A.
      ex_and H1 B.
      ex_and H2 C.
      unfold not_flat_ang'.
      split.
        auto.
      exists A.
      exists B.
      exists C.
      assert(HH:= H3 A B C).
      destruct HH.
      assert(a A B C).
        apply H4.
        apply conga_refl; auto.
      split.
        auto.
      apply (H0 A B C).
      auto.
    intros.
    unfold not_flat_ang' in H.
    spliter.
    ex_and H0 A.
    ex_and H1 B.
    ex_and H0 C.
    unfold not_flat_ang.
    split; auto.
    intros.
    assert(Conga A0 B0 C0 A B C).
      apply (ang_conga a); auto.
    intro.
    apply H1.
    apply (bet_conga_bet A0 B0 C0); auto.
Qed.

Definition is_null_anga := fun a => anga a /\ forall A B C, a A B C -> out B A C.
Definition is_null_anga' := fun a => anga a /\ exists A, exists B, exists C, a A B C /\ out B A C.

Definition not_null_anga := fun a => anga a /\ forall A B C, a A B C -> ~out B A C.

Lemma ang_const : forall a A B, ang a -> A <> B -> exists C, a A B C.
Proof.
    intros.
    unfold ang in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= H2 A0 B0 C0).
    destruct HH.
    assert(a A0 B0 C0).
      apply H3.
      apply conga_refl; auto.
    assert(HH :=not_col_exists A B H0).
    ex_and HH P.
    induction(eq_dec_points A0 C0).
      subst C0.
      exists A.
      assert(HH:= (H2 A B A)).
      destruct HH.
      apply H7.
      apply conga_trivial_1; auto.
    assert(Distincts A0 B0 C0).
      repeat split; auto.
    assert(HH:=angle_construction_2 A0 B0 C0 A B P H8 H0 H6).
    ex_and HH C.
    exists C.
    apply H2.
    auto.
Qed.

End Angles_3.

Ltac ang_instance1 a A B C :=
	assert(tempo_ang:= ang_const a A B);
        match goal with
           |H: ang a |-  _ => assert(tempo_H:= H);apply tempo_ang in tempo_H; ex_elim tempo_H C
        end;
        clear tempo_ang.

Section Angles_4.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma ang_sym : forall a A B C, ang a -> a A B C -> a C B A.
Proof.
    intros.
    unfold ang in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= H2 A B C).
    destruct HH.
    apply H4 in H0.
    apply conga_right_comm in H0.
    assert(HH:= H2 C B A).
    destruct HH.
    apply H5.
    auto.
Qed.

Lemma ang_not_null_lg : forall a l A B C, ang a -> lg l -> a A B C -> l A B -> ~lg_null l.
Proof.
    intros.
    intro.
    unfold ang in H.
    unfold lg_null in H3.
    spliter.
    unfold lg in H0.
    ex_and H A0.
    ex_and H5 B0.
    ex_and H C0.
    assert(HH:= H6 A B C).
    destruct HH.
    assert(Conga A0 B0 C0 A B C).
      apply H8.
      auto.
    apply conga_distinct in H8.
      spliter.
      ex_and H0 A1.
      ex_and H14 B1.
      assert(HH:= H0 A B).
      destruct HH.
      ex_and H4 A'.
      assert(HH:= H0 A' A').
      destruct HH.
      assert(Cong A1 B1 A' A').
        apply H17.
        auto.
      assert(Cong A1 B1 A B).
        apply H15.
        auto.
      apply cong_identity in H17.
        subst B1.
        apply cong_symmetry in H19.
        apply cong_identity in H19.
        contradiction.
      auto.
    auto.
Qed.

Lemma ang_distincts : forall a A B C, ang a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(HH:= ex_lg A B).
    ex_and HH la.
    assert(HH:= ex_lg C B).
    ex_and HH lc.
    assert(HH:= ang_not_null_lg a la A B C H H1 H0 H2).
    assert(a C B A).
      apply ang_sym; auto.
    assert(HQ:= ang_not_null_lg a lc C B A H H3 H5 H4).
    split; intro; subst B.
      apply HH.
      unfold lg_null.
      split.
        auto.
      exists A.
      auto.
    apply HQ.
    unfold lg_null.
    split.
      auto.
    exists C.
    auto.
Qed.

Lemma anga_sym : forall a A B C, anga a -> a A B C -> a C B A.
Proof.
    intros.
    unfold anga in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= H1 A B C).
    destruct HH.
    apply H3 in H0.
    apply conga_right_comm in H0.
    assert(HH:= H1 C B A).
    destruct HH.
    apply H4.
    auto.
Qed.

Lemma anga_not_null_lg : forall a l A B C, anga a -> lg l -> a A B C -> l A B -> ~lg_null l.
Proof.
    intros.
    intro.
    unfold anga in H.
    unfold lg_null in H3.
    spliter.
    unfold lg in H0.
    ex_and H A0.
    ex_and H5 B0.
    ex_and H C0.
    assert(HH:= H5 A B C).
    destruct HH.
    assert(Conga A0 B0 C0 A B C).
      apply H7.
      auto.
    apply conga_distinct in H8.
    spliter.
    ex_and H0 A1.
    ex_and H13 B1.
    assert(HH:= H0 A B).
    destruct HH.
    ex_and H4 A'.
    assert(HH:= H0 A' A').
    destruct HH.
    assert(Cong A1 B1 A' A').
      apply H16.
      auto.
    assert(Cong A1 B1 A B).
      apply H14.
      auto.
    apply cong_identity in H17.
    subst B1.
    apply cong_symmetry in H18.
    apply cong_identity in H18.
    contradiction.
Qed.

Lemma anga_distincts : forall a A B C, anga a -> a A B C -> A <> B /\ C <> B.
Proof.
    intros.
    assert(HH:= ex_lg A B).
    ex_and HH la.
    assert(HH:= ex_lg C B).
    ex_and HH lc.
    assert(HH:= anga_not_null_lg a la A B C H H1 H0 H2).
    assert(a C B A).
      apply anga_sym; auto.
    assert(HQ:= anga_not_null_lg a lc C B A H H3 H5 H4).
    split; intro; subst B.
      apply HH.
      unfold lg_null.
      split.
        auto.
      exists A.
      auto.
    apply HQ.
    unfold lg_null.
    split.
      auto.
    exists C.
    auto.
Qed.

Lemma ang_const_o : forall a A B P, ~Col A B P -> ang a -> not_null_ang a -> not_flat_ang a -> exists C, a A B C /\ one_side A B C P.
Proof.
    intros.
    assert(HH:= H0).
    unfold ang in HH.
    ex_and HH A0.
    ex_and H3 B0.
    ex_and H4 C0.
    assert(HH:= H5 A0 B0 C0).
    destruct HH.
    assert(a A0 B0 C0).
      apply H6.
      apply conga_refl; auto.
    assert(HH:=ang_distincts a A0 B0 C0 H0 H8).
    assert(A0 <> C0).
      intro.
      subst C0.
      unfold not_null_ang in H1.
      spliter.
      assert(HH:=H11 A0 B0 A0 H8).
      apply HH.
      apply out_trivial; auto.
    spliter.
    assert(Distincts A0 B0 C0).
      repeat split; auto.
    assert(A <> B).
      intro.
      subst B.
      apply H.
      Col.
    assert(HH:=angle_construction_2 A0 B0 C0 A B P H12 H13 H).
    ex_and HH C.
    exists C.
    assert(a A B C).
      assert(HH:= H5 A B C).
      destruct HH.
      apply H16.
      auto.
    split.
      auto.
    induction H15.
      auto.
    unfold not_null_ang in H1.
    spliter.
    assert(HH:= H17 A B C H16).
    unfold not_flat_ang in H2.
    spliter.
    assert(Hh:=H18 A B C H16).
    apply False_ind.
    assert(HH0:=ang_distincts a A B C H0 H16).
    spliter.
    assert(HP:=or_bet_out A B C H19 H20).
    induction HP.
      contradiction.
    induction H21.
      contradiction.
    contradiction.
Qed.


Lemma anga_const : forall a A B, anga a -> A <> B -> exists C, a A B C.
Proof.
    intros.
    apply anga_is_ang in H.
    apply ang_const; auto.
Qed.

End Angles_4.

Ltac anga_instance1 a A B C :=
	assert(tempo_anga:= anga_const a A B);
        match goal with
           |H: anga a |-  _ => assert(tempo_H:= H); apply tempo_anga in tempo_H; ex_elim tempo_H C
        end;
        clear tempo_anga.

Section Angles_5.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma null_anga_null_anga' : forall a, is_null_anga a <-> is_null_anga' a.
Proof.
    intro.
    split.
      intro.
      unfold is_null_anga in H.
      unfold is_null_anga'.
      spliter.
      split.
        auto.
      anga_instance a A B C.
      assert(HH:= H0 A B C H1).
      exists A.
      exists B.
      exists C.
      split; auto.
    intro.
    unfold is_null_anga' in H.
    unfold is_null_anga.
    spliter.
    ex_and H0 A.
    ex_and H1 B.
    ex_and H0 C.
    split; auto.
    intros.
    assert(Conga A B C A0 B0 C0).
      apply (anga_conga a); auto.
    apply (out_conga_out A B C); auto.
Qed.

Lemma is_null_anga_out : forall a A B C, anga a -> a A B C -> is_null_anga a -> out B A C.
Proof.
    intros.
    unfold is_null_anga in H1.
    spliter.
    assert(HH:= (H2 A B C)).
    apply HH.
    auto.
Qed.


Lemma acute_not_bet : forall A B C, acute A B C -> ~Bet A B C.
Proof.
    intros.
    unfold acute in H.
    ex_and H A0.
    ex_and H0 B0.
    ex_and H C0.
    unfold lta in H0.
    spliter.
    unfold lea in H0.
    ex_and H0 P.
    unfold InAngle in H0.
    spliter.
    ex_and H5 X.
    intro.
    assert(Distincts A B C).
      apply conga_distinct in H2.
      spliter.
      repeat split; auto.
      intro.
      subst C.
      apply between_identity in H7.
      contradiction.
    induction H6.
      subst X.
      apply H1.
      apply conga_line; auto.
      repeat split; auto.
      intro.
      subst C0.
      apply between_identity in H5.
      contradiction.
    assert(Bet A0 B0 P).
      apply (bet_conga_bet A B C); auto.
    assert(Bet A0 B0 C0).
      unfold out in H6.
      spliter.
      induction H11.
        eBetween.
      eBetween.
    apply H1.
    apply (conga_line A B C); auto.
    apply conga_distinct in H2.
    spliter.
    repeat split; auto.
    intro.
    subst C0.
    apply between_identity in H5.
    subst X.
    apply between_identity in H10.
    contradiction.
Qed.

Lemma anga_acute : forall a A B C , anga a -> a A B C -> acute A B C.
Proof.
    intros.
    unfold anga in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HH:= acute_lea_acute A B C A0 B0 C0).
    apply HH.
      auto.
    unfold lea.
    exists C0.
    split.
      unfold InAngle.
      apply acute_distinct in H.
      spliter.
      repeat split; auto.
      exists C0.
      split.
        Between.
      right.
      apply out_trivial.
      auto.
    assert(HP:= H1 A B C).
    destruct HP.
    apply conga_sym.
    apply H3.
    auto.
Qed.

Lemma acute_col_out : forall A B C, acute A B C -> Col A B C -> out B A C.
Proof.
    intros.
    assert(HH:= acute_not_bet A B C H).
    induction H0.
      contradiction.
    unfold out.
    apply acute_distinct in H.
    spliter.
    repeat split; auto.
    induction H0.
      right.
      auto.
    left.
    Between.
Qed.

Lemma not_null_not_col : forall a A B C, anga a -> ~is_null_anga a -> a A B C -> ~Col A B C.
Proof.
    intros.
    intro.
    apply H0.
    unfold is_null_anga.
    split.
      auto.
    assert(acute A B C).
      apply (anga_acute a); auto.
    intros.
    assert(out B A C).
      apply acute_col_out; auto.
    assert(HH:= anga_conga a A B C A0 B0 C0 H H1 H4).
    apply (out_conga_out A B C); auto.
Qed.


Lemma ang_cong_ang : forall a A B C A' B' C', ang a -> a A B C -> Conga A B C A' B' C' -> a A' B' C'.
Proof.
    intros.
    assert(is_ang A B C a).
      unfold is_ang.
      split; auto.
    assert(is_ang A' B' C' a).
      apply (is_ang_conga_is_ang A B C); auto.
    unfold is_ang in H3.
    tauto.
Qed.

Lemma is_null_ang_out : forall a A B C, ang a -> a A B C -> is_null_ang a -> out B A C.
Proof.
    intros.
    unfold is_null_ang in H1.
    spliter.
    assert(HH:= (H2 A B C)).
    apply HH.
    auto.
Qed.

Lemma out_null_ang : forall a A B C, ang a -> a A B C -> out B A C -> is_null_ang a.
Proof.
    intros.
    unfold is_null_ang.
    split.
      auto.
    intros.
    assert(HH:=out_conga_out A B C A0 B0 C0 H1).
    apply HH.
    apply (ang_conga a); auto.
Qed.

Lemma bet_flat_ang : forall a A B C, ang a -> a A B C -> Bet A B C -> is_flat_ang a.
Proof.
    intros.
    unfold is_flat_ang.
    split.
      auto.
    intros.
    assert(HH:=bet_conga_bet A B C A0 B0 C0 H1).
    apply HH.
    apply (ang_conga a); auto.
Qed.

Lemma out_null_anga : forall a A B C, anga a -> a A B C -> out B A C -> is_null_anga a.
Proof.
    intros.
    unfold is_null_anga.
    split.
      auto.
    intros.
    assert(HH:=out_conga_out A B C A0 B0 C0 H1).
    apply HH.
    apply (anga_conga a); auto.
Qed.

Lemma anga_not_flat : forall a, anga a -> not_flat_ang a.
Proof.
    intros.
    unfold not_flat_ang.
    split.
      apply anga_is_ang in H.
      auto.
    intros.
    assert(HH:= anga_acute a A B C H H0).
    unfold anga in H.
    ex_and H A0.
    ex_and H1 B0.
    ex_and H C0.
    assert(HP:= H1 A B C).
    apply acute_not_bet.
    auto.
Qed.


Lemma anga_const_o : forall a A B P, ~Col A B P -> ~ is_null_anga a -> anga a -> exists C, a A B C /\ one_side A B C P.
Proof.
    intros.
    assert(ang a).
      apply anga_is_ang; auto.
    assert(not_null_ang a).
      unfold not_null_ang.
      split.
        auto.
      intros A' B' C' HP.
      intro.
      apply H0.
      eapply (out_null_anga a A' B' C'); auto.
    assert(not_flat_ang a).
      apply anga_not_flat.
      auto.
    assert(HH:= ang_const_o a A B P H H2 H3 H4).
    auto.
Qed.

End Angles_5.
