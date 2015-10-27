 (* Gabriel Braun April 2013 *)

Require Export GeoCoq.Tarski_dev.Ch13_1.

Section Length_1.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

(** Pappus Desargues *)



(******************** length *********************)

Definition lg (A : Tpoint -> Tpoint -> Prop) := exists a, exists b, forall x y, Cong a b x y <-> A x y.

Definition long  A B := fun x y => Cong A B x y.


Lemma lg_exists : forall A B, exists l, lg l /\ l A B.
Proof.
    intros.
    unfold lg.
    exists (fun x y => Cong A B x y).
    split.
      exists A.
      exists B.
      intros.
      split.
        intro.
        unfold long.
        auto.
      intro.
      unfold long in H.
      auto.
    unfold long.
    Cong.
Qed.


Lemma lg_cong : forall l A B C D, lg l -> l A B -> l C D -> Cong A B C D.
Proof.
    intros.
    unfold lg in H.
    ex_and H X.
    ex_and H2 Y.
    assert(HH:= H A B).
    destruct HH.
    assert(HH:= H C D).
    destruct HH.
    apply H3 in H0.
    apply H5 in H1.
    eCong.
Qed.

Lemma lg_cong_lg : forall l A B C D, lg l -> l A B -> Cong A B C D -> l C D.
Proof.
    intros.
    unfold lg in H.
    ex_and H A0.
    ex_and H2 B0.
    assert(HP:= H A B).
    assert(HQ:= H C D).
    destruct HP.
    destruct HQ.
    apply H4.
    eapply cong_transitivity.
      apply H3.
      assumption.
    assumption.
Qed.

Lemma lg_sym : forall l A B, lg l -> l A B -> l B A.
Proof.
    intros.
    apply (lg_cong_lg l A B); Cong.
Qed.

Lemma ex_points_lg : forall l, lg l -> exists A, exists B, l A B.
Proof.
    intros.
    unfold lg in H.
    ex_and H A.
    ex_and H0 B.
    assert(HH:= H A B).
    destruct HH.
    exists A.
    exists B.
    apply H0.
    Cong.
Qed.

End Length_1.

Ltac lg_instance l A B :=
  assert(tempo_sg:= ex_points_lg l);
  match goal with
    |H: lg l |-  _ => assert(tempo_H:=H); apply tempo_sg in tempo_H; elim tempo_H; intros A ; intro tempo_HP; clear tempo_H; elim tempo_HP; intro B; intro; clear tempo_HP
  end;
  clear tempo_sg.

Section Length_2.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Definition is_len := fun A B l => lg l /\ l A B.


Lemma is_len_cong : forall A B C D l, is_len A B l -> is_len C D l -> Cong A B C D.
Proof.
    intros.
    unfold is_len in *.
    spliter.
    eapply (lg_cong l); auto.
Qed.

Lemma is_len_cong_is_len : forall A B C D l, is_len A B l -> Cong A B C D -> is_len C D l.
Proof.
    intros.
    unfold is_len in *.
    spliter.
    split.
      auto.
    unfold lg in H.
    ex_and H a.
    ex_and H2 b.
    assert(HH:= H A B).
    destruct HH.
    assert(HH1:= H C D).
    destruct HH1.
    apply H3 in H1.
    apply H4.
    eCong.
Qed.

Lemma not_cong_is_len : forall A B C D l , ~(Cong A B C D) -> is_len A B l -> ~(l C D).
Proof.
    intros.
    unfold is_len in H0.
    spliter.
    intro.
    apply H.
    apply (lg_cong l); auto.
Qed.

Lemma not_cong_is_len1 : forall A B C D l , ~Cong A B C D -> is_len A B l -> ~is_len C D l.
Proof.
    intros.
    intro.
    unfold is_len in *.
    spliter.
    apply H.
    apply (lg_cong l); auto.
Qed.

Definition lg_null := fun l => lg l /\ exists A, l A A.

Lemma lg_null_instance : forall l A, lg_null l -> l A A.
Proof.
    intros.
    unfold lg_null in H.
    spliter.
    unfold lg in H.
    ex_and H X.
    ex_and H1 Y.
    assert(HH:= H A A).
    destruct HH.
    ex_and H0 P.
    assert(HH:=(H P P)).
    destruct HH.
    apply H4 in H3.
    apply H1.
    apply cong_symmetry in  H3.
    apply cong_reverse_identity in H3.
    subst Y.
    apply cong_trivial_identity.
Qed.

Lemma lg_null_trivial : forall l A, lg l -> l A A -> lg_null l.
Proof.
    intros.
    unfold lg_null.
    split.
      auto.
    exists A.
    auto.
Qed.

Lemma lg_null_dec : forall l, lg l -> lg_null l \/ ~lg_null l.
Proof.
    intros.
    assert(HH:=H).
    unfold lg in H.
    ex_and H A.
    ex_and H0 B.
    induction(eq_dec_points A B).
      subst B.
      left.
      unfold lg_null.
      split.
        auto.
      exists A.
      apply H.
      Cong.
    right.
    intro.
    unfold lg_null in H1.
    spliter.
    ex_and H2 P.
    apply H0.
    assert(Cong A B P P).
      apply H; auto.
    apply cong_identity in H2.
    auto.
Qed.

Lemma ex_point_lg : forall l A, lg l -> exists B, l A B.
Proof.
    intros.
    induction(lg_null_dec l).
      exists A.
      apply lg_null_instance.
      auto.
      assert(HH:= H).
      unfold lg in HH.
      ex_and HH X.
      ex_and H1 Y.
      assert(HH:= other_point_exists A).
      ex_and HH P.
      assert(HP:= H2 X Y).
      destruct HP.
      assert(l X Y).
        apply H3.
        apply cong_reflexivity.
      assert(X <> Y).
        intro.
        subst Y.
        apply H0.
        unfold lg_null.
        split.
          auto.
        exists X.
        auto.
      assert(HH:= segment_construction_3 A P X Y H1 H6).
      ex_and HH B.
      exists B.
      assert(HH:= H2 A B).
      destruct HH.
      apply H9.
      Cong.
    auto.
Qed.




Lemma ex_point_lg_out : forall l A P, A <> P -> lg l -> ~lg_null l -> exists B, l A B /\ out A B P.
Proof.
    intros.
    assert(HH:= H0).
    unfold lg in HH.
    ex_and HH X.
    ex_and H2 Y.
    assert(HP:= H3 X Y).
    destruct HP.
    assert(l X Y).
      apply H2.
      apply cong_reflexivity.
    assert(X <> Y).
      intro.
      subst Y.
      apply H1.
      unfold lg_null.
      split.
        auto.
      exists X.
      auto.
    assert(HH:= segment_construction_3 A P X Y H H6).
    ex_and HH B.
    exists B.
    split.
      assert(HH:= H3 A B).
      destruct HH.
      apply H9.
      Cong.
    apply l6_6.
    auto.
Qed.

Lemma ex_point_lg_bet : forall l A M, lg l -> exists B : Tpoint, l M B /\ Bet A M B.
Proof.
    intros.
    assert(HH:= H).
    unfold lg in HH.
    ex_and HH X.
    ex_and H0 Y.
    assert(HP:= H1 X Y).
    destruct HP.
    assert(l X Y).
      apply H0.
      apply cong_reflexivity.
    prolong A M B X Y.
    exists B.
    split; auto.
    eapply (lg_cong_lg l X Y); Cong.
Qed.

End Length_2.

Ltac lg_instance1 l A B :=
  assert(tempo_sg:= ex_point_lg l);
  match goal with
    |H: lg l |-  _ => assert(tempo_H:=H); apply (tempo_sg A) in tempo_H; ex_elim tempo_H B; exists B
  end;
  clear tempo_sg.

(* TODO : translate this kind of notations *)
Tactic Notation "soit" ident(A) ident(B) "de" "longueur" ident(l) := lg_instance1 l A B.

Ltac lg_instance2 l A P B :=
  assert(tempo_sg:= ex_point_lg_out l);
  match goal with
    |H: A <> P |-  _ =>
                        match goal with
                           |HP : lg l |-  _ =>
                                               match goal with
                                                 |HQ : ~lg_null l |-  _ => assert(tempo_HQ:=HQ);
                                                                           apply (tempo_sg A P H HP) in tempo_HQ;
                                                                           ex_and tempo_HQ B
                                               end
                        end
  end;
  clear tempo_sg.


Tactic Notation "soit" ident(B) "sur" "la" "demie" "droite" ident(A) ident(P) "/" "longueur" ident(A) ident(B) "=" ident(l) := lg_instance2 l A P B.

Section Length_3.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma ex_points_lg_not_col : forall l P, lg l -> ~ lg_null l -> exists A, exists B, l A B /\ ~Col A B P.
Proof.
    intros.
    assert(HH:=other_point_exists P).
    ex_elim HH A.
    assert(HH:= not_col_exists P A H1).
    ex_elim HH Q.
    exists A.
    assert(A <> Q).
      intro.
      subst Q.
      apply H2.
      Col.
    lg_instance2 l A Q B.
    exists B.
    split.
      auto.
    intro.
    apply H2.
    assert(A <> B).
      intro.
      subst B.
      unfold out in H5.
      tauto; apply out_col in H5.
    apply out_col in H5.
    ColR.
Qed.

End Length_3.

Ltac lg_instance_not_col l P A B :=
  assert(tempo_sg:= ex_points_lg_not_col l P);
  match goal with
        |HP : lg l |-  _ => match goal with
                                  |HQ : ~lg_null l |-  _ => assert(tempo_HQ:=HQ);
                                                            apply (tempo_sg HP) in tempo_HQ;
                                                            elim tempo_HQ;
                                                            intro A;
                                                            intro tempo_HR;
                                                            elim tempo_HR;
                                                            intro B;
                                                            intro;
                                                            spliter;
                                                            clear tempo_HR tempo_HQ
                            end
  end;
  clear tempo_sg.



Tactic Notation "soit" ident(B) "sur" "la" "demie" "droite" ident(A) ident(P) "/" "longueur" ident(A) ident(B) "=" ident(l) := lg_instance2 l A P B.

Section Length_4.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Definition eqL := fun (l1 l2 : Tpoint -> Tpoint -> Prop)=>  forall A B, l1 A B <-> l2 A B.

Notation "l1 =l= l2" := (eqL l1 l2) (at level 80, right associativity).

Lemma ex_eql : forall l1 l2, (exists A , exists B, is_len A B l1 /\ is_len A B l2)  -> l1 =l= l2.
Proof.
    intros.
    ex_and H A.
    ex_and H0 B.
    assert(HH:=H).
    assert(HH0:=H0).
    unfold is_len in HH.
    unfold is_len in HH0.
    spliter.
    unfold eqL.
    repeat split; auto.
      intro.
      assert(is_len A0 B0 l1).
        unfold is_len.
        split; auto.
      assert(Cong A B A0 B0).
        apply (is_len_cong _ _ _ _ l1); auto.
      assert(is_len A0 B0 l2).
        apply(is_len_cong_is_len A B).
          apply H0.
        auto.
      unfold is_len in H8.
      spliter.
      auto.
    intro.
    assert(is_len A0 B0 l2).
      unfold is_len.
      split; auto.
    assert(Cong A B A0 B0).
      apply (is_len_cong _ _ _ _ l2); auto.
    assert(is_len A0 B0 l1).
      apply(is_len_cong_is_len A B).
        apply H.
      auto.
    unfold is_len in H8.
    spliter.
    auto.
Qed.


Lemma all_eql : forall A B l1 l2, is_len A B l1 -> is_len A B l2 -> eqL l1 l2.
Proof.
    intros.
    apply ex_eql.
    exists A.
    exists B.
    split; auto.
Qed.



Lemma null_len : forall A B la lb, is_len A A la -> is_len B B lb -> eqL la lb.
Proof.
    intros.
    eapply (all_eql A A).
      apply H.
    eapply (is_len_cong_is_len B B); Cong.
Qed.

Require Export Setoid.

Global Instance eqL_equivalence : Equivalence eqL.
Proof.
split.
- unfold Reflexive.
  intros.
  unfold eqL.
  intros.
  tauto.
- unfold Symmetric.
  intros.
  unfold eqL in *.
  firstorder.
- unfold Transitive.
  unfold eqL.
  intros.
  rewrite H.
  apply H0.
Qed.


Lemma ex_lg : forall A B, exists l, lg l /\ l A B.
Proof.
    intros.
    exists (fun C D => Cong A B C D).
    unfold lg.
    split.
      exists A. exists B.
      tauto.
    Cong.
Qed.



End Length_4.