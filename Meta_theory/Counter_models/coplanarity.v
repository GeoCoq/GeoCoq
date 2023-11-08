Require Export GeoCoq.Tarski_dev.Annexes.coplanar.
Require Export GeoCoq.Tarski_dev.Ch09_plane.

Section Coplanarity.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Definition InPlane P A B C := exists Q, Col A B Q /\ Col C P Q.

Definition InPlane' P A B C := Col A B P \/ OS A B C P \/ TS A B C P.

Definition Cop A B C D := exists E F G,
  ~ Col E F G /\ InPlane A E F G /\ InPlane B E F G /\
                 InPlane C E F G /\ InPlane D E F G.

Definition Copl A B C D := exists E F G,
  ~ Col E F G /\ InPlane' A E F G /\ InPlane' B E F G /\
                 InPlane' C E F G /\ InPlane' D E F G.

Lemma InPlane__Coplanar : forall A B C P, InPlane P A B C -> Coplanar A B C P.
Proof. intros A B C P [Q []]; exists Q; Col. Qed.

Lemma InPlane'__Coplanar : forall A B C P, InPlane' P A B C -> Coplanar A B C P.
Proof. intros A B C P [|[|]]; Cop; apply os__coplanar; auto. Qed.

Lemma Cop_1243 : forall A B C D, Cop A B C D -> Cop A B D C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_1324 : forall A B C D, Cop A B C D -> Cop A C B D.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_1342 : forall A B C D, Cop A B C D -> Cop A C D B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_1423 : forall A B C D, Cop A B C D -> Cop A D B C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_1432 : forall A B C D, Cop A B C D -> Cop A D C B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_2134 : forall A B C D, Cop A B C D -> Cop B A C D.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_2143 : forall A B C D, Cop A B C D -> Cop B A D C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_2314 : forall A B C D, Cop A B C D -> Cop B C A D.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_2341 : forall A B C D, Cop A B C D -> Cop B C D A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_2413 : forall A B C D, Cop A B C D -> Cop B D A C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_2431 : forall A B C D, Cop A B C D -> Cop B D C A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_3124 : forall A B C D, Cop A B C D -> Cop C A B D.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_3142 : forall A B C D, Cop A B C D -> Cop C A D B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_3214 : forall A B C D, Cop A B C D -> Cop C B A D.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_3241 : forall A B C D, Cop A B C D -> Cop C B D A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_3412 : forall A B C D, Cop A B C D -> Cop C D A B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_3421 : forall A B C D, Cop A B C D -> Cop C D B A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_4123 : forall A B C D, Cop A B C D -> Cop D A B C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_4132 : forall A B C D, Cop A B C D -> Cop D A C B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_4213 : forall A B C D, Cop A B C D -> Cop D B A C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_4231 : forall A B C D, Cop A B C D -> Cop D B C A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_4312 : forall A B C D, Cop A B C D -> Cop D C A B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Cop_4321 : forall A B C D, Cop A B C D -> Cop D C B A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Hint Resolve Cop_1243 Cop_1324 Cop_1342 Cop_1423 Cop_1432
     Cop_2134 Cop_2143 Cop_2314 Cop_2341 Cop_2413 Cop_2431
     Cop_3124 Cop_3142 Cop_3214 Cop_3241 Cop_3412 Cop_3421
     Cop_4123 Cop_4132 Cop_4213 Cop_4231 Cop_4312 Cop_4321 : copl_perm.

Ltac Copl := auto; try (auto 2 with copl_perm).

Lemma Copl_1243 : forall A B C D, Copl A B C D -> Copl A B D C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_1324 : forall A B C D, Copl A B C D -> Copl A C B D.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_1342 : forall A B C D, Copl A B C D -> Copl A C D B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_1423 : forall A B C D, Copl A B C D -> Copl A D B C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_1432 : forall A B C D, Copl A B C D -> Copl A D C B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_2134 : forall A B C D, Copl A B C D -> Copl B A C D.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_2143 : forall A B C D, Copl A B C D -> Copl B A D C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_2314 : forall A B C D, Copl A B C D -> Copl B C A D.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_2341 : forall A B C D, Copl A B C D -> Copl B C D A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_2413 : forall A B C D, Copl A B C D -> Copl B D A C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_2431 : forall A B C D, Copl A B C D -> Copl B D C A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_3124 : forall A B C D, Copl A B C D -> Copl C A B D.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_3142 : forall A B C D, Copl A B C D -> Copl C A D B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_3214 : forall A B C D, Copl A B C D -> Copl C B A D.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_3241 : forall A B C D, Copl A B C D -> Copl C B D A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_3412 : forall A B C D, Copl A B C D -> Copl C D A B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_3421 : forall A B C D, Copl A B C D -> Copl C D B A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_4123 : forall A B C D, Copl A B C D -> Copl D A B C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_4132 : forall A B C D, Copl A B C D -> Copl D A C B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_4213 : forall A B C D, Copl A B C D -> Copl D B A C.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_4231 : forall A B C D, Copl A B C D -> Copl D B C A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_4312 : forall A B C D, Copl A B C D -> Copl D C A B.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Lemma Copl_4321 : forall A B C D, Copl A B C D -> Copl D C B A.
Proof.
intros A B C D [E [F [G]]]; spliter; exists E, F, G; repeat split; auto.
Qed.

Hint Resolve Copl_1243 Copl_1324 Copl_1342 Copl_1423 Copl_1432
     Copl_2134 Copl_2143 Copl_2314 Copl_2341 Copl_2413 Copl_2431
     Copl_3124 Copl_3142 Copl_3214 Copl_3241 Copl_3412 Copl_3421
     Copl_4123 Copl_4132 Copl_4213 Copl_4231 Copl_4312 Copl_4321 : copla_perm.

Ltac Copl' := auto; try (auto 2 with copla_perm).

Lemma l9_33 : forall A B C D, Copl A B C D <-> Coplanar A B C D.
Proof.
intros A B C D; split; [intros [E [F [G]]]; spliter|intro HCop];
[apply coplanar_pseudo_trans with E F G; auto; apply InPlane'__Coplanar; auto|].
assert (HE : forall A B C D, A <> B -> Coplanar A B C D -> Copl A B C D).
  {
  clear -TnEQD; intros A B C D HAB HCop.
  elim (col_dec A B C); intro HABC; elim (col_dec A B D); intro HABD.

    {
    destruct (not_col_exists A B) as [E]; auto.
    exists A, B, E; repeat split; auto; left; Col.
    }

    {
    exists A, B, D; repeat split; auto;
    [left..|right; left; apply one_side_reflexivity]; Col.
    }

    {
    exists A, B, C; repeat split; auto;
    [left..|right; left; apply one_side_reflexivity|left]; Col.
    }

    {
    exists A, B, C; repeat split; auto;
    [left..|right; left; apply one_side_reflexivity|]; Col.
    destruct (cop__one_or_two_sides A B C D); Col; right; [right|left]; auto.
    }
  }
elim (eq_dec_points A B); intro; [|cut (Copl A B C D); [Copl'|apply HE; Cop]].
elim (eq_dec_points A C); intro; [|cut (Copl A C B D); [Copl'|apply HE; Cop]].
elim (eq_dec_points A D); intro; [|cut (Copl A D B C); [Copl'|apply HE; Cop]].
elim (eq_dec_points B C); intro; [|cut (Copl B C A D); [Copl'|apply HE; Cop]].
elim (eq_dec_points B D); intro; [|cut (Copl B D A C); [Copl'|apply HE; Cop]].
elim (eq_dec_points C D); intro; [|cut (Copl C D A B); [Copl'|apply HE; Cop]].
subst B; subst C; subst D; destruct (another_point A) as [B].
destruct (not_col_exists A B) as [C]; auto.
exists A, B, C; repeat split; [|left..]; Col.
Qed.

Lemma Cop_aabc : forall A B C, Cop A A B C.
Proof.
intros A B C; assert (HE : forall A B C, A <> B -> Cop A A B C).
  {
  clear -TnEQD; intros A B C HAB.
  elim (col_dec A B C); intro HC; [destruct (not_col_exists A B) as [D]; auto|];
  [exists A, B, D; repeat split; [|exists A..|exists B|exists C]; Col|].
  exists A, B, C; repeat split; [|exists A..|exists B|exists A]; Col.
  }
elim (eq_dec_points A B); intro; [|cut (Cop A A B C); [Copl|apply HE; auto]].
elim (eq_dec_points A C); intro; [|cut (Cop A A C B); [Copl|apply HE; auto]].
subst B; subst C; destruct (another_point A) as [B].
destruct (not_col_exists A B) as [C]; auto.
exists A, B, C; repeat split; [|exists A..]; Col.
Qed.

Lemma Cop__Coplanar : forall A B C D, Cop A B C D <-> Coplanar A B C D.
Proof.
intros A B C D; split; [intros [E [F [G]]]; spliter|intros [X HX]];
[apply coplanar_pseudo_trans with E F G; auto; apply InPlane__Coplanar; auto|].
assert (HE : forall A B C D, Col A B X -> Col C D X -> Cop A B C D).
  {
  clear -TnEQD; intros A B C D HC1 HC2.
  elim (eq_dec_points A B); intro HAB; [subst; apply Cop_aabc|].
  assert (HE : forall A B C D,
             (Col A B C /\ Col A B D) \/ ~ (Col A B C /\ Col A B D)).
    {
    clear -TnEQD; intros A B C D.
    elim (col_dec A B C); elim (col_dec A B D); tauto.
    }
  elim (HE A B C D); [intros [HC3 HC4]|]; clear HE.

    {
    assert (HY : exists Y, X <> Y /\ Col X Y A /\ Col X Y B /\
                           Col X Y C /\ Col X Y D).
      {
      elim (eq_dec_points A X); intro; [|exists A; repeat split; ColR].
      elim (eq_dec_points B X); intro; [|exists B; repeat split; ColR].
      subst A; subst B; exfalso; intuition.
      }
    destruct HY as [Y]; spliter.
    destruct (not_col_exists X Y) as [Z]; auto.
    exists X, Y, Z; repeat split; [|exists A|exists B|exists C|exists D]; Col.
    }

    {
    intro HC; assert (HNC : ~ Col A B C \/ ~ Col A B D);
    [elim (col_dec A B C); elim (col_dec A B D); tauto|clear HC].
    destruct HNC as [HNC|HNC]; [exists A, B, C|exists A, B, D];
    repeat split; Col; try solve [exists A; Col]; try solve [exists B; Col];
    try solve [exists X; Col].
    }
  }
destruct HX as [[]|HX]; [cut (Cop A B C D); [Copl|apply HE; Col]|].
destruct HX as [[]|HX]; [cut (Cop A C B D); [Copl|apply HE; Col]|].
destruct HX as []; cut (Cop A D B C); [Copl|apply HE; Col].
Qed.

End Coplanarity.