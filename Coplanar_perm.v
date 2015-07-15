Require Export Ch10_line_reflexivity.

Section Coplanar_perm.

Context `{MT:Tarski_neutral_dimensionless}.
Context `{EqDec:EqDecidability Tpoint}.

Definition coplanar A B C D :=
  exists X, (Col A B X /\ Col C D X) \/ (Col A C X /\ Col B D X) \/ (Col A D X /\ Col B C X).

Lemma coplanar_perm_1 : forall A B C D,
  coplanar A B C D -> coplanar A B D C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_2 : forall A B C D,
  coplanar A B C D -> coplanar A C B D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_3 : forall A B C D,
  coplanar A B C D -> coplanar A C D B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_4 : forall A B C D,
  coplanar A B C D -> coplanar A D B C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_5 : forall A B C D,
  coplanar A B C D -> coplanar A D C B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_6 : forall A B C D,
  coplanar A B C D -> coplanar B A C D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_7 : forall A B C D,
  coplanar A B C D -> coplanar B A D C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_8 : forall A B C D,
  coplanar A B C D -> coplanar B C A D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_9 : forall A B C D,
  coplanar A B C D -> coplanar B C D A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_10 : forall A B C D,
  coplanar A B C D -> coplanar B D A C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_11 : forall A B C D,
  coplanar A B C D -> coplanar B D C A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_12 : forall A B C D,
  coplanar A B C D -> coplanar C A B D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_13 : forall A B C D,
  coplanar A B C D -> coplanar C A D B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_14 : forall A B C D,
  coplanar A B C D -> coplanar C B A D.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_15 : forall A B C D,
  coplanar A B C D -> coplanar C B D A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_16 : forall A B C D,
  coplanar A B C D -> coplanar C D A B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_17 : forall A B C D,
  coplanar A B C D -> coplanar C D B A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_18 : forall A B C D,
  coplanar A B C D -> coplanar D A B C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_19 : forall A B C D,
  coplanar A B C D -> coplanar D A C B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_20 : forall A B C D,
  coplanar A B C D -> coplanar D B A C.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_21 : forall A B C D,
  coplanar A B C D -> coplanar D B C A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_22 : forall A B C D,
  coplanar A B C D -> coplanar D C A B.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_perm_23 : forall A B C D,
  coplanar A B C D -> coplanar D C B A.
Proof.
intros A B C D HCop.
destruct HCop as [X H]; exists X.
induction H; try (induction H); spliter; Col5.
Qed.

Lemma coplanar_trivial : forall A B C, coplanar A A B C.
Proof.
intros.
exists B; Col5.
Qed.

Lemma col_coplanar : forall A B C D,
  Col A B C -> coplanar A B C D.
Proof.
intros.
exists C; Col5.
Qed.

End Coplanar_perm.

Hint Resolve coplanar_perm_1 coplanar_perm_2 coplanar_perm_3 coplanar_perm_4 coplanar_perm_5 coplanar_perm_6
coplanar_perm_7 coplanar_perm_8 coplanar_perm_9 coplanar_perm_10 coplanar_perm_11 coplanar_perm_12
coplanar_perm_13 coplanar_perm_14 coplanar_perm_15 coplanar_perm_16 coplanar_perm_17 coplanar_perm_18
coplanar_perm_19 coplanar_perm_20 coplanar_perm_21 coplanar_perm_22 coplanar_perm_23
coplanar_trivial col_coplanar : cop.

Ltac Cop := auto 3 with cop.