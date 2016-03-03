Require Import GeoCoq.Highschool.circumcenter.

Section Concyclic.

Context `{MT:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

Definition Concyclic A B C D := Coplanar A B C D /\ exists O, Cong O A O B /\ Cong O A O C /\ Cong O A O D.

Lemma concyclic_trans : forall A B C D E,
 ~ Col A B C ->
 Concyclic A B C D  -> Concyclic A B C E -> Concyclic A B D E.
Proof.
intros.
unfold Concyclic in *.
decompose [ex and] H0;clear H0.
decompose [ex and] H1;clear H1.
split.
apply all_coplanar.
exists x.
repeat split;Cong.
assert (x=x0).
assert_diffs.
apply is_circumcenter_unicity with A B C;try assumption.
unfold is_circumcenter;split;eCong.
unfold is_circumcenter;split;eCong.
subst.
Cong.
Qed.

Lemma concyclic_perm_1: forall A B C D,
  Concyclic A B C D -> Concyclic A B D C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_2 : forall A B C D,
  Concyclic A B C D -> Concyclic A C B D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_3 : forall A B C D,
  Concyclic A B C D -> Concyclic A C D B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_4 : forall A B C D,
  Concyclic A B C D -> Concyclic A D B C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_5 : forall A B C D,
  Concyclic A B C D -> Concyclic A D C B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_6 : forall A B C D,
  Concyclic A B C D -> Concyclic B A C D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_7 : forall A B C D,
  Concyclic A B C D -> Concyclic B A D C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_8 : forall A B C D,
  Concyclic A B C D -> Concyclic B C A D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_9 : forall A B C D,
  Concyclic A B C D -> Concyclic B C D A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_10 : forall A B C D,
  Concyclic A B C D -> Concyclic B D A C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_11 : forall A B C D,
  Concyclic A B C D -> Concyclic B D C A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_12 : forall A B C D,
  Concyclic A B C D -> Concyclic C A B D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_13 : forall A B C D,
  Concyclic A B C D -> Concyclic C A D B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_14 : forall A B C D,
  Concyclic A B C D -> Concyclic C B A D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_15 : forall A B C D,
  Concyclic A B C D -> Concyclic C B D A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_16 : forall A B C D,
  Concyclic A B C D -> Concyclic C D A B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_17 : forall A B C D,
  Concyclic A B C D -> Concyclic C D B A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_18 : forall A B C D,
  Concyclic A B C D -> Concyclic D A B C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_19 : forall A B C D,
  Concyclic A B C D -> Concyclic D A C B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_20 : forall A B C D,
  Concyclic A B C D -> Concyclic D B A C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_21 : forall A B C D,
  Concyclic A B C D -> Concyclic D B C A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_22 : forall A B C D,
  Concyclic A B C D -> Concyclic D C A B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_23 : forall A B C D,
  Concyclic A B C D -> Concyclic D C B A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_1123 : forall A B C,
 ~ Col A B C ->
 Concyclic A A B C.
Proof.
intros A B C HABC.
unfold Concyclic.
split.
apply coplanar_trivial.
destruct (exists_circumcenter A B C HABC) as [G HG].
exists G.
apply circumcenter_cong in HG;spliter;Cong.
Qed.

End Concyclic.
