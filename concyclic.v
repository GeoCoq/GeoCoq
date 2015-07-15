Require Import circumcenter.

Section Concyclic.

Context `{MT:Tarski_2D_euclidean}.
Context `{EqDec:EqDecidability Tpoint}.

Definition concyclic A B C D := coplanar A B C D /\ exists O, Cong O A O B /\ Cong O A O C /\ Cong O A O D.

Lemma concyclic_trans : forall A B C D E,
 ~ Col A B C -> 
 concyclic A B C D  -> concyclic A B C E -> concyclic A B D E.
Proof.
intros.
unfold concyclic in *.
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
  concyclic A B C D -> concyclic A B D C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_2 : forall A B C D,
  concyclic A B C D -> concyclic A C B D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_3 : forall A B C D,
  concyclic A B C D -> concyclic A C D B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_4 : forall A B C D,
  concyclic A B C D -> concyclic A D B C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_5 : forall A B C D,
  concyclic A B C D -> concyclic A D C B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_6 : forall A B C D,
  concyclic A B C D -> concyclic B A C D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_7 : forall A B C D,
  concyclic A B C D -> concyclic B A D C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_8 : forall A B C D,
  concyclic A B C D -> concyclic B C A D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_9 : forall A B C D,
  concyclic A B C D -> concyclic B C D A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_10 : forall A B C D,
  concyclic A B C D -> concyclic B D A C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_11 : forall A B C D,
  concyclic A B C D -> concyclic B D C A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_12 : forall A B C D,
  concyclic A B C D -> concyclic C A B D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_13 : forall A B C D,
  concyclic A B C D -> concyclic C A D B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_14 : forall A B C D,
  concyclic A B C D -> concyclic C B A D.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_15 : forall A B C D,
  concyclic A B C D -> concyclic C B D A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_16 : forall A B C D,
  concyclic A B C D -> concyclic C D A B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_17 : forall A B C D,
  concyclic A B C D -> concyclic C D B A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_18 : forall A B C D,
  concyclic A B C D -> concyclic D A B C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_19 : forall A B C D,
  concyclic A B C D -> concyclic D A C B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_20 : forall A B C D,
  concyclic A B C D -> concyclic D B A C.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_21 : forall A B C D,
  concyclic A B C D -> concyclic D B C A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_22 : forall A B C D,
  concyclic A B C D -> concyclic D C A B.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

Lemma concyclic_perm_23 : forall A B C D,
  concyclic A B C D -> concyclic D C B A.
Proof.
intros A B C D H.
destruct H as [H1 [X H2]].
split; try apply all_coplanar; spliter; exists X; repeat split; eCong.
Qed.

End Concyclic.