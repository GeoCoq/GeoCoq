Require Import GeoCoq.Tarski_dev.Ch05_bet_le.
Require Import GeoCoq.Axioms.continuity_axioms.

Require Import Logic.ChoiceFacts.

Section CantorVariant.

Context `{TnEQD:Tarski_neutral_dimensionless_with_decidable_point_equality}.

Definition Nested_bis (A B:nat -> Tpoint -> Prop) :=
  (forall n, exists An Bn, A n An /\ B n Bn) /\
  (forall n An An', A n An -> A n An' -> An = An') /\
  (forall n Bn Bn', B n Bn -> B n Bn' -> Bn = Bn') /\
  forall n An Am Bm Bn,
    A n An -> A (S n) Am -> B (S n) Bm -> B n Bn -> Bet An Am Bm /\ Bet Am Bm Bn /\ Am <> Bm.

Definition cantor_variant := forall A B, Nested_bis A B ->
  exists X, forall n An Bn, A n An -> B n Bn -> Bet An X Bn.

Lemma nested_bis__nested : forall A B, Nested_bis A B -> Nested A B.
Proof.
  unfold Nested_bis, Nested; intros; spliter; split; assumption.
Qed.

Lemma cantor__cantor_variant : FunctionalChoice_on nat Tpoint ->
  cantor_s_axiom <-> cantor_variant.
Proof.
  intro choice.
  split.
    intros cantor A B HAB; apply cantor, nested_bis__nested, HAB.
  intros cantor A B [H1 H2].
  destruct (choice A) as [fA HfA].
    intro n; destruct (H1 n) as [An [_ [HAn _]]]; exists An; exact HAn.
  destruct (choice B) as [fB HfB].
    intro n; destruct (H1 n) as [_ [Bn [_ HBn]]]; exists Bn; exact HBn.
  assert (HN : Nested_bis (fun n => (fun An => An = fA n)) (fun n => (fun Bn => Bn = fB n))).
  { split; [|split; [|split]]; intro n.
    - exists (fA n), (fB n); split; apply eq_refl.
    - intros; subst; apply eq_refl.
    - intros; subst; apply eq_refl.
    - intros An Am Bm Bn; intros; subst.
      apply (H2 n); auto.
  }
  apply cantor in HN.
  destruct HN as [X HX].
  exists X.
  intros n An Bn HAn HBn.
  destruct (H2 n An (fA (S n)) (fB (S n)) Bn) as [HBet1 [HBet2 Hd]]; auto.
  assert (HBet3 : Bet (fA (S n)) X (fB (S n))) by (apply (HX (S n)); apply eq_refl).
  clear dependent A; clear dependent B.
  apply bet3__bet with (fA (S n)) (fB (S n)); eBetween.
Qed.

End CantorVariant.