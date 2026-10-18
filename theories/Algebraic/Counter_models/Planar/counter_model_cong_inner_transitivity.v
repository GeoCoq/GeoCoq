Require Import GeoCoq.Algebraic.Counter_models.Planar.independence.

Inductive Point := P0 | P1 | P2.
Definition Bet (A B C : Point) := A = B \/ B = C.
Definition Cong (A B C D : Point) := (A = B) \/ (B = C /\ A = D).
Definition PA := P0.
Definition PB := P1.
Definition PC := P2.

Lemma cong_inner_transitivity : ~ cong_inner_transitivityP Point Cong.
Proof.
unfold cong_inner_transitivityP, Cong; intro H.
elim (H P0 P1 P2 P2 P1 P0); try tauto; [intro HF|intros [H1 H2]]; discriminate.
Qed.

Lemma point_equality_decidability : point_equality_decidabilityP Point.
Proof.
unfold point_equality_decidabilityP;
destruct A, B; try tauto; right; discriminate.
Qed.

Lemma bet_inner_transitivity : bet_inner_transitivityP Point Bet.
Proof.
unfold bet_inner_transitivityP, Bet;
destruct A, B, C, D; intuition discriminate.
Qed.

Lemma cong_pseudo_reflexivity : cong_pseudo_reflexivityP Point Cong.
Proof. unfold cong_pseudo_reflexivityP, Cong; destruct A, B; tauto. Qed.

Lemma cong_identity : cong_identityP Point Cong.
Proof.
unfold cong_identityP, Cong; destruct A, B, C; intro; intuition discriminate.
Qed.

Lemma inner_pasch : inner_paschP Point Bet.
Proof. unfold inner_paschP, Bet; intuition. Qed.

Lemma bet_symmetry : bet_symmetryP Point Bet.
Proof. unfold bet_symmetryP, Bet; destruct A, B, C; intuition. Qed.

Lemma col_alt_def : forall A B C, Col Point Bet A B C <->
  A = B \/ B = C \/ A = C.
Proof.
split.
unfold Col.
intros [? | [? | ?]];
destruct H as [? | ?]; subst ; tauto.
unfold Col, Bet.
intros [? | [? | ?]]; subst ;
tauto.
Qed.

Lemma euclid : euclidP Point Bet.
Proof.
unfold euclidP; intros A B C D P Q HPar HC HNC HCop.
destruct HPar as [HParS|[HAB [HCD [HC1 HC2]]]].
  {
  destruct HParS as [HAB [HCD [_ HNI]]].
  exfalso; apply HNI.
  destruct A, B, C, D; try tauto;
  try (exists P0; split; apply col_alt_def; tauto);
  try (exists P1; split; apply col_alt_def; tauto);
  try (exists P2; split; apply col_alt_def; tauto).
  }

  {
  exists P; split; apply col_alt_def; [tauto|].
  apply col_alt_def in HC.
  destruct HC as [? | [ ? | ?]]; (try tauto); subst.

    {
    apply col_alt_def in HC2.
    destruct HC2 as [ ? | [ ? | ?]]; subst; tauto.
    }

    {
    apply col_alt_def in HC1.
    destruct HC1 as [ ? | [ ? | ?]]; subst ; tauto.
    }
  }
Qed.

Lemma five_segment : five_segmentP Point Bet Cong.
Proof.
unfold five_segmentP, Bet, Cong.
intros A A' B B' C C' D D' HCong1 HCong2 HCong3 HCong4 [H|H] HBet2 HNEq;
[contradiction|subst].
destruct HCong1 as [H|[H1 H2]]; [contradiction|subst].
destruct HCong4 as [H|[H1 H2]]; [auto|subst].
destruct HBet2 as [H|H]; [intuition|subst; tauto].
Qed.

Lemma segment_construction : segment_constructionP Point Bet Cong.
Proof.
unfold segment_constructionP, Bet, Cong.
destruct A, B, C, D; firstorder;
try (exists P0; tauto);
try (exists P1; tauto);
exists P2; tauto.
Qed.

Lemma lower_dim : lower_dimP Point Bet PA PB PC.
Proof. unfold lower_dimP, Col, Bet; intuition discriminate. Qed.

Lemma upper_dim : upper_dimP Point Bet Cong.
Proof. unfold upper_dimP, Col, Bet, Cong; destruct P, Q, A, B, C; tauto. Qed.

Require Import Classical.

Lemma continuity : continuityP Point Bet.
Proof.
unfold continuityP, Bet; intros Xi Upsilon [A H].
elim (classic (exists Z, Xi Z /\ Upsilon Z /\ Z <> A)).
- intros [Z [HXZ [HUZ HZA]]]; exists Z; intros X Y HX HY.
  destruct (H Z Y HXZ HY) as [HAZ|HZY]; [congruence|auto].
- intro HN; exists A; intros X Y HX HY.
  destruct (H X Y HX HY) as [HAX|HXY]; [auto|subst Y].
  elim (classic (A = X)); [auto|intro HAX; exfalso].
  apply HN; exists X; split; [|split]; auto; congruence.
Qed.