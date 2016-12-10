Require Export GeoCoq.Meta_theory.Parallel_postulates.archimedes.
Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid.

Section Szmielew.

Context `{T2D:Tarski_2D}.

Definition hyperbolic_plane_postulate := forall A1 A2 P, ~ Col A1 A2 P -> exists B1 B2 C1 C2,
  Par A1 A2 B1 B2 /\ Col P B1 B2 /\
  Par A1 A2 C1 C2 /\ Col P C1 C2 /\
  ~ Col C1 B1 B2.

Lemma aah__hpp : hypothesis_of_acute_saccheri_quadrilaterals -> hyperbolic_plane_postulate.
Proof.
  intros aah A1 A2 P HNCol.
  destruct (l8_18_existence A1 A2 P HNCol) as [Q [HCol1 HPerp]].
  destruct (diff_col_ex3 A1 A2 Q HCol1) as [X [HXA1 [HXA2 [HXQ HCol2]]]].
  destruct (segment_construction X Q X Q) as [Y [HBet HCong]].
  assert_diffs.
  assert (HCol3 : Col A1 A2 Y) by ColR.
  assert (HInt : Per P Q X /\ Per P Q Y).
    split; apply perp_per_1; auto; apply perp_sym, perp_col2 with A1 A2; Perp.
  destruct HInt as [HPer HPer'].
  destruct (per__ex_saccheri Q P X) as [B1 HSac]; auto.
  destruct (per__ex_saccheri Q P Y) as [C1 HSac']; auto.
  exists B1; exists P; exists C1; exists P; repeat split; Col.
    apply sac__par1423 in HSac; apply par_symmetry, par_col2_par_bis with Q X; Col; Par.
    apply sac__par1423 in HSac'; apply par_symmetry, par_col2_par_bis with Q Y; Col; Par.
  intro HCol.
  assert (HBet0 : Bet B1 P C1).
  { apply sac__par_strict1234 in HSac; apply sac__par_strict1234 in HSac'.
    apply col_two_sides_bet with Q; Col.
    apply l9_8_2 with X; [|apply l12_6; Par].
    apply l9_2, l9_8_2 with Y; [|apply l12_6; Par].
    repeat split; auto; try (intro; apply HNCol; ColR).
    exists Q; split; Col; Between.
  }
  apply (nlta B1 P C1).
  assert (HConga: CongA P Q X P Q Y) by (apply l11_16; auto).
  assert (HNCol1 : ~ Col P Q X) by (apply per_not_col; auto).
  assert (HNCol2 : ~ Col P Q Y) by (apply per_not_col; auto).
  assert (HNCol3 : ~ Col Q P B1) by (apply sac__ncol123 with X; trivial).
  assert (HNCol4 : ~ Col Q P C1) by (apply sac__ncol123 with Y; trivial).
  assert (HTS : TS Q P X Y) by (repeat split; Col; exists Q; split; Col).
  apply isi_lta2_suma2__lta with B1 P Q Q P C1 P Q X P Q X.
  - apply acute_per__lta; auto; apply acute_sym, (aah Q P B1 X HSac).
  - apply acute_per__lta; auto; apply (aah Q P C1 Y HSac').
  - apply (conga2_isi__isi X Q P P Q Y); CongA.
    repeat split; auto.
      right; intro; apply HNCol1; Col.
    exists Y; split; CongA; split; Side.
    intro HTS1; destruct HTS1 as [_ []]; assert_cols; Col.
  - assert_diffs; apply inangle__suma; repeat split; Col.
    exists P; split; auto.
  - assert_diffs; apply (conga3_suma__suma X Q P P Q Y X Q Y); CongA; [|apply conga_line; auto].
    apply inangle__suma; repeat split; Col.
    exists Q; split; auto.
Qed.


Lemma szmielew_s_theorem : archimedes_postulate -> 
  (forall P : Prop,
  (playfair_s_postulate -> P) -> 
  (hyperbolic_plane_postulate -> ~ P)->
  (P <-> playfair_s_postulate)).
Proof.
  intros archi P H1 H2.
  split; [|apply H1].
  intro HP; destruct (archi__acute_or_right archi) as [aah|rah].
  - absurd(P); auto.
    apply H2, (aah__hpp aah).
  - apply playfair_bis__playfair, triangle__playfair_bis.
      apply aristotle__greenberg, (t22_24 archi).
    apply (rah__triangle rah).
Qed.

End Szmielew.