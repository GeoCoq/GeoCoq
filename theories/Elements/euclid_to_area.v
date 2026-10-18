Require GeoCoq.Axioms.euclidean_axioms.
Require GeoCoq.Axioms.euclidean_area_axioms.
Require GeoCoq.Elements.OriginalProofs.euclidean_defs.
Require Import GeoCoq.Elements.euclid_to_tarski.
Require Import GeoCoq.Main.Tarski_dev.Ch13_6_Desargues_Hessenberg.
Require Import GeoCoq.Main.Highschool.orthocenter.
Require Import GeoCoq.Elements.equal_figures.

Section Shear.

Context `{TE : Tarski_euclidean}.

Lemma shear A B C D E K G A' K' :
  Par A D B C -> Col A D A' -> Per A' B C ->
  Bet A K C -> A <> K -> K <> C -> Bet B G C -> B <> G -> G <> C ->
  Par E K B C -> Col E K K' -> Par A B G K -> Per K' G C ->
  Bet A' K' C /\ A' <> K' /\ K' <> C.
Proof.
intros HPar1 HCol1 HPer1 HB1 HAK HKC HB2 HBG HGC HPar2 HCol2 HPar3 HPer2.
assert (HBC : B <> C) by (intro; treat_equalities; auto).
assert (HAC : A <> C) by (intro; treat_equalities; auto).
destruct (col_dec A B C) as [HCol|HNC].
- destruct HPar1 as [[_ HN]|[HAD [_ [_ HCol3]]]]; [exfalso; apply HN; exists A; split; Col|].
  assert (HA' : A' = B).
    {
    destruct (l8_9 A' B C) as [|]; [auto|ColR|auto|exfalso; auto].
    }
  assert (HCol4 : Col B C K) by ColR.
  destruct HPar2 as [[_ HN]|[HEK [_ [HCol5 HCol6]]]]; [exfalso; apply HN; exists K; split; Col|].
  assert (HK' : K' = G).
    {
    destruct (l8_9 K' G C) as [|]; [auto|ColR|auto|exfalso; auto].
    }
  subst; repeat split; auto.
- assert (HPS1 : Par_strict A D B C)
    by (destruct HPar1 as [|[_ [_ [HC1 _]]]]; [auto|exfalso; apply HNC; Col]).
  assert (HNC1 : ~ Col A D C) by (intro; destruct HPS1 as [_ HN]; apply HN; exists C; split; Col).
  assert (HNC2 : ~ Col B C K) by (intro; apply HNC; ColR).
  assert (HPS2 : Par_strict E K B C)
    by (apply par_strict_symmetry, par_not_col_strict with K; [Par|Col|auto]).
  assert (HNC3 : ~ Col A D K).
    {
    intro; apply HAK, (l6_21 A D C A); Col.
    }
  assert (HPS3 : Par_strict A D E K)
    by (apply par_not_col_strict with K; [apply par_trans with B C; Par|Col|auto]).
  assert (HNC4 : ~ Col E K A) by (intro; destruct HPS3 as [_ HN]; apply HN; exists A; split; Col).
  assert (HNC5 : ~ Col A' B C) by (intro; destruct HPS1 as [_ HN]; apply HN; exists A'; split; Col).
  assert (HTS : TS E K A' C).
    {
    apply l9_8_2 with A; [apply invert_two_sides, bet__ts; Col|].
    destruct (eq_dec_points A A') as [|HAA']; [subst; apply one_side_reflexivity; Col|].
    apply l12_6, par_strict_col2_par_strict with A D; [auto|apply par_strict_symmetry; auto|Col|Col].
    }
  destruct HTS as [HNC6 [HNC7 [T [HT1 HT2]]]].
  assert (HPar4 : Par B A' G T).
    {
    destruct (eq_dec_points A A') as [|HAA'].
    - subst A'.
      assert (T = K) by (apply (l6_21 E K A C); Col).
      subst; Par.
    - assert (HKT : K <> T).
        {
        intro; subst T; apply HAA', (l6_21 A D C A); Col.
        apply bet_col in HB1; apply bet_col in HT2; ColR.
        }
      apply (l13_15 A B A' K G T C).
      + intro; destruct HPS1 as [_ HN]; apply HN; exists B; split; [ColR|Col].
      + destruct HPS1 as [HCop _]; CopR.
      + apply par_strict_right_comm, par_not_col_strict with K; [auto|Col|intro; apply HNC; ColR].
      + apply par_strict_col2_par_strict with E K; [auto| |Col|Col].
        apply par_strict_symmetry, par_strict_col2_par_strict with A D; [auto|Par|Col|Col].
      + Col.
      + Col.
      + Col.
    }
  assert (HGT : G <> T) by (intro; subst; destruct HPS2 as [_ HN]; apply HN; exists T; split; Col).
  assert (HPer3 : Per T G C).
    {
    apply perp_per_2.
    assert (HP : Perp G T B C).
      {
      apply cop_par_perp__perp with B A'; [auto| |destruct HPS2 as [HCop _]; CopR].
      apply perp_left_comm, per_perp; [intro; subst; apply HNC5; Col|auto|auto].
      }
    assert (Perp C G G T) by (apply perp_col with B; [auto|Perp|Col]).
    Perp.
    }
  assert (HK'T : K' = T).
    {
    destruct (eq_dec_points K' T) as [|HK'T]; [auto|exfalso].
    assert (HCol3 : Col K' T G).
      {
      apply cop_per2__col with C; [|auto|auto|auto].
      destruct HPS2 as [HCop _]; CopR.
      }
    destruct HPS2 as [_ HN]; apply HN; exists G; split; [ColR|Col].
    }
  subst; repeat split; [auto|intro; subst; Col..].
Qed.

End Shear.

Section Euclid_to_area.

Context `{Ax:euclidean_axioms.euclidean_euclidean}.

Existing Instance Tarski_follows_Euclid.
Existing Instance Tarski_follows_Euclid_dec.
Existing Instance Tarski_euclidean_follows_Euclid.

Lemma BetS_E_T A B C : euclidean_axioms.BetS A B C -> BetS A B C.
Proof. intro H; exact (Bet_of_BetS A B C H). Qed.

Lemma BetS_T_E A B C : BetS A B C -> euclidean_axioms.BetS A B C.
Proof. intros [H1 [H2 H3]]; exact (BetS_of_Bet A B C H1 H2 H3). Qed.

Lemma Cong_E_T A B C D : euclidean_axioms.Cong A B C D -> Cong A B C D.
Proof. intro H; hnf; left; exact H. Qed.

Lemma Cong_3_E_T A B C a b c :
  euclidean_axioms.Cong_3 A B C a b c -> Cong_3 A B C a b c.
Proof.
intros [H1 [H2 H3]].
split; [|split]; apply Cong_E_T; assumption.
Qed.

Lemma Col_E_T A B C : euclidean_axioms.Col A B C -> Col A B C.
Proof.
intro HCol; unfold euclidean_axioms.Col, euclidean_axioms.eq in HCol.
destruct HCol as [H|[H|[H|[H|[H|H]]]]]; try (subst; Col);
apply BetS_E_T in H; destruct H as [H _]; Col.
Qed.

Lemma nCol_E_T A B C : euclidean_axioms.nCol A B C -> ~ Col A B C.
Proof.
intros [HAB [HAC [HBC [H1 [H2 H3]]]]] [HBet|[HBet|HBet]].
- apply H1, BetS_T_E; repeat split; auto.
- apply H2, euclidean_axioms.axiom_betweennesssymmetry, BetS_T_E; repeat split; auto.
- apply H3, euclidean_axioms.axiom_betweennesssymmetry, BetS_T_E; repeat split; auto.
Qed.

Lemma Col_T_E A B C : Col A B C -> euclidean_axioms.Col A B C.
Proof.
intro HCol; unfold euclidean_axioms.Col, euclidean_axioms.eq.
destruct (eq_dec_points A B); [left; auto|].
destruct (eq_dec_points A C); [right; left; auto|].
destruct (eq_dec_points B C); [right; right; left; auto|].
destruct HCol as [HB|[HB|HB]].
- do 4 right; left; apply BetS_T_E; repeat split; auto.
- do 5 right; apply euclidean_axioms.axiom_betweennesssymmetry, BetS_T_E; repeat split; auto.
- do 3 right; left; apply euclidean_axioms.axiom_betweennesssymmetry, BetS_T_E; repeat split; auto.
Qed.

Lemma Par_E_T A B C D : euclidean_defs.Par A B C D -> Par A B C D.
Proof.
intros [U [V [u [v [X [HAB [HCD [HU [HV [HUV [Hu [Hv [Huv [HNM [HB1 HB2]]]]]]]]]]]]]]].
apply Col_E_T in HU; apply Col_E_T in HV; apply Col_E_T in Hu; apply Col_E_T in Hv.
apply BetS_E_T in HB1; destruct HB1 as [HB1 _].
apply BetS_E_T in HB2; destruct HB2 as [HB2 _].
assert (HAB' : A <> B) by exact HAB.
assert (HCD' : C <> D) by exact HCD.
assert (HUV' : U <> V) by exact HUV.
assert (Huv' : u <> v) by exact Huv.
assert (HCop1 : Coplanar u v U V) by (exists X; right; right; split; Col).
assert (HCop2 : Coplanar u v A B)
  by (apply col2_cop__cop with U V; [auto|auto|apply col3 with A B; Col..]).
assert (HCop3 : Coplanar A B u v) by Cop.
left; split; [apply col2_cop__cop with u v; [auto|auto|apply col3 with C D; Col..]|].
intros [Y [HY1 HY2]]; apply HNM.
exists Y; split; [auto|split; [auto|split; apply Col_T_E; Col]].
Qed.

Lemma Per_E_T A B C : euclidean_defs.Per A B C -> Per A B C /\ A <> B /\ B <> C.
Proof.
intros [X [HB [HC1 [HC2 HBC]]]].
apply BetS_E_T in HB; destruct HB as [HB [HAB _]].
apply Cong_E_T in HC1; apply Cong_E_T in HC2.
split; [apply l8_2; exists X; split; [split; [auto|Cong]|Cong]|split; [auto|exact HBC]].
Qed.

Lemma RE_E_T A B C D : euclidean_defs.RE A B C D -> Rectangle A B C D /\ A <> B /\ B <> C.
Proof.
intros [_ [HP2 [HP3 [HP4 [X [HB1 HB2]]]]]].
destruct (Per_E_T _ _ _ HP2) as [HP2' [HAB HBC]].
destruct (Per_E_T _ _ _ HP3) as [HP3' [_ HCD]].
destruct (Per_E_T _ _ _ HP4) as [HP4' [_ HDA]].
apply BetS_E_T in HB1; destruct HB1 as [HB1 _].
apply BetS_E_T in HB2; destruct HB2 as [HB2 _].
split; [|split; auto].
apply cop_perp3__rect; [exists X; right; left; split; Col|apply per_perp; auto..].
Qed.

Lemma TS_E_T P A B Q : euclidean_axioms.TS P A B Q -> TS A B P Q.
Proof.
intros [X [HBet [HCol HNC]]].
apply BetS_E_T in HBet; destruct HBet as [HBet [HPX HXQ]].
apply Col_E_T in HCol; apply nCol_E_T in HNC.
assert (HAB : A <> B) by (intro; subst; apply HNC; Col).
split; [intro; apply HNC; Col|split; [|exists X; split; Col]].
intro; apply HNC.
apply col3 with X Q; [auto|apply col3 with A B; Col..|apply bet_col in HBet; Col].
Qed.

Lemma EqQ_convex2 J K L M j k l m : EqQ J K L M j k l m -> Convex j k l m.
Proof. intros [A [B [C [D [a [b [c [d [_ [[HCv _] _]]]]]]]]]]; auto. Qed.

Lemma EqQ_rot_right J K L M j k l m :
  EqQ J K L M j k l m -> EqQ J K L M k l m j.
Proof.
intro H.
destruct (EqQ_ncol j k l m J K L M (proj1 (EqQ_sym _ _ _ _ _ _ _ _) H)) as [HNC|HNC];
(apply EqQ_trans with j k l m; [auto|apply EqQ_abcd_bcda; [apply EqQ_convex2 with J K L M; auto|]]);
[left|right]; Col.
Qed.

Lemma EqQ_refl_right J K L M j k l m :
  EqQ J K L M j k l m -> EqQ J K L M j m l k.
Proof.
intro H.
destruct (EqQ_ncol j k l m J K L M (proj1 (EqQ_sym _ _ _ _ _ _ _ _) H)) as [HNC|HNC];
(apply EqQ_trans with j k l m; [auto|apply EqQ_abcd_adcb; [apply EqQ_convex2 with J K L M; auto|]]);
[left|right]; Col.
Qed.

Lemma EqQ_rot_left J K L M j k l m :
  EqQ J K L M j k l m -> EqQ K L M J j k l m.
Proof.
intro H; apply EqQ_sym, EqQ_rot_right, EqQ_sym; auto.
Qed.

Lemma EqT_perm2 A B C a b c :
  EqT A B C a b c ->
  EqT A B C b c a /\ EqT A B C a c b /\ EqT A B C b a c /\
  EqT A B C c b a /\ EqT A B C c a b.
Proof.
intro HE.
destruct (EqT_not_col _ _ _ _ _ _ HE) as [_ HNC].
destruct (B6_3 a b c HNC) as [H1 [H2 [H3 [H4 H5]]]].
repeat split; apply EqT_trans with a b c; auto.
Qed.

Instance area_follows_Euclid : euclidean_area_axioms.area Ax.
Proof.
apply (euclidean_area_axioms.Build_area _ _ _ (EqQ (Tn:=Tarski_follows_Euclid))
                                           (EqT (Tn:=Tarski_follows_Euclid))).
- intros A B C a b c HT HC.
  apply Cong_3__EqT; [apply nCol_E_T; exact HT|apply Cong_3_E_T; exact HC].
- apply EqT_perm2.
- intros; apply EqT_sym; auto.
- intros A B C D a b c d H.
  assert (H1 : EqQ A B C D b c d a) by (apply EqQ_rot_right; auto).
  assert (H2 : EqQ A B C D c d a b) by (apply EqQ_rot_right; auto).
  assert (H3 : EqQ A B C D d a b c) by (apply EqQ_rot_right; auto).
  assert (H4 : EqQ A B C D a d c b) by (apply EqQ_refl_right; auto).
  assert (H5 : EqQ A B C D d c b a) by (apply EqQ_rot_right; auto).
  assert (H6 : EqQ A B C D c b a d) by (apply EqQ_rot_right; auto).
  assert (H7 : EqQ A B C D b a d c) by (apply EqQ_rot_right; auto).
  repeat split; auto.
- intros A B C D a b c d HE1 HTS1 HE2 HTS2 HQ.
  apply TS_E_T, invert_two_sides in HTS1.
  apply TS_E_T, invert_two_sides in HTS2.
  destruct (EqT_not_col _ _ _ _ _ _ HE1) as [HNC1 HNC2].
  destruct (EqT_not_col _ _ _ _ _ _ HE2) as [HNC3 HNC4].
  assert (HE1' : EqT C B A C B D).
    {
    apply EqT_trans with A B C; [destruct (@B6_3 _ _ Tarski_euclidean_follows_Euclid C B A); Col; spliter; auto|].
    apply EqT_trans with B C D; [auto|destruct (@B6_3 _ _ Tarski_euclidean_follows_Euclid B C D); Col; spliter; auto].
    }
  assert (HE2' : EqT c b a c b d).
    {
    apply EqT_trans with a b c; [destruct (@B6_3 _ _ Tarski_euclidean_follows_Euclid c b a); Col; spliter; auto|].
    apply EqT_trans with b c d; [auto|destruct (@B6_3 _ _ Tarski_euclidean_follows_Euclid b c d); Col; spliter; auto].
    }
  assert (HQ' : EqQ C A B D c a b d)
    by (do 3 apply EqQ_rot_left; do 3 apply EqQ_rot_right; auto).
  assert (HE : EqT C B A c b a) by (apply halves_of_equals with D d; auto).
  apply EqT_trans with C B A; [destruct (@B6_3 _ _ Tarski_euclidean_follows_Euclid A B C); Col; spliter; auto|].
  apply EqT_trans with c b a; [auto|destruct (@B6_3 _ _ Tarski_euclidean_follows_Euclid c b a); Col; spliter; auto].
- intros; apply EqQ_sym; auto.
- intros A B C D P Q R S a b c d H1 H2; apply EqQ_trans with a b c d; auto.
- intros A B C P Q R a b c H1 H2; apply EqT_trans with a b c; auto.
- intros A B C D E a b c d e H1 H2 H3 H4 H5 H6.
  destruct (BetS_E_T _ _ _ H1) as [? [? ?]]; destruct (BetS_E_T _ _ _ H2) as [? [? ?]];
  destruct (BetS_E_T _ _ _ H3) as [? [? ?]]; destruct (BetS_E_T _ _ _ H4) as [? [? ?]].
  apply (@cutoff1 _ _ Tarski_euclidean_follows_Euclid A B C D E a b c d e); auto.
- intros A B C D E a b c d e H1 H2 H3 H4.
  destruct (BetS_E_T _ _ _ H1) as [? [? ?]]; destruct (BetS_E_T _ _ _ H2) as [? [? ?]].
  apply (@cutoff2 _ _ Tarski_euclidean_follows_Euclid A B C D E a b c d e); auto.
- intros A B C D E a b c d e H1 H2 H3 H4 H5 H6.
  destruct (BetS_E_T _ _ _ H1) as [? [? ?]]; destruct (BetS_E_T _ _ _ H2) as [? [? ?]];
  destruct (BetS_E_T _ _ _ H3) as [? [? ?]]; destruct (BetS_E_T _ _ _ H4) as [? [? ?]].
  apply (@paste1 _ _ Tarski_euclidean_follows_Euclid A B C D E a b c d e); auto.
- intros B C D E H.
  destruct (BetS_E_T _ _ _ H) as [? [? ?]].
  apply (@B6_4 _ _ Tarski_euclidean_follows_Euclid B E D C); auto.
- intros A B C E F HT H1 H2.
  destruct (BetS_E_T _ _ _ H1) as [? [? ?]]; destruct (BetS_E_T _ _ _ H2) as [? [? ?]].
  apply B6_5; [apply nCol_E_T; exact HT|auto..].
- intros A B C D E M a b c d e m H1 H2 H3 H4 H5 H6 H7 H8.
  destruct (BetS_E_T _ _ _ H1) as [? [? ?]]; destruct (BetS_E_T _ _ _ H2) as [? [? ?]];
  destruct (BetS_E_T _ _ _ H5) as [? [? ?]]; destruct (BetS_E_T _ _ _ H6) as [? [? ?]];
  destruct (BetS_E_T _ _ _ H7) as [? [? ?]]; destruct (BetS_E_T _ _ _ H8) as [? [? ?]].
  apply (@paste2 _ _ Tarski_euclidean_follows_Euclid A B C D E M a b c d e m); auto.
- intros A B C D M a b c d m H1 H2 H3 H4 H5 H6.
  destruct (BetS_E_T _ _ _ H3) as [? [? ?]]; destruct (BetS_E_T _ _ _ H5) as [? [? ?]].
  apply (@paste3 _ _ Tarski_euclidean_follows_Euclid A B C D M a b c d m); auto.
- intros A B C D F G H J K L M P e m H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
  destruct (BetS_E_T _ _ _ H3) as [? [? ?]]; destruct (BetS_E_T _ _ _ H4) as [? [? ?]];
  destruct (BetS_E_T _ _ _ H5) as [? [? ?]]; destruct (BetS_E_T _ _ _ H6) as [? [? ?]];
  destruct (BetS_E_T _ _ _ H7) as [? [? ?]]; destruct (BetS_E_T _ _ _ H8) as [? [? ?]];
  destruct (BetS_E_T _ _ _ H9) as [? [? ?]]; destruct (BetS_E_T _ _ _ H10) as [? [? ?]].
  apply (@paste4 _ _ Tarski_euclidean_follows_Euclid A B C D F G H J K L M P e m); auto.
Defined.

Lemma lemma_5_12 A B C D :
  euclidean_axioms.nCol A B C -> euclidean_defs.Par A B C D ->
  euclidean_area_axioms.ET A B C A B D.
Proof.
intros HNC HPar.
apply (@B5_12 _ _ Tarski_euclidean_follows_Euclid); [apply nCol_E_T|apply Par_E_T]; auto.
Qed.

Lemma lemma_shear A B C D E K G A' K' :
  euclidean_defs.Par A D B C -> euclidean_axioms.Col A D A' -> euclidean_defs.Per A' B C ->
  euclidean_axioms.BetS A K C -> euclidean_axioms.BetS B G C ->
  euclidean_defs.Par E K B C -> euclidean_axioms.Col E K K' -> euclidean_defs.Par A B G K ->
  euclidean_defs.Per K' G C ->
  euclidean_axioms.BetS A' K' C.
Proof.
intros HPar1 HCol1 HPer1 HB1 HB2 HPar2 HCol2 HPar3 HPer2.
destruct (BetS_E_T _ _ _ HB1) as [? [? ?]]; destruct (BetS_E_T _ _ _ HB2) as [? [? ?]].
apply BetS_T_E.
apply (@shear _ _ Tarski_euclidean_follows_Euclid A B C D E K G A' K');
  [apply Par_E_T|apply Col_E_T|apply Per_E_T|auto..|apply Par_E_T|apply Col_E_T|apply Par_E_T|apply Per_E_T];
  auto.
Qed.

Lemma lemma_7_10 C D P Q c d p q A B E F G H K L M :
  euclidean_defs.RE C D P Q -> euclidean_defs.RE c d p q -> euclidean_defs.RE A B M L ->
  euclidean_axioms.Cong C D A B -> euclidean_axioms.Cong D P B M ->
  euclidean_defs.RE B E F G -> euclidean_axioms.Cong c d B E -> euclidean_axioms.Cong d p E F ->
  euclidean_axioms.BetS H A L -> euclidean_axioms.BetS H G F -> euclidean_axioms.BetS F E K ->
  euclidean_axioms.BetS K M L -> euclidean_axioms.BetS A B E -> euclidean_axioms.BetS G B M ->
  euclidean_axioms.BetS H B K ->
  euclidean_area_axioms.EF C D P Q c d p q.
Proof.
intros HR1 HR2 HR3 HC1 HC2 HR4 HC3 HC4 HB1 HB2 HB3 HB4 HB5 HB6 HB7.
destruct (RE_E_T _ _ _ _ HR1) as [HR1' [? ?]]; destruct (RE_E_T _ _ _ _ HR2) as [HR2' [? ?]].
destruct (RE_E_T _ _ _ _ HR3) as [HR3' _]; destruct (RE_E_T _ _ _ _ HR4) as [HR4' _].
apply Cong_E_T in HC1; apply Cong_E_T in HC2; apply Cong_E_T in HC3; apply Cong_E_T in HC4.
destruct (BetS_E_T _ _ _ HB1) as [? _]; destruct (BetS_E_T _ _ _ HB2) as [? _];
destruct (BetS_E_T _ _ _ HB3) as [? _]; destruct (BetS_E_T _ _ _ HB4) as [? _];
destruct (BetS_E_T _ _ _ HB5) as [? _]; destruct (BetS_E_T _ _ _ HB6) as [? _];
destruct (BetS_E_T _ _ _ HB7) as [? _].
apply (@EqR__EqQ _ _ Tarski_euclidean_follows_Euclid).
do 6 (split; [auto|]).
exists A, B, E, F, G, H, K, L, M.
repeat (split; [auto|]); auto.
Qed.

Lemma lemma_7_12 A B C D E F O :
  euclidean_axioms.BetS A O C -> euclidean_axioms.BetS B O D -> euclidean_axioms.Cong B O O D ->
  euclidean_defs.RE A C E F -> euclidean_axioms.Col F D E ->
  euclidean_area_axioms.EF A B C D A C E F.
Proof.
intros HB1 HB2 HC HR HCol.
destruct (BetS_E_T _ _ _ HB1) as [? _]; destruct (BetS_E_T _ _ _ HB2) as [? [? ?]].
destruct (RE_E_T _ _ _ _ HR) as [HR' [? ?]].
apply (@B7_12 _ _ Tarski_euclidean_follows_Euclid A B C D E F O);
  [auto|auto|auto|apply Cong_E_T; auto|auto|auto|auto|apply Col_E_T; auto].
Qed.

Lemma lemma_really_triangle A B C D a b c d :
  euclidean_area_axioms.EF A B C D a b c d ->
  euclidean_axioms.BetS B C D -> euclidean_axioms.BetS b c d ->
  euclidean_axioms.nCol A B D -> euclidean_axioms.nCol a b d ->
  euclidean_area_axioms.ET A B D a b d.
Proof.
intros HQ HB1 HB2 HNC1 HNC2.
destruct (BetS_E_T _ _ _ HB1) as [? _]; destruct (BetS_E_T _ _ _ HB2) as [? _].
apply (@EqQ_bet__EqT _ _ Tarski_euclidean_follows_Euclid A B C D a b c d);
  [apply nCol_E_T; auto|apply nCol_E_T; auto|auto|auto|auto].
Qed.

End Euclid_to_area.