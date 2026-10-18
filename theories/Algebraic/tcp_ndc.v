Require Import GeoCoq.Algebraic.coplanarity.
Require Import GeoCoq.Main.Tarski_dev.Ch12_parallel_inter_dec.
Require Import GeoCoq.Main.Annexes.quadrilaterals_inter_dec.
Require Import GeoCoq.Main.Highschool.gravityCenter.

Section tcp_ndc.

Context `{TE: Tarski_euclidean}.

Lemma tcp_aligned_plane_exists : forall A B M,
  A <> B -> Midpoint M A B ->
  exists P Q R MAR MBR, ~ Col A B R /\ Midpoint MAR A R /\ Midpoint MBR B R /\
                        ~ Col P Q R /\ Midpoint MAR MBR P /\ Midpoint MBR MAR Q.
Proof.
intros A B M HAB HM.
destruct (not_col_exists A B) as [R HR]; [auto|].
destruct (midpoint_existence A R) as [MAR HMAR].
destruct (midpoint_existence B R) as [MBR HMBR].
destruct (symmetric_point_construction MBR MAR) as [P HP].
destruct (symmetric_point_construction MAR MBR) as [Q HQ].
exists P, Q, R, MAR, MBR; repeat (split; finish).
assert (HTS : TS P Q A R);[|destruct HTS as [_ [? _]]; Col].
assert (HD : MAR <> MBR) by (intro; treat_equalities; Col).
apply col_preserves_two_sides with MAR Q; [intro; treat_equalities|ColR|Col|];
[apply HD, between_equality with P; finish|].
apply bet__ts; [intro; treat_equalities; Col| |finish].
intro; apply HR; ColR.
Qed.

Lemma tcp_aligned_inplane : forall A B M P Q R MAR MBR,
  Midpoint M A B -> ~ Col A B R -> ~ Col P Q R ->
  Midpoint MAR A R -> Midpoint MBR B R ->
  Midpoint MAR MBR P -> Midpoint MBR MAR Q ->
  (exists X, (Col P Q X /\ P <> Q /\ P <> X /\ Q <> X) /\
             (Col R A X /\ R <> A /\ R <> X /\ A <> X)) /\
  (exists X, (Col P Q X /\ P <> Q /\ P <> X /\ Q <> X) /\
             (Col R B X /\ R <> B /\ R <> X /\ B <> X)) /\
  (exists X, (Col P Q X /\ P <> Q /\ P <> X /\ Q <> X) /\
             (Col R M X /\ R <> M /\ R <> X /\ M <> X)).
Proof.
intros A B M P Q R MAR MBR HM HABR HPQR HMAR HMBR HP HQ.
assert (HD : MAR <> MBR) by (intro; treat_equalities; Col).
split; [exists MAR; repeat split; [ColR| | | |ColR|..];
        intro; treat_equalities; Col|].
split; [exists MBR; repeat split; [ColR| | | |ColR|..];
        intro; treat_equalities; Col|].
assert (HPQ : P <> Q) by (assert_diffs; auto).
assert (HParS : Par_strict A B MAR MBR)
  by (apply triangle_mid_par_strict with R; finish).
assert (HPQA : ~ Col P Q A)
  by (intro; destruct HParS as [_ HF]; apply HF; exists A; split; [Col|ColR]).
assert (HPQB : ~ Col P Q B)
  by (intro; destruct HParS as [_ HF]; apply HF; exists B; split; [Col|ColR]).
assert (HX : TS P Q M R).
  {
  apply l9_8_2 with A; [repeat split|apply l9_17 with B; [|finish]];
  [intro; apply HABR; ColR..|exists MAR; split; [ColR|finish]|].
  exists R; split; split; Col; split; Col; [exists MAR|exists MBR];
  split; [ColR|Between|ColR|Between].
  }
destruct HX as [HPQM [_ [X [HC HMXR]]]].
assert (HTS : TS M R P Q).
  {
  apply bet_ts__ts with MBR;
  [|apply outer_transitivity_between2 with MAR; finish].
  apply l9_2, bet_ts__ts with MAR; [apply l9_2|finish].
  apply invert_two_sides, l9_31.

    {
    apply one_side_transitivity with B;
    [apply out_one_side_1 with A|apply out_one_side_1 with R];
    [|Col|apply bet_out; [intro; treat_equalities; Col|finish]|
     |Col|apply l6_6, bet_out; [intro; treat_equalities; Col|finish]];
    intro; apply HABR; ColR.
    }

    {
    apply one_side_transitivity with A;
    [apply out_one_side_1 with B|apply out_one_side_1 with R];
    [|Col|apply bet_out; [intro; treat_equalities; Col|finish]|
     |Col|apply l6_6, bet_out; [intro; treat_equalities; Col|finish]];
    intro; apply HABR; ColR.
    }
  }
destruct HTS as [HMPR [HMQR _]].
exists X; repeat split; [Col|intro; treat_equalities..|Col| | |];
[apply HPQ|apply HMPR|apply HMQR|intro; treat_equalities..]; Col.
Qed.

Lemma tcp_ncols_ndc : forall A B C X MAB MAC MBC,
  ~ Col A B C -> Cong A X B X -> Cong A X C X ->
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  ~ Col MAB MAC X \/ ~ Col MAB MBC X \/ ~ Col MAC MBC X.
Proof.
intros A B C X MAB MAC MBC HNC HC1 HC2 HMAB HMAC HMBC.
assert (HF : ~ Col MAB MAC MBC).
  {
  assert (HF : Par_strict B C MAB MAC)
    by (apply triangle_mid_par_strict with A; finish).
  intro; destruct HF as [_ HF]; apply HF; exists MBC; split; Col.
  }
elim (col_dec MAB MAC X); [intro HNC1|left; auto].
elim (col_dec MAB MBC X); [intro HNC2|right; left; auto].
elim (col_dec MAC MBC X); [intro HNC3|right; right; auto].
assert (HX1 : X = MAB)
  by (assert_diffs; apply l6_21 with MAB MAC MBC MAB; Col).
assert (HX2 : X = MAC)
  by (assert_diffs; apply l6_21 with MAC MAB MBC MAC; Col).
exfalso; apply HF; treat_equalities; Col.
Qed.

Lemma tcp_ncol_midpoints : forall A B C MAB MAC MBC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  ~ Col A B C ->
  ~ Col MAB MAC MBC.
Proof.
intros A B C MAB MAC MBC HMAB HMAC HMBC HNC.
cut (Par_strict A B MAC MBC); [intros [_ H]; intro; apply H; exists MAB; Col|].
apply triangle_mid_par_strict with C; Col.
Qed.

Lemma tcp_pars : forall A B C MAB MAC MBC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  ~ Col A B C ->
  Par_strict MAB MAC MBC B.
Proof.
intros A B C MAB MAC MBC HMAB HMAC HMBC HNC.
eapply par_strict_col2_par_strict; [|apply par_strict_symmetry|..];
[|apply triangle_mid_par_strict with A; eCol; finish|..];
finish; intro; treat_equalities; Col.
Qed.

Lemma tcp_ts_mab_mac_a_mbc : forall A B C MAB MAC MBC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  ~ Col A B C ->
  TS MAB MAC A MBC.
Proof.
intros A B C MAB MAC MBC HMAB HMAC HMBC HNC.
assert (HP : Par_strict MAB MAC MBC B) by (apply tcp_pars with A C; finish).
spliter; apply bet_ts__ts with MBC; [|finish].
apply l9_2, l9_8_2 with B; [|apply pars__os3412; finish].
apply bet__ts; [intro; treat_equalities; Col| |finish].
intro; apply (tcp_ncol_midpoints A B C MAB MAC MBC); finish; ColR.
Qed.

Lemma tcp_ts_a_mbc_mab_mac : forall A B C MAB MAC MBC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  ~ Col A B C ->
  TS A MBC MAB MAC.
Proof.
intros A B C MAB MAC MBC HMAB HMAC HMBC HNC.
assert (HNE : A <> MBC) by (intro; treat_equalities; Col).
apply l9_8_2 with B; [|apply out_one_side_1 with A];
[|intro; apply HNC; ColR|Col|assert_diffs; repeat split; finish].
apply l9_2, l9_8_2 with C; [|apply out_one_side_1 with A];
[|intro; apply HNC; ColR|Col|assert_diffs; repeat split; finish].
repeat split; [intro; apply HNC; ColR..|exists MBC; finish].
Qed.

Lemma tcp_ts_mmab_mac_a_mbc : forall A B C MAB MAC MBC MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  ~ Col A B C -> Midpoint MMAB A MAB ->
  TS MMAB MAC A MBC.
Proof.
intros A B C MAB MAC MBC MMAB HMAB HMAC HMBC HNC1 HMMAB.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS1 : TS MAB MAC A MBC) by (apply tcp_ts_mab_mac_a_mbc with B C; auto).
assert (HTS2 : TS A MBC MAB MAC) by (apply tcp_ts_a_mbc_mab_mac with B C; auto).
destruct (ts2__ex_bet2 MAB A MAC MBC) as [Y [HBet1 HBet2]]; auto.
destruct (inner_pasch A MAC MAB MMAB Y) as [Z [HBet3 HBet4]]; finish.
apply (l9_18 _ _ _ _ Y) in HTS1; apply (l9_18 _ _ _ _ Y) in HTS2; Col.
assert (HNE1 : A <> Y) by (intro; apply HNC2; ColR).
assert (HNE2 : MMAB <> MAC) by (intro; apply HNC2; ColR).
assert (HBet : Bet A Z MBC) by (apply between_exchange4 with Y; finish).
assert (HNE3 : MBC <> Z) by (intro; treat_equalities; apply HNC2; Col).
split; [intro; apply HNC2; ColR|].
split; [intro; apply HNC2; ColR|exists Z; split; finish].
Qed.

Local Notation "'Lines_meet' A1 A2 B1 B2" :=
  (exists Y, (Col A1 A2 Y /\ A1 <> A2 /\ A1 <> Y /\ A2 <> Y) /\
             (Col B1 B2 Y /\ B1 <> B2 /\ B1 <> Y /\ B2 <> Y))
  (at level 10, A1, A2, B1, B2 at level 0).

Local Ltac contra_ncol :=
  match goal with H : ~ Col _ _ _ |- _ => exfalso; apply H; solve [Col] end.

Lemma tcp_meet_swapl : forall A1 A2 B1 B2,
  Lines_meet A1 A2 B1 B2 -> Lines_meet A2 A1 B1 B2.
Proof.
intros A1 A2 B1 B2 [Y [HA HB]]; exists Y; spliter; repeat split; finish.
Qed.

Lemma tcp_meet_swapr : forall A1 A2 B1 B2,
  Lines_meet A1 A2 B1 B2 -> Lines_meet A1 A2 B2 B1.
Proof.
intros A1 A2 B1 B2 [Y [HA HB]]; exists Y; spliter; repeat split; finish.
Qed.

Lemma tcp_ncol_inplane_4 : forall A1 A2 B1 B2,
  Coplanar A1 A2 B1 B2 -> ~ Par_strict A1 A2 B1 B2 -> A1 <> A2 ->
  ~ Col A1 B1 B2 -> ~ Col A2 B1 B2 -> ~ Col B1 A1 A2 -> ~ Col B2 A1 A2 ->
  Lines_meet A1 A2 B1 B2.
Proof.
intros A1 A2 B1 B2 HCop HNP HNE HNC1 HNC2 HNC3 HNC4.
destruct (cop_npars__inter_exists A1 A2 B1 B2) as [Y []]; auto.
exists Y; repeat split; Col; intro; treat_equalities; Col.
Qed.

Lemma tcp_ts2__meet : forall A1 A2 B1 B2,
  TS A1 A2 B1 B2 -> TS B1 B2 A1 A2 -> Lines_meet A1 A2 B1 B2.
Proof.
intros A1 A2 B1 B2 HTS1 HTS2.
destruct (ts2__ex_bet2 A1 B1 A2 B2) as [Y [HBet1 HBet2]]; auto.
destruct HTS1 as [HNC1 [HNC2 _]]; destruct HTS2 as [HNC3 [HNC4 _]].
exists Y; repeat split; Col; intro; treat_equalities; contra_ncol.
Qed.

Lemma tcp_os2_npars__meet : forall A1 A2 B1 B2,
  OS A1 A2 B1 B2 -> OS B1 B2 A1 A2 -> ~ Par_strict A1 A2 B1 B2 ->
  Lines_meet A1 A2 B1 B2.
Proof.
intros A1 A2 B1 B2 HOS1 HOS2 HNP.
assert (HNC1 := one_side_not_col123 _ _ _ _ HOS1).
assert (HNC2 := one_side_not_col124 _ _ _ _ HOS1).
assert (HNC3 := one_side_not_col123 _ _ _ _ HOS2).
assert (HNC4 := one_side_not_col124 _ _ _ _ HOS2).
apply tcp_ncol_inplane_4; Col; [apply os__coplanar; auto|].
intro; treat_equalities; Col.
Qed.

Lemma tcp_ts_mab_mac_a_p : forall A B C MAB MAC MBC SA P,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P ->
  TS MAB MAC A P.
Proof.
intros A B C MAB MAC MBC SA P HMAB HMAC HMBC HSA HNC HBP.
apply bet_ts__ts with MBC; [apply tcp_ts_mab_mac_a_mbc with B C; auto|].
apply between_exchange4 with SA; finish.
Qed.

Lemma tcp_ts_a_p_mab_mac : forall A B C MAB MAC MBC SA P,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P ->
  TS A P MAB MAC.
Proof.
intros A B C MAB MAC MBC SA P HMAB HMAC HMBC HSA HNC HBP.
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : A <> P) by (intro; treat_equalities; Col).
apply col_two_sides with MBC; [ColR|auto|].
apply tcp_ts_a_mbc_mab_mac with B C; auto.
Qed.

Lemma tcp_meet_mab_mac_a : forall A B C MAB MAC MBC SA P,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P ->
  Lines_meet MAB MAC P A.
Proof.
intros A B C MAB MAC MBC SA P HMAB HMAC HMBC HSA HNC HBP.
apply tcp_meet_swapr, tcp_ts2__meet;
[apply tcp_ts_mab_mac_a_p with B C MBC SA|
 apply tcp_ts_a_p_mab_mac with B C MBC SA]; auto.
Qed.

Lemma tcp_meet_mmab_mac_a : forall A B C MAB MAC MBC SA P MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAB A MAB ->
  Lines_meet MMAB MAC P A.
Proof.
intros A B C MAB MAC MBC SA P MMAB HMAB HMAC HMBC HSA HNC HBP HMMAB.
apply tcp_meet_swapr, tcp_ts2__meet.
- apply bet_ts__ts with MBC; [apply tcp_ts_mmab_mac_a_mbc with B C MAB; auto|].
  apply between_exchange4 with SA; finish.
- apply l9_5 with MAB A; [apply tcp_ts_a_p_mab_mac with B C MBC SA; auto|Col|].
  apply l6_6, bet_out; [intro; treat_equalities; Col|finish].
Qed.

Lemma tcp_meet_mab_mmac_a : forall A B C MAB MAC MBC SA P MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAC A MAC ->
  Lines_meet MAB MMAC P A.
Proof.
intros A B C MAB MAC MBC SA P MMAC HMAB HMAC HMBC HSA HNC HBP HMMAC.
apply tcp_meet_swapl, (tcp_meet_mmab_mac_a A C B MAC MAB MBC SA); finish.
Qed.

Lemma tcp_os_mab_mac_b_p : forall A B C MAB MAC MBC SA P,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P ->
  OS MAB MAC B P.
Proof.
intros A B C MAB MAC MBC SA P HMAB HMAC HMBC HSA HNC1 HBP.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MAB MAC A P)
  by (apply tcp_ts_mab_mac_a_p with B C MBC SA; auto).
exists A; split; [|finish].
split; [intro; apply HNC2; ColR|].
split; [intro; apply HNC2; ColR|].
exists MAB; finish.
Qed.

Lemma tcp_os_b_p_mab_mac : forall A B C MAB MAC MBC SA P,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P ->
  OS B P MAB MAC.
Proof.
intros A B C MAB MAC MBC SA P HMAB HMAC HMBC HSA HNC1 HBP.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MAB MAC A P)
  by (apply tcp_ts_mab_mac_a_p with B C MBC SA; auto).
assert (HBP' : Bet MBC SA P) by (apply between_exchange3 with A; finish).
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : A <> P) by (intro; treat_equalities; Col).
assert (HNE3 : MBC <> SA) by (intro; treat_equalities; Col).
assert (HNE4 : B <> P) by (intro; treat_equalities; apply HNC2; ColR).
apply one_side_transitivity with A; [apply out_one_side_1 with B|];
[intro; apply HNC2; ColR|Col|assert_diffs; repeat split; finish|].
apply l9_17 with C; [|finish].
apply one_side_transitivity with MBC;
[apply out_one_side_1 with P|apply out_one_side_1 with B]; Col;
[intro; apply HNC2; ColR| |intro; apply HNC2; ColR|];
repeat split; finish; try solve [intro; treat_equalities; Col].
right; apply between_symmetry, outer_transitivity_between with SA; finish.
Qed.

Lemma tcp_npars_mab_mac_b_p : forall A B C MAB MAC MBC SA P,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P ->
  ~ Par_strict MAB MAC B P.
Proof.
intros A B C MAB MAC MBC SA P HMAB HMAC HMBC HSA HNC HBP.
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : A <> P) by (intro; treat_equalities; Col).
assert (HPar : Par_strict MAB MAC MBC B) by (apply tcp_pars with A C; finish).
intro HPF; assert (HC : Col B MBC P)
  by (destruct (parallel_uniqueness MAB MAC B MBC B P B); finish).
cut (MBC = P); [intro; subst P|apply l6_21 with B C A P; finish; ColR].
assert (SA = MBC) by (apply between_equality with A; finish).
treat_equalities; Col.
Qed.

Lemma tcp_meet_mab_mac_b : forall A B C MAB MAC MBC SA P,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P ->
  Lines_meet MAB MAC P B.
Proof.
intros A B C MAB MAC MBC SA P HMAB HMAC HMBC HSA HNC HBP.
apply tcp_meet_swapr, tcp_os2_npars__meet;
[apply tcp_os_mab_mac_b_p with A C MBC SA|
 apply tcp_os_b_p_mab_mac with A C MBC SA|
 apply tcp_npars_mab_mac_b_p with A C MBC SA]; auto.
Qed.

Lemma tcp_meet_mab_mac_c : forall A B C MAB MAC MBC SA P,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P ->
  Lines_meet MAB MAC P C.
Proof.
intros A B C MAB MAC MBC SA P HMAB HMAC HMBC HSA HNC HBP.
apply tcp_meet_swapl, (tcp_meet_mab_mac_b A C B MAC MAB MBC SA); finish.
Qed.

Lemma tcp_ts_mmab_mac_a_p : forall A B C MAB MAC MBC SA P MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAB A MAB ->
  TS MMAB MAC A P.
Proof.
intros A B C MAB MAC MBC SA P MMAB HMAB HMAC HMBC HSA HNC HBP HMMAB.
apply bet_ts__ts with MBC; [apply tcp_ts_mmab_mac_a_mbc with B C MAB; auto|].
apply between_exchange4 with SA; finish.
Qed.

Lemma tcp_os_mmab_mac_b_p : forall A B C MAB MAC MBC SA P MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAB A MAB ->
  OS MMAB MAC B P.
Proof.
intros A B C MAB MAC MBC SA P MMAB HMAB HMAC HMBC HSA HNC HBP HMMAB.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MMAB MAC A P)
  by (apply tcp_ts_mmab_mac_a_p with B C MAB MBC SA; auto).
assert (HNE1 : A <> MMAB) by (intro; treat_equalities; Col).
assert (HNE2 : B <> MMAB).
  {
  intro; treat_equalities; cut (B = MAB); [assert_diffs; auto|].
  apply between_equality with A; finish.
  }
exists A; split; [|finish].
split; [intro; apply HNC2; ColR|].
split; [intro; apply HNC2; ColR|].
exists MMAB; split; [finish|].
apply between_symmetry, between_exchange4 with MAB; finish.
Qed.

Lemma tcp_os_b_p_mmab_mac : forall A B C MAB MAC MBC SA P MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAB A MAB ->
  OS B P MMAB MAC.
Proof.
intros A B C MAB MAC MBC SA P MMAB HMAB HMAC HMBC HSA HNC HBP HMMAB.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HOS : OS B P MAB MAC)
  by (apply tcp_os_b_p_mab_mac with A C MBC SA; auto).
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : B <> P) by (apply one_side_not_col123 in HOS; assert_diffs; auto).
apply one_side_transitivity with MAB; [|auto].
apply out_one_side; [right; intro; apply HNC2; ColR|].
repeat split; [intro; treat_equalities..|right]; Col;
[cut (MAB = MMAB); [assert_diffs; auto|apply between_equality with A; finish]|].
apply between_inner_transitivity with A; finish.
Qed.

Lemma tcp_npars_mmab_mac_b_sa : forall A B C MAB MAC MBC SA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAB A MAB ->
  ~ Par_strict MMAB MAC B SA.
Proof.
intros A B C MAB MAC MBC SA MMAB HMAB HMAC HMBC HSA HNC1 HMMAB.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HP : Par_strict B SA MAB MBC)
  by (apply triangle_mid_par_strict with A; finish; intro; apply HNC2; ColR).
cut (~ Par MAB MBC MMAB MAC);
[intros HF ?; apply HF; apply par_trans with B SA; finish|clear HP; intro HP1].
destruct (midpoint_existence A MBC) as [MAMBC HAMABC].
assert (HP2 : Par_strict MAB MBC MMAB MAMBC)
  by (apply triangle_mid_par_strict with A; finish; intro; apply HNC2; ColR).
assert (HC : Col MMAB MAMBC MAC)
  by (destruct (parallel_uniqueness MAB MBC MMAB MAC MMAB MAMBC MMAB); finish).
assert (HP3 : Par_strict MBC C MAMBC MAC)
  by (apply triangle_mid_par_strict with A; finish; intro; apply HNC2; ColR).
cut (Col MAB MBC C); [intro; apply HNC2; ColR|].
destruct (parallel_uniqueness MMAB MAC MAB MBC MBC C MBC); finish.
apply par_col4__par with MAMBC MAC MBC C; finish; [|assert_diffs; auto].
intro; treat_equalities; assert_diffs; auto.
Qed.

Lemma tcp_meet_mmab_mac_b_sa : forall A B C MAB MAC MBC SA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAB A MAB ->
  Lines_meet MMAB MAC SA B.
Proof.
intros A B C MAB MAC MBC SA MMAB HMAB HMAC HMBC HSA HNC HMMAB.
apply tcp_meet_swapr, tcp_os2_npars__meet;
[apply tcp_os_mmab_mac_b_p with A C MAB MBC SA|
 apply tcp_os_b_p_mmab_mac with A C MAB MBC SA|
 intro; apply (tcp_npars_mmab_mac_b_sa A B C MAB MAC MBC SA MMAB)];
finish.
Qed.

Lemma tcp_bet_sa_b_inter_mab_mac_b_sa : forall A B C MAB MAC MBC SA MMAB I,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAB A MAB ->
  Col MMAB MAC I -> Col SA B I ->
  Bet SA B I.
Proof.
intros A B C MAB MAC MBC SA MMAB I HMAB HMAC HMBC HSA HNC HMMAB HC1 HOut.
elim (bet_dec SA B I); [finish|intro HNBet; exfalso].
apply not_bet_out in HOut; [clear HNBet|finish].
assert (HTS : TS MMAB MAC A MBC)
  by (apply tcp_ts_mmab_mac_a_mbc with B C MAB; auto).
destruct HTS as [_ [_ [T [HC2 HBet1]]]].
destruct (symmetric_point_construction A T) as [ST HST].
assert (HNC2 : OS MMAB MAC B SA)
  by (apply tcp_os_mmab_mac_b_p with A C MAB MBC SA; finish).
apply one_side_not_col123 in HNC2.
assert (HNE : A <> T) by (intro; treat_equalities; apply HNC2; ColR).
assert (HNE8 : MAB <> ST).
  {
  destruct (tcp_ts_a_mbc_mab_mac A B C MAB MAC MBC) as [HNC6 _]; auto.
  intro; treat_equalities; apply HNC6; ColR.
  }
assert (HC3 : Col C MAB ST).
  {
  destruct (parallel_uniqueness MMAB MAC MAB ST MAB C MAB); Col;
  apply par_symmetry, par_strict_par;
  [apply par_strict_col2_par_strict with MMAB T; Col|];
  [intro; treat_equalities; Col|..];
  apply triangle_mid_par_strict with A; finish; intro; apply HNC2; ColR.
  }
assert (HTS : TS MAB ST A MBC).
  {
  apply col_preserves_two_sides with MAB C; finish.
  apply l9_2, l9_8_2 with B;
  [split; [|split]; [intro; apply HNC2; ColR..|exists MAB; finish]|].
  apply invert_one_side, out_one_side; [left; intro; apply HNC2; ColR|].
  repeat split; [assert_diffs; auto..|finish].
  }
assert (HBet2 : Bet A ST MBC).
  {
  destruct HTS as [_ [_ [X []]]]; cut (ST = X); [intro; subst; auto|].
  apply l6_21 with A MBC MAB ST; Col; [intro; apply HNC2|]; ColR.
  }
assert (HNE9 : MBC <> ST) by (intro; treat_equalities; assert_diffs; auto).
destruct (symmetric_point_construction A ST) as [SST HSST].
apply (bet_double_bet _ SST SA) in HBet2; finish.
assert (HF : TS B SST A SA).
  {
  split; [intro; apply HNC2; ColR|].
  split; [|exists SST; finish].
  destruct HTS as [HF _]; assert (SA <> SST); intro; apply HF; ColR.
  }
apply (l9_9 _ _ _ _ HF).
apply out_out_one_side with I; [|finish].
apply one_side_transitivity with MMAB; [apply out_one_side|];
[left; intro; apply HNC2; ColR|repeat split; [assert_diffs; auto..|right]|];
[apply between_exchange2 with MAB; finish|apply l12_6].
apply par_not_col_strict with MMAB; [|Col|intro; apply HNC2; ColR].
assert (HNE10 : MMAB <> I) by (intro; treat_equalities; apply HNC2; ColR).
apply par_strict_trans with MAB C;
[apply par_strict_col2_par_strict with MAB ST|
 apply par_strict_col2_par_strict with MMAB MAC];
[intro; treat_equalities|..]; Col; apply triangle_mid_par_strict with A; finish;
intro; apply HNC2; ColR.
Qed.

Lemma tcp_meet_mmab_mac_b : forall A B C MAB MAC MBC SA P MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAB A MAB ->
  Lines_meet MMAB MAC P B.
Proof.
intros A B C MAB MAC MBC SA P MMAB HMAB HMAC HMBC HSA HNC HBP HMMAB.
assert (HOS1 : OS MMAB MAC B P)
  by (apply tcp_os_mmab_mac_b_p with A C MAB MBC SA; auto).
assert (HOS2 : OS B P MMAB MAC)
  by (apply tcp_os_b_p_mmab_mac with A C MAB MBC SA; auto).
assert (HNC2 := one_side_not_col123 _ _ _ _ HOS1).
assert (HNC3 := one_side_not_col124 _ _ _ _ HOS1).
assert (HNC4 := one_side_not_col124 _ _ _ _ HOS2).
assert (HNC5 := one_side_not_col123 _ _ _ _ HOS2).
cut (exists Z, Col MMAB MAC Z /\ Col P B Z);
[intros [Y []]; exists Y; repeat split; Col; intro; treat_equalities; Col|].
destruct (tcp_meet_mmab_mac_b_sa A B C MAB MAC MBC SA MMAB) as [Y HY]; auto.
destruct (tcp_ts_mmab_mac_a_p A B C MAB MAC MBC SA SA MMAB) as [_ [_ HX]];
[finish..|].
destruct HX as [X HX]; assert (HBet : Bet X SA P)
  by (apply between_exchange3 with A; spliter; auto).
assert (HNE : X <> Y).
  {
  intro; treat_equalities; spliter.
  assert (HOS3 : OS MMAB MAC B SA)
    by (apply tcp_os_mmab_mac_b_p with A C MAB MBC SA; finish).
  apply (one_side_not_col124 _ _ _ _ HOS3); ColR.
  }
cut (Bet Y B SA); [intro; destruct (outer_pasch X Y SA P B) as [Z []]; auto|];
[spliter; exists Z; split; ColR|apply between_symmetry; spliter].
apply tcp_bet_sa_b_inter_mab_mac_b_sa with A C MAB MAC MBC MMAB; finish.
Qed.

Lemma tcp_ts_mab_mmac_a_p : forall A B C MAB MAC MBC SA P MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAC A MAC ->
  TS MAB MMAC A P.
Proof.
intros A B C MAB MAC MBC SA P MMAC HMAB HMAC HMBC HSA HNC HBP HMMAC.
apply invert_two_sides, (tcp_ts_mmab_mac_a_p A C B MAC MAB MBC SA); finish.
Qed.

Lemma tcp_os_mab_mmac_b_p : forall A B C MAB MAC MBC SA P MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAC A MAC ->
  OS MAB MMAC B P.
Proof.
intros A B C MAB MAC MBC SA P MMAC HMAB HMAC HMBC HSA HNC HBP HMMAC.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MAB MMAC A P)
  by (apply tcp_ts_mab_mmac_a_p with B C MAC MBC SA; auto).
exists A; split; [|finish].
split; [intro; apply HNC2; ColR|].
split; [intro; apply HNC2; ColR|].
exists MAB; finish.
Qed.

Lemma tcp_os_b_p_mab_mmac : forall A B C MAB MAC MBC SA P MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAC A MAC ->
  OS B P MAB MMAC.
Proof.
intros A B C MAB MAC MBC SA P MMAC HMAB HMAC HMBC HSA HNC HBP HMMAC.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HBP' : Bet MBC SA P) by (apply between_exchange3 with A; finish).
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : A <> P) by (intro; treat_equalities; Col).
assert (HNE3 : B <> SA) by (intro; treat_equalities; Col).
assert (HNE4 : MBC <> SA) by (intro; treat_equalities; Col).
apply one_side_transitivity with MAC;
[apply tcp_os_b_p_mab_mac with A C MBC SA; auto|].
apply l9_17 with A; [apply one_side_symmetry|finish].
apply l9_17 with C; [|finish].
apply one_side_transitivity with MBC; [apply invert_one_side|];
apply out_one_side; [left; intro| |right; intro|]; try solve [apply HNC2; ColR];
repeat split; finish; try solve [intro; treat_equalities; Col].
right; apply between_symmetry, outer_transitivity_between with SA; finish.
Qed.

Lemma tcp_npars_mab_mmac_b_p : forall A B C MAB MAC MBC SA P MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAC A MAC ->
  ~ Par_strict MAB MMAC B P.
Proof.
intros A B C MAB MAC MBC SA P MMAC HMAB HMAC HMBC HSA HNC HBP HMMAC.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HP : Par_strict B MAC MAB MMAC)
  by (apply triangle_mid_par_strict with A; finish; intro; apply HNC2; ColR).
cut (~ Par B MAC B P);
[intros HF ?; apply HF; apply par_trans with MAB MMAC; finish|].
clear HP; intros [[_ HF]|[HNE2 [HNE3 [_ HC]]]]; [apply HF; exists B; finish|].
assert (HOS : OS B P MAB MAC)
  by (apply tcp_os_b_p_mab_mac with A C MBC SA; auto).
apply (one_side_not_col124 _ _ _ _ HOS); Col.
Qed.

Lemma tcp_meet_mab_mmac_b : forall A B C MAB MAC MBC SA P MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAC A MAC ->
  Lines_meet MAB MMAC P B.
Proof.
intros A B C MAB MAC MBC SA P MMAC HMAB HMAC HMBC HSA HNC HBP HMMAC.
apply tcp_meet_swapr, tcp_os2_npars__meet;
[apply tcp_os_mab_mmac_b_p with A C MAC MBC SA|
 apply tcp_os_b_p_mab_mmac with A C MAC MBC SA|
 apply tcp_npars_mab_mmac_b_p with A C MAC MBC SA]; auto.
Qed.

Lemma tcp_meet_mmab_mac_c : forall A B C MAB MAC MBC SA P MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAB A MAB ->
  Lines_meet MMAB MAC P C.
Proof.
intros A B C MAB MAC MBC SA P MMAB HMAB HMAC HMBC HSA HNC HBP HMMAB.
apply tcp_meet_swapl, (tcp_meet_mab_mmac_b A C B MAC MAB MBC SA); finish.
Qed.

Lemma tcp_meet_mab_mmac_c : forall A B C MAB MAC MBC SA P MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Bet A SA P -> Midpoint MMAC A MAC ->
  Lines_meet MAB MMAC P C.
Proof.
intros A B C MAB MAC MBC SA P MMAC HMAB HMAC HMBC HSA HNC HBP HMMAC.
apply tcp_meet_swapl, (tcp_meet_mmab_mac_b A C B MAC MAB MBC SA); finish.
Qed.


Lemma tcp_ncol_ndc_ncol : forall A B C MAB MAC MBC SA MMAB MMAC X P,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C ->
  Midpoint MMAB A MAB -> Midpoint MMAC A MAC -> ~ Col MAB MAC X ->
  Cong A X B X -> Cong A X C X -> Coplanar A B C X ->
  Bet A SA P -> P <> X -> Col MMAB MAC X ->
  ~ Col MMAB MAC P -> ~ Col MAC P X -> ~ Col MAB MMAC X ->
  ~ Col MAB P X.
Proof.
intros A B C MAB MAC MBC SA MMAB MMAC X P HMAB HMAC HMBC HSA HNC1 HMMAB HMMAC.
intros HNC2 HC1 HC2 HCop HBet1 HNE1 HCol1 HNC4 HNC5 HNC6 HCol2.
assert (HXMAB : X <> MAB) by (intro; subst; apply HNC6; Col).
assert (HXMAC : X <> MAC) by (intro; subst; apply HNC5; Col).
assert (HMMABMAC : MMAB <> MAC) by (intro; subst; apply HNC4; Col).
assert (HCong : Cong P A P B).
  {
  apply per_double_cong with MAB; [|Midpoint].
  apply l8_2, per_col with X; auto; [apply l8_2; exists B; split; Cong|Col].
  }
assert (HPer1 : Per A C MAB).
  {
  assert (HPer : Per MMAB MAC A).
    {
    apply l8_2, per_col with X; auto; [apply l8_2; exists C; split; Cong|Col].
    }
  assert (HPerp : Perp MMAB MAC C A).
    {
    apply perp_col4 with MMAB MAC MAC A; Col; [intro; subst; Col|].
    apply per_perp; auto; intro; treat_equalities; Col.
    }
  apply perp_per_1, perp_sym, cop_par_perp__perp with MMAB MAC; [|auto|Cop].
  apply par_symmetry, triangle_mid_par with A; Midpoint.
  intro; treat_equalities; apply HNC1; Col.
  }
assert (HCSA : C <> SA)
  by (intro; subst SA; apply HNC1;
      assert (A = B) by (apply symmetric_point_uniqueness with C MBC; Midpoint);
      subst; Col).
assert (HLt1 : Lt C A A SA).
  {
  destruct (inner_pasch A C B MAB MBC) as [I [HI1 HI2]]; Between.
  assert (HCI : C <> I) by (intro; subst; apply HNC1; ColR).
  assert (HLeA : LeA A C MAB A C SA).
    {
    apply inangle__lea; repeat split; [intro; subst; Col|auto|
                                       intro; subst; apply HNC1; Col|].
    exists I; split; [apply between_exchange4 with MBC; Between|right].
    apply bet_out; Between.
    }
  assert (HAC : A <> C) by (intro; subst; Col).
  apply l11_46; auto.
  elim (angle_partition A C SA HAC HCSA); [intro HAcute; exfalso|auto].
  apply (lea__nlta A C MAB A C SA); auto.
  apply acute_per__lta; auto; intro; treat_equalities; apply HNC1; Col.
  }
destruct (segment_construction P SA SA B) as [D [HBet2 HCong2]].
apply (lt__nle P B P A); [|apply cong__le; Cong].
apply le1234_lt__lt with P D; [apply triangle_inequality with SA; Cong|].
apply bet2_lt_le__lt with SA SA; Between; Cong.
apply cong2_lt__lt with C A A SA; Cong.
apply cong_transitivity with SA B; Cong.
apply cong_right_commutativity, l7_13 with MBC; Midpoint.
Qed.

Lemma tcp_ncol_ndc_choice_col : forall A B C MAB MAC MBC SA MMAB MMAC X P,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C ->
  Midpoint MMAB A MAB -> Midpoint MMAC A MAC -> ~ Col MAB MAC X ->
  Cong A X B X -> Cong A X C X -> Coplanar A B C X ->
  Bet A SA P -> P <> X -> Col MMAB MAC X ->
  ~ Col MAB P X /\ ~ Col MAC P X /\ ~ Par_strict MAB MAC P X \/
  ~ Col MAB P X /\ ~ Col MMAC P X /\
  ~ Par_strict MAB MMAC P X /\ ~ Col MAB MMAC X.
Proof.
intros A B C MAB MAC MBC SA MMAB MMAC X P.
intros HMAB HMAC HMBC MSA HNC1 HMMAB HMMAC HNC2 HC1 HC2 HCop HBet1 HNE1 HCol1.
assert (HNC3 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HNC4 : ~ Col MMAB MAC P).
  {
  intro HF; cut (TS MMAB MAC A P); [intros [_ [? _]]; Col|].
  apply bet_ts__ts with MBC; [|apply between_exchange4 with SA; finish].
  apply l9_2, l9_8_2 with C;
  [split; [|split]; [intro; apply HNC3; ColR..|exists MAC; finish]|].
  apply l9_17 with B; [|finish].
  apply one_side_transitivity with MAB; [|apply out_one_side];
  [|left; intro; apply HNC3; ColR|repeat split];
  [|intro; treat_equalities..|left; apply between_exchange3 with A]; finish;
  [|cut (B = MAB); [assert_diffs; auto|apply between_equality with A; finish]].
  cut (Par_strict MAB C MMAB MAC); [finish|].
  apply triangle_mid_par_strict with A; finish; intro; apply HNC3; ColR.
  }
assert (HNC5 : ~ Col MAC P X).
  {
  intro HF; cut (MAC = X); [|apply l6_21 with MMAB MAC P X; Col].
  intro; treat_equalities; Col.
  }
elim (col_dec MAB MMAC X); [intro HCol2|intro HNC6].

  {
  assert (HBet2 : Bet A X MBC).
    {
    destruct (midpoint_existence A MBC) as [M HM1].
    cut (Bet A X M); [intro; apply between_exchange4 with M; finish|].
    assert (HCol3 : Col MAB MAC M).
      {
      destruct (parallel_uniqueness B C MAB M MAC M M); Col;
      [apply par_col4__par with B MBC MAB M|
       apply par_col4__par with C MBC MAC M]; Col;
      try solve [intro; treat_equalities; Col];
      assert_diffs; apply triangle_mid_par with A; finish.
      }
    assert (HM2 : Midpoint M MAB MAC).
      {
      cut (Cong MAB M MAC M);
      [intro; destruct (l7_20 M MAB MAC); treat_equalities; finish|].
      destruct (midpoint_existence B MBC) as [M1].
      destruct (midpoint_existence C MBC) as [M2].
      assert (HC3 : Cong MBC M1 MBC M2)
        by (apply cong_cong_half_2 with B C; finish).
      cut (Cong MAB M MBC M1 /\ Cong MAC M MBC M2); [intros []; CongR|].
      destruct (triangle_mid_par_strict_cong A C MBC M2 M MAC) as [_ ?]; finish;
      [intro; apply HNC3; ColR|].
      destruct (triangle_mid_par_strict_cong A B MBC M1 M MAB) as [_ ?]; finish;
      [intro; apply HNC3; ColR|spliter; split; finish].
      }
    assert (HCol4 : Col A X M).
      {
      cut (Col X M A); [|apply is_gravity_center_col with MAB MAC]; finish.
      split; [intro; apply HNC3; ColR|exists MMAC, MMAB].
      repeat split; finish.
      }
    cut (TS MMAB MAC A M); [intros [_ [_ [I []]]]; cut (X = I)|];
    [intro; subst; auto|apply l6_21 with MMAB MAC A M; Col; intro|];
    [apply HNC3; ColR|treat_equalities; Col|].
    apply l9_2, l9_8_2 with MAB;
    [split; [|split]; [intro; apply HNC3; ColR..|exists MMAB; finish]|].
    apply invert_one_side, out_one_side; [left; intro; apply HNC3; ColR|].
    repeat split; finish; intro; treat_equalities; Col.
    }
  assert (HNE2 : A <> SA) by (intro; treat_equalities; Col).
  left; split; [|split]; [intro; apply HNC3; ColR..|].
  intros [_ HF]; apply HF; clear HF.
  cut (TS MAB MAC A P); [intros [_ [_ [I []]]]; exists I; split; ColR|].
  apply bet_ts__ts with SA; [|finish].
  apply bet_ts__ts with MBC; [|finish].
  apply tcp_ts_mab_mac_a_mbc with B C; finish.
  }

  {
  assert (HNC7 : ~ Col MAB P X)
    by (apply tcp_ncol_ndc_ncol with A B C MAC MBC SA MMAB MMAC; auto).
  assert (HPE : ~ Par_strict MAB MAC P X \/ ~ Par_strict MAB MMAC P X).
    {
    elim (par_dec MAB MAC P X); [|intro HF; left; intro; apply HF; finish].
    elim (par_dec MAB MMAC P X); [|intros HF; right; intro; apply HF; finish].
    intros HP1 HP2; exfalso; cut (Col MAB MAC MMAC); [intro; apply HNC3; ColR|].
    destruct (parallel_uniqueness P X MAB MAC MAB MMAC MAB); finish.
    }
  elim (col_dec MMAC P X); [intro HCol2; left|tauto].
  split; [|split]; Col; intros [_ HF]; apply HF; clear HF.
  assert (HNE2 : A <> SA) by (intro; treat_equalities; Col).
  assert (HNE3 : MMAC <> P) by (intro; treat_equalities; apply HNC3; ColR).
  cut (TS MAB MAC MMAC P); [intros [_ [_ [I []]]]; exists I; split; ColR|].
  apply l9_8_2 with A; [|apply invert_one_side, out_one_side];
  [|left; intro; apply HNC3; ColR|assert_diffs; repeat split; finish].
  apply bet_ts__ts with MBC; [apply tcp_ts_mab_mac_a_mbc with B C; finish|].
  apply between_exchange4 with SA; finish.
  }
Qed.

Lemma tcp_ncol_ndc_choice : forall A B C MAB MAC MBC SA SSA MMAB MMAC X,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAB A MAB -> Midpoint MMAC A MAC -> ~ Col MAB MAC X ->
  Cong A X B X -> Cong A X C X -> Coplanar A B C X ->
  exists P, Bet A SA P /\
  (~ Col MAB P X /\ ~ Col MAC P X /\ ~ Par_strict MAB MAC P X \/
   ~ Col MMAB P X /\ ~ Col MAC P X /\
   ~ Par_strict MMAB MAC P X /\ ~ Col MMAB MAC X \/
   ~ Col MAB P X /\ ~ Col MMAC P X /\
   ~ Par_strict MAB MMAC P X /\ ~ Col MAB MMAC X).
Proof.
intros A B C MAB MAC MBC SA SSA MMAB MMAC X.
intros HMAB HMAC HMBC MSA HSSA HNC1 HMMAB HMMAC HNC2 HC1 HC2 HCop.
assert (HBet : Bet A SA SSA).
  {
  apply outer_transitivity_between2 with MBC; finish.
  intro; treat_equalities; Col.
  }
assert (HNEE : SA <> X \/ SSA <> X).
  {
  elim (eq_dec_points SA X); [elim (eq_dec_points SSA X); [|auto]|auto].
  intros; treat_equalities; exfalso; Col.
  }
cut (forall P, Bet A SA P -> P <> X ->
               ~ Col MAB P X /\ ~ Col MAC P X /\ ~ Par_strict MAB MAC P X \/
               ~ Col MMAB P X /\ ~ Col MAC P X /\
               ~ Par_strict MMAB MAC P X /\ ~ Col MMAB MAC X \/
               ~ Col MAB P X /\ ~ Col MMAC P X /\
               ~ Par_strict MAB MMAC P X /\ ~ Col MAB MMAC X);
[intro HP; destruct HNEE; [exists SA|exists SSA]; split; finish|
 clear dependent SSA; intros P HBet HNE1].
assert (HNE2 : A <> MBC) by (intro; treat_equalities; Col).
assert (HNC3 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HNC4 : ~ Col C MAB P).
  {
  intro HF; cut (TS MAB C A SA); [intros [? [? [I []]]]|];
  [cut (I <> P); intro; [apply HNC3; ColR|treat_equalities; Col]|].
  apply bet_ts__ts with MBC; [|finish].
  apply l9_2, l9_8_2 with B; [|apply invert_one_side, out_one_side];
  [|left; intro; apply HNC3; ColR|repeat split; finish; assert_diffs; auto].
  split; [|split]; [intro; apply HNC3; ColR..|exists MAB; finish].
  }
assert (HNC5 : ~ Col B MAC P).
  {
  intro HF; cut (TS MAC B A SA); [intros [? [? [I []]]]|];
  [cut (I <> P); intro; [apply HNC3; ColR|treat_equalities; Col]|].
  apply bet_ts__ts with MBC; [|finish].
  apply l9_2, l9_8_2 with C; [|apply invert_one_side, out_one_side];
  [|left; intro; apply HNC3; ColR|repeat split; finish; assert_diffs; auto].
  split; [|split]; [intro; apply HNC3; ColR..|exists MAC; finish].
  }
assert (HNC6 : ~ Col MMAB MMAC P).
  {
  intro HF; cut (TS MMAB MMAC A P); [intros [_ [? _]]; Col|].
  apply bet_ts__ts with MBC; [|apply between_exchange4 with SA; finish].
  apply l9_2, l9_8_2 with MAB;
  [split; [|split]; [intro; apply HNC3; ColR..|exists MMAB; finish]|].
  assert (HP1 : Par_strict MAB MAC MMAB MMAC)
    by (apply triangle_mid_par_strict with A; finish; intro; apply HNC3; ColR).
  assert (HP2 : Par_strict B C MAB MAC)
    by (apply triangle_mid_par_strict with A; finish).
  assert (HP3 : Par_strict B MBC MMAB MMAC).
    {
    assert (HNE4 : B <> MMAB).
      {
      intro; treat_equalities.
      destruct (between_equality B MAB A); finish.
      treat_equalities; Col.
      }
    apply par_not_col_strict with MMAB; [|Col|intro; apply HNC3; ColR].
    apply par_trans with MAB MAC; [|finish].
    apply par_symmetry, par_col2_par with B C; finish.
    intro; treat_equalities; Col.
    }
  apply one_side_transitivity with B; [|finish].
  apply out_one_side; [apply par_strict_not_cols in HP3; spliter; finish|].
  repeat split; [intro; treat_equalities..|]; [Col|apply HNC3; ColR|left].
  apply between_exchange3 with A; finish.
  }
assert (HE : ~ Col MMAB MAC X /\ ~ Col MAB MMAC X \/
             Col MMAB MAC X \/ Col MAB MMAC X)
  by (elim (col_dec MMAB MAC X); elim (col_dec MAB MMAC X); auto).
destruct HE as [[HNC7 HNC8]|HE].
  {
  elim (col_dec MAB P X); [|elim (col_dec MAC P X)];
  [intro HC; right; left|intros HC _; right; right|];
  [repeat split; intro HF..|]; Col;
  try solve [destruct (col2__eq _ _ _ _ HC HF); [intro; apply HNC1; ColR|auto]];
  try solve [destruct (col2__eq _ _ _ _ HC HF); [intro; apply HNC2; ColR|auto]];
  [apply HNC4|apply HNC5|];
  [destruct (parallel_uniqueness MMAB MAC MAB C P X MAB); finish;
  apply par_symmetry, par_strict_par, triangle_mid_par_strict with A; finish|
  destruct (parallel_uniqueness MMAC MAB MAC B P X MAC); finish;
  apply par_symmetry, par_strict_par, triangle_mid_par_strict with A; finish|];
  [intro; apply HNC2; ColR..|intros HNC9 HNC10].
  elim (par_dec MAB MAC P X); [intro HP; right|];
  [|intro HNP; left; repeat split; [..|intro; apply HNP]; finish].
  elim (col_dec MMAB P X); intro HC; [right|left]; repeat split; auto;
  intro HF; [destruct (col2__eq _ _ _ _ HC HF); Col|..];
  [cut (Col MAB MAC MMAC)|cut (Col MAB MAC MMAB)];
  try (intro; apply HNC3; ColR);
  [destruct (parallel_uniqueness P X MAB MAC MAB MMAC MAB); finish|
   destruct (parallel_uniqueness P X MAB MAC MAC MMAB MAC); finish].
  }

  {
  destruct HE;
  [assert (HEE := tcp_ncol_ndc_choice_col A B C MAB MAC MBC SA MMAB MMAC X P)|
   assert (HEE := tcp_ncol_ndc_choice_col A C B MAC MAB MBC SA MMAC MMAB X P)];
  destruct HEE as [|]; finish; [left|right; left];
  spliter; repeat split; finish.
  }
Qed.

Lemma tcp_ncol_inplane_aux : forall A B C MAB MAC MBC X,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C -> ~ Col A B C ->
  ~ Col MAB MAC X -> Cong A X B X -> Cong A X C X -> Coplanar A B C X ->
  exists E F G, ~ Col E F G /\
                Lines_meet E F G A /\ Lines_meet E F G B /\
                Lines_meet E F G C /\ Lines_meet E F G X.
Proof.
intros A B C MAB MAC MBC X HMAB HMAC HMBC HNC1 HNC2 HC1 HC2 HCop.
destruct (symmetric_point_construction A MBC) as [SA HSA].
destruct (symmetric_point_construction MBC SA) as [SSA HSSA].
destruct (midpoint_existence A MAB) as [MMAB HMMAB].
destruct (midpoint_existence A MAC) as [MMAC HMMAC].
destruct (tcp_ncol_ndc_choice A B C MAB MAC MBC SA SSA MMAB MMAC X)
  as [P [HBP HE]]; finish; clear dependent SSA.
assert (HNC3 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HNE : A <> SA) by (intro; treat_equalities; Col).
assert (HCop1 : forall Q, Col A MBC Q -> Coplanar MAB MAC MBC Q).
  {
  intros Q HQ; apply col_cop__cop with A; [|intro; treat_equalities; Col|Col].
  assert (HPar : Par_strict MAC MBC MAB A).
    {
    apply par_strict_col2_par_strict with A B; Col;
    [intro; treat_equalities; Col|].
    apply par_strict_symmetry, triangle_mid_par_strict with C; finish.
    }
  apply pars__coplanar in HPar; Cop.
  }
assert (HCop2 : forall Q, Coplanar A B C Q -> Coplanar MAB MAC MBC Q).
  {
  intros Q HQ; apply coplanar_pseudo_trans with A B C; Cop;
  apply coplanar_pseudo_trans with MAB MAC MBC; Cop.
  }
assert (HCopP : Coplanar MAB MAC MBC P) by (apply HCop1; ColR).
assert (HCopX : Coplanar MAB MAC MBC X) by (apply HCop2; Cop).
assert (HCopMMAB : Coplanar MAB MAC MBC MMAB).
  {
  apply HCop2; assert (Col A B MMAB); [|Cop].
  assert (A <> MAB) by (intro; treat_equalities; Col); ColR.
  }
assert (HCopMMAC : Coplanar MAB MAC MBC MMAC).
  {
  apply HCop2; assert (Col A C MMAC); [|Cop].
  assert (A <> MAC) by (intro; treat_equalities; Col); ColR.
  }
destruct HE as [HE|[HE|HE]]; spliter.
- assert (HNC4 : ~ Col MAB MAC P)
    by (apply (one_side_not_col124 _ _ B), tcp_os_mab_mac_b_p with A C MBC SA;
        finish).
  exists MAB, MAC, P; split; [auto|].
  split; [apply tcp_meet_mab_mac_a with B C MBC SA; finish|].
  split; [apply tcp_meet_mab_mac_b with A C MBC SA; finish|].
  split; [apply tcp_meet_mab_mac_c with A B MBC SA; finish|].
  apply tcp_ncol_inplane_4; Col; [|intro; treat_equalities; Col].
  apply coplanar_pseudo_trans with MAB MAC MBC; Cop.
- assert (HNC4 : ~ Col MMAB MAC P)
    by (apply (one_side_not_col124 _ _ B), tcp_os_mmab_mac_b_p
          with A C MAB MBC SA; finish).
  exists MMAB, MAC, P; split; [auto|].
  split; [apply tcp_meet_mmab_mac_a with B C MAB MBC SA; finish|].
  split; [apply tcp_meet_mmab_mac_b with A C MAB MBC SA; finish|].
  split; [apply tcp_meet_mmab_mac_c with A B MAB MBC SA; finish|].
  apply tcp_ncol_inplane_4; Col; [|intro; treat_equalities; Col].
  apply coplanar_pseudo_trans with MAB MAC MBC; Cop.
- assert (HNC4 : ~ Col MAB MMAC P)
    by (apply (one_side_not_col124 _ _ B), tcp_os_mab_mmac_b_p
          with A C MAC MBC SA; finish).
  exists MAB, MMAC, P; split; [auto|].
  split; [apply tcp_meet_mab_mmac_a with B C MAC MBC SA; finish|].
  split; [apply tcp_meet_mab_mmac_b with A C MAC MBC SA; finish|].
  split; [apply tcp_meet_mab_mmac_c with A B MAC MBC SA; finish|].
  apply tcp_ncol_inplane_4; Col; [|intro; treat_equalities; Col].
  apply coplanar_pseudo_trans with MAB MAC MBC; Cop.
Qed.

Lemma tcp_ncol_inplane : forall A B C X,
  ~ Col A B C -> Cong A X B X -> Cong A X C X -> Coplanar A B C X ->
  exists E F G, ~ Col E F G /\
                (exists Y, (Col E F Y /\ E <> F /\ E <> Y /\ F <> Y) /\
                           (Col G A Y /\ G <> A /\ G <> Y /\ A <> Y)) /\
                (exists Y, (Col E F Y /\ E <> F /\ E <> Y /\ F <> Y) /\
                           (Col G B Y /\ G <> B /\ G <> Y /\ B <> Y)) /\
                (exists Y, (Col E F Y /\ E <> F /\ E <> Y /\ F <> Y) /\
                           (Col G C Y /\ G <> C /\ G <> Y /\ C <> Y)) /\
                (exists Y, (Col E F Y /\ E <> F /\ E <> Y /\ F <> Y) /\
                           (Col G X Y /\ G <> X /\ G <> Y /\ X <> Y)).
Proof.
intros A B C X HNC1 HC1 HC2 HCop.
destruct (midpoint_existence A B) as [MAB HMAB].
destruct (midpoint_existence A C) as [MAC HMAC].
destruct (midpoint_existence B C) as [MBC HMBC].
destruct (tcp_ncols_ndc A B C X MAB MAC MBC) as [HNC2|HNC2]; auto;
[apply tcp_ncol_inplane_aux with MAB MAC MBC; auto|].
destruct HNC2 as [HNC2|HNC2];
[destruct (tcp_ncol_inplane_aux B A C MAB MBC MAC X) as [E [F [G H]]]|
 destruct (tcp_ncol_inplane_aux C A B MAC MBC MAB X) as [E [F [G H]]]];
finish; [CongR| |CongR|]; exists E, F, G; spliter; repeat split; Col.
Qed.

End tcp_ndc.