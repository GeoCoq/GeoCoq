Require Import GeoCoq.Algebraic.coplanarity.
Require Import GeoCoq.Main.Tarski_dev.Ch12_parallel_inter_dec.
Require Import GeoCoq.Main.Annexes.quadrilaterals_inter_dec.
Require Import GeoCoq.Main.Highschool.circumcenter.
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

Lemma tcp_ts_mab_mac_a_sa : forall A B C MAB MAC MBC SA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C ->
  TS MAB MAC A SA.
Proof.
intros A B C MAB MAC MBC SA HMAB HMAC HMBC HSA HNC.
assert (HTS : TS MAB MAC A MBC) by (apply tcp_ts_mab_mac_a_mbc with B C; auto).
apply bet_ts__ts with MBC; finish.
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

Lemma tcp_ts_a_sa_mab_mac : forall A B C MAB MAC MBC SA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C ->
  TS A SA MAB MAC.
Proof.
intros A B C MAB MAC MBC SA HMAB HMAC HMBC HSA HNC.
assert (HNE : A <> SA) by (intro; treat_equalities; Col).
assert (HTS : TS A MBC MAB MAC) by (apply tcp_ts_a_mbc_mab_mac with B C; auto).
apply col_two_sides with MBC; finish.
Qed.

Lemma tcp_ncol_inplane_1_1 : forall A B C MAB MAC MBC SA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C ->
  (exists Y, (Col MAB MAC Y /\ MAB <> MAC /\ MAB <> Y /\ MAC<> Y) /\
             (Col SA A Y /\ SA <> A /\ SA <> Y /\ A <> Y)).
Proof.
intros A B C MAB MAC MBC SA HMAB HMAC HMBC HSA HNC.
assert (HTS1 : TS MAB MAC A SA)
  by (apply tcp_ts_mab_mac_a_sa with B C MBC; auto).
assert (HTS2 : TS A SA MAB MAC)
  by (apply tcp_ts_a_sa_mab_mac with B C MBC; auto).
destruct (ts2__ex_bet2 MAB A MAC SA) as [Y [HBet1 HBet2]]; auto.
apply (l9_18 _ _ _ _ Y) in HTS1; apply (l9_18 _ _ _ _ Y) in HTS2; Col.
destruct HTS1 as [_ [HNC3 HNC4]]; destruct HTS2 as [_ [HNC5 HNC6]].
exists Y; repeat split; Col; intro ; treat_equalities; Col;
[apply HNC5|apply HNC6|apply HNC4|apply HNC3]; Col.
Qed.

Lemma tcp_ts_mab_mac_a_ssa : forall A B C MAB MAC MBC SA SSA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  TS MAB MAC A SSA.
Proof.
intros A B C MAB MAC MBC SA SSA HMAB HMAC HMBC HSA HSSA HNC.
assert (HTS : TS MAB MAC A SA)
  by (apply tcp_ts_mab_mac_a_sa with B C MBC; auto).
apply l9_2, l9_8_2 with SA; [finish|].
assert (HNE1 : MBC <> SA) by (intro; treat_equalities; Col).
destruct HTS as [_ [? [Y []]]]; apply out_one_side_1 with Y; Col.
assert (HNE2 : SSA <> Y).
  {
  intro; treat_equalities; cut (SA = SSA); [assert_diffs; auto|].
  apply between_equality with MBC; [|finish].
  apply between_inner_transitivity with A; [finish|apply between_symmetry].
  apply outer_transitivity_between with SA; finish.
  }
repeat split; [intro; treat_equalities; Col|auto|left; apply between_symmetry].
apply between_inner_transitivity with A; [apply between_symmetry|finish].
apply between_exchange2 with MBC; [|finish].
apply outer_transitivity_between with SA; finish.
Qed.

Lemma tcp_ts_a_ssa_mab_mac : forall A B C MAB MAC MBC SA SSA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  TS A SSA MAB MAC.
Proof.
intros A B C MAB MAC MBC SA SSA HMAB HMAC HMBC HSA HSSA HNC.
assert (HNE : MBC <> SA) by (intro; treat_equalities; Col).
assert (HTS : TS A SA MAB MAC)
  by (apply tcp_ts_a_sa_mab_mac with B C MBC; auto).
apply col_two_sides with SA; [ColR| |finish].
intro; treat_equalities; apply HNE.
apply between_equality with A; finish.
Qed.

Lemma tcp_ncol_inplane_1_2 : forall A B C MAB MAC MBC SA SSA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  (exists Y, (Col MAB MAC Y /\ MAB <> MAC /\ MAB <> Y /\ MAC<> Y) /\
             (Col SSA A Y /\ SSA <> A /\ SSA <> Y /\ A <> Y)).
Proof.
intros A B C MAB MAC MBC SA SSA HMAB HMAC HMBC HSA HSSA HNC1.
assert (HTS1 : TS MAB MAC A SSA)
  by (apply tcp_ts_mab_mac_a_ssa with B C MBC SA; auto).
assert (HTS2 : TS A SSA MAB MAC)
  by (apply tcp_ts_a_ssa_mab_mac with B C MBC SA; auto).
destruct (ts2__ex_bet2 MAB A MAC SSA) as [Y [HBet1 HBet2]]; auto.
apply (l9_18 _ _ _ _ Y) in HTS1; apply (l9_18 _ _ _ _ Y) in HTS2; Col.
destruct HTS1 as [_ [HNC2 HNC3]]; destruct HTS2 as [_ [HNC4 HNC5]].
exists Y; repeat split; Col; intro ; treat_equalities; Col;
[apply HNC4|apply HNC5|apply HNC3|apply HNC2]; Col.
Qed.

Lemma tcp_ncol_inplane_1_3 : forall A B C MAB MAC MBC SA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAB A MAB ->
  (exists Y, (Col MMAB MAC Y /\ MMAB <> MAC /\ MMAB <> Y /\ MAC<> Y) /\
             (Col SA A Y /\ SA <> A /\ SA <> Y /\ A <> Y)).
Proof.
intros A B C MAB MAC MBC SA MMAB HMAB HMAC HMBC HSA HNC1 HMMAB.
assert (HTS1 : TS MAB MAC A SA)
  by (apply tcp_ts_mab_mac_a_sa with B C MBC; auto).
assert (HTS2 : TS A SA MAB MAC)
  by (apply tcp_ts_a_sa_mab_mac with B C MBC; auto).
destruct (ts2__ex_bet2 MAB A MAC SA) as [Y [HBet1 HBet2]]; auto.
destruct (inner_pasch A MAC MAB MMAB Y) as [Z [HBet3 HBet4]]; finish.
apply (l9_18 _ _ _ _ Y) in HTS1; apply (l9_18 _ _ _ _ Y) in HTS2; Col.
destruct HTS1 as [_ [HNC2 HNC3]]; destruct HTS2 as [_ [HNC4 HNC5]].
assert (HNE : A <> Y) by (intro; apply HNC2; ColR).
exists Z; repeat split; [ColR| | | |ColR|..]; intro; treat_equalities; Col;
[apply HNC4..|apply HNC5|apply HNC3|apply HNC2]; ColR.
Qed.

Lemma tcp_ncol_inplane_1_4 : forall A B C MAB MAC MBC SA SSA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAB A MAB ->
  (exists Y, (Col MMAB MAC Y /\ MMAB <> MAC /\ MMAB <> Y /\ MAC<> Y) /\
             (Col SSA A Y /\ SSA <> A /\ SSA <> Y /\ A <> Y)).
Proof.
intros A B C MAB MAC MBC SA SSA MMAB HMAB HMAC HMBC HSA HSSA HNC1 HMMAB.
assert (HTS1 : TS MAB MAC A SSA)
  by (apply tcp_ts_mab_mac_a_ssa with B C MBC SA; auto).
assert (HTS2 : TS A SSA MAB MAC)
  by (apply tcp_ts_a_ssa_mab_mac with B C MBC SA; auto).
destruct (ts2__ex_bet2 MAB A MAC SSA) as [Y [HBet1 HBet2]]; auto.
destruct (inner_pasch A MAC MAB MMAB Y) as [Z [HBet3 HBet4]]; finish.
apply (l9_18 _ _ _ _ Y) in HTS1; apply (l9_18 _ _ _ _ Y) in HTS2; Col.
destruct HTS1 as [_ [HNC2 HNC3]]; destruct HTS2 as [_ [HNC4 HNC5]].
assert (HNE : A <> Y) by (intro; apply HNC2; ColR).
exists Z; repeat split; [ColR| | | |ColR|..]; intro; treat_equalities; Col;
[apply HNC4..|apply HNC5|apply HNC3|apply HNC2]; ColR.
Qed.

Lemma tcp_ncol_inplane_1_5 : forall A B C MAB MAC MBC SA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAC A MAC ->
  (exists Y, (Col MAB MMAC Y /\ MAB <> MMAC /\ MAB <> Y /\ MMAC<> Y) /\
             (Col SA A Y /\ SA <> A /\ SA <> Y /\ A <> Y)).
Proof.
intros A B C MAB MAC MBC SA MMAC HMAB HMAC HMBC HSA HNC HMMAC.
destruct (tcp_ncol_inplane_1_3 A C B MAC MAB MBC SA MMAC) as [Y]; finish.
spliter; exists Y; repeat split; finish.
Qed.

Lemma tcp_ncol_inplane_1_6 : forall A B C MAB MAC MBC SA SSA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAC A MAC ->
  (exists Y, (Col MAB MMAC Y /\ MAB <> MMAC /\ MAB <> Y /\ MMAC<> Y) /\
             (Col SSA A Y /\ SSA <> A /\ SSA <> Y /\ A <> Y)).
Proof.
intros A B C MAB MAC MBC SA SSA MMAC HMAB HMAC HMBC HSA HSSA HNC HMMAC.
destruct (tcp_ncol_inplane_1_4 A C B MAC MAB MBC SA SSA MMAC) as [Y]; finish.
spliter; exists Y; repeat split; finish.
Qed.

Lemma tcp_os_mab_mac_b_sa : forall A B C MAB MAC MBC SA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C ->
  OS MAB MAC B SA.
Proof.
intros A B C MAB MAC MBC SA HMAB HMAC HMBC HSA HNC1.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MAB MAC A SA)
  by (apply tcp_ts_mab_mac_a_sa with B C MBC; auto).
exists A; split; [|finish].
split; [intro; apply HNC2; ColR|].
split; [intro; apply HNC2; ColR|].
exists MAB; finish.
Qed.

Lemma tcp_os_b_sa_mab_mac : forall A B C MAB MAC MBC SA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C ->
  OS B SA MAB MAC.
Proof.
intros A B C MAB MAC MBC SA HMAB HMAC HMBC HSA HNC1.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : B <> SA) by (intro; treat_equalities; Col).
apply one_side_transitivity with A; [apply out_one_side_1 with B|];
[intro; apply HNC2; ColR|Col|assert_diffs; repeat split; finish|].
apply l9_17 with C; [apply one_side_transitivity with MBC|finish];
[apply out_one_side_1 with SA|apply out_one_side_1 with B]; Col;
[intro; apply HNC2; ColR| |intro; apply HNC2; ColR|];
repeat split; finish; intro; treat_equalities; Col.
Qed.

Lemma tcp_npars_mab_mac_b_sa : forall A B C MAB MAC MBC SA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C ->
  ~ Par_strict MAB MAC B SA.
Proof.
intros A B C MAB MAC MBC SA HMAB HMAC HMBC HSA HNC.
assert (HP : Par_strict MAB MAC MBC B) by (apply tcp_pars with A C; finish).
intro HPF; assert (HC : Col B MBC SA)
  by (destruct (parallel_uniqueness MAB MAC B MBC B SA B); finish).
cut (MBC = SA); [intro; treat_equalities; Col|].
apply l6_21 with B C A SA; finish; [|ColR].
intro; treat_equalities; Col.
Qed.

Lemma tcp_ncol_inplane_2_1 : forall A B C MAB MAC MBC SA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C ->
  (exists Y, (Col MAB MAC Y /\ MAB <> MAC /\ MAB <> Y /\ MAC<> Y) /\
             (Col SA B Y /\ SA <> B /\ SA <> Y /\ B <> Y)).
Proof.
intros A B C MAB MAC MBC SA HMAB HMAC HMBC HSA HNC.
assert (HOS1 : OS MAB MAC B SA)
  by (apply tcp_os_mab_mac_b_sa with A C MBC; auto).
assert (HOS2 : OS B SA MAB MAC)
  by (apply tcp_os_b_sa_mab_mac with A C MBC; auto).
assert (HNP : ~ Par_strict MAB MAC B SA)
  by (apply tcp_npars_mab_mac_b_sa with A C MBC; auto).
assert (HNC2 := one_side_not_col123 _ _ _ _ HOS1).
assert (HNC3 := one_side_not_col124 _ _ _ _ HOS1).
assert (HNC4 := one_side_not_col124 _ _ _ _ HOS2).
assert (HNC5 := one_side_not_col123 _ _ _ _ HOS2).
destruct (cop_npars__inter_exists MAB MAC B SA) as [Y [HC1 HC2]]; finish.
exists Y; repeat split; Col; intro; treat_equalities; Col.
Qed.

Lemma tcp_os_mab_mac_b_ssa : forall A B C MAB MAC MBC SA SSA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  OS MAB MAC B SSA.
Proof.
intros A B C MAB MAC MBC SA SSA HMAB HMAC HMBC HSA HSSA HNC1.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MAB MAC A SSA)
  by (apply tcp_ts_mab_mac_a_ssa with B C MBC SA; auto).
exists A; split; [|finish].
split; [intro; apply HNC2; ColR|].
split; [intro; apply HNC2; ColR|].
exists MAB; finish.
Qed.

Lemma tcp_os_b_ssa_mab_mac : forall A B C MAB MAC MBC SA SSA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  OS B SSA MAB MAC.
Proof.
intros A B C MAB MAC MBC SA SSA HMAB HMAC HMBC HSA HSSA HNC1.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MAB MAC A SSA)
  by (apply tcp_ts_mab_mac_a_ssa with B C MBC SA; auto).
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : A <> SSA) by (assert_diffs; auto).
assert (HNE3 : MBC <> SA) by (intro; treat_equalities; Col).
assert (HNE4 : B <> SSA) by (intro; treat_equalities; apply HNC2; ColR).
apply one_side_transitivity with A; [apply out_one_side_1 with B|];
[intro; apply HNC2; ColR|Col|assert_diffs; repeat split; finish|].
apply l9_17 with C; [|finish].
apply one_side_transitivity with MBC;
[apply out_one_side_1 with SSA|apply out_one_side_1 with B]; Col;
[intro; apply HNC2; ColR| |intro; apply HNC2; ColR|];
repeat split; finish; try solve [intro; treat_equalities; Col].
right; apply between_symmetry, outer_transitivity_between with SA; finish.
Qed.

Lemma tcp_npars_mab_mac_b_ssa : forall A B C MAB MAC MBC SA SSA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  ~ Par_strict MAB MAC B SSA.
Proof.
intros A B C MAB MAC MBC SA SSA HMAB HMAC HMBC HSA HSSA HNC1.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MAB MAC A SSA)
  by (apply tcp_ts_mab_mac_a_ssa with B C MBC SA; auto).
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : A <> SSA) by (assert_diffs; auto).
assert (HP : Par_strict MAB MAC MBC B) by (apply tcp_pars with A C; finish).
intro HPF; assert (HC : Col B MBC SSA)
  by (destruct (parallel_uniqueness MAB MAC B MBC B SSA B); finish).
cut (MBC = SSA); [intro; treat_equalities; Col|].
apply l6_21 with B C A SSA; finish; ColR.
Qed.

Lemma tcp_ncol_inplane_2_2 : forall A B C MAB MAC MBC SA SSA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  (exists Y, (Col MAB MAC Y /\ MAB <> MAC /\ MAB <> Y /\ MAC<> Y) /\
             (Col SSA B Y /\ SSA <> B /\ SSA <> Y /\ B <> Y)).
Proof.
intros A B C MAB MAC MBC SA SSA HMAB HMAC HMBC HSA HSSA HNC.
assert (HOS1 : OS MAB MAC B SSA)
  by (apply tcp_os_mab_mac_b_ssa with A C MBC SA; auto).
assert (HOS2 : OS B SSA MAB MAC)
  by (apply tcp_os_b_ssa_mab_mac with A C MBC SA; auto).
assert (HNP : ~ Par_strict MAB MAC B SSA)
  by (apply tcp_npars_mab_mac_b_ssa with A C MBC SA; auto).
assert (HNC2 := one_side_not_col123 _ _ _ _ HOS1).
assert (HNC3 := one_side_not_col124 _ _ _ _ HOS1).
assert (HNC4 := one_side_not_col124 _ _ _ _ HOS2).
assert (HNC5 := one_side_not_col123 _ _ _ _ HOS2).
destruct (cop_npars__inter_exists MAB MAC B SSA) as [Y [HC3 HC4]]; finish.
exists Y; repeat split; Col; intro; treat_equalities; Col.
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

Lemma tcp_ts_mmab_mac_a_sa : forall A B C MAB MAC MBC SA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAB A MAB ->
  TS MMAB MAC A SA.
Proof.
intros A B C MAB MAC MBC SA MMAB HMAB HMAC HMBC HSA HNC1 HMMAB.
assert (HTS : TS MMAB MAC A MBC)
  by (apply tcp_ts_mmab_mac_a_mbc with B C MAB; auto).
apply bet_ts__ts with MBC; finish.
Qed.

Lemma tcp_os_mmab_mac_b_sa : forall A B C MAB MAC MBC SA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAB A MAB ->
  OS MMAB MAC B SA.
Proof.
intros A B C MAB MAC MBC SA MMAB HMAB HMAC HMBC HSA HNC HMMAB.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MMAB MAC A SA)
  by (apply tcp_ts_mmab_mac_a_sa with B C MAB MBC; auto).
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

Lemma tcp_os_b_sa_mmab_mac : forall A B C MAB MAC MBC SA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAB A MAB ->
  OS B SA MMAB MAC.
Proof.
intros A B C MAB MAC MBC SA MMAB HMAB HMAC HMBC HSA HNC HMMAB.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : B <> SA) by (intro; treat_equalities; Col).
apply one_side_transitivity with MAB;
[|apply tcp_os_b_sa_mab_mac with A C MBC; auto].
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

Lemma tcp_ncol_inplane_2_3 : forall A B C MAB MAC MBC SA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAB A MAB ->
  (exists Y, (Col MMAB MAC Y /\ MMAB <> MAC /\ MMAB <> Y /\ MAC<> Y) /\
             (Col SA B Y /\ SA <> B /\ SA <> Y /\ B <> Y)).
Proof.
intros A B C MAB MAC MBC SA MMAB HMAB HMAC HMBC HSA HNC1 HMMAB.
assert (HOS1 : OS MMAB MAC B SA)
  by (apply tcp_os_mmab_mac_b_sa with A C MAB MBC; auto).
assert (HOS2 : OS B SA MMAB MAC)
  by (apply tcp_os_b_sa_mmab_mac with A C MAB MBC; auto).
assert (HNP : ~ Par_strict MMAB MAC B SA)
  by (apply tcp_npars_mmab_mac_b_sa with A C MAB MBC; auto).
assert (HNC2 := one_side_not_col123 _ _ _ _ HOS1).
assert (HNC3 := one_side_not_col124 _ _ _ _ HOS1).
assert (HNC4 := one_side_not_col124 _ _ _ _ HOS2).
assert (HNC5 := one_side_not_col123 _ _ _ _ HOS2).
destruct (cop_npars__inter_exists MMAB MAC B SA) as [Y [HC1 HC2]]; finish.
exists Y; repeat split; Col; intro; treat_equalities; Col.
Qed.

Lemma tcp_os_mmab_mac_b_ssa : forall A B C MAB MAC MBC SA SSA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAB A MAB ->
  OS MMAB MAC B SSA.
Proof.
intros A B C MAB MAC MBC SA SSA MMAB HMAB HMAC HMBC HSA HSSA HNC HMMAB.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MMAB MAC A SSA).
  {
  apply bet_ts__ts with SA;
  [apply tcp_ts_mmab_mac_a_sa with B C MAB MBC; auto|].
  apply outer_transitivity_between2 with MBC; finish.
  intro; treat_equalities; Col.
  }
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

Lemma tcp_os_b_ssa_mmab_mac : forall A B C MAB MAC MBC SA SSA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAB A MAB ->
  OS B SSA MMAB MAC.
Proof.
intros A B C MAB MAC MBC SA SSA MMAB HMAB HMAC HMBC HSA HSSA HNC HMMAB.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MAB MAC A SSA)
  by (apply tcp_ts_mab_mac_a_ssa with B C MBC SA; auto).
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : A <> SSA) by (assert_diffs; auto).
assert (HNE3 : B <> SA) by (intro; treat_equalities; Col).
assert (HNE4 : B <> SSA) by (intro; treat_equalities; apply HNC2; ColR).
apply one_side_transitivity with MAB;
[|apply tcp_os_b_ssa_mab_mac with A C MBC SA; auto].
apply out_one_side; [right; intro; apply HNC2; ColR|].
repeat split; [intro; treat_equalities..|right]; Col;
[cut (MAB = MMAB); [assert_diffs; auto|apply between_equality with A; finish]|].
apply between_inner_transitivity with A; finish.
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
  by (apply tcp_os_mmab_mac_b_sa with A C MAB MBC; auto).
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

Lemma tcp_ncol_inplane_2_4 : forall A B C MAB MAC MBC SA SSA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAB A MAB ->
  (exists Y, (Col MMAB MAC Y /\ MMAB <> MAC /\ MMAB <> Y /\ MAC<> Y) /\
             (Col SSA B Y /\ SSA <> B /\ SSA <> Y /\ B <> Y)).
Proof.
intros A B C MAB MAC MBC SA SSA MMAB HMAB HMAC HMBC HSA HSSA HNC HMMAB.
assert (HOS1 : OS MMAB MAC B SSA)
  by (apply tcp_os_mmab_mac_b_ssa with A C MAB MBC SA; auto).
assert (HOS2 : OS B SSA MMAB MAC)
  by (apply tcp_os_b_ssa_mmab_mac with A C MAB MBC SA; auto).
assert (HNC2 := one_side_not_col123 _ _ _ _ HOS1).
assert (HNC3 := one_side_not_col124 _ _ _ _ HOS1).
assert (HNC4 := one_side_not_col124 _ _ _ _ HOS2).
assert (HNC5 := one_side_not_col123 _ _ _ _ HOS2).
cut (exists Z, Col MMAB MAC Z /\ Col SSA B Z);
[intros [Y []]; exists Y; repeat split; Col; intro; treat_equalities; Col|].
destruct (tcp_ncol_inplane_2_3 A B C MAB MAC MBC SA MMAB) as [Y HY]; auto.
destruct (tcp_ts_mmab_mac_a_sa A B C MAB MAC MBC SA MMAB) as [_ [_ HX]]; auto.
destruct HX as [X HX]; assert (HBet : Bet X SA SSA).
  {
  apply between_exchange3 with A; [spliter; auto|].
  apply outer_transitivity_between2 with MBC; finish.
  intro; treat_equalities; Col.
  }
assert (HNE : X <> Y) by (intro; treat_equalities; spliter; apply HNC5; ColR).
cut (Bet Y B SA); [intro; destruct (outer_pasch X Y SA SSA B) as [Z []]; auto|];
[spliter; exists Z; split; ColR|apply between_symmetry; spliter].
apply tcp_bet_sa_b_inter_mab_mac_b_sa with A C MAB MAC MBC MMAB; finish.
Qed.

Lemma tcp_ts_mab_mmac_a_sa : forall A B C MAB MAC MBC SA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAC A MAC ->
  TS MAB MMAC A SA.
Proof.
intros A B C MAB MAC MBC SA MMAC HMAB HMAC HMBC HSA HNC1 HMMAC.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
apply bet_ts__ts with MBC; [|finish].
assert (HTS1 : TS MAB MAC A MBC) by (apply tcp_ts_mab_mac_a_mbc with B C; auto).
assert (HTS2 : TS A MBC MAB MAC) by (apply tcp_ts_a_mbc_mab_mac with B C; auto).
destruct (ts2__ex_bet2 MAB A MAC MBC) as [Y [HBet1 HBet2]]; auto.
destruct (inner_pasch A MAB MAC MMAC Y) as [Z [HBet3 HBet4]]; finish.
apply (l9_18 _ _ _ _ Y) in HTS1; apply (l9_18 _ _ _ _ Y) in HTS2; Col.
assert (HNE1 : A <> Y) by (intro; apply HNC2; ColR).
assert (HNE2 : MAB <> MMAC) by (intro; apply HNC2; ColR).
assert (HBet : Bet A Z MBC) by (apply between_exchange4 with Y; finish).
assert (HNE3 : MBC <> Z) by (intro; treat_equalities; apply HNC2; Col).
split; [intro; apply HNC2; ColR|].
split; [intro; apply HNC2; ColR|exists Z; split; finish].
Qed.

Lemma tcp_os_mab_mmac_b_sa : forall A B C MAB MAC MBC SA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAC A MAC ->
  OS MAB MMAC B SA.
Proof.
intros A B C MAB MAC MBC SA MMAC HMAB HMAC HMBC HSA HNC HMMAC.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MAB MMAC A SA)
  by (apply tcp_ts_mab_mmac_a_sa with B C MAC MBC; auto).
assert (HNE1 : A <> MMAC) by (intro; treat_equalities; Col).
assert (HNE2 : C <> MMAC).
  {
  intro; treat_equalities; cut (C = MAC); [assert_diffs; auto|].
  apply between_equality with A; finish.
  }
exists A; split; [|finish].
split; [intro; apply HNC2; ColR|].
split; [intro; apply HNC2; ColR|].
exists MAB; split; finish.
Qed.

Lemma tcp_os_b_sa_mab_mmac : forall A B C MAB MAC MBC SA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAC A MAC ->
  OS B SA MAB MMAC.
Proof.
intros A B C MAB MAC MBC SA MMAC HMAB HMAC HMBC HSA HNC HMMAC.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : B <> SA) by (intro; treat_equalities; Col).
apply one_side_transitivity with MAC;
[apply tcp_os_b_sa_mab_mac with A C MBC; auto|].
apply l9_17 with A; [apply one_side_symmetry|finish].
apply l9_17 with C; [|finish].
apply one_side_transitivity with MBC; [apply invert_one_side|];
apply out_one_side; [left; intro| |right; intro|]; try solve [apply HNC2; ColR];
repeat split; finish; intro; treat_equalities; Col.
Qed.

Lemma tcp_npars_mab_mmac_b_sa : forall A B C MAB MAC MBC SA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAC A MAC ->
  ~ Par_strict MAB MMAC B SA.
Proof.
intros A B C MAB MAC MBC SA MMAC HMAB HMAC HMBC HSA HNC1 HMMAC.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HP : Par_strict B MAC MAB MMAC)
  by (apply triangle_mid_par_strict with A; finish; intro; apply HNC2; ColR).
cut (~ Par B MAC B SA);
[intros HF ?; apply HF; apply par_trans with MAB MMAC; finish|].
clear HP; intros [[_ HF]|[HNE2 [HNE3 [_ HC]]]]; [apply HF; exists B; finish|].
assert (HOS : OS B SA MAB MAC)
  by (apply tcp_os_b_sa_mab_mac with A C MBC; auto).
apply (one_side_not_col124 _ _ _ _ HOS); Col.
Qed.

Lemma tcp_ncol_inplane_2_5 : forall A B C MAB MAC MBC SA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAC A MAC ->
  (exists Y, (Col MAB MMAC Y /\ MAB <> MMAC /\ MAB <> Y /\ MMAC<> Y) /\
             (Col SA B Y /\ SA <> B /\ SA <> Y /\ B <> Y)).
Proof.
intros A B C MAB MAC MBC SA MMAC HMAB HMAC HMBC HSA HNC HMMAC.
assert (HOS1 : OS MAB MMAC B SA)
  by (apply tcp_os_mab_mmac_b_sa with A C MAC MBC; auto).
assert (HOS2 : OS B SA MAB MMAC)
  by (apply tcp_os_b_sa_mab_mmac with A C MAC MBC; auto).
assert (HNP : ~ Par_strict MAB MMAC B SA)
  by (apply tcp_npars_mab_mmac_b_sa with A C MAC MBC; auto).
assert (HNC2 := one_side_not_col123 _ _ _ _ HOS1).
assert (HNC3 := one_side_not_col124 _ _ _ _ HOS1).
assert (HNC4 := one_side_not_col124 _ _ _ _ HOS2).
assert (HNC5 := one_side_not_col123 _ _ _ _ HOS2).
destruct (cop_npars__inter_exists MAB MMAC B SA) as [Y [HC1 HC2]]; finish.
exists Y; repeat split; Col; intro; treat_equalities; Col.
Qed.

Lemma tcp_os_mab_mmac_b_ssa : forall A B C MAB MAC MBC SA SSA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAC A MAC ->
  OS MAB MMAC B SSA.
Proof.
intros A B C MAB MAC MBC SA SSA MMAC HMAB HMAC HMBC HSA HSSA HNC HMMAC.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MAB MMAC A SA)
  by (apply tcp_ts_mab_mmac_a_sa with B C MAC MBC; auto).
assert (HNE1 : A <> MMAC) by (intro; treat_equalities; Col).
assert (HNE2 : C <> MMAC).
  {
  intro; treat_equalities; cut (C = MAC); [assert_diffs; auto|].
  apply between_equality with A; finish.
  }
exists A; split; [repeat split|apply l9_2, bet_ts__ts with SA];
[intro; apply HNC2; ColR..|exists MAB; finish|finish|].
apply outer_transitivity_between2 with MBC; finish.
intro; treat_equalities; Col.
Qed.

Lemma tcp_os_b_ssa_mab_mmac : forall A B C MAB MAC MBC SA SSA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAC A MAC ->
  OS B SSA MAB MMAC.
Proof.
intros A B C MAB MAC MBC SA SSA MMAC HMAB HMAC HMBC HSA HSSA HNC HMMAC.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HTS : TS MAB MAC A SSA)
  by (apply tcp_ts_mab_mac_a_ssa with B C MBC SA; auto).
assert (HNE1 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE2 : A <> SSA) by (assert_diffs; auto).
assert (HNE3 : B <> SA) by (intro; treat_equalities; Col).
apply one_side_transitivity with MAC;
[apply tcp_os_b_ssa_mab_mac with A C MBC SA; auto|].
apply l9_17 with A; [apply one_side_symmetry|finish].
apply l9_17 with C; [|finish].
apply one_side_transitivity with MBC; [apply invert_one_side|];
apply out_one_side; [left; intro| |right; intro|]; try solve [apply HNC2; ColR];
repeat split; finish; try solve [intro; treat_equalities; Col].
right; apply between_symmetry, outer_transitivity_between with SA; finish.
intro; treat_equalities; Col.
Qed.

Lemma tcp_npars_mab_mmac_b_ssa : forall A B C MAB MAC MBC SA SSA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAC A MAC ->
  ~ Par_strict MAB MMAC B SSA.
Proof.
intros A B C MAB MAC MBC SA SSA MMAC HMAB HMAC HMBC HSA HSSA HNC HMMAC.
assert (HNC2 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HP : Par_strict B MAC MAB MMAC)
  by (apply triangle_mid_par_strict with A; finish; intro; apply HNC2; ColR).
cut (~ Par B MAC B SSA);
[intros HF ?; apply HF; apply par_trans with MAB MMAC; finish|].
clear HP; intros [[_ HF]|[HNE2 [HNE3 [_ HC]]]]; [apply HF; exists B; finish|].
assert (HOS : OS B SSA MAB MAC)
  by (apply tcp_os_b_ssa_mab_mac with A C MBC SA; auto).
apply (one_side_not_col124 _ _ _ _ HOS); Col.
Qed.

Lemma tcp_ncol_inplane_2_6 : forall A B C MAB MAC MBC SA SSA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAC A MAC ->
  (exists Y, (Col MAB MMAC Y /\ MAB <> MMAC /\ MAB <> Y /\ MMAC<> Y) /\
             (Col SSA B Y /\ SSA <> B /\ SSA <> Y /\ B <> Y)).
Proof.
intros A B C MAB MAC MBC SA SSA MMAC HMAB HMAC HMBC HSA HSSA HNC HMMAC.
assert (HOS1 : OS MAB MMAC B SSA)
  by (apply tcp_os_mab_mmac_b_ssa with A C MAC MBC SA; auto).
assert (HOS2 : OS B SSA MAB MMAC)
  by (apply tcp_os_b_ssa_mab_mmac with A C MAC MBC SA; auto).
assert (HNP : ~ Par_strict MAB MMAC B SSA)
  by (apply tcp_npars_mab_mmac_b_ssa with A C MAC MBC SA; auto).
assert (HNC2 := one_side_not_col123 _ _ _ _ HOS1).
assert (HNC3 := one_side_not_col124 _ _ _ _ HOS1).
assert (HNC4 := one_side_not_col124 _ _ _ _ HOS2).
assert (HNC5 := one_side_not_col123 _ _ _ _ HOS2).
destruct (cop_npars__inter_exists MAB MMAC B SSA) as [Y [HC1 HC2]]; finish.
exists Y; repeat split; Col; intro; treat_equalities; Col.
Qed.

Lemma tcp_ncol_inplane_3_1 : forall A B C MAB MAC MBC SA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C ->
  (exists Y, (Col MAB MAC Y /\ MAB <> MAC /\ MAB <> Y /\ MAC<> Y) /\
             (Col SA C Y /\ SA <> C /\ SA <> Y /\ C <> Y)).
Proof.
intros A B C MAB MAC MBC SA HMAB HMAC HMBC HSA HNC.
destruct (tcp_ncol_inplane_2_1 A C B MAC MAB MBC SA) as [Y]; finish.
spliter; exists Y; repeat split; finish.
Qed.

Lemma tcp_ncol_inplane_3_2 : forall A B C MAB MAC MBC SA SSA,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  (exists Y, (Col MAB MAC Y /\ MAB <> MAC /\ MAB <> Y /\ MAC<> Y) /\
             (Col SSA C Y /\ SSA <> C /\ SSA <> Y /\ C <> Y)).
Proof.
intros A B C MAB MAC MBC SA SSA HMAB HMAC HMBC HSA HSSA HNC.
destruct (tcp_ncol_inplane_2_2 A C B MAC MAB MBC SA SSA) as [Y]; finish.
spliter; exists Y; repeat split; finish.
Qed.

Lemma tcp_ncol_inplane_3_3 : forall A B C MAB MAC MBC SA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAB A MAB ->
  (exists Y, (Col MMAB MAC Y /\ MMAB <> MAC /\ MMAB <> Y /\ MAC<> Y) /\
             (Col SA C Y /\ SA <> C /\ SA <> Y /\ C <> Y)).
Proof.
intros A B C MAB MAC MBC SA MMAB HMAB HMAC HMBC HSA HNC HMMAB.
destruct (tcp_ncol_inplane_2_5 A C B MAC MAB MBC SA MMAB) as [Y]; finish.
spliter; exists Y; repeat split; finish.
Qed.

Lemma tcp_ncol_inplane_3_4 : forall A B C MAB MAC MBC SA SSA MMAB,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAB A MAB ->
  (exists Y, (Col MMAB MAC Y /\ MMAB <> MAC /\ MMAB <> Y /\ MAC<> Y) /\
             (Col SSA C Y /\ SSA <> C /\ SSA <> Y /\ C <> Y)).
Proof.
intros A B C MAB MAC MBC SA SSA MMAB HMAB HMAC HMBC HSA HSSA HNC HMMAB.
destruct (tcp_ncol_inplane_2_6 A C B MAC MAB MBC SA SSA MMAB) as [Y]; finish.
spliter; exists Y; repeat split; finish.
Qed.

Lemma tcp_ncol_inplane_3_5 : forall A B C MAB MAC MBC SA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> ~ Col A B C -> Midpoint MMAC A MAC ->
  (exists Y, (Col MAB MMAC Y /\ MAB <> MMAC /\ MAB <> Y /\ MMAC<> Y) /\
             (Col SA C Y /\ SA <> C /\ SA <> Y /\ C <> Y)).
Proof.
intros A B C MAB MAC MBC SA MMAC HMAB HMAC HMBC HSA HNC HMMAC.
destruct (tcp_ncol_inplane_2_3 A C B MAC MAB MBC SA MMAC) as [Y]; finish.
spliter; exists Y; repeat split; finish.
Qed.

Lemma tcp_ncol_inplane_3_6 : forall A B C MAB MAC MBC SA SSA MMAC,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C ->
  Midpoint MBC SA A -> Midpoint SA MBC SSA -> ~ Col A B C ->
  Midpoint MMAC A MAC ->
  (exists Y, (Col MAB MMAC Y /\ MAB <> MMAC /\ MAB <> Y /\ MMAC<> Y) /\
             (Col SSA C Y /\ SSA <> C /\ SSA <> Y /\ C <> Y)).
Proof.
intros A B C MAB MAC MBC SA SSA MMAC HMAB HMAC HMBC HSA HSSA HNC HMMAC.
destruct (tcp_ncol_inplane_2_4 A C B MAC MAB MBC SA SSA MMAC) as [Y]; finish.
spliter; exists Y; repeat split; finish.
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
intros A B C MAB MAC MBC SA MMAB MMAC X P HMAB HMAC HMBC MSA HNC1 HMMAB HMMAC.
intros HNC2 HC1 HC2 HCop HBet1 HNE1 HCol1 HNC4 HNC5 HNC6 HCol2.
assert (HNC3 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HOS1 : OS A B MAC P).
  {
  apply one_side_transitivity with MBC; [apply l12_6|];
  [apply triangle_mid_par_strict_cong_simp with C; finish|].
  apply out_one_side; [left; intro; apply HNC3; ColR|].
  repeat split; [intro; treat_equalities; Col..|left].
  apply between_exchange4 with SA; finish.
  }
destruct (symmetric_point_construction P MAB) as [SP HSP].
assert (HNE2 : A <> SA) by (intro; treat_equalities; Col).
assert (HNE3 : MAB <> P) by (intro; treat_equalities; apply HNC4; ColR).
destruct (symmetric_point_construction MAC MMAB) as [SMAC HSMAC].
assert (HP1 : Per SP MAB MMAB).
  {
  apply perp_per_2, perp_col2_bis with A B; [|ColR..|assert_diffs; auto].
  apply perp_col2 with X MAB; [|assert_diffs; auto|ColR..].
  apply perp_bisect_perp, cong_mid_perp_bisect; finish;
  intro; treat_equalities; Col.
  }
assert (HCongA : CongA A MAB C MAB MMAB SMAC).
  {
  apply conga_trans with A MMAB MAC;
  [|assert_diffs; apply l11_14; finish].
  apply conga_comm, par_preserves_conga_os; finish;
  [apply par_left_comm, triangle_mid_par with A; finish|..];
  [intro; treat_equalities; Col|assert_diffs; auto|].
  apply out_one_side_1 with A; [intro; apply HNC3; ColR|Col|].
  assert_diffs; repeat split; finish.
  }
assert (HLeA : LeA A MAB C A MAB MBC).
  {
  apply inangle__lea; repeat split; [intro; treat_equalities; Col..|].
  destruct (inner_pasch A C B MAB MBC) as [I []]; finish.
  exists I; split; [finish|right].
  apply bet_out_1; [|finish].
  intro; treat_equalities; apply HNC3; ColR.
  }
assert (HNE4 : MBC <> P).
  {
  intro; cut (MBC = SA); [intro; treat_equalities; Col|].
  treat_equalities; apply between_equality with A; finish.
  }
assert (HAcute1 : Acute A MAB MBC).
  {
  exists A, MAB, P; split; [apply col_col_per_per with MMAB SP; finish|];
  [intro; treat_equalities; Col..|].
  apply inangle__lta; [intro; apply HNC3; ColR|].
  repeat split; [intro; treat_equalities; Col..|].
  exists MBC; split; [|right; apply out_trivial; assert_diffs; auto].
  apply between_exchange4 with SA; finish.
  }
assert (HAcute2 : Acute MAB MMAB SMAC).
  {
  apply acute_conga__acute with A MAB C; [|finish].
  apply acute_lea_acute with A MAB MBC; finish.
  }
assert (HOS2 : OS MAB MMAB SP SMAC).
  {
  apply col2_os__os with A B; [assert_diffs; auto|ColR..|].
  exists P; split; [split; [|split]|];
  [intro; apply HNC3; ColR..|exists MAB; finish|].
  apply l9_2, l9_8_2 with MAC; [|finish].
  split; [|split]; [intro; apply HNC3; ColR..|].
  exists MMAB; split; [ColR|finish].
  }
assert (HX : euclid_s_parallel_postulate)
  by (apply postulates_in_euclidean_context; simpl; tauto).
destruct (ex_suma SP MAB MMAB MAB MMAB SMAC) as [E [F [G HSumA]]];
[intro; treat_equalities; Col..|].
destruct (HX SP MAB MMAB SMAC E F G) as [I [HOut1 HOut2]]; auto;
[apply acute_per__sams|
 apply acute_per_suma__nbet with SP MAB MMAB MAB MMAB SMAC|];
finish; [intro; treat_equalities; Col..|clear E F G HSumA].
cut (X = I); [intro; treat_equalities|];
[|apply l6_21 with MMAB SMAC MAB SP; Col; [| |ColR..]];
[|intro; apply HNC3; ColR|intro; treat_equalities; Col].
cut (Out MAB X P); [intro HF; apply (l6_7 _ _ _ _ HOut1) in HF|];
[apply l6_4_1 in HF; destruct HF as [_ HF]; apply HF; finish|].
assert (HTS1 : TS MAB P B C).
  {
  apply bet_ts__ts with MBC; [|finish].
  apply l9_2, l9_8_2 with A; [|apply invert_one_side, out_one_side];
  [|left; intro; apply HNC3; ColR|repeat split; [assert_diffs; auto..|]];
  [|right; apply between_exchange2 with SA; finish].
  split; [|split]; [intro; apply HNC3; ColR..|exists MAB; finish].
  }
destruct (l8_18_existence MAB X C) as [PC [HCol3 HPC]];
[destruct HTS1 as [_ [HF _]]; intro; apply HF; ColR|].
assert (HNE5 : MAB <> PC).
  {
  intro; treat_equalities; cut (Par A MAB C MAB); [intro HF|];
  [apply HNC3; apply (not_strict_par1 A MAB C MAB MAB) in HF; ColR|].
  apply l12_9 with MAB X; Cop; Perp; [CopR|].
  apply perp_col4 with MMAB MAB MAB SP; finish; [assert_diffs; auto..|].
  apply per_perp; assert_diffs; finish.
  }
assert (HP2 : Per C PC MAB)
  by (apply perp_per_1, perp_col4 with PC C MAB X; finish; assert_diffs; auto).
destruct (ex_suma MAB PC C PC C A) as [E [F [G HSumA]]];
[assert_diffs; auto..|].
assert (HPS1 : Par_strict MAB A PC C).
  {
  apply par_not_col_strict with C; Col; [|intro; apply HNC3; ColR].
  apply l12_9 with MAB X; Cop; Perp; [CopR|].
  apply perp_col4 with MMAB MAB MAB SP; finish; [assert_diffs; auto..|].
  apply per_perp; assert_diffs; finish.
  }
assert (HPS2 : Par_strict A B C SA)
  by (apply par_strict_right_comm, midpoint_par_strict with MBC; finish).
assert (HCol4 : Col C SA PC).
  {
  destruct (parallel_uniqueness A B C SA C PC C); finish.
  assert_diffs; apply par_col4__par with A MAB C PC; finish.
  }
assert (HOS4 : OS MAB P A C).
  {
  exists B; split; [|finish].
  repeat split; [intro; apply HNC3; ColR..|exists MAB; finish].
  }
assert (HBet2 : Bet MAB PC P).
  {
  elim (eq_dec_points P PC); [intro; treat_equalities; finish|intro HNE7].
  apply col_two_sides_bet with C; [ColR|].
  apply l9_8_2 with A; [|finish].
  repeat split; [intro; apply HNC3; try ColR| |exists SA; finish].
  intro; apply HNE7, l6_21 with C PC MAB P; Col; [|ColR].
  apply par_strict_not_col_3 in HPS1; Col.
  }
assert (HBet3 : Bet C SA PC).
  {
  elim (eq_dec_points SA PC); [intro; treat_equalities; finish|intro HNE7].
  apply col_two_sides_bet with A; [Col|].
  apply l9_2, l9_8_2 with B;
  [repeat split; [intro; apply HNC3; ColR..|exists MBC; finish]|].
  apply one_side_transitivity with MAB;
  [apply invert_one_side, out_one_side; [left; intro; apply HNC3; ColR|]|];
  [assert_diffs; repeat split; finish|].
  apply out_one_side_1 with P; [intro; apply HNC3; ColR|Col|].
  assert_diffs; repeat split; finish.
  intro; treat_equalities; apply HNC3; ColR.
  }
assert (HPara : Parallelogram A MAB MBC MAC).
  {
  destruct (triangle_mid_par_cong A B C MBC MAC MAB);
  [assert_diffs; finish..|spliter].
  apply par_par_cong_cong_parallelogram; [assert_diffs; auto|Cong..| |];
  [apply par_col4__par with MAB MBC A C|
   apply par_col4__par with A B MBC MAC]; assert_diffs; finish.
  }
assert (HAcute3 : Acute PC C A).
  {
  apply acute_conga__acute with A MAB MBC; [finish|].
  assert (HOS5 : OS A MAC MBC PC).
    {
    apply one_side_transitivity with SA; [apply out_one_side|];
    [left; intro; apply HNC3; ColR|assert_diffs; repeat split; finish|].
    apply out_one_side_1 with C; [intro; apply HNC3; ColR|Col|].
    assert_diffs; repeat split; finish.
    }
  apply conga_trans with A MAC MBC; [apply conga_right_comm|];
  [apply plg_conga in HPara; [spliter|assert_diffs; repeat split]; auto|].
  apply conga_left_comm, l12_22; [assert_diffs; repeat split; finish|auto|].
  apply par_trans with A MAB; Par.
  apply plg_par in HPara; [spliter; finish|assert_diffs; auto..].
  }
destruct (HX MAB PC C A E F G) as [I [HOut3 HOut4]]; finish;
[apply acute_per__sams|
 apply acute_per_suma__nbet with MAB PC C PC C A|]; finish;
[assert_diffs; auto..|clear E F G HSumA].
assert (HNE6 : MAC <> I) by (intro; treat_equalities; apply HNC3; ColR).
destruct (l10_15 I MAC MAC P) as [J HJ]; [Col|intro; apply HNC3; ColR|].
destruct HJ as [HJ HOS3].
assert (HBet4 : Bet I A C).
  {
  apply (l9_19 _ _ _ _ I) in HOS4; [|ColR..].
  destruct HOS4 as [HOut7 _].
  cut (Bet C A I); [|apply out2__bet]; finish.
  }
assert (HTS2 : TS MAB A I P).
  {
  apply l9_2, l9_8_2 with PC; [|apply out_one_side];
  [|right; intro; apply HNC3; ColR|assert_diffs; repeat split; finish].
  apply l9_8_2 with C; [|finish].
  apply (l9_19 _ _ _ _ I) in HOS4; [|ColR..].
  destruct HOS4 as [HOut7 _].
  repeat split; [intro; apply HNC3; ColR..|exists A; finish].
  }
assert (HBet5 : Bet I MAB P)
  by (apply col_two_sides_bet with A; [ColR|auto]).
assert (HAcute4 : Acute MAC I P).
  {
  apply acute_out2__acute with C PC; [apply out_bet_out_2 with A|..];
  [..|apply l6_6, out_bet_out_2 with MAB|]; finish; [apply bet_out..|];
  [assert_diffs; finish..|destruct (l11_43 PC C I)];
  [|assert_diffs|left|apply acute_sym]; auto;
  [intro; assert_diffs; apply HNC3; ColR|].
  apply perp_per_1, perp_col4 with PC C MAB X; finish;
  [intro; treat_equalities; apply HNC3..|]; ColR.
  }
destruct (ex_suma J MAC I MAC I P) as [E [F [G HSumA]]];
[assert_diffs; auto..|].
destruct (HX J MAC I P E F G) as [Y [HOut5 HOut6]]; auto;
[|apply acute_per__sams|
 apply acute_per_suma__nbet with J MAC I MAC I P|]; finish;
[assert_diffs; auto..|clear E F G HSumA].
assert (HNE7 : MAB <> I).
  {
  intro; treat_equalities; cut (A = MAC); [intro; assert_diffs; auto|].
  apply l6_21 with A B C MAC; Col; [assert_diffs; auto|ColR].
  }
repeat split; [assert_diffs; auto..|apply l5_2 with I; finish].
assert (HBet6 : Bet I MAB Y).
  {
  assert (HTS3 : TS MAC MBC MAB P).
    {
    apply l9_8_2 with A; [|apply ncol134_plg__pars1234 in HPara];
    [|finish|intro; apply HNC3; ColR].
    repeat split; [intro; apply HNC3; ColR..|].
    exists MBC; split; [Col|apply between_exchange4 with SA; finish].
    }
  destruct HTS3 as [_ [_ [K [HCol5 HK]]]].
  assert (HBet6 : Bet I MAB K)
    by (apply between_inner_transitivity with P; finish).
  assert (HNE8 : MAB <> K) by (intro; treat_equalities; apply HNC3; ColR).
  cut (Bet I K Y); [intro; apply between_exchange4 with K; finish|].
  apply col_two_sides_bet with MAC; [ColR|].
  apply invert_two_sides, lta_os__ts; [intro; apply HNC3; ColR|..];
  [|apply invert_one_side, one_side_transitivity with P];
  [|apply out_one_side..]; finish; [|right|left|];
  [|intro; apply HNC3; ColR..|repeat split; [assert_diffs; auto..|right]];
  [|apply outer_transitivity_between2 with MAB; finish].
  apply acute_per__lta; [..|apply perp_per_1, perp_col4 with MAC I MAC J];
  finish; [|assert_diffs; auto..].
  assert (HOut7 : Out MAC I A).
    {
    repeat split; [assert_diffs; auto..|right].
    apply between_exchange3 with C; finish.
    }
  assert (HOut8 : Out MAC K MBC).
    {
    repeat split; [|assert_diffs; auto|right];
    [intro; treat_equalities; apply HNC3; ColR|].
    apply col_two_sides_bet with A; [ColR|].
    apply l9_2, l9_8_2 with MAB; [|apply out_one_side_1 with P];
    [..|intro; apply HNC3; ColR|ColR|repeat split];
    [|assert_diffs; auto|intro; treat_equalities; apply HNC3; ColR|finish].
    apply ncol124_plg__plgs in HPara; [|intro; apply HNC3; ColR].
    apply plgs_two_sides in HPara; spliter; finish.
    }
  apply acute_out2__acute with A MBC; [finish..|].
  apply acute_conga__acute with A MAB MBC; [finish|].
  apply plg_conga in HPara; [spliter; finish|].
  assert_diffs; repeat split; auto.
  }
cut (X = Y); [intro; treat_equalities; finish|].
apply l6_21 with MAB P MAC J; Col;
[intro; apply HNC3; ColR|assert_diffs; auto|ColR|].
apply cong_cop2_perp_bisect_col with A C; [Cop|CopR|Cong|].
apply perp_mid_perp_bisect; [finish|].
apply perp_col4 with MAC J I MAC; finish; [assert_diffs; auto..| |]; ColR.
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
  ~ Col MAB SA X /\ ~ Col MAC SA X /\ ~ Par_strict MAB MAC SA X \/
  ~ Col MAB SSA X /\ ~ Col MAC SSA X /\ ~ Par_strict MAB MAC SSA X \/
  ~ Col MMAB SA X /\ ~ Col MAC SA X /\
  ~ Par_strict MMAB MAC SA X /\ ~ Col MMAB MAC X \/
  ~ Col MMAB SSA X /\ ~ Col MAC SSA X /\
  ~ Par_strict MMAB MAC SSA X /\ ~ Col MMAB MAC X \/
  ~ Col MAB SA X /\ ~ Col MMAC SA X /\
  ~ Par_strict MAB MMAC SA X /\ ~ Col MAB MMAC X \/
  ~ Col MAB SSA X /\ ~ Col MMAC SSA X /\
  ~ Par_strict MAB MMAC SSA X /\ ~ Col MAB MMAC X.
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
[intro HP; destruct HNEE|clear dependent SSA; intros P HBet HNE1];
[destruct (HP SA) as [|[|]]|destruct (HP SSA) as [|[|]]|]; finish; auto 7.
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

Lemma tcp_ncol_inplane_4 : forall A1 A2 B1 B2,
  Coplanar A1 A2 B1 B2 -> ~ Par_strict A1 A2 B1 B2 -> A1 <> A2 ->
  ~ Col A1 B1 B2 -> ~ Col A2 B1 B2 -> ~ Col B1 A1 A2 -> ~ Col B2 A1 A2 ->
  exists Y, (Col A1 A2 Y /\ A1 <> A2 /\ A1 <> Y /\ A2 <> Y) /\
            (Col B1 B2 Y /\ B1 <> B2 /\ B1 <> Y /\ B2 <> Y).
Proof.
intros A1 A2 B1 B2 HCop HNP HNE HNC1 HNC2 HNC3 HNC4.
destruct (cop_npars__inter_exists A1 A2 B1 B2) as [Y []]; auto.
exists Y; repeat split; Col; intro; treat_equalities; Col.
Qed.

Lemma tcp_ncol_inplane_aux : forall A B C MAB MAC MBC X,
  Midpoint MAB A B -> Midpoint MAC A C -> Midpoint MBC B C -> ~ Col A B C ->
  ~ Col MAB MAC X -> Cong A X B X -> Cong A X C X -> Coplanar A B C X ->
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
intros A B C MAB MAC MBC X HMAB HMAC HMBC HNC1 HNC2 HC1 HC2 HCop.
destruct (symmetric_point_construction A MBC) as [SA HSA].
destruct (symmetric_point_construction MBC SA) as [SSA HSSA].
destruct (midpoint_existence A MAB) as [MMAB HMMAB].
destruct (midpoint_existence A MAC) as [MMAC HMMAC].
assert (HE := tcp_ncol_ndc_choice A B C MAB MAC MBC SA SSA MMAB MMAC X).
assert (HNC3 : ~ Col MAB MAC MBC)
  by (apply tcp_ncol_midpoints with A B C; auto).
assert (HNC4 : ~ Col MAB MAC SA).
  {
  cut (OS MAB MAC B SA); [intro HOS; apply one_side_not_col124 in HOS; Col|].
  apply (tcp_os_mab_mac_b_sa A B C MAB MAC MBC SA); finish.
  }
assert (HNC5 : ~ Col MAB MAC SSA).
  {
  cut (OS MAB MAC B SSA); [intro HOS; apply one_side_not_col124 in HOS; Col|].
  apply (tcp_os_mab_mac_b_ssa A B C MAB MAC MBC SA SSA); finish.
  }
assert (HNC6 : ~ Col MMAB MAC SA).
  {
  cut (OS MMAB MAC B SA); [intro HOS; apply one_side_not_col124 in HOS; Col|].
  apply (tcp_os_mmab_mac_b_sa A B C MAB MAC MBC SA); finish.
  }
assert (HNC7 : ~ Col MMAB MAC SSA).
  {
  cut (OS MMAB MAC B SSA); [intro HOS; apply one_side_not_col124 in HOS; Col|].
  apply (tcp_os_mmab_mac_b_ssa A B C MAB MAC MBC SA SSA); finish.
  }
assert (HNC8 : ~ Col MAB MMAC SA).
  {
  cut (OS MAB MMAC B SA); [intro HOS; apply one_side_not_col124 in HOS; Col|].
  apply (tcp_os_mab_mmac_b_sa A B C MAB MAC MBC SA); finish.
  }
assert (HNC9 : ~ Col MAB MMAC SSA).
  {
  cut (OS MAB MMAC B SSA); [intro HOS; apply one_side_not_col124 in HOS; Col|].
  apply (tcp_os_mab_mmac_b_ssa A B C MAB MAC MBC SA SSA); finish.
  }
assert (HPS : Par_strict MAB MBC MAC A /\ Par_strict MAB MBC MAC A /\
             Par_strict MAB MAC MBC B /\ Par_strict MAB MAC MBC C /\
             Par_strict MAC MBC MAB A /\ Par_strict MAC MBC MAB B).
  {
  split; [|split; [|split; [|split; [|split]]]];
  eapply par_strict_col2_par_strict; try apply par_strict_symmetry;
  try solve [apply triangle_mid_par_strict with A; eCol; finish];
  try solve [apply triangle_mid_par_strict with B; eCol; finish];
  try solve [apply triangle_mid_par_strict with C; eCol; finish];
  finish; intro; treat_equalities; Col.
  }
assert (HCS : Coplanar MAB MAC MBC A /\ Coplanar MAB MAC MBC B /\
              Coplanar MAB MAC MBC C).
  {
  spliter; repeat split; [apply coplanar_perm_2|..];
  apply pars__coplanar; auto.
  }
assert (HCMMAB : Coplanar MAB MAC MBC MMAB).
  {
  spliter; apply coplanar_perm_12, col_cop__cop with A; finish.
  intro; treat_equalities; Col.
  }
assert (HCMMAC : Coplanar MAB MAC MBC MMAC).
  {
  spliter; apply coplanar_perm_2, col_cop__cop with A; finish.
  intro; treat_equalities; Col.
  }
assert (HCSA : Coplanar MAB MAC MBC SA)
  by (spliter; apply col_cop__cop with A; Col; intro; treat_equalities; Col).
assert (HCSSA : Coplanar MAB MAC MBC SSA).
  {
  spliter; apply col_cop__cop with A; Col; [|ColR].
  intro; treat_equalities; Col.
  }
destruct (tcp_ncol_inplane_1_1 A B C MAB MAC MBC SA) as [Y11 HY11]; finish.
destruct (tcp_ncol_inplane_2_1 A B C MAB MAC MBC SA) as [Y21 HY21]; finish.
destruct (tcp_ncol_inplane_3_1 A B C MAB MAC MBC SA) as [Y31 HY31]; finish.
destruct (tcp_ncol_inplane_1_2 A B C MAB MAC MBC SA SSA) as [Y12 HY12]; finish.
destruct (tcp_ncol_inplane_2_2 A B C MAB MAC MBC SA SSA) as [Y22 HY22]; finish.
destruct (tcp_ncol_inplane_3_2 A B C MAB MAC MBC SA SSA) as [Y32 HY32]; finish.
destruct (tcp_ncol_inplane_1_3 A B C MAB MAC MBC SA MMAB) as [Y13 HY13]; finish.
destruct (tcp_ncol_inplane_2_3 A B C MAB MAC MBC SA MMAB) as [Y23 HY23]; finish.
destruct (tcp_ncol_inplane_3_3 A B C MAB MAC MBC SA MMAB) as [Y33 HY33]; finish.
destruct (tcp_ncol_inplane_1_4 A B C MAB MAC MBC SA SSA MMAB) as [Y14 HY14]; finish.
destruct (tcp_ncol_inplane_2_4 A B C MAB MAC MBC SA SSA MMAB) as [Y24 HY24]; finish.
destruct (tcp_ncol_inplane_3_4 A B C MAB MAC MBC SA SSA MMAB) as [Y34 HY34]; finish.
destruct (tcp_ncol_inplane_1_5 A B C MAB MAC MBC SA MMAC) as [Y15 HY15]; finish.
destruct (tcp_ncol_inplane_2_5 A B C MAB MAC MBC SA MMAC) as [Y25 HY25]; finish.
destruct (tcp_ncol_inplane_3_5 A B C MAB MAC MBC SA MMAC) as [Y35 HY35]; finish.
destruct (tcp_ncol_inplane_1_6 A B C MAB MAC MBC SA SSA MMAC) as [Y16 HY16]; finish.
destruct (tcp_ncol_inplane_2_6 A B C MAB MAC MBC SA SSA MMAC) as [Y26 HY26]; finish.
destruct (tcp_ncol_inplane_3_6 A B C MAB MAC MBC SA SSA MMAC) as [Y36 HY36]; finish.
destruct HE as [HE|[HE|[HE|[HE|[HE|HE]]]]]; finish;
[exists MAB, MAC, SA|exists MAB, MAC, SSA|exists MMAB, MAC, SA|
 exists MMAB, MAC, SSA|exists MAB, MMAC, SA|exists MAB, MMAC, SSA];
repeat split; Col;
 [exists Y11|exists Y21|exists Y31| |
  exists Y12|exists Y22|exists Y32| |
  exists Y13|exists Y23|exists Y33| |
  exists Y14|exists Y24|exists Y34| |
  exists Y15|exists Y25|exists Y35| |
  exists Y16|exists Y26|exists Y36|]; try solve [spliter; auto];
clear Y11 HY11 Y21 HY21 Y31 HY31 Y12 HY12 Y22 HY22 Y32 HY32;
clear Y13 HY13 Y23 HY23 Y33 HY33 Y14 HY14 Y24 HY24 Y34 HY34;
clear Y15 HY15 Y25 HY25 Y35 HY35 Y16 HY16 Y26 HY26 Y36 HY36;
apply tcp_ncol_inplane_4; spliter; Col; try solve [assert_diffs; auto];
apply coplanar_pseudo_trans with MAB MAC MBC; Cop; Col;
apply coplanar_pseudo_trans with A B C; Cop.
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
