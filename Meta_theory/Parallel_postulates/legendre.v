Require Export GeoCoq.Meta_theory.Parallel_postulates.angle_archimedes.

Section Legendre.

Context `{T2D:Tarski_2D}.

(** The difference between a flat angle and the sum of the angles of the triangle ABC.
    It is a non-oriented angle, so we can't discriminate between positive and negative difference *)
Definition Defect A B C D E F := exists G H I J K L,
  TriSumA A B C G H I /\ Bet J K L /\ SumA G H I D E F J K L.


Lemma defect_distincts : forall A B C D E F, Defect A B C D E F ->
  A <> B /\ B <> C /\ A <> C /\ D <> E /\ E <> F.
Proof.
  intros A B C D E F HDef.
  destruct HDef as [G [H [I [J [K [L [[M [N [O [HSuma HSuma1]]]] [HBet HSuma2]]]]]]]].
  suma.assert_diffs; repeat split; auto.
Qed.

Lemma ex_defect : forall A B C, A <> B -> B <> C -> A <> C -> exists D E F, Defect A B C D E F.
Proof.
  intros A B C HAB HBC HAC.
  destruct (ex_trisuma A B C) as [G [H [I HTri]]]; auto.
  destruct (segment_construction G H G H) as [G' [HBet HCong]].
  assert (Hd := trisuma_distincts A B C G H I HTri); spliter; assert_diffs.
  exists I; exists H; exists G'; exists G; exists H; exists I; exists G; exists H; exists G'.
  repeat split; auto.
  apply inangle__suma.
  repeat split; auto.
  exists H; auto.
Qed.

Lemma conga_defect__defect : forall A B C D E F D' E' F', Defect A B C D E F -> CongA D E F D' E' F' ->
  Defect A B C D' E' F'.
Proof.
  intros A B C D E F D' E' F' HDef HConga.
  destruct HDef as [G [H [I [J [K [L [HTri [HBet HSuma]]]]]]]].
  exists G; exists H; exists I; exists J; exists K; exists L; repeat split; trivial.
  suma.assert_diffs; apply (conga3_suma__suma G H I D E F J K L); CongA.
Qed.

Lemma defect2__conga : forall A B C D E F D' E' F', Defect A B C D E F -> Defect A B C D' E' F' ->
  CongA D E F D' E' F'.
Proof.
  intros A B C D E F D' E' F' HDef HDef'.
  destruct HDef as [G [H [I [J [K [L [HTri [HBet HSuma]]]]]]]].
  destruct HDef' as [G' [H' [I' [J' [K' [L' [HTri' [HBet' HSuma']]]]]]]].
  suma.assert_diffs.
  apply (conga_line J K L) in HBet'; auto.
  apply (trisuma2__conga A B C G H I) in HTri'; trivial.
  apply (conga3_suma__suma _ _ _ _ _ _ _ _ _ G H I D' E' F' J K L) in HSuma'; CongA.
  clear dependent G'; clear dependent H'; clear dependent J'; clear dependent K'; clear I' L'.
  apply isi2_suma2__conga456 with G H I J K L; trivial; apply bet_suma__isi with J K L; trivial.
Qed.

Lemma defect_perm_231 : forall A B C D E F, Defect A B C D E F -> Defect  B C A D E F.
Proof.
  intros A B C D E F HDef.
  destruct HDef as [G [H [I [J [K [L [HTri [HBet HSuma]]]]]]]].
  exists G; exists H; exists I; exists J; exists K; exists L; repeat split; trivial.
  apply trisuma_perm_231, HTri.
Qed.

Lemma defect_perm_312 : forall A B C D E F, Defect A B C D E F -> Defect C A B D E F.
Proof.
  intros.
  do 2 apply defect_perm_231; trivial.
Qed.

Lemma defect_perm_321 : forall A B C D E F, Defect A B C D E F -> Defect C B A D E F.
Proof.
  intros A B C D E F HDef.
  destruct HDef as [G [H [I [J [K [L [HTri [HBet HSuma]]]]]]]].
  exists G; exists H; exists I; exists J; exists K; exists L; repeat split; trivial.
  apply trisuma_perm_321, HTri.
Qed.

Lemma defect_perm_213 : forall A B C D E F, Defect A B C D E F -> Defect B A C D E F.
Proof.
  intros.
  apply defect_perm_321, defect_perm_312; trivial.
Qed.

Lemma defect_perm_132 : forall A B C D E F, Defect A B C D E F -> Defect A C B D E F.
Proof.
  intros.
  apply defect_perm_321, defect_perm_231; trivial.
Qed.

Lemma conga3_defect__defect : forall A B C D E F A' B' C', Defect A B C D E F ->
  CongA A B C A' B' C' -> CongA B C A B' C' A' -> CongA C A B C' A' B' ->
  Defect A' B' C' D E F.
Proof.
  intros A B C D E F A' B' C' HDef HCongaB HCongaC HCongaA.
  destruct HDef as [G [H [I [J [K [L [HTri [HBet HSuma]]]]]]]].
  exists G; exists H; exists I; exists J; exists K; exists L; repeat split; trivial.
  apply (conga3_trisuma__trisuma A B C); trivial.
Qed.

Lemma col_defect__out : forall A B C D E F, Col A B C -> Defect A B C D E F -> Out E D F.
Proof.
  intros A B C D E F HCol HDef.
  destruct HDef as [G [H [I [J [K [L [HTri [HBet HSuma]]]]]]]].
  suma.assert_diffs.
  apply (isi_suma__out546 G H I).
  - apply (conga3_suma__suma G H I D E F J K L); CongA.
    apply conga_line; trivial.
    apply (col_trisuma__bet A B C); Col.
  - apply bet_suma__isi with J K L; trivial.
Qed.

Lemma rah_defect__out : hypothesis_of_right_saccheri_quadrilaterals ->
  forall A B C D E F, Defect A B C D E F -> Out E D F.
Proof.
  intros rah A B C D E F HDef.
  destruct HDef as [G [H [I [J [K [L [HTri [HBet HSuma]]]]]]]].
  suma.assert_diffs.
  apply (isi_suma__out546 G H I).
  - apply (conga3_suma__suma G H I D E F J K L); CongA.
    apply conga_line; trivial.
    apply (t22_14__bet rah A B C), HTri.
  - apply bet_suma__isi with J K L; trivial.
Qed.

Lemma defect_ncol_out__rah : forall A B C D E F, ~ Col A B C -> Defect A B C D E F ->
  Out E D F -> hypothesis_of_right_saccheri_quadrilaterals.
Proof.
  intros A B C D E F HNCol HDef HOut.
  destruct HDef as [G [H [I [J [K [L [HTri [HBet HSuma]]]]]]]].
  apply (t22_14__rah A B C G H I); trivial.
  apply (bet_conga_bet J K L); trivial.
  apply conga_sym, out546_suma__conga with D E F; trivial.
Qed.

Lemma noah_suma__isi : ~ hypothesis_of_obtuse_saccheri_quadrilaterals -> forall A B C D E F,
  SumA A B C B C A D E F -> Isi D E F C A B.
Proof.
  intros noah A B C D E F HSuma.
  suma.assert_diffs.
  destruct (ex_suma D E F C A B) as [G [H [I HSuma1]]]; auto.
  elim (Col_dec A B C).
  { intro HCol.
    apply bet_suma__isi with G H I; trivial.
    apply (col_trisuma__bet A B C); trivial.
    exists D; exists E; exists F; auto.
  }
  intro HNCol.
  destruct saccheri_s_three_hypotheses as [aah|[rah|oah]]; [| |contradiction].
    destruct (t22_14__isi_nbet aah B C A D E F G H I); Col.
  apply bet_suma__isi with G H I; trivial.
  apply (t22_14__bet rah A B C).
  exists D; exists E; exists F; auto.
Qed.

(** Additivity of the defect : if C1 is between A and C, the defect of ABC is
    the sum of the defects of AC1C and BC1C.
    In this proof, we have to exclude the semi-elliptical case so that the sums of angles behave. *)
Lemma t22_16_1 : ~ hypothesis_of_obtuse_saccheri_quadrilaterals -> forall A B C C1 D E F G H I K L M,
  Bet A C1 C -> Defect A B C1 D E F -> Defect B C1 C G H I -> SumA D E F G H I K L M ->
  Isi D E F G H I /\ Defect A B C K L M.
Proof.
  intros noah A B C C1 D E F G H I K L M HBet HDefA HDefC HSuma.
  assert (HDA := defect_distincts A B C1 D E F HDefA).
  assert (HDC := defect_distincts B C1 C G H I HDefC).
  spliter; clean.
  apply defect_perm_321 in HDefA.
  destruct HDefA as [P [Q [R [S [T [U [HTri [HBet' HSuma']]]]]]]].
  assert (HSuma1 : SumA P Q R D E F A C1 C).
  { suma.assert_diffs; apply (conga3_suma__suma P Q R D E F S T U); try (apply conga_refl); auto.
    apply conga_line; auto.
  }
  clear dependent S; clear T U.
  destruct HTri as [S [T [U [HSuma2 HSuma3]]]].
  assert (HInter : SumA S T U D E F B C1 C /\ Isi S T U D E F).
  { suma.assert_diffs.
    destruct (ex_suma S T U D E F) as [B' [C1' [C' HSuma']]]; auto.
    assert (HSuma4 : SumA B C1 C A C1 B A C1 C) by (apply suma_sym, inangle__suma, in_angle_line; auto).
    destruct (ex_suma A C1 B D E F) as [V [W [X HSuma5]]]; auto.
    assert (HIsi : Isi P Q R D E F) by (apply bet_suma__isi with A C1 C; trivial).
    assert (HIsi1 : Isi S T U A C1 B) by (apply (noah_suma__isi noah), HSuma2).
    assert (HIsi2 : Isi A C1 B D E F).
    { apply isi_lea2__isi with P Q R D E F; Lea.
      apply (isi_suma__lea456789 S T U); trivial.
    }
    assert (HSuma6 : SumA S T U V W X A C1 C) by (apply suma_assoc_1 with A C1 B D E F P Q R; trivial).
    assert (HIsi3 : Isi S T U D E F).
      apply isi_lea2__isi with P Q R D E F; Lea; apply isi_suma__lea123789 with A C1 B; SumA.
    assert (HSuma7 : SumA B' C1' C' A C1 B A C1 C) by (apply suma_assoc_2 with S T U D E F V W X; SumA).
    split; trivial.
    apply (conga3_suma__suma S T U D E F B' C1' C'); try (apply conga_refl); auto.
    apply isi2_suma2__conga123 with A C1 B A C1 C; trivial; apply bet_suma__isi with A C1 C; trivial.
  }
  clear dependent P; clear Q R.

  destruct HInter as [HSuma3 HIsi3].
  apply defect_perm_231 in HDefC.
  destruct HDefC as [P [Q [R [V [W [X [HTri1 [HBet1 HSuma0]]]]]]]].
  assert (HSuma1 : SumA P Q R G H I A C1 C).
  { suma.assert_diffs; apply (conga3_suma__suma P Q R G H I V W X); try (apply conga_refl); auto.
    apply conga_line; auto.
  }
  clear dependent V; clear W X.
  destruct HTri1 as [V [W [X [HSuma4 HSuma5]]]].
  assert (HIsi1 : Isi P Q R G H I) by (apply bet_suma__isi with A C1 C; trivial).
  assert (HIsi5 : Isi V W X B C1 C) by (apply (noah_suma__isi noah), HSuma4).
  assert (HIsi : Isi D E F G H I).
  { apply isi_lea2__isi with P Q R G H I; Lea.
    apply lea_trans with B C1 C.
      apply (isi_suma__lea456789 S T U); trivial.
    apply (isi_suma__lea456789 V W X); trivial.
  }
  split; trivial.

  suma.assert_diffs.
  destruct (ex_suma V W X S T U) as [A' [B' [C' HSuma6]]]; auto.
  assert (HIsi6 : Isi V W X S T U).
  { apply isi_lea2__isi with V W X B C1 C; Lea.
    apply isi_suma__lea123789 with D E F; trivial.
  }
  assert (HSuma7 : SumA A' B' C' D E F P Q R) by (apply suma_assoc_2 with V W X S T U B C1 C; trivial).
  assert (HSuma8 : SumA A' B' C' K L M A C1 C).
  { apply suma_assoc_1 with D E F G H I P Q R; trivial.
    apply isi_assoc_2 with V W X S T U B C1 C; trivial.
  }
  exists A'; exists B'; exists C'; exists A; exists C1; exists C.
  repeat (split; trivial).
  clear dependent D; clear dependent E; clear dependent G; clear dependent H;
  clear dependent K; clear dependent L; clear dependent P; clear dependent Q; clear F I M R.

  destruct (ex_suma V W X C1 B A) as [D [E [F HSuma]]]; auto.
  assert (HIsi : Isi V W X C1 B A).
  { apply isi_lea2__isi with V W X S T U; Lea.
    apply isi_suma__lea123789 with B A C1; SumA.
  }
  suma.assert_diffs.
  apply trisuma_perm_132.
  exists D; exists E; exists F.
  split.
  - assert (HConga : CongA C1 C B A C B).
    { apply (out_conga C1 C B C1 C B); try (apply out_trivial); CongA.
      apply bet_out; Between.
    }
    apply (conga3_suma__suma C1 C B C B A D E F); CongA.
    assert (HInAngle : InAngle C1 C B A).
      repeat split; auto; exists C1; split; Between; right; apply out_trivial; auto.
    apply suma_assoc_1 with C B C1 C1 B A V W X; SumA.
  - assert (HConga : CongA B A C B A C1).
      apply (out_conga B A C1 B A C1); try (apply out_trivial); CongA; apply bet_out; auto.
    apply (conga3_suma__suma D E F B A C1 A' B' C'); CongA.
    apply suma_assoc_2 with V W X C1 B A S T U; SumA.
Qed.

Lemma t22_16_1bis : ~ hypothesis_of_obtuse_saccheri_quadrilaterals -> forall A B C C1 D E F G H I K L M,
  Bet A C1 C -> Defect A B C1 D E F -> Defect B C1 C G H I -> Defect A B C K L M ->
  Isi D E F G H I /\ SumA D E F G H I K L M.
Proof.
  intros noah A B C C1 D E F G H I K L M HBet HDefA HDefB HDef.
  assert (Hd := defect_distincts A B C1 D E F HDefA).
  assert (Hd' := defect_distincts B C1 C G H I HDefB).
  spliter.
  destruct (ex_suma D E F G H I) as [K' [L' [M' HSuma]]]; auto.
  destruct (t22_16_1 noah A B C C1 D E F G H I K' L' M') as [HIsi HDef']; trivial.
  split; trivial.
  apply (conga3_suma__suma D E F G H I K' L' M'); try (apply conga_refl); auto.
  apply (defect2__conga A B C); trivial.
Qed.


Lemma t22_16_2aux : ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R,
  Defect A B C D1 D2 D3 -> Defect A B D C1 C2 C3 -> Defect A D C B1 B2 B3 -> Defect C B D A1 A2 A3 ->
  Bet A O C -> Bet B O D -> Col A B C -> SumA D1 D2 D3 B1 B2 B3 P Q R ->
  Isi C1 C2 C3 A1 A2 A3 /\ SumA C1 C2 C3 A1 A2 A3 P Q R.
Proof.
  intros noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R
    HDefD HDefC HDefB HDefA HBet HBet2 HCol HSuma.
  assert (Hd := defect_distincts A B D C1 C2 C3 HDefC).
  assert (Hd' := defect_distincts C B D A1 A2 A3 HDefA).
  assert (Hd'' := defect_distincts A B C D1 D2 D3 HDefD).
  spliter; suma.assert_diffs.
  apply col_defect__out in HDefD; trivial.
  destruct (Col_dec A D C) as [HCol1|HNCol].
  { assert (Col C B D) by ColR.
    assert (Col A B D) by ColR.
    apply col_defect__out in HDefA; trivial.
    apply col_defect__out in HDefB; trivial.
    apply col_defect__out in HDefC; trivial.
    split; [SumA|].
    apply (conga3_suma__suma D1 D2 D3 B1 B2 B3 P Q R); try (apply conga_refl); auto;
    apply l11_21_b; trivial.
  }
  assert (B = O) by (apply (l6_21 A C D B); Col).
  subst O.
  apply out213_suma__conga in HSuma; trivial.
  destruct (t22_16_1bis noah A D C B C1 C2 C3 A1 A2 A3 B1 B2 B3) as [HIsi HSuma1]; trivial.
    apply defect_perm_132, HDefC.
    apply defect_perm_321, HDefA.
  split; trivial.
  apply (conga3_suma__suma C1 C2 C3 A1 A2 A3 B1 B2 B3); CongA.
Qed.

Lemma t22_16_2aux1 : ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R,
  Defect A B C D1 D2 D3 -> Defect A B D C1 C2 C3 -> Defect A D C B1 B2 B3 -> Defect C B D A1 A2 A3 ->
  Bet A O C -> Bet B O D -> Col A B D -> SumA D1 D2 D3 B1 B2 B3 P Q R ->
  Isi C1 C2 C3 A1 A2 A3 /\ SumA C1 C2 C3 A1 A2 A3 P Q R.
Proof.
  intros noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R
    HDefD HDefC HDefB HDefA HBet HBet2 HCol HSuma.
  assert (Hd := defect_distincts A B D C1 C2 C3 HDefC).
  assert (Hd' := defect_distincts C B D A1 A2 A3 HDefA).
  spliter; suma.assert_diffs.
  assert (HOut : Out C2 C1 C3) by (apply (col_defect__out A B D); trivial).
  split; [SumA|].
  assert (HSuma1 : SumA C1 C2 C3 A1 A2 A3 A1 A2 A3) by (apply out213__suma; auto).
  apply (conga3_suma__suma C1 C2 C3 A1 A2 A3 A1 A2 A3); try (apply conga_refl); auto.
  apply (suma2__conga D1 D2 D3 B1 B2 B3); trivial.
  destruct (t22_16_2aux noah B A D C B1 B2 B3 A1 A2 A3 D1 D2 D3 C1 C2 C3 O A1 A2 A3); Col;
  apply defect_perm_213; trivial.
Qed.

(** In a convex quadrilateral ABCD, the sum of the defects of ABC and ADC is equal to
    the sum of the defects of ABD and CBD. We add some hypotheses to make the proof easier *)
Lemma t22_16_2 : ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R,
  Defect A B C D1 D2 D3 -> Defect A B D C1 C2 C3 -> Defect A D C B1 B2 B3 -> Defect C B D A1 A2 A3 ->
  Bet A O C -> Bet B O D -> Isi D1 D2 D3 B1 B2 B3 -> SumA D1 D2 D3 B1 B2 B3 P Q R ->
  Isi C1 C2 C3 A1 A2 A3 /\ SumA C1 C2 C3 A1 A2 A3 P Q R.
Proof.
  intros noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O P Q R
    HDefD HDefC HDefB HDefA HBet HBet2 HIsi HSuma.
  assert (Hd := defect_distincts A B D C1 C2 C3 HDefC).
  assert (Hd' := defect_distincts C B D A1 A2 A3 HDefA).
  spliter; suma.assert_diffs.

  destruct (Col_dec A B C) as [HCol|HNCol].
    apply (t22_16_2aux noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O); trivial.
  destruct (Col_dec A D C) as [HCol1|HNCol1].
    apply (t22_16_2aux noah A D C B A1 A2 A3 D1 D2 D3 C1 C2 C3 B1 B2 B3 O); Between; SumA;
    apply defect_perm_132; trivial.
  destruct (Col_dec A B D) as [HCol2|HNCol2].
    apply (t22_16_2aux1 noah A B C D A1 A2 A3 B1 B2 B3 C1 C2 C3 D1 D2 D3 O); trivial.
  destruct (Col_dec C B D) as [HCol3|HNCol3].
    destruct (t22_16_2aux1 noah C B A D C1 C2 C3 B1 B2 B3 A1 A2 A3 D1 D2 D3 O P Q R); Between; SumA;
    apply defect_perm_321; trivial.
  assert (Hdiff : O <> A /\ O <> B /\ O <> C /\ O <> D).
    assert_cols; repeat split; intro; subst O; Col.
  spliter.

  destruct (ex_defect A B O) as [S1 [T1 [U1 HDef1]]]; auto.
  destruct (ex_defect B C O) as [S2 [T2 [U2 HDef2]]]; auto.
  destruct (ex_defect C D O) as [S3 [T3 [U3 HDef3]]]; auto.
  destruct (ex_defect A D O) as [S4 [T4 [U4 HDef4]]]; auto.
  destruct (t22_16_1bis noah A B C O S1 T1 U1 S2 T2 U2 D1 D2 D3) as [HIsi12 HSuma12]; trivial.
    apply defect_perm_132, HDef2.
  destruct (t22_16_1bis noah A D C O S4 T4 U4 S3 T3 U3 B1 B2 B3) as [HIsi34 HSuma34]; trivial.
    apply defect_perm_231, HDef3.
  destruct (t22_16_1bis noah B A D O S1 T1 U1 S4 T4 U4 C1 C2 C3) as [HIsi14 HSuma14]; trivial.
    apply defect_perm_213, HDef1.
    apply defect_perm_132, HDef4.
    apply defect_perm_213, HDefC.
  destruct (t22_16_1bis noah B C D O S2 T2 U2 S3 T3 U3 A1 A2 A3) as [HIsi23 HSuma23]; trivial.
    apply defect_perm_132, HDef3.
    apply defect_perm_213, HDefA.
  suma.assert_diffs.

  destruct (ex_suma D1 D2 D3 S3 T3 U3) as [V [W [X HSuma1]]]; auto.
  assert (HIsi1 : Isi D1 D2 D3 S3 T3 U3).
    apply isi_lea2__isi with D1 D2 D3 B1 B2 B3; Lea; apply (isi_suma__lea456789 S4 T4 U4); trivial.
  assert (HSuma2 : SumA V W X S4 T4 U4 P Q R).
    apply suma_assoc_2 with D1 D2 D3 S3 T3 U3 B1 B2 B3; SumA.
  assert (HIsi2 : Isi V W X S4 T4 U4).
    apply isi_assoc_2 with D1 D2 D3 S3 T3 U3 B1 B2 B3; SumA.
  assert (HSuma3 : SumA A1 A2 A3 S1 T1 U1 V W X).
    apply suma_assoc_2 with S3 T3 U3 S2 T2 U2 D1 D2 D3; SumA.
  assert (HIsi3 : Isi A1 A2 A3 S1 T1 U1).
    apply isi_assoc_2 with S3 T3 U3 S2 T2 U2 D1 D2 D3; SumA.
  split.
    apply isi_assoc_2 with S4 T4 U4 S1 T1 U1 V W X; SumA.
  apply suma_assoc_2 with S4 T4 U4 S1 T1 U1 V W X; SumA.
Qed.

Lemma legendre_aux : ~ hypothesis_of_obtuse_saccheri_quadrilaterals -> 
  forall A B C D B1 C1 P Q R S T U V W X, ~ Col A B C -> CongA A C B C B D ->
  Cong A C B D -> TS B C A D -> Out A B B1 -> Out A C C1 -> Bet B1 D C1 ->
  Defect A B C P Q R -> Defect A B1 C1 S T U -> SumA P Q R P Q R V W X ->
  Isi P Q R P Q R /\ LeA V W X S T U.
Proof.
  intros noah A B C D B1 C1 P Q R S T U V W X HNCol HConga HCong HTS HOutB HOutC HBet HDef HDef1 HSuma.
  assert (H := A).
  destruct (l11_49 A C B D B C) as [HCong1 [HConga1 HConga2]]; CongA; Cong.
    assert_diffs; auto.
  assert (HPar : Par_strict A C B D).
  { apply par_not_col_strict with B; Col.
    apply par_left_comm, l12_21_b; Side; CongA.
  }
  assert (HPar' : Par_strict A B C D).
  { apply par_not_col_strict with C; Col.
    apply par_left_comm, l12_21_b; Side; CongA.
  }
  assert (HNCol2:= HPar'); assert (HNCol3 := HPar'); assert (HNCol4 := HPar').
  apply par_strict_not_col_2 in HNCol2; apply par_strict_not_col_3 in HNCol3; apply par_strict_not_col_4 in HNCol4.
  assert (HB : ~ Col B1 B D /\ TS B D B1 C1 /\ Bet A B B1).
  { assert_diffs.
    apply par_strict_symmetry, (par_strict_col_par_strict B D A C C1) in HPar; Col.
    assert (HNCol' := par_strict_not_col_4 B D A C1 HPar).
    assert (B <> B1) by (intro; subst B1; apply HNCol'; Col).
    assert (~ Col B1 B D) by (intro; apply HNCol4; ColR).
    assert (TS B D B1 C1) by (repeat split; Col; exists D; Col).
    repeat (split; auto).
    apply col_two_sides_bet with D; Col.
    apply l9_8_2 with C1; Side.
  }
  destruct HB as [HNCol5 [HTS1 HBetB]].
  assert (HC : ~ Col C D B1 /\ C <> C1 /\ Bet A C C1).
  { assert_diffs.
    apply par_strict_symmetry, (par_strict_col_par_strict C D A B B1) in HPar'; Col.
    assert (HNCol' := par_strict_not_col_4 C D A B1 HPar').
    assert (C <> C1) by (intro; subst C1; apply HNCol'; Col).
    repeat split; auto.
    apply col_two_sides_bet with D; Col.
    apply l9_8_2 with B1; Side.
    repeat split; Col.
      intro; apply HNCol3; ColR.
    exists D; Col.
  }
  destruct HC as [HNCol6 [HCC1 HBetC]].
  assert_diffs.
  destruct (ts2__ex_bet2 B C D B1) as [Z [HZ1 HZ2]].
    apply l9_8_2 with C1; Side; apply one_side_symmetry, l12_6, par_strict_col_par_strict with A; Col; Par.
    { apply l9_31.
        apply l9_17 with C1; trivial.
        exists A; assert_diffs; repeat split; Col; try (intro; apply HNCol; ColR);
        [exists B|exists C]; split; Col; Between.
      apply one_side_symmetry, l12_6, par_strict_col_par_strict with A; Col; Par.
    }

  clear H.
  destruct (ex_defect A B1 C) as [G [H [I HDef2]]]; auto.
  destruct (ex_defect B1 C C1) as [J [K [L HDef3]]]; auto.
  destruct (ex_defect C B B1) as [M [N [O HDef4]]]; auto.
  destruct (ex_defect B1 C D) as [A' [B' [C' HDef5]]]; auto.
  destruct (ex_defect C D C1) as [D' [E' [F' HDef6]]]; auto.
    intro; subst C1; apply HNCol3; Col.
  destruct (ex_defect B1 B D) as [M' [N' [O' HDef7]]]; auto.
  assert (Hd := defect_distincts A B1 C G H I HDef2).
  assert (Hd2 := defect_distincts C B B1 M N O HDef4).
  assert (Hd3 := defect_distincts B1 C D A' B' C' HDef5).
  spliter; clean.
  destruct (ex_suma G H I A' B' C') as [G' [H' [I' HSuma1]]]; auto.
  destruct (ex_suma M N O A' B' C') as [J' [K' [L' HSuma2]]]; auto.

  destruct (t22_16_1bis noah A B1 C1 C G H I J K L S T U) as [HIsi3 HSuma3]; trivial.
  destruct (t22_16_1bis noah B1 C C1 D A' B' C' D' E' F' J K L) as [HIsi4 HSuma4]; trivial.
  destruct (t22_16_1bis noah A C B1 B P Q R M N O G H I) as [HIsi5 HSuma5]; trivial.
    apply defect_perm_132, HDef.
    apply defect_perm_132, HDef2.
  assert (HIsi1 : Isi G H I A' B' C').
    apply isi_lea2__isi with G H I J K L; Lea.
    apply isi_suma__lea123789 with D' E' F'; trivial.
  assert (HIsi2 : Isi M N O A' B' C').
    apply isi_lea2__isi with G H I A' B' C'; Lea.
    apply isi_suma__lea456789 with P Q R; trivial.
  assert (HSuma6 : SumA G' H' I' D' E' F' S T U).
    apply suma_assoc_2 with G H I A' B' C' J K L; trivial.
  assert (HIsi6 : Isi G' H' I' D' E' F').
    apply isi_assoc_2 with G H I A' B' C' J K L; trivial.
  assert (HSuma7 : SumA P Q R J' K' L' G' H' I').
    apply suma_assoc_1 with M N O A' B' C' G H I; trivial.
  assert (HIsi7 : Isi P Q R J' K' L').
    apply isi_assoc_1 with M N O A' B' C' G H I; trivial.
  destruct (t22_16_2 noah C B B1 D M' N' O' A' B' C' P Q R M N O Z J' K' L') as [HIsi8 HSuma8]; trivial.
    apply defect_perm_231, (conga3_defect__defect A B C); CongA.
    apply defect_perm_231, HDef5.
  assert (HLea : LeA P Q R J' K' L') by (apply isi_suma__lea123789 with M' N' O'; trivial).

  split.
    suma.assert_diffs.
    apply isi_lea2__isi with P Q R J' K' L'; Lea.
  apply lea_trans with G' H' I'.
    apply isi_lea456_suma2__lea with P Q R P Q R J' K' L'; trivial.
  apply isi_suma__lea123789 with D' E' F'; trivial.
Qed.

Lemma legendre_aux1 : forall A B C B' C', ~ Col A B C -> Out A B B' -> Out A C C' ->
  exists D', InAngle D' B A C /\ CongA A C' B' C' B' D' /\ Cong A C' B' D' /\ TS B' C' A D'.
Proof.
  intros A B C B' C' HNCol HOutB HOutC.
  assert_diffs.
  assert (HNCol' : ~ Col A B' C') by (intro; assert_diffs; apply HNCol; ColR).
  destruct (midpoint_existence B' C') as [M HM].
  destruct (symmetric_point_construction A M) as [D' HD].
  assert (HNCol1 : ~ Col A M B') by (intro; assert_diffs; apply HNCol'; ColR).
  assert (HNCol2 : ~ Col D' B' C') by (intro; assert_diffs; apply HNCol'; ColR).
  exists D'.
  assert_diffs; destruct HM; destruct HD; split.
    apply l11_25 with D' B' C'; try (apply out_trivial); auto.
    repeat split; auto.
    exists M; split; trivial.
    right; apply bet_out; auto.
  destruct (l11_49 A M C' D' M B') as [HCong1 [HConga1 HConga2]]; Cong.
    apply l11_14; Between.
  split.
    apply (out_conga A C' M M B' D'); try (apply out_trivial); try (apply bet_out); Between; CongA.
  split; Cong.
  repeat split; Col.
  exists M; split; Col.
Qed.

Lemma legendre_aux2 : ~ hypothesis_of_obtuse_saccheri_quadrilaterals ->
  forall A B C,  ~ Col A B C ->  Acute B A C ->
  (forall T : Tpoint, InAngle T B A C -> exists X Y : Tpoint, Out A B X /\ Out A C Y /\ Bet X T Y) ->
  forall P Q R S T U, Defect A B C P Q R -> GradAExp P Q R S T U ->
  exists B' C' P' Q' R', (Out A B B' /\ Out A C C' /\ Defect A B' C' P' Q' R' /\ LeA S T U P' Q' R').
Proof.
  intros noah A B C HNCol HAcute legendre P Q R S T U HDef.
  induction 1; rename A0 into P; rename B0 into Q; rename C0 into R.
    exists B; exists C; exists P; exists Q; exists R; assert_diffs.
    repeat split; (try apply out_trivial); Lea.
  rename D into S; rename E into T; rename F into U.
  destruct IHGradAExp as [B' [C' [P' [Q' [R' [HOutB [HOutC [HDef' HLea]]]]]]]]; trivial.
  destruct (legendre_aux1 A B C B' C') as [D' [HInangle [HConga [HCong HTS]]]]; trivial.
  assert (HNCol' : ~ Col A B' C') by (destruct HTS; Col).
  destruct (legendre D' HInangle) as [B'' [C'' [HOutB' [HOutC' HBet]]]].
  assert (Hd := defect_distincts A B' C' P' Q' R' HDef'); spliter; assert_diffs.
  destruct (ex_defect A B'' C'') as [P'' [Q'' [R'' HDef'']]]; auto.
    intro; subst; apply HNCol; ColR.
  exists B''; exists C''; exists P''; exists Q''; exists R''.
  repeat (split; trivial).
  destruct (ex_suma P' Q' R' P' Q' R') as [V [W [X HSuma1]]]; auto.
  destruct (legendre_aux noah A B' C' D' B'' C'' P' Q' R' P'' Q'' R'' V W X) as [HIsi1 HLea1]; trivial.
    apply l6_7 with B; trivial; apply l6_6; trivial.
    apply l6_7 with C; trivial; apply l6_6; trivial.
  apply lea_trans with V W X; trivial.
  apply isi_lea2_suma2__lea with S T U S T U P' Q' R' P' Q' R'; trivial.
Qed.

Lemma legendre_s_theorem :
  archimedes_postulate ->
  legendre_s_postulate ->
  postulate_of_right_saccheri_quadrilaterals.
Proof.
  intros archi legendre.
  destruct legendre as [B [A [C [HNCol [HAcute legendre]]]]].
  assert_diffs.
  destruct (ex_defect A B C) as [P [Q [R HDef]]]; auto.
  destruct (Col_dec P Q R) as [HCol|HNCol1].
  - apply archi__obtuse_case_elimination in archi.
    apply (defect_ncol_out__rah A B C P Q R); Col.
    apply not_bet_out; Col.
    intro HBet.
    apply HNCol.
    apply defect_perm_213 in HDef.
    destruct HDef as [D [E [F [G [H [I [[J [K [L [HSuma1 HSuma2]]]] [HBet1 HSuma3]]]]]]]].
    apply out_col, l6_6, out_lea__out with D E F.
      apply bet_suma__isi, isi_sym in HSuma3; trivial.
      destruct HSuma3 as [_ [[HOut|HNBet]]]; trivial.
      absurd (Bet P Q R); trivial.
    apply isi_suma__lea456789 with J K L; trivial.
    apply (t22_20 archi); trivial.
  - destruct (archi__gradaexp_destruction archi P Q R HNCol1) as [S [T [U [HGAE HObtuse]]]].
    apply archi__obtuse_case_elimination in archi.
    apply not_col_permutation_4 in HNCol.
    destruct (legendre_aux2 archi A B C HNCol HAcute legendre P Q R S T U HDef HGAE) as [B' [C' HInter]].
    destruct HInter as [P' [Q' [R' [HOutB [HOutC [HDef' HLea]]]]]].
    apply (obtuse_gea_obtuse P' Q' R'), obtuse__nisi in HObtuse; auto.
    exfalso.
    apply HObtuse.
    destruct (legendre_aux1 A B C B' C') as [D' [HInangle [HConga [HCong HTS]]]]; trivial.
    assert (HNCol' : ~ Col A B' C') by (destruct HTS; Col).
    destruct (legendre D' HInangle) as [B'' [C'' [HOutB' [HOutC' HBet]]]].
    assert_diffs.
    destruct (ex_defect A B'' C'') as [S' [T' [U' HDef'']]]; auto.
      intro; subst; apply HNCol; ColR.
    destruct (ex_suma P' Q' R' P' Q' R') as [V [W [X HSuma]]]; auto.
    destruct (legendre_aux archi A B' C' D' B'' C'' P' Q' R' S' T' U' V W X); trivial;
    [apply l6_7 with B|apply l6_7 with C]; trivial; apply l6_6; trivial.
Qed.

End Legendre.