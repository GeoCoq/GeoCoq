Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Annexes.suma.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section consecutive_interior_angles_alternate_interior_angles.

Context `{T2D:Tarski_2D}.

Lemma consecutive_interior__alternate_interior :
   consecutive_interior_angles_postulate -> alternate_interior_angles_postulate.
Proof.
  intros cia A B C D Hts HPar.
  assert (HD' := symmetric_point_construction D C).
  destruct HD' as [D'].
  assert(HNCol1 : ~ Col B A C) by (destruct Hts; auto).
  assert(HNCol2 : ~ Col D A C) by (destruct Hts as [_ []]; auto).
  assert_diffs.
  assert(~ Col A C D') by (intro; apply HNCol2; ColR).
  assert (HB' := ex_conga_ts A C D' C A B).
  destruct HB' as [B' []]; Col.
  assert_diffs.
  assert(HSuma : SumA B A C A C D' B A B').
    exists B'; repeat (split; CongA). apply l9_9; Side.
  assert(TS A C D' D).
    repeat (split; Col); exists C; split; Col; Between.
  assert(Bet B A B').
  { apply (cia B A C D'); trivial.
    exists D; split; auto.
    apply (par_col_par B A C D); Par; Col.
  }
  apply (sams2_suma2__conga123 _ _ _ _ _ _ A C D' D C D').
  - split; auto.
    split.
    right; intro; apply HNCol1; Col.
    exists B'.
    split; CongA.
    split.
    apply l9_9; Side.
    intro HNts.
    destruct HNts as [_ []]; assert_cols; Col.

  - apply (sams_chara _ _ _ _ _ _ D'); Between; Lea.

  - apply (conga3_suma__suma B A C A C D' B A B'); try (apply conga_refl); auto.
    apply conga_line; Between.

  - exists D'.
    repeat (split; CongA).
    apply l9_9; Side.
Qed.

End consecutive_interior_angles_alternate_interior_angles.