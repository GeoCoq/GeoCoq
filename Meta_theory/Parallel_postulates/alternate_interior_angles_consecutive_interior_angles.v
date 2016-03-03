Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section alternate_interior_angles_consecutive_interior_angles.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma alternate_interior__consecutive_interior :
   alternate_interior_angles_postulate -> consecutive_interior_angles_postulate.
Proof.
  intros aia A B C D P Q R Hos HPar HSuma.
  assert(HA' := symmetric_point_construction A B).
  destruct HA' as [A'].
  apply (bet_conga_bet A B A'); Between.
  apply (suma2__conga A B C B C D); auto.
  assert(HNCol : ~ Col B C A) by (apply (one_side_not_col _ _ _ D); auto).
  assert_diffs.
  assert(TS B C A A').
  { repeat split; Col.
    intro; apply HNCol; ColR.
    exists B.
    split; Col; Between.
  }
  apply (conga3_suma__suma A B C C B A' A B A'); try (apply conga_refl); auto.
    exists A'; repeat (split; CongA); apply l9_9; auto.
  apply conga_comm.
  apply aia.
    apply l9_2; apply (l9_8_2 _ _ A); auto.
  apply (par_col_par_2 _ A); Col; Par.
Qed.

End alternate_interior_angles_consecutive_interior_angles.
