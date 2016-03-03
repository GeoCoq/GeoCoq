Require Export Meta_theory.Parallel_postulates.Euclid_def.

Section rah_universal_posidonius.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma rah__universal_posidonius : saccheri_s_right_angle_hypothesis -> universal_posidonius.
Proof.
  intros rah A1 A2 A3 B1 B2 B3 HSac HA HB HPerp.
  assert(Hdiff := sac_distincts A1 B1 B2 A2 HSac).
  spliter.
  assert_diffs.
  elim(eq_dec_points A1 A3).
  { intro.
    subst A3.
    assert(B1 = B3).
    2: subst; Cong.
    apply (l6_21 B1 B2 A1 B1); Col.
      apply not_col_permutation_1; apply (sac__ncol123 _ _ _ A2); assumption.
      unfold Saccheri in HSac; spliter; apply (perp_perp_col _ _ _ A1 A2); Perp.
  }
  intro.
  destruct(segment_construction_3 A3 B3 A1 B1) as [B'3 []]; auto.
  assert_diffs.
  assert(B3 = B'3).
  2: subst; assumption.
  assert(Par_strict B1 B2 A1 A3).
  { apply (par_strict_col_par_strict _ _ _ A2); auto.
    apply par_strict_symmetry.
    apply sac__par_strict; assumption.
  }
  apply (l6_21 B1 B2 A3 B3); Col.
    apply (par_strict_not_col_4 _ _ A1); auto.
  apply col_permutation_2.
  apply (per_per_col _ _ A1); auto; apply l8_2.
    apply (rah _ _ _ A2); auto.
  apply (rah _ _ _ A3).
  unfold Saccheri in *.
  spliter.
  assert(B1 <> B3).
  { intro.
    subst B3.
    assert(A1 = A3); auto.
    apply (l8_18_unicity A1 A2 B1); Col; Perp.
    apply not_col_permutation_1; apply per_not_col; auto.
  }
  assert(Per A1 A3 B'3).
  { apply perp_per_1; auto.
    apply perp_comm; apply (perp_col _ A2); Col.
    apply (perp_col1 _ _ _ B3); Col.
  }
  repeat split; Cong.
    apply (per_col _ _ A2); auto.    
  apply (one_side_transitivity _ _ _ B3).
    apply l12_6; auto; apply (par_strict_col_par_strict _ _ _ B2); Col; Par.
    apply invert_one_side; apply out_one_side; auto; right; apply not_col_permutation_4; apply per_not_col; auto.
Qed.

End rah_universal_posidonius.
