Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section aristotle_greenberg.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma aristotle__greenberg : aristotle_s_postulate -> greenberg_s_postulate.
Proof.
  intros aristotle P Q R A B C.
  intros HNColB HABCacute HQRdiff HQright.
  elim (eq_dec_points P Q); intro HPQdiff.
  { treat_equalities.
    assert_diffs.
    exists R.
    split.
    2: apply out_trivial; auto.
    split.
    apply lea121345; auto.
    intro.
    apply HNColB.
    apply col_permutation_4.
    apply out_col.
    apply (eq_conga_out P R); auto.
  }
  assert (HXY : (exists X Y, out B A X /\ out B C Y /\ Per B X Y /\ lt P Q X Y)) by (apply aristotle; assumption).
  destruct HXY as [X [Y [PX [PY [HXright [Hle HNcong]]]]]].
  assert_diffs.
  assert (HXYdiff : X <> Y) by (intro; treat_equalities; apply HPQdiff; apply le_zero with X; auto).
  assert (HT : (exists T, out Q T P /\ Cong Q T X Y)) by (apply l6_11_existence; auto).
  destruct HT as [T []].
  assert (HS : (exists S, out Q S R /\ Cong Q S X B)) by (apply l6_11_existence; auto).
  destruct HS as [S []].
  assert_diffs.
  exists S.
  split; auto.
  assert_cols.
  assert (Per S Q P) by (apply (l8_3 R); Perp; Col).
  assert (Per T Q S) by (apply (l8_3 P); Perp; Col).
  assert (P<>S).
  { intro; treat_equalities.
    assert (P=Q) by (apply l8_8; auto); treat_equalities; absurde.
  }
  assert (T<>S).
  { intro; treat_equalities.
    assert (T=Q) by (apply l8_8; auto); treat_equalities; absurde.
  }
  apply conga_preserves_lta with P S Q T S Q; try (apply conga_refl; auto).
  2: split.
  - apply conga_trans with X B Y.
    2: apply (out_conga A B C A B C); Conga; apply out_trivial; auto.
    assert (HInter : (Cong T S Y B /\ (T <> S -> Conga Q T S X Y B /\ Conga Q S T X B Y))).
    { apply (l11_49 T Q S Y X B); Cong.
      apply l11_16; Perp.
    }
    destruct HInter as [_ [_ HConga]]; auto.
    apply conga_left_comm; auto.

  - apply lea_comm.
    apply (l11_29_b Q S P Q S T).
    exists T.
    split; Conga.
    repeat split; auto.
    exists P.
    split.
    2: right; apply out_trivial; auto.
    apply l6_13_1.
    apply l6_6; auto.
    apply (le_transitivity Q P X Y).
    apply (le_transitivity Q P P Q); Le.
    apply (cong__le); Cong.

  - intro HConga.
    assert (HInter : Cong Q P Q T /\ Cong S P S T /\ Conga Q P S Q T S).
    { apply l11_50_1; Cong.
      { intro.
        assert (HUn : S=Q\/P=Q) by (apply l8_9; Col).
        destruct HUn; treat_equalities; absurde.
      }
      apply l11_16; Perp.
      Conga.
    }
    destruct HInter as [HCong _].
    apply HNcong.
    apply (cong_transitivity P Q T Q); Cong.
Qed.

End aristotle_greenberg.