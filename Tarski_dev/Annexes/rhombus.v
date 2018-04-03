(*   Roland Coghetto, 29 March 2018
     GNU Lesser General Public License v3.0 
     See LICENSE GeoCoq 2.3.0
     
     MOTIVATION: 
     
      - Existence of a rhombus (absolute geometry).
      - Unicity of rhomus with 3 points determinated (absolute geometry).
      
     TODO:
     
      - In Euclidean geometry, construction of a rhombus from 3 determined points.
      - What about rhombus in non-euclidean geometry case ?

*)

Require Export GeoCoq.Tarski_dev.Annexes.perp_bisect.

Section Rhombus_Existence_Unicity.

Context `{T2D:Tarski_2D}.

Lemma PlgLeft: forall A B C D, Plg A B C D -> (A <> C \/ B <> D).
Proof.
  intros.
  unfold Plg in H. spliter.
assumption.
Qed.

Lemma PlgEquivDef: forall A B C D, (A <> C \/ B <> D) -> ((exists M,
OnCircle C M A /\ OnCircle D M B /\ Bet C M A /\ Bet D M B) <-> Plg A B C D).
Proof.
  intros.
  split.
  - intros.
    unfold OnCircle in *.
    split. 
    assumption.
    ex_and H0 M.
    exists M.
    split.
    { unfold Midpoint.
      split;Between. 
      Cong. 
    }
    { unfold Midpoint in *.
      split;Between. 
      Cong.
    }
  - intros.
    unfold OnCircle in *.
    ex_and H0 M.
    ex_and H1 M1.
    unfold Midpoint in *.
    exists M1.
    split;Cong.
    split;[Cong|Between].
Qed.

Lemma PlgAABB: forall A B, A <> B -> Plg A A B B.
Proof.
  intros.
  unfold Plg.
  split;auto.
  midpoint M A B.
  exists M.
  split;auto.
Qed.

Lemma PlgEx: exists A B C D, Plg A B C D.
Proof.
  destruct two_distinct_points as [A [B H]].
  exists A, A, B, B.
  apply PlgAABB.
  assumption.
Qed.

Lemma RhombusEx: exists A B C D, Rhombus A B C D.
Proof.
  destruct lower_dim_ex as [A [B [C HNC]]].
  assert (H1 : ~ Col A B C) by auto.
  clear HNC.
  assert_diffs.
  assert (HAB := perp_bisect_existence A B);
  destruct HAB as [C1 [C2 HAB]]; try (assert_diffs; assumption).
  assert(Cong A C1 B C1).
  apply perp_bisect_cong_2 with C2.
  apply perp_bisect_sym_1.
  assumption.
  unfold Perp_bisect in HAB.
  spliter.
  unfold ReflectL in *.
  spliter.
  destruct H0 as [M H0];
  spliter.
  assert(H10 := H).
  unfold Midpoint in H10.
  spliter.
  assert (exists x, Bet C1 M x /\ Cong M x C1 M) by (apply segment_construction).
  ex_and H8 x.
  exists A.
  exists C1.
  exists B.
  exists x.
  assert(Plg A C1 B x).
  unfold Plg.
  split.
  tauto.
  exists M.
  split.
  apply l7_2;assumption.
  unfold Midpoint.
  split.
  assumption.
  Cong.
  unfold Rhombus.
  split.
  assumption.
  Cong.
Qed.

Lemma RhombusUnicity: forall A B C D E, Rhombus A B C D -> Rhombus A B C E -> D = E.
Proof.
  intros.
  unfold Rhombus in *.
  spliter.
  unfold Plg in *.
  spliter.
  ex_and H4 M.
  ex_and H3 N.
  assert (M = N). 
  apply l7_17 with A C;assumption.
  subst.
  apply symmetric_point_uniqueness with B N;assumption.
Qed.


