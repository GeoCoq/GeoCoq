Require Export GeoCoq.Meta_theory.Parallel_postulates.Euclid_def.

Section proclus_SPP.

Context `{MT:Tarski_2D}.
Context `{EqDec:EqDecidability Tpoint}.

Lemma proclus_s_postulate_implies_strong_parallel_postulate :
  proclus_postulate -> SPP.
Proof.
intros HP P Q R S T U HPTQ HRTS HNC HCop HCong1 Hcong2.
destruct (HP P R Q S P U) as [I [HCol1 HCol2]]; try exists I; Col.
apply l12_17 with T; assert_diffs; Col; split; Cong; unfold BetS in *; spliter; Between.
Qed.

End proclus_SPP.
