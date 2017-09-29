Require Import GeoCoq.Axioms.parallel_postulates.
Require Import GeoCoq.Tarski_dev.Ch12_parallel.

Section proclus_SPP.

Context `{T2D:Tarski_2D}.

Lemma proclus_s_postulate_implies_strong_parallel_postulate :
  proclus_postulate -> SPP.
Proof.
intros HP P Q R S T U HPTQ HRTS HNC HCop HCong1 Hcong2.
destruct (HP P R Q S P U) as [I [HCol1 HCol2]]; try exists I; Col.
apply l12_17 with T; assert_diffs; Col; split; Cong; unfold BetS in *; spliter; Between.
Qed.

End proclus_SPP.