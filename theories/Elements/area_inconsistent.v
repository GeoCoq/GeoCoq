Require Export GeoCoq.Elements.OriginalProofs.lemma_extension.
Require Export GeoCoq.Elements.OriginalProofs.lemma_congruenceflip.
Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencesymmetric.
Require Export GeoCoq.Elements.OriginalProofs.lemma_congruencetransitive.
Require Export GeoCoq.Elements.OriginalProofs.lemma_NCdistinct.
Require Import GeoCoq.Axioms.euclidean_area_axioms.

Section Euclid.

Context `{Ax : Area_inconsistent.area_inconsistent}.

Instance area_inconsistent_area : area _ :=
{|
  EF := Area_inconsistent.EF;
  ET := Area_inconsistent.ET;
  axiom_congruentequal :=
    fun A B C a b c _ => Area_inconsistent.axiom_congruentequal A B C a b c;
  axiom_ETpermutation := Area_inconsistent.axiom_ETpermutation;
  axiom_ETsymmetric := Area_inconsistent.axiom_ETsymmetric;
  axiom_EFpermutation := Area_inconsistent.axiom_EFpermutation;
  axiom_halvesofequals := Area_inconsistent.axiom_halvesofequals;
  axiom_EFsymmetric := Area_inconsistent.axiom_EFsymmetric;
  axiom_EFtransitive := Area_inconsistent.axiom_EFtransitive;
  axiom_ETtransitive := Area_inconsistent.axiom_ETtransitive;
  axiom_cutoff1 := Area_inconsistent.axiom_cutoff1;
  axiom_cutoff2 := Area_inconsistent.axiom_cutoff2;
  axiom_paste1 := Area_inconsistent.axiom_paste1;
  axiom_deZolt1 := Area_inconsistent.axiom_deZolt1;
  axiom_deZolt2 := Area_inconsistent.axiom_deZolt2;
  axiom_paste2 := Area_inconsistent.axiom_paste2;
  axiom_paste3 := Area_inconsistent.axiom_paste3;
  axiom_paste4 := Area_inconsistent.axiom_paste4
|}.

Lemma area_inconsistent : False.
Proof.
assert (HNC := axiom_lower_dim).
assert (HAB : PA <> PB) by (forward_using lemma_NCdistinct).
assert (HBA : PB <> PA) by (conclude lemma_inequalitysymmetric).
assert (HD : exists D, (BetS PA PB D /\ Cong PB D PA PB)) by (conclude lemma_extension).
destruct HD as [D [HB1 HC1]].
assert (HPBD : PB <> D) by (forward_using lemma_betweennotequal).
assert (HC : exists C, (BetS PB D C /\ Cong D C PA PB)) by (conclude lemma_extension).
destruct HC as [C [HB2 HC2]].
assert (HB3 : BetS D PB PA) by (conclude axiom_betweennesssymmetry).
assert (HC3 : Cong D PB PB D) by (conclude cn_equalityreverse).
assert (HC4 : Cong PB PA D C).
  {
  assert (HC4 : Cong PB PA PA PB) by (conclude cn_equalityreverse).
  assert (HC5 : Cong PA PB D C) by (conclude lemma_congruencesymmetric).
  conclude lemma_congruencetransitive.
  }
assert (HC5 : Cong D PA PB C) by (conclude cn_sumofparts).
assert (HC6 : Cong PA C C PA) by (conclude cn_equalityreverse).
assert (HC7 : Cong D C PB PA).
  {
  assert (HC7 : Cong PA PB PB PA) by (conclude cn_equalityreverse).
  conclude lemma_congruencetransitive.
  }
assert (HC : Cong_3 D PA C PB C PA) by (unfold Cong_3; auto).
assert (HET : ET D PA C PB C PA) by (conclude Area_inconsistent.axiom_congruentequal).
assert (HF  : ~ ET D PA C PB PA C) by (apply axiom_deZolt1; auto).
apply HF; forward_using axiom_ETpermutation.
Qed.

End Euclid.