Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq.
From mathcomp
Require Import tuple fintype bigop.
From mathcomp
Require Import ssralg ssrnum matrix.
From mathcomp
Require Import zmodp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.
Require Import GeoCoq.Algebraic.POF_to_Tarski.

Section RfTarskinp2D.

Variable n : nat.
Variable R : realFieldType.

Definition o := @to_nD R n (row2   0  0).

Definition i := @to_nD R n (row2 (-1) 0).

Definition basis : n.+2.-tuple 'rV_(n.+2) :=
  map_tuple (fun i => @delta_mx R _ _ 0 (inord i)) (iota_tuple n.+2 0).

Lemma nth_basis i : (i < n.+2)%N -> tnth basis (inord i) = delta_mx 0 (inord i).
Proof.
move => iP; rewrite /basis /tnth (@nth_map nat 0%N) ?size_iota //.
by rewrite inordK // nth_iota.
Qed.

Lemma basis_nth0 : delta_mx 0 (inord 0) = @to_nD R n (row2 1 0).
Proof.
rewrite -matrixP /to_nD => i j; rewrite !mxE; case: i => m; case: m => // i.
have {i} -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
have -> : @inord O O = 0 by apply val_inj; rewrite val_insubd.
have -> : @inord (S n) O = 0 by apply val_inj; rewrite val_insubd.
rewrite eqxx; case: splitP => i; rewrite mxE; last by case: (j =P 0) => // ->.
case: i => m; case: m => [i|m]; [|case: m => [i|//]].
- have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
  have -> /= : @inord (S O) O = 0 by apply val_inj; rewrite val_insubd.
  move => jP; have {jP} -> : j = inord 0 by apply: val_inj; rewrite val_insubd.
  by have -> /= : @inord (S n) O = 0 by apply val_inj; rewrite val_insubd.
- have -> : Ordinal i = inord 1 by apply: val_inj; rewrite val_insubd.
  have -> /= : @inord (S O) (S O) = 1 by apply val_inj; rewrite val_insubd.
  by rewrite div.modnS /= div.mod0n; case: (j =P 0) => // ->.
Qed.

Lemma basis_nth1 : delta_mx 0 1 = @to_nD R n (row2 0 1).
Proof.
rewrite -matrixP /to_nD => i j; rewrite !mxE; case: i => m; case: m => // i.
have {i} -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
have -> : @inord O O = 0 by apply val_inj; rewrite val_insubd.
rewrite eqxx; case: splitP => i; rewrite mxE; last by case: (j =P 1) => // ->.
case: i => m; case: m => [i|m]; [|case: m => [i|//]].
- have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
  have -> /= : @inord (S O) O = 0 by apply val_inj; rewrite val_insubd.
  by case: (j =P 1) => // ->.
- have -> : Ordinal i = inord 1 by apply: val_inj; rewrite val_insubd.
  have -> /= : @inord (S O) (S O) = 1 by apply val_inj; rewrite val_insubd.
  rewrite div.modnS /= div.mod0n => jP.
  have {jP} -> : j = inord 1 by apply: val_inj; rewrite val_insubd.
  by have -> /= : @inord (S n) (S O) = 1 by apply val_inj; rewrite val_insubd.
Qed.

Lemma i_neq_basis_nth0 : i <> delta_mx 0 (inord 0).
Proof.
rewrite basis_nth0 /i /to_nD => HF; move: (eq_row_mx HF) => {HF} [/eqP].
by rewrite row2_eq eqxx andbT eq_sym -subr_eq0 opprK (pnatr_eq0 _ 2).
Qed.

Lemma eq_nD_2D (p q : 'rV[R]_2) : to_nD n p == to_nD n q = (p == q).
Proof.
by apply/eqP/eqP => [|->//]; rewrite /to_nD => pqP; move: (eq_row_mx pqP) => [].
Qed.

Lemma to_nD0 : @to_nD R n 0 = 0.
Proof. by apply /rowP => i; rewrite mxE; case: splitP => j _; rewrite !mxE. Qed.

Lemma to_nDB (p q : 'rV[R]_2) : to_nD n p - to_nD n q = to_nD n (p - q).
Proof. by rewrite /to_nD opp_row_mx add_row_mx subr0. Qed.

Lemma to_nD_scale (a : R) (p : 'rV[R]_2) : a *: to_nD n p = to_nD n (a *: p).
Proof. by rewrite /to_nD scale_row_mx scaler0. Qed.

Lemma pick_to_nD (a b : 'rV[R]_2) i :
  [pick k | (b - a) 0 k != 0 ] = Some i ->
  [pick k | (to_nD n b - to_nD n a) 0 k != 0 ] = Some (lshift n i).
Proof.
rewrite /pick /to_nD opp_row_mx add_row_mx subrr /= /row_mx.
set p1 := (fun k : 'I_2 => (b - a) 0 k != 0).
set p2 := (fun k : 'I_(n.+2) => row_mx (b - a) 0 0 k != 0).
suff: (ohead (enum p2) = ohead (map (fun k => lshift n k) (enum p1))) => [->|].
  case: (enum _) (mem_enum p1) => [//|h t /= _ H].
  by have -> : h = i by move: H; apply: Some_inj.
move: i => _; rewrite /enum_mem -enumT !enum_ordSl.
rewrite -[X in _ :: X]cat1s -cat1s !filter_cat /=; set t_nil := filter _ _.
have: (t_nil == [::]) => [|/eqP->]; rewrite ?cats0.
  rewrite /t_nil -size_eq0 -all_pred0 all_filter; apply /allP => x xP.
  move/mapP: xP => [] x0 /mapP [] x1 _ -> ->; rewrite !inE implybF /in_mem /p2.
  set i := lift _ _; have -> : (i = rshift 2 x1) by rewrite /i; apply: val_inj.
  by rewrite /= row_mxEr mxE eqxx.
apply /eqP; rewrite eq_sym /enum_mem -enumT !enum_ordSl -cat1s.
move: t_nil => _; rewrite filter_cat map_cat.
rewrite -[ord0 :: [seq lift ord0 i | i <- enum 'I_0]]cat1s.
rewrite map_cat filter_cat map_cat /=; suff: ((ord0 \in p1) = (ord0 \in p2)).
  suff: ((lift ord0 ord0 \in p2) = (lift ord0 ord0 \in p1)) => [<- ->|].
    case: (ord0 \in p2) => //=; case: (lift ord0 ord0 \in p2) => //=.
    suff: enum 'I_0 == [::] by move=> /eqP->.
    by rewrite -size_eq0 size_enum_ord eqxx.
  rewrite /p1 /p2 /in_mem /=.
  have -> : lift ord0 ord0 = lshift n (lift ord0 ord0) :> 'I_(2+n);
  by rewrite ?row_mxEl //; apply val_inj.
rewrite /p1 /p2 /in_mem /=.
have -> : ord0 = lshift n ord0 :> 'I_(2+n) by apply val_inj.
by rewrite row_mxEl.
Qed.

Lemma betR_nD_2D (a b c : 'rV[R]_2) :
  betR (to_nD n a) (to_nD n b) (to_nD n c) = betR a b c.
Proof.
apply /eqP; rewrite /betR/ ratio eq_sym; move: (@pick_to_nD a c).
case: pickP => [i _ H|HF _].
  rewrite (H i) // /to_nD eq_sym mxE row_mxEl mxE row_mxEl mxE row_mxEl.
  by rewrite mxE row_mxEl !mxE.
case: pickP => //= x; rewrite /to_nD !mxE; case: (splitP x) => [i ? iP|?];
by rewrite ?subrr ?eqxx //; move: (HF i); rewrite !mxE iP.
Qed.

Lemma betS_nD_2D (a b c : 'rV[R]_2) :
  betS (to_nD n a) (to_nD n b) (to_nD n c) = betS a b c.
Proof. by rewrite /betS betR_nD_2D !to_nDB to_nD_scale eq_nD_2D. Qed.

Lemma bet_nD_2D (a b c : 'rV[R]_2) :
  bet (to_nD n a) (to_nD n b) (to_nD n c) = bet a b c.
Proof. by rewrite /bet betS_nD_2D /betE !eq_nD_2D. Qed.

Lemma betR_o_i_basis_nth0 : @betR R 2 (row2 (-1) 0) (row2 0 0) (row2 1 0) = 1%:R / 2%:R.
Proof.
rewrite /betR /ratio; case: pickP => /= [x|/all_v_neq0 H]; last first.
- by exfalso; apply H; rewrite subr_eq0 row2_eq -subr_eq0 opprK (pnatr_eq0 _ 2).
case: x => m; case: m => [j|m]; [|case: m => // j].
  + have -> : Ordinal j = inord 0 by apply: val_inj; rewrite val_insubd.
    have -> : @inord (S O) O = 0 by apply val_inj; rewrite val_insubd.
    by rewrite !mxE /= opprK add0r.
  + have -> : Ordinal j = inord 1 by apply: val_inj; rewrite val_insubd.
    have -> : @inord (S O) (S O) = 1 by apply val_inj; rewrite val_insubd.
    by rewrite !mxE /= subr0 eqxx.
Qed.

Lemma bet_o_i_basis_nth0 : bet i o (delta_mx 0 (inord 0)).
Proof.
suff: @betS R 2 (row2 (-1) 0) (row2 0 0) (row2 1 0)
  by rewrite basis_nth0 /i /o /to_nD bet_nD_2D /bet => ->; rewrite orbT.
rewrite /betS betR_o_i_basis_nth0.
rewrite ltr_pdivlMr ?ltr_pdivrMr ?addr_gt0 ?ltr01 //.
rewrite mul0r !mul1r ltrDr ltr01 /= andbT eq_inv_scale ?add11_neq0 //.
apply /eqP; rewrite -matrixP => i j; case: i => m; case: m => // i.
have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
have -> : @inord O O = 0 by apply val_inj; rewrite val_insubd.
case: j => m; case: m => [j|m]; [|case: m => // j].
- have -> : Ordinal j = inord 0 by apply: val_inj; rewrite val_insubd.
  have -> : @inord (S O) O = 0 by apply val_inj; rewrite val_insubd.
  by rewrite !mxE /= opprK add0r mulr1.
- have -> : Ordinal j = inord 1 by apply: val_inj; rewrite val_insubd.
  have -> : @inord (S O) (S O) = 1 by apply val_inj; rewrite val_insubd.
  by rewrite !mxE /= subr0 mulr0.
Qed.

Lemma oP : o = const_mx 0.
Proof.
rewrite /o /to_nD; suff -> : @row2 R 0 0 = const_mx 0 by rewrite row_mx_const.
rewrite -matrixP => i j; case: i => m; case: m => // i.
have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
have -> : @inord O O = 0 by apply val_inj; rewrite val_insubd.
case: j => m; case: m => [j|m]; [|case: m => // j].
- have -> : Ordinal j = inord 0 by apply: val_inj; rewrite val_insubd.
  suff -> : @inord (S O) O = 0 by rewrite !mxE.
  by apply val_inj; rewrite val_insubd.
- have -> : Ordinal j = inord 1 by apply: val_inj; rewrite val_insubd.
  suff -> : @inord (S O) (S O) = 1 by rewrite !mxE.
  by apply val_inj; rewrite val_insubd.
Qed.

Lemma iP : i = - (delta_mx 0 0).
Proof.
have -> : @delta_mx R (S O) (2 + n) 0 0 = delta_mx 0 (inord 0).
- by have -> : @inord (S n) O = 0 by apply val_inj; rewrite val_insubd.
apply /eqP; rewrite /i basis_nth0 /to_nD -subr_eq0 opprK add_row_mx addr0.
rewrite row_mx_eq0 eqxx andbT addr_eq0; apply /eqP.
rewrite -matrixP => i j; case: i => m; case: m => // i.
have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
have -> : @inord O O = 0 by apply val_inj; rewrite val_insubd.
case: j => m; case: m => [j|m]; [|case: m => // j].
- have -> : Ordinal j = inord 0 by apply: val_inj; rewrite val_insubd.
  suff -> : @inord (S O) O = 0 by rewrite !mxE.
  by apply val_inj; rewrite val_insubd.
- have -> : Ordinal j = inord 1 by apply: val_inj; rewrite val_insubd.
  suff -> : @inord (S O) (S O) = 1 by rewrite !mxE oppr0.
  by apply val_inj; rewrite val_insubd.
Qed.

Lemma lower_dim_all1 j :
  (0 <= j < n.+2)%N -> cong o i o (tnth basis (inord j)).
Proof.
move => /andP[j_ge0 j_le_np2]; rewrite nth_basis // oP iP /cong.
by rewrite !subr0 mulNmx dotC mulNmx opprK !trmx_delta !mul_delta_mx.
Qed.

Lemma lower_dim_all2 j k :
  (0 <= j < k)%N -> (k < n.+2)%N ->
  cong (tnth basis (inord j)) (tnth basis (inord k))
       i                      (delta_mx 0 (inord 1)).
Proof.
move => /andP[j_ge0 j_lt_k] k_lt_np2; rewrite !nth_basis ?(ltn_trans j_lt_k) //.
rewrite iP /cong mulmxBl dotC mulmxBl trmx_delta dotC mulmxBl trmx_delta.
rewrite !mul_delta_mx !mul_delta_mx_cond (eq_sym (inord k)) opprK.
rewrite mulmxDl dotC mulmxDl trmx_delta dotC mulmxDl trmx_delta.
rewrite !mul_delta_mx !mul_delta_mx_cond (eq_sym (inord 1)).
have -> /= : @inord (S n) (S O) = 1 by apply: val_inj; rewrite val_insubd.
case: (inord j =P inord k) => [HF|_/=]; last first.
- by rewrite mulr0n subr0 sub0r opprK addr0 add0r.
have: val (@inord n.+1 j) = val (@inord n.+1 k) by rewrite HF.
rewrite !val_insubd k_lt_np2 (ltn_trans j_lt_k) // => {}HF.
by move: j_lt_k; rewrite HF ltnn.
Qed.

Lemma lower_dim : lower_dimP _ (@bet R (n.+2)) (@cong R (n.+2)) n.+2 o i basis.
Proof.
rewrite /lower_dimP /orthonormal_basis /= !nth_basis //.
split; first by apply i_neq_basis_nth0.
split; first by rewrite bet_o_i_basis_nth0.
split; [apply big_andb_and|apply big_pairs_andb_and]; rewrite big_all.
- by apply /allP => j jP; rewrite lower_dim_all1 // -mem_index_iota.
apply /allP => j jP; rewrite big_all; apply /allP => k kP.
move: jP kP; rewrite !mem_index_iota => /andP[j_ge0 _] /andP[j_lt_k k_le_np2].
by rewrite lower_dim_all2 //.
Qed.

Lemma nth_new_basis i p :
  (i < n.+1)%N -> tnth (@rot_tuple n.+2 1 _ (belast_tuple p basis))
                       (inord i) = delta_mx 0 (inord i).
Proof.
move => iP; rewrite /basis /tnth; set f := fun j => delta_mx 0 (inord j).
rewrite /rot /= belast_map /rot /=; move: iP.
case: i => /= [|m i]; first rewrite inordK //=.
rewrite inordK ?(ltn_trans i) //= nth_cat size_map size_belast size_iota.
have m_lt_n : (m < n)%N by move: i; rewrite -ltn_predRL.
rewrite m_lt_n (@nth_map nat 0%N) ?size_belast ?size_iota //.
suff -> : nth O (belast (S O) (iota 2 n)) m = m.+1 by rewrite /f.
suff: forall l, (m < l)%N -> nth O (belast (S O) (iota 2 l)) m = m.+1.
- by move => lP; rewrite (lP n).
move => {p f i m_lt_n} l; elim l => // {}l IHl m_lt_lp1.
rewrite -(addn1 l) iotaD belast_cat nth_cat size_belast size_iota.
case: (m =P l) => [-> {IHl m_lt_lp1 m}|/eqP lm_neq]; last first.
- suff m_lt_l : (m < l)%N by rewrite m_lt_l IHl.
  by move: (ltnSE m_lt_lp1) lm_neq; rewrite leq_eqVlt => /orP[/eqP ->/eqP|->].
rewrite ltnn subnn /= -nth_last size_iota.
case: (l =P O) => [-> //|/eqP l_nz]; rewrite nth_iota ?ltn_predL ?lt0n //.
by move: l_nz; case: l.
Qed.

Lemma betR_ud_2D : @betR R 2 (row2 0 1) (const_mx 0) (row2 0 (-1)) = 1%:R / 2%:R.
Proof.
rewrite /betR /ratio; case: pickP => /= [x|/all_v_neq0 H]; last first.
- exfalso; apply H; rewrite subr_eq0 row2_eq eqxx.
  by rewrite eq_sym -subr_eq0 opprK (pnatr_eq0 _ 2).
case: x => m; case: m => [j|m]; [|case: m => // j].
  + have -> : Ordinal j = inord 0 by apply: val_inj; rewrite val_insubd.
    have -> : @inord (S O) O = 0 by apply val_inj; rewrite val_insubd.
    by rewrite !mxE /= subr0 eqxx.
  + have -> : Ordinal j = inord 1 by apply: val_inj; rewrite val_insubd.
    have -> : @inord (S O) (S O) = 1 by apply val_inj; rewrite val_insubd.
    by rewrite !mxE /= add0r mulNr -mulrN -invrN opprB opprK.
Qed.

Lemma dist_10_01 :
  (delta_mx 0 (inord 1) - i) *m (delta_mx 0 (inord 1) - i)^T =
  delta_mx 0 0 + delta_mx 0 0.
Proof.
rewrite iP opprK mulmxDl dotC mulmxDl trmx_delta dotC mulmxDl trmx_delta.
rewrite !mul_delta_mx_cond !eqxx mulr1n eq_sym.
have -> /= : @inord (S n) 1 = 1 by apply: val_inj; rewrite val_insubd.
rewrite mulr0n add0r addr0 -matrixP => i j.
by case: i => m; case: m => // i; case: j => m; case: m => // j.
Qed.

Lemma upper_dimS p :
  i <> tnth (rot_tuple 1 (belast_tuple p basis)) (inord 0) ->
  bet i o (tnth (rot_tuple 1 (belast_tuple p basis)) (inord 0)) ->
  \big[and/True]_(0 <= i0 < n.+2)
    cong o i o (tnth (rot_tuple 1 (belast_tuple p basis)) (inord i0)) ->
  \big[and/True]_(0 <= i0 < n.+2)
    \big[and/True]_(i0.+1 <= j < n.+2)
      cong (tnth (rot_tuple 1 (belast_tuple p basis)) (inord i0))
           (tnth (rot_tuple 1 (belast_tuple p basis)) (inord j))
           i
           (tnth (rot_tuple 1 (belast_tuple p basis)) (inord 1)) ->
  tnth basis (inord n.+1) <> p -> betS (tnth basis (inord n.+1)) o p.
Proof.
move => _ _; set new_basis := rot_tuple 1 (belast_tuple p basis).
rewrite -big_andb_and -big_pairs_andb_and !big_all => /allP HC1 /allP HC2.
have pE : tnth new_basis (inord n.+1) = p.
- rewrite /basis /tnth /=.
  have -> : nat_of_ord (@inord n.+1 n.+1) = (size new_basis).-1.
  + by rewrite inordK // size_rot size_belast size_map size_iota.
  by rewrite nth_last last_cat.
have {}HC1 : cong o i o p.
- suff: cong o i o (tnth new_basis (inord n.+1)) by rewrite pE.
  by move: (HC1 n.+1); rewrite mem_index_iota ltnSn /= => ->.
have {}HC2 : (n =  O -> cong (delta_mx 0 0) p i p) /\
             (n <> O -> forall j, (0 <= j < n.+1)%N ->
                          cong p (tnth basis (inord j))
                               i (delta_mx 0 (inord 1))).
- case: (n =P O) => [n_ez|n_nz]; split; [|tauto|tauto|]; move => _.
  + suff -> : cong (delta_mx 0 0) p i p by done.
    move: (HC2 O); rewrite mem_index_iota ltn0Sn /= big_all => {}HC2.
    move: (HC2 is_true_true) => /= /andP[{}HC2 _].
    have {}pE : tnth new_basis (inord 1) = p.
    * suff -> : @inord (S n) 1 = inord n.+1 by rewrite pE.
      by rewrite n_ez.
    move: HC2; rewrite pE nth_new_basis //.
    by have -> // : @inord (S n) O = 0 by apply val_inj; rewrite val_insubd.
  + suff: forall j, (0 <= j < n.+1)%N ->
                    cong (tnth basis (inord j)) p
                         i (delta_mx 0 (inord 1)).
    * move => H j jP; move/eqP: (H _ jP); rewrite /cong.
      by move => <-; rewrite -opprB mulNmx dotC -mulNmx opprK.
    move => j /andP[j_ge0 j_lt_np1]; move: n_nz (HC2 j) => /eqP n_nz.
    rewrite mem_index_iota j_ge0 (ltn_trans j_lt_np1) //= big_all => {}HC2.
    move: (HC2 is_true_true) => {HC2} /allP HC2; move: (HC2 n.+1).
    rewrite mem_index_iota ltnSn j_lt_np1 pE /= => {}HC2.
    move: (HC2 is_true_true); rewrite nth_basis ?(ltn_trans j_lt_np1) //.
    by rewrite !nth_new_basis // ltnS lt0n.
set i_n := tnth basis (inord n.+1); move => i_n_neq_p.
suff: (n = O -> betS i_n o p) /\ (n <> O -> betS i_n o p)
  by case (n =P O); tauto.
case: (n =P O) => [n_ez|n_nz]; split; [|tauto|tauto|]; move => _.
- have {}HC2 : cong (delta_mx 0 0) p i p by tauto.
  have i_nP : i_n = to_nD n (row2 0 1).
  + rewrite /i_n nth_basis // /to_nD.
    have -> : inord n.+1 = @inord (S n) 1 by rewrite n_ez.
    rewrite -matrixP => i j; case: i => m; case: m => // i.
    have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
    have -> : @inord O O = 0 by apply val_inj; rewrite val_insubd.
    case: j => m; case: m => [j|m]; [|case: m => [j|m j]].
    * have -> : Ordinal j = inord 0 by apply: val_inj; rewrite val_insubd.
      have -> : @inord (S n) O = 0 by apply val_inj; rewrite val_insubd.
      have -> : @inord (S n) (S O) = 1 by apply val_inj; rewrite val_insubd.
      rewrite !mxE; case: splitP => // k; case: k => k; case: k => // k.
      have -> : Ordinal k = inord 0 by apply: val_inj; rewrite val_insubd.
      suff -> : @inord (S O) O = 0 by rewrite mxE.
      by apply val_inj; rewrite val_insubd.
    * have -> : Ordinal j = inord 1 by apply: val_inj; rewrite val_insubd.
      have -> : @inord (S n) (S O) = 1 by apply val_inj; rewrite val_insubd.
      rewrite !mxE !eqxx; case: splitP => //= k.
      rewrite div.modnS /= div.mod0n.
      case: k => k; case: k => //k; case: k => // k _.
      have -> : Ordinal k = inord 1 by apply: val_inj; rewrite val_insubd.
      suff -> : @inord (S O) (S O) = 1 by rewrite mxE.
      by apply val_inj; rewrite val_insubd.
    * have: (m + 2 < 0 + 2)%N by move: j; rewrite n_ez.
      by rewrite ltn_add2r ltn0.
  suff -> : p = to_nD n (row2 0 (-1)).
  + rewrite i_nP oP -row_mx_const betS_nD_2D.
    rewrite /betS betR_ud_2D ltr_pdivlMr ?ltr_pdivrMr ?addr_gt0 ?ltr01 //.
    rewrite mul0r !mul1r ltrDr ltr01 /= andbT eq_inv_scale ?add11_neq0 //.
    apply /eqP; rewrite -matrixP => i j; case: i => m; case: m => // i.
    have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
    have -> : @inord O O = 0 by apply val_inj; rewrite val_insubd.
    case: j => m; case: m => [j|m]; [|case: m => // j].
    * have -> : Ordinal j = inord 0 by apply: val_inj; rewrite val_insubd.
      have -> : @inord (S O) O = 0 by apply val_inj; rewrite val_insubd.
      by rewrite !mxE /= subr0 mulr0.
    * have -> : Ordinal j = inord 1 by apply: val_inj; rewrite val_insubd.
      have -> : @inord (S O) (S O) = 1 by apply val_inj; rewrite val_insubd.
      by rewrite !mxE /= add0r mulrN mulr1 -opprB opprK.
  suff [p0 p1] : p 0 0 = (to_nD n (row2 0 (-1))) 0 0 /\
                 p 0 1 = (to_nD n (row2 0 (-1))) 0 1.
  + rewrite -matrixP => i j; case: i => m; case: m => // i.
    have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
    have -> : @inord O O = 0 by apply val_inj; rewrite val_insubd.
    case: j => m; case: m => [j|m]; [|case: m => // [j|m j]].
    * have -> : Ordinal j = inord 0 by apply: val_inj; rewrite val_insubd.
      suff -> : @inord (S n) O = 0 by rewrite p0.
      by apply val_inj; rewrite val_insubd.
    * have -> : Ordinal j = inord 1 by apply: val_inj; rewrite val_insubd.
      suff -> : @inord (S n) (S O) = 1 by rewrite p1.
      by apply val_inj; rewrite val_insubd.
    * have: (m + 2 < 0 + 2)%N by move: j; rewrite n_ez.
      by rewrite ltn_add2r ltn0.
  rewrite /to_nD !mxE; case: splitP => k; case: k => // k; case: k => // k _.
  have {k} -> : Ordinal k = inord 0 by apply: val_inj; rewrite val_insubd.
  have -> : @inord (S O) O = 0 by apply: val_inj; rewrite val_insubd.
  case: splitP => // k; case: k => k; case: k => // k; case: k => // k.
  have {k} -> : Ordinal k = inord 1 by apply: val_inj; rewrite val_insubd.
  have -> : @inord (S O) (S O) = 1 by apply: val_inj; rewrite val_insubd.
  rewrite !mxE /=; have: p = p 0 0 *: delta_mx 0 0 + p 0 1 *: delta_mx 0 1.
  + rewrite {1}(row_sum_delta p) -matrixP => i j.
    rewrite summxE (bigD1 j) // mxE /= big1 ?addr0; last first.
    * by move => k /negPf kP; rewrite !mxE /= (eq_sym j) kP andbF mulr0.
    case: i => m; case: m => // i.
    have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
    have -> : @inord O O = 0 by apply val_inj; rewrite val_insubd.
    case: j => m; case: m => [j|m]; [|case: m => // [j|m j]].
    * have -> : Ordinal j = inord 0 by apply: val_inj; rewrite val_insubd.
      have -> : @inord (S n) O = 0 by apply val_inj; rewrite val_insubd.
      by rewrite !mxE /= mulr1 mulr0 addr0.
    * have -> : Ordinal j = inord 1 by apply: val_inj; rewrite val_insubd.
      have -> : @inord (S n) (S O) = 1 by apply val_inj; rewrite val_insubd.
      by rewrite !mxE /= mulr1 mulr0 add0r.
    * have: (m + 2 < 0 + 2)%N by move: j; rewrite n_ez.
      by rewrite ltn_add2r ltn0.
  move => {}pE; move: HC2; rewrite {1 2}pE iP /cong opprK addrAC.
  rewrite -{2}(scale1r (delta_mx 0 0)) -scalerBl dotC.
  rewrite -{2}(scale1r (delta_mx 0 0)) -scalerBl eq_sym addrAC.
  rewrite -{2}(scale1r (delta_mx 0 0)) -scalerDl dotC.
  rewrite -{2}(scale1r (delta_mx 0 0)) -scalerDl.
  rewrite !mulmxDl dotC eq_sym dotC !mulmxDl -!scalemxAl.
  rewrite dotC -scalemxAl trmx_delta dotC -scalemxAl trmx_delta.
  rewrite dotC mulmxDl -!scalemxAl trmx_delta.
  rewrite !mul_delta_mx_cond /= mulr0n !scaler0 add0r addr0.
  rewrite mulr1n dotC -scalemxAl trmx_delta dotC -scalemxAl trmx_delta.
  rewrite dotC mulmxDl -!scalemxAl trmx_delta.
  rewrite !mul_delta_mx_cond /= mulr0n !scaler0 add0r addr0 mulr1n.
  rewrite addrC eq_sym addrC add2r_eq !scalerA -subr_eq0 -scalerBl.
  rewrite scaler_eq0; have /negPf-> : @delta_mx R (S O) (S O) 0 0 != 0.
  + apply /eqP; rewrite -matrixP => HF; move: (HF 0 0).
    by rewrite !mxE /=; apply /eqP; rewrite oner_neq0.
  rewrite orbF mulrDl mulrBl !mul1r opprB addrA addrACA -(addrA _ 1).
  rewrite subrr addr0 -2?addrA addrC -!addrA -mulrN opprB -mulrDr.
  rewrite addrACA -addrA (addrC 1) !addrA subrr add0r mulrDr mulr1.
  rewrite -!mulr2n -mulrnA mulrn_eq0 /= => /eqP p0; rewrite p0; split => //.
  move: HC1; rewrite {1}pE p0 scale0r add0r oP iP /cong !subr0.
  rewrite mulNmx dotC -mulNmx opprK trmx_delta.
  rewrite -scalemxAl dotC -scalemxAl trmx_delta !mul_delta_mx_cond /=.
  rewrite !mulr1n scalerA -subr_eq0 -{1}(scale1r (delta_mx 0 0)) -scalerBl.
  rewrite scaler_eq0; have /negPf-> : @delta_mx R (S O) (S O) 0 0 != 0.
  + apply /eqP; rewrite -matrixP => HF; move: (HF 0 0).
    by rewrite !mxE /=; apply /eqP; rewrite oner_neq0.
  rewrite -expr2 subr_eq0 eq_sym sqrf_eq1 orbF => /orP[|]/eqP // p1.
  exfalso; apply i_n_neq_p; rewrite i_nP pE p0 p1 scale0r scale1r add0r.
  by rewrite basis_nth1.
- move: HC2 => [_ HC2]; move: (HC2 n_nz) => {}HC2.
  have {HC1} pP : p *m p^T = delta_mx 0 0.
  + move: HC1; rewrite /cong oP iP !subr0 mulNmx dotC mulNmx opprK.
    by rewrite trmx_delta mul_delta_mx_cond eqxx mulr1n => /eqP ->.
  have {}HC2 : forall j, (0 <= j < n.+1)%N -> p 0 (inord j) = 0.
  + move => j jP; move: jP (HC2 j jP) => /andP[j_ge0 j_lt_n].
    rewrite /cong dist_10_01 nth_basis ?(ltn_trans j_lt_n) //.
    rewrite mulmxDl dotC mulmxDl trmx_delta.
    rewrite dotC mulmxDl dotC trmx_delta !mulNmx dotC mulNmx opprK.
    rewrite mul_delta_mx_cond eqxx mulr1n pP -!addrA add2r_eq.
    rewrite addrC -addrA addrC -{2}(addr0 (delta_mx 0 0)) -addrA add2r_eq.
    have -> : p *m delta_mx (inord j) 0 = (p 0 (inord j))%:M.
    * rewrite -trmx_delta dotC -rowE -matrixP => i k.
      case: i => m; case: m => // i; case: k => m; case: m => // k.
      have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
      have -> : Ordinal k = inord 0 by apply: val_inj; rewrite val_insubd.
      have -> : @inord O O = 0 by apply val_inj; rewrite val_insubd.
      by rewrite !mxE eqxx mulr1n.
    move => /eqP; rewrite -matrixP => p_eq0; move: (p_eq0 0 0).
    rewrite !mxE eqxx mulr1n; move => /eqP; rewrite subr_eq0.
    by rewrite eq_sym -addr_eq0 -mulr2n mulrn_eq0 /= => /eqP.
  rewrite /i_n nth_basis // oP.
  suff -> : p = - delta_mx 0 (inord n.+1).
  + suff: @betR R n.+2 (delta_mx 0 (inord n.+1)) (const_mx 0)
                       (- delta_mx 0 (inord n.+1)) = 1%:R / 2%:R.
    * rewrite /betS => ->; rewrite add0r -mulr2n -scalerMnr scalerMnl.
      rewrite mulr2n addf_divrr ?divff ?(pnatr_eq0 _ 2) // scale1r eqxx.
      rewrite ltr_pdivlMr ?ltr_pdivrMr ?addr_gt0 ?ltr01 //.
      by rewrite mul0r mul1r ltrDr ltr01.
    rewrite /betR /ratio; case: pickP => /= [x xP|/all_v_neq0 H]; last first.
    * exfalso; apply H; apply /eqP/matrixP => HF; move: (HF 0 (inord n.+1)).
      rewrite !mxE !eqxx -mulNrn mulr1n; apply /eqP.
      by rewrite subr_eq0 eq_sym -subr_eq0 opprK (pnatr_eq0 _ 2).
    apply /eqP; rewrite add0r !mxE eqxx /= -mulNrn.
    case: (x =P inord n.+1) => [_ /=|/eqP/negPf HF]; last first.
    * by exfalso; move/eqP: xP; rewrite !mxE /= -mulNrn HF mulr0n addr0.
    by rewrite mulr1n mulNr -mulrN -invrN opprB opprK.
  move: (row_sum_delta p); rewrite big_ord_recr; set pl := BigOp.bigop _ _ _.
  suff /eqP plE : pl == 0.
  + move => {pE}; rewrite plE /= add0r /ord_max.
    have -> : Ordinal (ltnSn n.+1) = inord n.+1
      by apply: val_inj; rewrite val_insubd ltnSn.
    move => pE; suff p_maxE : p 0 (inord n.+1) = - 1
      by move: pE; rewrite p_maxE scaleN1r.
    move: pP; rewrite pE -scalemxAl dotC -scalemxAl trmx_delta.
    rewrite mul_delta_mx scalerA => /eqP.
    rewrite -{2}(scale1r (delta_mx 0 0)) -subr_eq0 -scalerBl.
    rewrite scaler_eq0 => /orP[|/eqP/matrixP HF]; last first.
    * by move/eqP: (HF 0 0); rewrite !mxE eqxx oner_eq0.
    rewrite -expr2 subr_eq0 sqrf_eq1 => /orP[|/eqP->]; last first.
    * by rewrite !mxE eqxx mulr1.
    move => /eqP p_maxE; move: pE; rewrite p_maxE scale1r => pE.
    by move: i_n_neq_p; rewrite pE /i_n nth_basis.
  rewrite /pl /= (eq_big_seq (fun i => 0)) /=.
  + by rewrite big_const iter_fix // addr0.
  move => i; rewrite /index_enum => _.
  have iP : (0 <= i < n.+1)%N.
  * rewrite leq0n /=; move: iP; case: i => m i iP.
    suff -> : Ordinal i = inord m by rewrite inordK.
    by apply: val_inj; rewrite val_insubd i.
  apply /matrixP => j k; rewrite !mxE; case: j => m; case: m => // j.
  have -> : Ordinal j = inord 0 by apply: val_inj; rewrite val_insubd.
  have -> : @inord O O = 0 by apply val_inj; rewrite val_insubd.
  set i' := widen_ord _ _; case: (k =P i') => /=; rewrite ?mulr0 //.
  rewrite mulr1 -(HC2 i iP) /i' /widen_ord => _.
  suff -> : Ordinal (widen_ord_proof i (leqnSn n.+1)) = inord i by [].
  move: iP => /andP[_ iP]; apply: val_inj.
  by rewrite val_insubd (ltn_trans iP).
Qed.

Lemma upper_dim : upper_dimP _ (@bet R (n.+2)) (@cong R (n.+2)) n.+2 o i basis.
Proof.
move => p H [NE1 [HB [HC1 HC2]]] NE2; move: (upper_dimS NE1 HB HC1 HC2 NE2).
by rewrite /bet => ->; rewrite orbT.
Qed.

End RfTarskinp2D.
