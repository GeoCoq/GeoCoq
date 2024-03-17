Require Import mathcomp.ssreflect.ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq order.
From mathcomp
Require Import fintype finset finfun bigop.
From mathcomp
Require Import ssralg ssrnum path generic_quotient matrix mxalgebra vector.
From mathcomp
Require Import zmodp.
From mathcomp Require Import tuple fintype bigop.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Order.Theory Num.Theory.
Local Open Scope ring_scope.

Require Import GeoCoq.Algebraic.Counter_models.nD.independence.
Require Import GeoCoq.Algebraic.POF_to_Tarski.
Require Import GeoCoq.Algebraic.Counter_models.nD.dimensional_axioms.

Section Tarskinp3D.

Variable n : nat.
Variable R : realFieldType.

Definition o := @to_nD R n.+1 (row2   0  0).

Definition i := @to_nD R n.+1 (row2 (-1) 0).

Definition basis : n.+2.-tuple 'rV_(n.+3) :=
  map_tuple (fun i => @delta_mx R _ _ 0 (inord i)) (iota_tuple n.+2 0).

Lemma nth_basis i : (i < n.+2)%N -> tnth basis (inord i) = delta_mx 0 (inord i).
Proof.
move => iP; rewrite /basis /tnth (@nth_map nat 0%N) ?size_iota //.
by rewrite inordK // nth_iota.
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
have -> : @delta_mx R (S O) (3 + n) 0 0 = delta_mx 0 (inord 0).
- by have -> : @inord (S (S n)) O = 0 by apply val_inj; rewrite val_insubd.
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
have -> /= : @inord (S (S n)) (S O) = 1 by apply: val_inj; rewrite val_insubd.
case: (inord j =P inord k) => [HF|_/=]; last first.
- by rewrite mulr0n subr0 sub0r opprK addr0 add0r.
have: val (@inord n.+2 j) = val (@inord n.+2 k) by rewrite HF.
have lt_np2_np3 : (n.+2 < n.+3)%N by [].
rewrite !val_insubd ?k_lt_np2__k_lt_np3.
rewrite ?(ltn_trans _ lt_np2_np3) // ?(ltn_trans j_lt_k) //= => {}HF.
by move: j_lt_k; rewrite HF ltnn.
Qed.

Lemma lower_dim : lower_dimP _ (@bet R (n.+3)) (@cong R (n.+3)) n.+2 o i basis.
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
rewrite -(addn1 l) 1?iota_add 1?iotaD belast_cat nth_cat size_belast size_iota.
case: (m =P l) => [-> {IHl m_lt_lp1 m}|/eqP lm_neq]; last first.
- suff m_lt_l : (m < l)%N by rewrite m_lt_l IHl.
  by move: (ltnSE m_lt_lp1) lm_neq; rewrite leq_eqVlt => /orP[/eqP ->/eqP|->].
rewrite ltnn subnn /= -nth_last size_iota.
case: (l =P O) => [-> //|/eqP l_nz]; rewrite nth_iota ?ltn_predL ?lt0n //.
by move: l_nz; case: l.
Qed.

Lemma last_new_basis p :
  tnth (@rot_tuple n.+2 1 _ (belast_tuple p basis)) (inord n.+1) = p.
Proof.
rewrite /basis /tnth /=.
have -> : nat_of_ord (@inord n.+1 n.+1) =
          (size (@rot_tuple n.+2 1 _ (belast_tuple p basis))).-1.
- by rewrite inordK // size_rot size_belast size_map size_iota.
by rewrite nth_last last_cat.
Qed.

Lemma upper_dim_all1 j p :
  (0 <= j < n.+2)%N ->
  cong o i o p ->
  cong o i o (tnth (@rot_tuple n.+2 1 _ (belast_tuple p basis)) (inord j)).
Proof.
move => /andP[j_ge0 j_le_np2]; move: j_le_np2; rewrite ltnS leq_eqVlt.
move => /orP[/eqP ->|j_le_np1]; first by rewrite last_new_basis.
rewrite nth_new_basis // oP iP /cong.
by rewrite !subr0 mulNmx dotC mulNmx opprK !trmx_delta !mul_delta_mx.
Qed.

Lemma upper_dim_all2 j k :
  (0 <= j < k)%N -> (k < n.+2)%N ->
  cong (tnth (@rot_tuple n.+2 1 _ (belast_tuple (delta_mx 0 (inord n.+2)) basis))
                                  (inord j))
       (tnth (@rot_tuple n.+2 1 _ (belast_tuple (delta_mx 0 (inord n.+2)) basis))
                                  (inord k))
       i
       (delta_mx 0 (inord 1)).
Proof.
move => /andP[j_ge0 j_lt_k] HE; move: HE j_lt_k; rewrite ltnS leq_eqVlt.
move => /orP[/eqP ->|j_lt_np1] j_lt_k.
- rewrite last_new_basis !nth_new_basis // iP /cong.
  rewrite mulmxBl dotC mulmxBl trmx_delta dotC mulmxBl trmx_delta.
  rewrite !mul_delta_mx_cond !eqxx (eq_sym (inord j)) opprK.
  rewrite mulmxDl dotC mulmxDl trmx_delta dotC mulmxDl trmx_delta.
  rewrite !mul_delta_mx !mul_delta_mx_cond (eq_sym (inord 1)).
  have -> /= : @inord (S (S n)) (S O) = 1 by apply: val_inj; rewrite val_insubd.
  have -> /= : (@inord n.+2 n.+2 == @inord n.+2 j) = false; last first.
  + by rewrite mulr0n mulr1n subr0 sub0r opprK addr0 add0r.
  apply /negbTE/eqP => HF.
  have {HF} : val (@inord n.+2 n.+2) = val (@inord n.+2 j) by rewrite HF.
  rewrite !val_insubd ltnSn (ltn_trans j_lt_k) //= => jP.
  by move: j_lt_k; rewrite -jP ltnNge (ltn_trans (ltnSn n)).
rewrite !nth_new_basis ?(ltn_trans j_lt_k) //.
rewrite iP /cong mulmxBl dotC mulmxBl trmx_delta dotC mulmxBl trmx_delta.
rewrite !mul_delta_mx !mul_delta_mx_cond (eq_sym (inord k)) opprK.
rewrite mulmxDl dotC mulmxDl trmx_delta dotC mulmxDl trmx_delta.
rewrite !mul_delta_mx !mul_delta_mx_cond (eq_sym (inord 1)).
have -> /= : @inord (S (S n)) (S O) = 1 by apply: val_inj; rewrite val_insubd.
case: (inord j =P inord k) => [HF|_/=]; last first.
- by rewrite mulr0n subr0 sub0r opprK addr0 add0r.
have: val (@inord n.+2 j) = val (@inord n.+2 k) by rewrite HF.
have lt_np1_np3 : (n.+1 < n.+3)%N by [].
rewrite !val_insubd ?(ltn_trans _ lt_np1_np3) // ?(ltn_trans j_lt_k) //.
by move => {}HF; move: j_lt_k; rewrite HF ltnn.
Qed.

Lemma to_nD'E : (addn n.+1 (S (S O)) = n.+3).
Proof. by rewrite -(addn1 1) addnA !addn1 /eqP. Qed.

Definition to_nD' (v : 'rV[R]_2) : 'rV[R]_(n.+3) :=
  castmx (erefl (S O), to_nD'E) (row_mx (@const_mx R 1 n.+1 0) v).

Lemma a2DE : o = to_nD' (@a2D R).
Proof.
apply /rowP => i; rewrite /a2D /to_nD' mxE castmxE /=; case: splitP => j jP.
- rewrite !mxE; case: splitP => k; rewrite mxE.
  + by move: jP; case: j => j; case: j => [//|j]; case: j.
  + move: jP; case: j => j; case: j => [|j]; [|case: j];
    by case: k => k; case: k => [|k]; [|case: k].
- rewrite !mxE; case: splitP => k; rewrite mxE //.
  by case: k => k; case: k => [|k]; [|case: k].
Qed.

Lemma b2DE : delta_mx 0 (inord n.+2) = to_nD' (@b2D R).
Proof.
apply /rowP => i; rewrite /b2D /to_nD' castmxE !mxE /=; case: splitP => j /= jP.
- suff -> : (i == inord n.+2) = false by rewrite mxE.
  move: jP; case: i => i ;case: j => j /= jP iP ijE; move: iP jP.
  rewrite -ijE => {ijE} iP jP.
  have -> : Ordinal iP =  inord i by apply: val_inj; rewrite val_insubd iP.
  move: jP; case: (i =P n.+2) => [->|iNE _];
  first by rewrite ltnNge (ltn_trans (ltnSn n)).
  apply /eqP => HF; apply iNE; move: HF => /= => {iNE} iE.
  have {iE} : val (@inord n.+2 i) = val (@inord n.+2 n.+2) by rewrite iE.
  by rewrite !val_insubd iP ltnSn.
- rewrite mxE /=; have {jP} -> : i = inord (n + j).+1.
  + by apply: val_inj; rewrite -addSn -jP val_insubd ltn_ord.
  case: j => j; case: j => [/= jP|j]; [|case: j => //= jP];
  rewrite ?addn1 ?eqxx // addn0; case: (inord n.+1 =P inord n.+2) => // HF.
  have {HF} : val (@inord n.+2 n.+1) = val (@inord n.+2 n.+2) by rewrite HF.
  rewrite !val_insubd ltnSn (ltn_trans (ltnSn n.+1)) ?ltnSn //.
  by move => /eqP nE; move: nE; rewrite eqn_leq -ltn_predRL /= ltnn andbF.
Qed.

Lemma c2DE : delta_mx 0 (inord n.+1) = to_nD' (@c2D R).
Proof.
apply /rowP => i; rewrite /c2D /to_nD' castmxE !mxE /=; case: splitP => j /= jP.
- suff -> : (i == inord n.+1) = false by rewrite mxE.
  move: jP; case: i => i ;case: j => j /= jP iP ijE; move: iP jP.
  rewrite -ijE => {ijE} iP jP.
  have -> : Ordinal iP =  inord i by apply: val_inj; rewrite val_insubd iP.
  move: jP; case: (i =P n.+1) => [->|iNE _]; first by rewrite ltnNge ltnSn.
  apply /eqP => HF; apply iNE; move: HF => /= => {iNE} iE.
  have {iE} : val (@inord n.+2 i) = val (@inord n.+2 n.+1) by rewrite iE.
  by rewrite !val_insubd iP (ltn_trans (ltnSn n.+1)) ?ltnSn.
- rewrite mxE /=; have {jP} -> : i = inord (n + j).+1.
  + by apply: val_inj; rewrite -addSn -jP val_insubd ltn_ord.
  case: j => j; case: j => [/= jP|j]; [|case: j => //= jP];
  rewrite ?addn0 ?eqxx // addn1; case: (inord n.+2 =P inord n.+1) => // HF.
  have {HF} : val (@inord n.+2 n.+2) = val (@inord n.+2 n.+1) by rewrite HF.
  rewrite !val_insubd ltnSn (ltn_trans (ltnSn n.+1)) ?ltnSn //.
  by move => /eqP nE; move: nE; rewrite eqn_leq ltnn.
Qed.

Lemma eq_nD'_2D (p q : 'rV[R]_2) : to_nD' p == to_nD' q = (p == q).
Proof.
apply/eqP/eqP => [|->//]; rewrite /to_nD' => /rowP pqP.
apply /rowP => i; move: (pqP (cast_ord to_nD'E (rshift n.+1 i))).
rewrite !castmxE !mxE cast_ord_id; case: splitP; rewrite ?mxE /= => j.
- move => /eqP HF; exfalso; move: HF.
  by rewrite eqn_leq leqNgt (ltn_addr i (ltn_ord j)).
- case: i => i; case: j => j jP iP; move: iP jP.
  case: i => [|i]; [|case: i => //] => iP;
  case: j => [|j]; [|case: j| |case: j] => // jP /=; rewrite ?addn0 ?addn1.
  + have -> : Ordinal iP = inord 0 by apply: val_inj; rewrite val_insubd.
    by have -> : Ordinal jP = inord 0 by apply: val_inj; rewrite val_insubd.
  + by move => /eqP HF; move: HF; rewrite eqn_leq -ltn_predRL ltnn andbF.
  + by move => /eqP HF; move: HF; rewrite eqn_leq ltnn.
  + have -> : Ordinal iP = inord 1 by apply: val_inj; rewrite val_insubd.
    by have -> : Ordinal jP = inord 1 by apply: val_inj; rewrite val_insubd.
Qed.

Lemma to_nD'B (p q : 'rV[R]_2) : to_nD' p - to_nD' q = to_nD' (p - q).
Proof.
rewrite /to_nD'; apply /rowP => i; rewrite !mxE !castmxE !mxE.
by case: splitP => j; rewrite !mxE ?subr0.
Qed.

Lemma to_nD'_scale (a : R) (p : 'rV[R]_2) : a *: to_nD' p = to_nD' (a *: p).
Proof.
rewrite /to_nD'; apply /rowP => i; rewrite mxE !castmxE !mxE.
by case: splitP => j; rewrite !mxE ?mulr0.
Qed.

(* Can be replaced with enum_ordSr once
   support for older versions of mathcomp is dropped. *)
Lemma my_enum_ordSr m :
  enum 'I_m.+1 = rcons (map (widen_ord (leqnSn _)) (enum 'I_m)) ord_max.
Proof.
apply: (inj_map val_inj); rewrite val_enum_ord.
rewrite -[in iota _  _]addn1 1?iota_add 1?iotaD /=.
rewrite cats1 map_rcons; congr (rcons _ _).
by rewrite -map_comp/= (@eq_map _ _ _ val) ?val_enum_ord.
Qed.

Lemma pick_to_nD' (a b : 'rV[R]_2) i :
  [pick k | (b - a) 0 k != 0 ] = Some i ->
  [pick k | (to_nD' b - to_nD' a) 0 k != 0 ] =
  Some (cast_ord to_nD'E (rshift n.+1 i)).
Proof.
rewrite /pick.
set p1 := (fun k : 'I_2 => (b - a) 0 k != 0).
set p2 := (fun k => (to_nD' b - to_nD' a) 0 k != 0).
suff: (ohead (enum p2) =
       ohead (map (fun k => cast_ord to_nD'E (rshift n.+1 k)) (enum p1))).
  move => ->; case: (enum _) (mem_enum p1) => [//|h t /= _ H].
  by have -> : h = i by move: H; apply: Some_inj.
move: i => _; rewrite /enum_mem -enumT 2?my_enum_ordSr -!cats1 filter_cat.
rewrite filter_map filter_cat map_cat -catA -filter_map -!map_comp.
set t_nil := @filter (Finite.sort (ordinal_finType (S (S (S n))))) _ _.
have: (t_nil == [::]) => [|/eqP->]; rewrite ?cat0s.
- rewrite /t_nil -size_eq0 -all_pred0 all_filter; apply /allP => x.
  rewrite -enumT /= => xP; move/mapP: xP => [] x0 /mapP [] x1 _ -> ->.
  rewrite /in_mem /p2 implybF /to_nD' /= !mxE !castmxE cast_ord_id !mxE /=.
  case: splitP => i; first by rewrite mxE subrr eqxx.
  move => /= /eqP HF; move: HF; rewrite eqn_leq andbC leqNgt.
  by rewrite (ltn_addr i (ltn_ord x1)).
apply /eqP; rewrite eq_sym /enum_mem -enumT 2?my_enum_ordSr -!cats1 filter_cat.
have -> : enum 'I_0 = [::] by apply/eqP; rewrite -size_eq0 size_enum_ord.
rewrite cat0s /filter /=.
have {t_nil} <- : (ord_max \in p1) = (ord_max \in p2).
- rewrite /in_mem /p1 /p2 /to_nD' /= !mxE !castmxE !mxE cast_ord_id /=.
  case: splitP => i /= /eqP.
  + by rewrite eqn_leq leqNgt (ltn_trans (ltn_ord i)) ?ltnSn.
  + case: i => i; case: i => i; first by rewrite addn0 eqn_leq ltnn.
    case: i => //= i _; suff -> : Ordinal i = ord_max by [].
    by apply: val_inj.
suff <- : (widen_ord (leqnSn 1) ord_max \in p1) =
          (widen_ord (leqnSn n.+2) ord_max \in p2).
- have E0 : cast_ord to_nD'E (rshift n.+1 (widen_ord (leqnSn 1) ord_max)) =
            widen_ord (leqnSn n.+2) ord_max by apply: val_inj; rewrite /= addn0.
  case: (widen_ord (leqnSn 1) ord_max \in p1); case: (ord_max \in p1);
  rewrite /= ?E0 ?eqxx //.
  suff -> : cast_ord to_nD'E (rshift n.+1 ord_max) = ord_max by [].
  by apply: val_inj; rewrite /= addn1.
rewrite /in_mem /p1 /p2 /to_nD' /= !mxE !castmxE !mxE cast_ord_id /=.
case: splitP => i /= /eqP; first by rewrite eqn_leq leqNgt (ltn_ord i).
case: i => i; case: i => i /=.
- have -> : Ordinal i = 0 by apply: val_inj.
  suff -> : widen_ord (leqnSn 1) ord_max = 0 by [].
  by apply: val_inj.
- by case: i => // i; rewrite addn1 eqn_leq andbC leqNgt ltnSn.
Qed.

Lemma betR_nD'_2D (a b c : 'rV[R]_2) :
  betR (to_nD' a) (to_nD' b) (to_nD' c) = betR a b c.
Proof.
apply /eqP; rewrite /betR/ ratio eq_sym; move: (@pick_to_nD' a c).
case: pickP => [i _ H|HF _].
  rewrite (H i) // /to_nD' eq_sym !mxE !castmxE /= cast_ordK cast_ord_id.
  by rewrite ?row_mxEr.
case: pickP => //= x; rewrite /to_nD' !mxE !castmxE !mxE /=.
case: splitP => [?|i ? iP]; rewrite ?subrr ?eqxx //.
by move: iP (HF i); rewrite cast_ord_id !mxE => ->.
Qed.

Lemma betS_nD'_2D (a b c : 'rV[R]_2) :
  betS (to_nD' a) (to_nD' b) (to_nD' c) = betS a b c.
Proof. by rewrite /betS betR_nD'_2D !to_nD'B to_nD'_scale eq_nD'_2D. Qed.

Lemma bet_nD'_2D (a b c : 'rV[R]_2) :
  bet (to_nD' a) (to_nD' b) (to_nD' c) = bet a b c.
Proof. by rewrite /bet betS_nD'_2D /betE !eq_nD'_2D. Qed.

Lemma upper_dim :
  ~ upper_dimP _ (@bet R (n.+3)) (@cong R (n.+3)) n.+2 o i basis.
Proof.
pose p : 'rV[R]_(n.+3) := delta_mx 0 (inord n.+2).
have HC : cong o i o p.
- rewrite oP iP /p /cong !subr0  mulNmx dotC mulNmx opprK.
  by rewrite !trmx_delta !mul_delta_mx.
pose new_basis := rot_tuple 1 (belast_tuple p basis).
have HNE : tnth basis (inord n.+1) <> p.
- rewrite nth_basis // /p -!row1 => HF; move: (row_eq HF) => {}HF.
  move: (HF (inord n.+1)); rewrite !mxE eqxx.
  case: (inord n.+2 =P inord n.+1) => {HF} [HF|_];
  last by apply /eqP; rewrite oner_neq0.
  have: val (@inord n.+2 n.+2) == val (@inord n.+2 n.+1) by rewrite HF.
  rewrite !val_insubd (ltn_trans (ltnSn n.+1)) ltnSn //.
  by rewrite eqn_leq leqnSn ltnn.
have bP : lower_dimP _ (@bet R (n.+3)) (@cong R (n.+3)) n.+2 o i new_basis.
- rewrite /lower_dimP /orthonormal_basis /= nth_new_basis //.
  split; first by apply i_neq_basis_nth0.
  split; first by rewrite bet_o_i_basis_nth0.
  split; [apply big_andb_and|apply big_pairs_andb_and]; rewrite big_all.
  + by apply /allP => j jP; rewrite upper_dim_all1 // -mem_index_iota.
apply /allP => j jP; rewrite big_all; apply /allP => k kP.
move: jP kP; rewrite !mem_index_iota => /andP[j_ge0 _] /andP[j_lt_k k_le_np2].
case: (n =P O) => [n_ez|/eqP n_nz]; last first.
- by rewrite (@nth_new_basis (S O)) ?upper_dim_all2 // -ltn_predRL /= lt0n.
have pP : tnth new_basis (inord 1) = p.
- suff -> : @inord (S n) (S O) = @inord (S n) (S n) by rewrite last_new_basis.
  by rewrite n_ez.
have {k_le_np2} : (k <= 1)%N by move: k_le_np2; rewrite n_ez.
rewrite leq_eqVlt ltnS leqn0 => /orP[/eqP kP|/eqP kP]; last first.
- by move: j_lt_k; rewrite kP => ?; rewrite pP ?nth_new_basis ?n_ez.
move: j_lt_k; rewrite kP => j_lt_k; rewrite pP ?nth_new_basis ?n_ez // /cong.
rewrite iP /p n_ez mulmxBl dotC mulmxBl trmx_delta dotC mulmxBl trmx_delta.
rewrite !mul_delta_mx !mul_delta_mx_cond (eq_sym (inord j)) opprK.
rewrite mulmxDl dotC mulmxDl trmx_delta dotC mulmxDl trmx_delta.
rewrite !mul_delta_mx !mul_delta_mx_cond !(eq_sym (inord 2)).
have inord2P : @inord (S (S O)) (S (S O)) = 1 + 1.
- by apply: val_inj; rewrite val_insubd.
suff -> /= : (@inord (S (S O)) j == inord 2) = false.
- by rewrite inord2P mulr0n subr0 !add0r opprK addr0.
apply /negbTE/eqP => HF.
have: val (@inord (S (S O)) j) = val (@inord (S (S O)) 2) by rewrite HF.
rewrite !val_insubd (ltn_trans j_lt_k) //= => {HF} jE.
by move: j_lt_k; rewrite jE ltnNge.
move => HF; move: (HF (delta_mx 0 (inord n.+2)) lower_dim bP HNE).
suff {HNE bP HF} -> : bet (tnth basis (inord n.+1)) o p = false by [].
rewrite nth_basis // /p a2DE b2DE c2DE bet_nD'_2D /bet /betE.
rewrite ca_neq_2D ab_neq_2D /= /betS.
suff [->|->] : betR (c2D R) (a2D R) (b2D R) = 0 \/
               betR (c2D R) (a2D R) (b2D R) = 1 by rewrite !ltxx !andbF.
rewrite /betR a2D_eq0 add0r /b2D /c2D /ratio; case: pickP => /= [x|/all_v_neq0 H];
last by exfalso; apply H; rewrite subr_eq0 bc_neq_2D.
rewrite !mxE; case: x => x; case: x => [|x]; [|case: x => //]; move => i.
- have -> : Ordinal i = inord 0 by apply: val_inj; rewrite val_insubd.
  have -> /= : @inord (S O) O = 0 by apply val_inj; rewrite val_insubd.
  by rewrite !add0r => HNE; rewrite divff //; tauto.
- have -> : Ordinal i = inord 1 by apply: val_inj; rewrite val_insubd.
  have -> /= : @inord 1 1 = 1 by apply val_inj; rewrite val_insubd.
  by rewrite subr0 divr1 oppr0; tauto.
Qed.

End Tarskinp3D.
