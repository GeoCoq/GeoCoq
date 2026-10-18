From mathcomp Require Import ssreflect.
From mathcomp
Require Import ssrbool ssrfun ssrnat eqtype choice seq.
From mathcomp
Require Import tuple fintype bigop.
From mathcomp
Require Import ssralg ssrnum matrix.
From mathcomp
Require Import zmodp.
From mathcomp
Require Import ring lra.

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

Lemma inord0 m : @inord m 0 = 0.
Proof. by apply: val_inj => /=; rewrite inordK. Qed.

Lemma inord1 m : @inord m.+1 1 = 1.
Proof. by apply: val_inj => /=; rewrite inordK. Qed.

Lemma rowP2 (u v : 'rV[R]_2) : u 0 0 = v 0 0 -> u 0 1 = v 0 1 -> u = v.
Proof. by move=> e0 e1; apply/eqP; rewrite vector2_eq e0 e1 !eqxx. Qed.

Lemma delta_to_nD (k : 'I_2) :
  delta_mx 0 (lshift n k) = @to_nD R n (delta_mx 0 k).
Proof. by rewrite delta_mx_lshift. Qed.

Lemma dot_delta (u : 'rV[R]_(n.+2)) j :
  POF_to_Tarski.dot R _ u (delta_mx 0 j) = u 0 j.
Proof. by rewrite dotE trmx_delta -colE mxE. Qed.

Lemma basis_nth0 : delta_mx 0 (inord 0) = @to_nD R n (row2 1 0).
Proof.
have -> : inord 0 = lshift n (0 : 'I_2) by apply: val_inj => /=; rewrite inordK.
by rewrite delta_to_nD; congr to_nD; apply: rowP2; rewrite !mxE.
Qed.

Lemma basis_nth1 : delta_mx 0 1 = @to_nD R n (row2 0 1).
Proof.
have -> : 1 = lshift n (1 : 'I_2) :> 'I_(2 + n) by apply: val_inj.
by rewrite delta_to_nD; congr to_nD; apply: rowP2; rewrite !mxE.
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

Lemma betS_o_i_basis_nth0 : betS i o (delta_mx 0 (inord 0)).
Proof.
rewrite basis_nth0 /i /o betS_nD_2D; apply: (betS_intro (r := 2%:R^-1)).
- by rewrite row2_eq eqxx andbT eq_sym -subr_eq0 opprK add11_neq0.
- by rewrite invr_gt0 ltr0n.
- by rewrite invf_lt1 ?ltr0n // ltr1n.
- by apply: rowP2; rewrite !mxE /=; field.
Qed.

Lemma bet_o_i_basis_nth0 : bet i o (delta_mx 0 (inord 0)).
Proof. by rewrite /bet betS_o_i_basis_nth0 orbT. Qed.

Lemma oP : o = const_mx 0.
Proof.
by rewrite /o (_ : row2 0 0 = 0) ?to_nD0 //; apply: rowP2; rewrite !mxE.
Qed.

Lemma iP : i = - (delta_mx 0 0).
Proof.
have -> : delta_mx 0 0 = delta_mx 0 (inord 0) :> 'rV[R]_(2 + n)
  by rewrite inord0.
rewrite basis_nth0 -scaleN1r to_nD_scale /i; congr to_nD.
by apply: rowP2; rewrite !mxE /= ?mulr1 ?mulr0.
Qed.

Lemma lower_dim_all1 j :
  (0 <= j < n.+2)%N -> cong o i o (tnth basis (inord j)).
Proof.
move => /andP[j_ge0 j_le_np2]; rewrite nth_basis // oP iP !congE.
by rewrite !subr0 mulNmx mulmx_trC mulNmx opprK !trmx_delta !mul_delta_mx.
Qed.

Lemma lower_dim_all2 j k :
  (0 <= j < k)%N -> (k < n.+2)%N ->
  cong (tnth basis (inord j)) (tnth basis (inord k))
       i                      (delta_mx 0 (inord 1)).
Proof.
move => /andP[j_ge0 j_lt_k] k_lt_np2; rewrite !nth_basis ?(ltn_trans j_lt_k) //.
rewrite iP !congE mulmxBl mulmx_trC mulmxBl trmx_delta mulmx_trC mulmxBl.
rewrite trmx_delta.
rewrite !mul_delta_mx !mul_delta_mx_cond (eq_sym (inord k)) opprK.
rewrite mulmxDl mulmx_trC mulmxDl trmx_delta mulmx_trC mulmxDl trmx_delta.
rewrite !mul_delta_mx !mul_delta_mx_cond (eq_sym (inord 1)).
rewrite inord1 /=.
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

Lemma dist_10_01 :
  (delta_mx 0 (inord 1) - i) *m (delta_mx 0 (inord 1) - i)^T =
  delta_mx 0 0 + delta_mx 0 0.
Proof.
rewrite iP opprK mulmxDl mulmx_trC mulmxDl trmx_delta mulmx_trC mulmxDl.
rewrite trmx_delta.
rewrite !mul_delta_mx_cond !eqxx mulr1n eq_sym inord1 /=.
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
move=> _ _; set new_basis := rot_tuple 1 (belast_tuple p basis).
rewrite -big_andb_and -big_pairs_andb_and !big_all.
move=> /allP HC1 /allP HC2 i_n_neq_p.
have pE : tnth new_basis (inord n.+1) = p.
- rewrite /basis /tnth /=.
  have -> : nat_of_ord (@inord n.+1 n.+1) = (size new_basis).-1.
  + by rewrite inordK // size_rot size_belast size_map size_iota.
  by rewrite nth_last last_cat.
have e_e (j : 'I_n.+2) :
  POF_to_Tarski.dot R _ (delta_mx 0 j) (delta_mx 0 j) = 1.
  by rewrite dot_delta mxE !eqxx.
have pp : POF_to_Tarski.dot R _ p p = 1.
  move: (HC1 n.+1); rewrite mem_index_iota ltnSn /= => /(_ isT).
  rewrite pE /cong oP iP !subr0 dot2N e_e => /eqP <- //.
have pj0 j : (j < n.+1)%N -> p 0 (inord j) = 0.
  move=> jn; move: (HC2 j); rewrite mem_index_iota /= ltnS (ltnW jn) big_all.
  move=> /(_ isT) /allP /(_ n.+1); rewrite mem_index_iota ltnSn jn /=.
  rewrite pE nth_new_basis // /cong iP opprK => /(_ isT).
  have [n0|n_nz] := eqVneq n 0%N.
    have j0 : j = 0%N by move: jn; rewrite n0; case: j.
    have -> : tnth new_basis (inord 1) = p.
      by rewrite -pE; congr tnth; apply: val_inj; rewrite /= !inordK // n0.
    rewrite j0 inord0 !dot2B !dot2D pp e_e dot_delta => /eqP; lra.
  rewrite nth_new_basis ?ltnS ?lt0n // inord1 !dot2B !dot2D pp !e_e.
  rewrite !dot_delta !mxE eqxx /= => /eqP; lra.
set i_n := tnth basis (inord n.+1); rewrite /i_n nth_basis // oP.
set e := delta_mx 0 (inord n.+1).
have pE' : p = p 0 (inord n.+1) *: e.
  apply/rowP => k; rewrite /e !mxE /=.
  have [->|kn] := eqVneq k (inord n.+1); first by rewrite mulr1n mulr1.
  rewrite mulr0n mulr0; have klt : (k < n.+1)%N.
    move: kn (ltn_ord k); rewrite -val_eqE /= inordK // ltnS leq_eqVlt.
    by move=> /negPf ->.
  by rewrite -(pj0 k klt) inord_val.
set c := p 0 (inord n.+1) in pE' *.
have [p1|pm1] : c = 1 \/ c = -1.
  move: pp; rewrite pE' dotZl dotZr e_e mulr1 => /eqP.
  by rewrite -expr2 sqrf_eq1 => /orP[/eqP->|/eqP->]; [left|right].
  by exfalso; apply: i_n_neq_p; rewrite /i_n nth_basis // pE' p1 scale1r.
rewrite pE' pm1 scaleN1r; apply: (betS_intro (r := 2%:R^-1)).
- apply/eqP => /rowP/(_ (inord n.+1)); rewrite /e !mxE ?eqxx /= ?mulr1n; lra.
- by rewrite invr_gt0 ltr0n.
- by rewrite invf_lt1 ?ltr0n // ltr1n.
- by apply/rowP => k; rewrite !mxE; field.
Qed.

Lemma upper_dim : upper_dimP _ (@bet R (n.+2)) (@cong R (n.+2)) n.+2 o i basis.
Proof.
move => p H [NE1 [HB [HC1 HC2]]] NE2; move: (upper_dimS NE1 HB HC1 HC2 NE2).
by rewrite /bet => ->; rewrite orbT.
Qed.

End RfTarskinp2D.