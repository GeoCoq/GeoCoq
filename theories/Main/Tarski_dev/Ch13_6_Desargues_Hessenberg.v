(* Gabriel Braun April 2013 *)

Require Export GeoCoq.Main.Tarski_dev.Ch13_5_Pappus_Pascal.

Section Desargues_Hessenberg.

Context `{TE:Tarski_euclidean}.

Lemma l13_15_1 : forall A B C A' B' C' O,
  ~ Col A B C -> ~ Par O B A C -> Coplanar O B A C ->
  Par_strict A B A' B' -> Par_strict A C A' C'->
  Col O A A' -> Col O B B' -> Col O C C' ->
  Par B C B' C'.
Proof.
    intros.
    assert(~Col B A' B').
      intro.
      apply H2.
      exists B.
      split; Col.
    assert(~Col A A' B').
      intro.
      apply H2.
      exists A.
      split; Col.
    assert(B <> O).
      intro.
      subst B.
      apply H2.
      exists A'.
      split; Col.
    assert(A <> O).
      intro.
      subst A.
      apply H2.
      exists B'.
      split; Col.
    assert(~ Col A' A C).
      eapply (par_not_col A' C').
        Par.
      Col.
    assert(C <> O).
      intro.
      subst C.
      apply H11.
      Col.
    assert(~Col O A B).
      intro.
      apply H2.
      exists O.
      split.
        Col.
      assert(Col O A B').
        apply (col_transitivity_1 _ B); Col.
      apply (col_transitivity_1 _ A); Col.
    assert(~Col O A C).
      intro.
      apply H3.
      exists O.
      split.
        Col.
      assert(Col O A C').
        apply (col_transitivity_1 _ C); Col.
      apply (col_transitivity_1 _ A); Col.
    assert(~ Col A' B' C').
      intro.
      apply H.
      assert(Par A' C' A B).
        apply(par_col_par_2 A' B' A B C').
          apply par_strict_distinct in H3.
          spliter.
          auto.
          auto.
        left.
        Par.
      assert(Par A C A B).
        apply(par_trans A C A' C'); Par.
      induction H17.
        apply False_ind.
        apply H17.
        exists A.
        split; Col.
      spliter; Col.
    induction(col_dec O B C).
      right.
      repeat split.
        intro.
        subst C.
        apply H.
        Col.
        intro.
        subst C'.
        apply H15.
        Col.
        assert(Col O B C').
          apply (col_transitivity_1 _ C); Col.
        apply (col_transitivity_1 _ O); Col.
      assert(Col O C B').
        apply (col_transitivity_1 _ B); Col.
      apply (col_transitivity_1 _ O); Col.
    assert(B' <> O).
      intro.
      subst B'.
      apply H8.
      Col.
    assert(B' <> O).
      intro.
      subst B'.
      apply H8.
      Col.
    assert(A' <> O).
      intro.
      subst A'.
      apply H7.
      Col.
    assert(~ Col A A' C').
      apply (par_not_col A C).
        Par.
      Col.
    assert(C' <> O).
      intro.
      subst C'.
      apply H20.
      Col.
    assert(~Col O A' B').
      intro.
      apply H2.
      exists O.
      split.
        assert(Col O A' B).
          apply (col_transitivity_1 _ B'); Col.
        apply (col_transitivity_1 _ A'); Col.
      Col.
    assert(~Col O A' C').
      intro.
      apply H3.
      exists O.
      split.
        ColR.
      Col.
    assert(~Col B' A B).
      intro.
      apply H2.
      exists B'.
      Col.
    assert(~Col A' A B).
      intro.
      apply H2.
      exists A'.
      split; Col.
    (********** construct L *********)
    assert(exists C : Tpoint, exists D : Tpoint, C <> D /\ Par O B C D /\ Col A C D).
      apply(parallel_existence O B A).
      auto.
    ex_and H26 X.
    ex_and H27 Y.
    assert(Coplanar O B X A) by (apply col_cop__cop with Y; Col; Cop).
    assert(Coplanar O B Y A) by (apply col_cop__cop with X; Col; Cop).
    assert(exists L : Tpoint, Col L X Y /\ Col L A' C').
      apply(cop_npar__inter_exists X Y A' C').
      apply coplanar_pseudo_trans with O A B; [Cop..|].
        apply coplanar_perm_12, col_cop__cop with C; Cop.
      intro.
      apply H0.
      eapply (par_trans O B X Y).
        auto.
      apply par_symmetry.
      apply (par_trans A C A' C').
        left.
        auto.
      Par.
    ex_and H31 L.
    assert(A <> L).
      intro.
      subst L.
      contradiction.
    assert(Par A L O B').
      apply par_symmetry.
      apply(par_col_par_2 _ B); Col.
      apply par_symmetry.
      apply par_left_comm.
      induction(eq_dec_points X L).
        subst X.
        apply (par_col_par_2 _ Y); Col.
        Par.
      apply (par_col_par_2 _ X); try auto.
        ColR.
      apply par_left_comm.
      apply (par_col_par_2 _ Y); Col.
      Par.
    (********** construct M *********)
    assert(~ Par X Y O C).
      intro.
      assert(Par O B O C).
        apply (par_trans O B X Y); Par.
      induction H36.
        apply H36.
        exists O.
        split; Col.
      spliter.
      apply H16.
      Col.
    assert(Coplanar X Y O C).
      apply coplanar_pseudo_trans with O A B; Cop.
    assert(HH:=cop_npar__inter_exists X Y O C H36 H35).
    ex_and HH M.
    assert(A <> M).
      intro.
      subst M.
      apply H14.
      Col.
    assert(Par O B A M).
      apply (par_col_par_2 _ B'); Col.
      apply par_symmetry.
      apply (par_col_par_2 _ L); try auto.
      ColR.
    (*************** construct N ********************)
    assert(L <> A').
      intro.
      subst L.
      clean_trivial_hyps.
      apply H13.
      induction(eq_dec_points A' X).
        subst X.
        assert(Par A' A O B).
          apply (par_col_par_2 _ Y); Col.
          Par.
        induction H32.
          apply False_ind.
          apply H32.
          exists O.
          split; Col.
        spliter.
        ColR.
      assert(Par X A' O B).
        apply (par_col_par_2 _ Y); Col.
        Par.
      assert(Par A' A O B).
        apply (par_col_par_2 _ X); try auto.
          ColR.
        Par.
      induction H42.
        apply False_ind.
        apply H42.
        exists O.
        split; Col.
      spliter.
      Col.
    assert(~ Par L B' A' B').
      intro.
      induction H42.
        apply H42.
        exists B'.
        split;Col.
      spliter.
      apply H15.
      eapply (col_transitivity_1 _ L); Col.
    assert(~ Par A B L B').
      apply(par_not_par A' B' A B L B').
        left.
        Par.
      intro.
      apply H42.
      Par.
    assert(Coplanar A B L B').
      apply coplanar_perm_4, col_cop__cop with O; Col; Cop.
    assert(HH:=cop_npar__inter_exists A B L B' H44 H43).
    ex_and HH N.
    assert(Par_strict A L O B').
      induction H34.
        auto.
      spliter.
      apply False_ind.
      apply H13.
      apply (col_transitivity_1 _ B'); Col.
    assert(A <> N).
      intro.
      subst N.
      apply H47.
      exists B'; Col.
    assert(Par A N A' B').
      apply (par_col_par_2 _ B); Col.
      left.
      Par.
    clean_duplicated_hyps.
    (**********************************)
    assert(Par O N L A').
      induction(par_dec A O N L).
        assert(Par_strict A O N L).
          induction H18.
            auto.
          spliter.
          apply False_ind.
          apply H24.
          assert(Col N A B').
            eapply (col_transitivity_1 _ L); Col.
          apply col_permutation_2.
          eapply (col_transitivity_1 _ N); Col.
        apply(l13_14 A O A' A N L N B'); Col.
          Par.
        Par.
      assert(N <> L).
        intro.
        subst L.
        apply H47.
        exists B.
        split; Col.
      assert(Coplanar A O N L).
        assert_diffs; apply coplanar_perm_1, col_cop__cop with B'; Col; Cop.
      assert(HH:=cop_npar__inter_exists A O N L H51 H18).
      ex_and HH P.
      apply par_right_comm.
      assert(P <> L).
        intro.
        subst P.
        apply H47.
        exists O.
        split; Col.
      assert(P <> O).
        intro.
        subst P.
        apply H47.
        exists L.
        split.
          Col.
        apply (col_transitivity_1 _ N); Col.
      assert(L <> B').
        intro.
        subst L.
        apply H47.
        exists B'.
        split; Col.
      assert(A <> P).
        intro.
        subst P.
        assert(Col A B L).
          apply (col_transitivity_1 _ N); Col.
        assert(Col L A B').
          apply (col_transitivity_1 _ N); Col.
        apply H43.
        apply par_symmetry.
        right.
        repeat split.
          assumption.
          intro.
          subst B.
          apply H24.
          Col.
          Col.
        ColR.
      assert(P <> N).
        intro.
        subst P.
        apply H13.
        apply col_permutation_2.
        apply (col_transitivity_1 _ N); Col.
      assert(A' <> P).
        intro.
        subst P.
        apply H42.
        right.
        repeat split; try assumption.
          intro.
          subst B'.
          apply H22.
          Col.
          ColR.
        Col.
      assert(B' <> P).
        intro.
        subst P.
        apply H22.
        apply (col_transitivity_1 _ A); Col.
      apply(l13_11 O A' A L N B' P); Par; [|ColR..].
      intro.
      apply H47.
      exists L.
      split.
        Col.
      assert(Col L O N).
        apply (col_transitivity_1 _ P); Col.
      apply (col_transitivity_1 _ N); Col.
    (* apply col_permutation_2.
    apply (col_transitivity_1 _ A); Col.
    apply col_permutation_1.
    apply (col_transitivity_1 _ O); Col.
    Col.
    apply col_permutation_2.
    apply (col_transitivity_1 _ L); Col.
    *)
    assert(Par A' C' O N).
      apply (par_col_par_2 _ L).
        intro.
        subst C'.
        apply H23.
        Col.
        Col.
      Par.
    assert(Par O N A C).
      apply (par_trans _ _ A' C'); Par.
    assert(Par N M B C).
      induction(par_dec A N O C).
        assert(Par_strict A N O C).
          induction H52.
            auto.
          spliter.
          apply False_ind.
          apply H14.
          Col.
        apply par_right_comm.
        apply(l13_14 A N B A O C M O ); Par; Col.
      assert(Coplanar A N O C) by Cop.
      assert(HH:= cop_npar__inter_exists A N O C H53 H52).
      ex_and HH P.
      assert(B <> P).
        intro.
        subst P.
        apply H16.
        Col.
      assert(A <> P).
        intro.
        subst P.
        apply H14.
        Col.
      assert(M <> P).
        intro.
        subst P.
        induction H40.
          apply H40.
          exists B.
          split.
            Col.
          apply col_permutation_2.
          apply (col_transitivity_1 _ N); Col.
        spliter.
        apply H13.
        apply col_permutation_2.
        apply (col_transitivity_1 _ M); Col.
      assert(O <> P).
        intro.
        subst P.
        induction H51.
          apply H51.
          exists A.
          split; Col.
        spliter.
        apply H14.
        Col.
      assert(P <> N).
        intro.
        subst P.
        induction H51.
          apply H51.
          exists C.
          split; Col.
        spliter.
        apply H14.
        Col.
      apply(l13_11 N B A C M O P); Par; [|ColR..].
      intro.
      assert(Col N A C) by ColR.
      apply H.
      ColR.
    (* apply col_permutation_2.
    apply (col_transitivity_1 _ A); Col.
    apply col_permutation_1.
    apply (col_transitivity_1 _ N); Col.
    apply col_permutation_2.
    apply (col_transitivity_1 _ O); Col.
    apply col_permutation_1.
    apply (col_transitivity_1 _ C); Col.
    *)
    assert(Par N M B' C').
      induction(par_dec N B' O C').
        assert(Par_strict N B' O C').
          induction H53.
            auto.
          spliter.
          apply False_ind.
          induction H51.
            apply H51.
            exists C.
            split.
              ColR.
            Col.
          spliter.
          contradiction.
        assert(M <> L).
          intro.
          subst M.
          apply H54.
          exists L.
          split.
            Col.
          apply col_permutation_2.
          apply(col_transitivity_1 _ C); Col.
        assert(L <> C').
          intro.
          subst C'.
          apply H54.
          exists L.
          split; Col.
        assert(Par L M O B').
          apply (par_col_par_2 _ A); try assumption.
            auto.
            ColR.
          Par.
        assert(Par L C' O N).
          apply (par_col_par_2 _ A'); Col.
          Par.
        apply par_right_comm.
        apply(l13_14 B' N B' L O C' M O); Par; ColR.
      assert(Coplanar N B' O C').
        apply coplanar_pseudo_trans with O A B; [Cop..|].
        apply coplanar_perm_12, col_cop__cop with C; Col; Cop.
      assert(HH:= cop_npar__inter_exists N B' O C' H54 H53).
      ex_and HH P.
      assert(B' <> P).
        intro.
        subst P.
        apply H16.
        ColR.
      induction(eq_dec_points C'  L).
        subst L.
        assert(C' = M).
          induction (col_dec O X C).
            apply (l6_21 O C Y X).
              intro.
              assert(Col O X Y) by ColR.
              induction H27.
                apply H27.
                exists O.
                split; Col.
              spliter.
              apply H13.
              apply(col3 X Y); Col.
              auto.
              Col.
              Col.
              Col.
              Col.
          apply (l6_21 O C X Y); Col.
        subst M.
        right.
        repeat split; auto.
          apply par_distincts in H52; spliter; auto.
          intro; subst; apply H15; Col.
          Col.
        Col.
      assert(L <> P).
        intro.
        subst P.
        apply H23.
        apply col_permutation_1.
        apply (col_transitivity_1 _ L); Col.
      induction (eq_dec_points L M).
        subst L.
        assert(C' = M).
          apply (l6_21 O C A' C'); Col.
            intro.
            apply H23.
            ColR.
            intro.
            subst C'.
            apply H23.
            Col.
            subst M.
            right.
            repeat split; auto. Col. Col.
              assert(Par L M O B').
            apply (par_col_par_2 _ A); try assumption. ColR.
              Par.
            assert(Par L C' N O).
              apply (par_col_par_2 _ A'); Col.
              Par.
            assert(B' <> N).
              intro.
              subst N.
              contradiction.
            apply(l13_11  N B' L  C' M O P); Par.
              intro.
              assert(Col P B' C').
                apply (col_transitivity_1 _ N).
                  intro.
                  subst N.
                  induction H50.
                    apply H50.
                    exists C'.
                    split; Col.
                  spliter.
                  apply H23.
                  ColR.
                  Col.
                Col.
              assert(Col C' O B' ).
                apply (col_transitivity_1 _ P).
                  intro.
                  subst P.
                  clean_trivial_hyps.
                  assert(Col B' C' L).
                    apply (col_transitivity_1 _ N); Col.
                  apply H15.
                  ColR.
                  Col.
                Col.
              assert(Col O B C').
                apply (col_transitivity_1 _ B'); Col.
              apply H16.
              ColR.
              ColR.
              intro.
              subst M.
              assert(Col B' P L).
                apply (col_transitivity_1 _ N); Col.
              assert(Col L A B').
                assert(Col P A L).
                  apply (col3 X Y); Col.
                apply (col_transitivity_1 _ P); Col.
              apply H47.
              exists B'.
              split; Col.
              intro.
              subst P.
              assert(N = B).
                apply (l6_21 A B O B'); Col.
                  subst N.
                  induction H52.
                    apply H52.
                    exists B.
                    split; Col.
                  spliter.
                  assert(B = O).
                    apply (l6_21 O B' M C); Col.
                  subst B.
                  induction H61.
                    apply H61.
                    exists L.
                    split; Col.
                  tauto.
                  ColR.
                  ColR.
                  apply (par_trans _ _ N M); Par.
Qed.

Lemma l13_15_2_aux : forall A B C A' B' C' O , ~Col A B C
                                         -> ~Par O A B C
                                         -> Par O B A C
                                         -> Par_strict A B A' B'
                                         -> Par_strict A C A' C'
                                         -> Col O A A' -> Col O B B' -> Col O C C'
                                         -> Par B C B' C'.
Proof.
    intros.
    assert(~Col O A B /\ ~Col O B C /\ ~Col O A C).
      induction H1; repeat split; intro.
        apply H1.
        exists A.
        split; Col.
        apply H1.
        exists C.
        split; Col.
        apply H1.
        exists O.
        split; Col.
        spliter.
        apply H; Col.
        spliter.
        apply H; Col.
      spliter.
      apply H; Col.
    spliter.
    assert( A <> O /\ B <> O /\ C <> O).
      repeat split; intro; subst O.
        apply H9.
        Col.
        apply H8.
        Col.
      apply H9.
      Col.
    spliter.
    assert( A' <> O).
      intro.
      subst A'.
      assert(Par O B A B).
        apply (par_col_par_2 _ B'); Col.
        left.
        Par.
      induction H13.
        apply H13.
        exists B.
        split; Col.
      spliter.
      contradiction.
    assert(B' <> O).
      intro.
      subst B'.
      assert(Par O A B A).
        apply(par_col_par_2 _ A'); Col.
        apply par_comm.
        apply par_symmetry.
        left.
        Par.
      induction H14.
        apply H14.
        exists A.
        split; Col.
      spliter.
      apply H7.
      Col.
    assert(C' <> O).
      intro.
      subst C'.
      assert(Par O A C A).
        apply (par_col_par_2 _ A'); Col.
        apply par_comm.
        apply par_symmetry.
        left.
        Par.
      induction H15.
        apply H15.
        exists A.
        split; Col.
      spliter.
      apply H9.
      Col.
    assert(~Col O A' B').
      intro.
      assert(Col O A B').
        apply (col_transitivity_1 _ A'); Col.
      apply H7.
      apply (col_transitivity_1 _ B'); Col.
    assert(~Col O B' C').
      intro.
      assert(Col O B C').
        apply (col_transitivity_1 _ B'); Col.
      apply H8.
      apply (col_transitivity_1 _ C'); Col.
    assert(~Col O A' C').
      intro.
      assert(Col O A C').
        apply (col_transitivity_1 _ A'); Col.
      apply H9.
      apply (col_transitivity_1 _ C'); Col.
    assert(A <> A').
      intro.
      subst A'.
      apply H3.
      exists A.
      split; Col.
    assert(B <> B').
      intro.
      subst B'.
      apply H2.
      exists B.
      split; Col.
    assert(C <> C').
      intro.
      subst C'.
      apply H3.
      exists C.
      split; Col.
    induction(par_dec B C B' C').
      auto.
    assert(B <> C).
      intro.
      subst C.
      apply H.
      Col.
    assert(HP:=parallel_existence B C B' H23).
    ex_and HP X.
    ex_and H24 Y.
    assert(~Par X Y O C).
      intro.
      assert(Par O C B C).
        apply (par_trans _ _  X Y); Par.
      induction H28.
        apply H28.
        exists C.
        split; Col.
      spliter.
      contradiction.
    assert(Coplanar X Y O C).
      induction H25.
        apply coplanar_pseudo_trans with B C B'.
          apply not_col_permutation_1, (par_not_col X Y); Par.
          apply coplanar_perm_1, col_cop__cop with Y; Col; Cop.
          apply coplanar_perm_1, col_cop__cop with X; Col; Cop.
          Cop.
          Cop.
      spliter.
      Cop.
    assert(HH:=cop_npar__inter_exists X Y O C H28 H27).
    ex_and HH C''.
    assert(B' <> C'').
      intro.
      subst C''.
      assert(Col O B C).
        apply (col_transitivity_1 _ B'); Col.
      contradiction.
    assert(Par B' C'' B C ).
      induction(eq_dec_points B' X).
        subst X.
        apply (par_col_par_2 _ Y).
          auto.
          Col.
        Par.
      apply (par_col_par_2 _ X).
        auto.
        apply col_permutation_2.
        apply(col_transitivity_1 _ Y); Col.
      apply par_left_comm.
      apply (par_col_par_2 _ Y); Col.
      Par.
    assert(Par A C A' C'').
      apply(l13_15_1 B A C B' A' C'' O); Col.
        Cop.
        apply par_strict_comm.
        auto.
      induction H32.
        Par.
      spliter.
      apply False_ind.
      apply H8.
      apply col_permutation_2.
      apply(col_transitivity_1 _ B'); Col.
    assert(C' <> C'').
      intro.
      subst C''.
      apply H22.
      Par.
    assert(Par A' C' A' C'').
      apply (par_trans _ _ A C).
        left.
        Par.
      Par.
    assert(C' = C'').
      apply (l6_21 A' C' O C); Col.
        induction H35.
        apply False_ind.
        apply H35.
        exists A'.
        split; Col.
        spliter.
        Col.
    contradiction.
Qed.

Lemma l13_15_2 : forall A B C A' B' C' O , ~Col A B C
                                         -> Par O B A C
                                         -> Par_strict A B A' B'
                                         -> Par_strict A C A' C'
                                         -> Col O A A' -> Col O B B' -> Col O C C'
                                         -> Par B C B' C'.
Proof.
    intros.
    induction(par_dec B C B' C').
      auto.
    assert(HH:=not_par_one_not_par B C B' C' O A H6).
    induction HH.
      apply (l13_15_2_aux A B C A' B' C' O); auto.
      intro.
      apply H7.
      Par.
    apply par_symmetry.
    assert(~ Col A' B' C').
      intro.
      apply H.
      assert(Par A' B' A' C').
        right.
        repeat split; Col.
          intro.
          subst B'.
          apply H1.
          exists A.
          split; Col.
        intro.
        subst C'.
        apply H2.
        exists A.
        split; Col.
      assert(Par A B A C).
        apply(par_trans _ _ A' B').
          left.
          auto.
        apply(par_trans _ _ A' C').
          Par.
        left.
        Par.
      induction H10.
        apply False_ind.
        apply H10.
        exists A.
        split; Col.
      spliter.
      Col.
    assert(B' <> O).
      intro.
      subst B'.
      assert(Par O A B A).
        apply (par_col_par_2 _ A'); Col.
          intro.
          subst A.
          apply H1.
          exists O.
          split; Col.
        apply par_comm.
        left.
        Par.
      induction H9.
        apply H9.
        exists A.
        split; Col.
      spliter.
      apply H1.
      exists O.
      split; Col.
    assert(Par O B O B').
      right.
      repeat split; Col.
      intro.
      subst B.
      apply par_distincts in H0.
      tauto.
    apply (l13_15_2_aux A' B' C' A B C O); Col; Par.
      intro.
      apply H7.
      apply par_symmetry.
      apply (par_col_par_2 _ A').
        intro.
        subst A.
        induction H0.
          apply H0.
          exists O.
          split; Col.
        spliter.
        apply H.
        Col.
        Col.
      Par.
    apply (par_trans _ _ O B).
      Par.
    apply (par_trans _ _ A C).
      Par.
    left.
    Par.
Qed.


Lemma l13_15 : forall A B C A' B' C' O , ~Col A B C -> Coplanar O B A C
                                         -> Par_strict A B A' B'
                                         -> Par_strict A C A' C'
                                         -> Col O A A' -> Col O B B' -> Col O C C'
                                         -> Par B C B' C'.
Proof.
    intros.
    induction(par_dec O B A C).
      apply (l13_15_2 A B C A' B' C' O); Col; Par.
    apply (l13_15_1 A B C A' B' C' O); Col; Par.
Qed.


Lemma l13_15_par : forall A B C A' B' C', ~Col A B C
                                         -> Par_strict A B A' B'
                                         -> Par_strict A C A' C'
                                         -> Par A A' B B'
                                         -> Par A A' C C'
                                         -> Par B C B' C'.
Proof.
    intros.
    assert(Plg B' A' A B).
      apply(pars_par_plg B' A' A B).
        apply par_strict_left_comm.
        Par.
      Par.
    apply plg_to_parallelogram in H4.
    apply plg_permut in H4.
    assert(Plg  A' C' C A).
      apply(pars_par_plg  A' C' C A).
        apply par_strict_right_comm.
        Par.
      Par.
    apply plg_to_parallelogram in H5.
    apply plg_permut in H5.
    assert(Parallelogram B B' C' C \/ B = B' /\ A' = A /\ C = C' /\ B = C).
      apply(plg_pseudo_trans B B' A' A C C').
        apply plg_sym.
        auto.
      apply plg_comm2.
      apply plg_permut.
      apply plg_permut.
      auto.
    assert(Par B B' C C').
      apply (par_trans _ _ A A'); Par.
    induction H7.
      induction H6.
        assert(B <> B').
          apply par_distincts in H2.
          tauto.
        apply plg_par in H6.
          spliter.
          Par.
          auto.
        intro.
        subst C'.
        apply H7.
        exists B'.
        split; Col.
      spliter.
      subst C.
      subst C'.
      apply False_ind.
      apply H7.
      exists B.
      split; Col.
    induction H6.
      apply plg_par in H6.
        spliter.
        Par.
        spliter.
        auto.
      spliter.
      intro.
      subst C'.
      assert(Par A B A C).
        apply (par_trans _ _ A' B'); left; Par.
      induction H11.
        apply H11.
        exists A.
        split; Col.
      spliter.
      apply H.
      Col.
    spliter.
    subst B'.
    subst A'.
    subst C'.
    subst C.
    apply False_ind.
    apply H1.
    exists A.
    split; Col.
Qed.

Lemma l13_18_2 : forall A B C A' B' C' O, ~Col A B C
                               -> Par_strict A B A' B'
                               -> Par_strict A C A' C'
                               -> (Par_strict B C B' C' /\ Col O A A' /\ Col O B B' -> Col O C C').
Proof.
    intros.
    spliter.
    assert(~ Col O A B).
      intro.
      apply H0.
      exists O.
      split.
        Col.
      apply(col_transitivity_1 _ A); Col.
        intro.
        subst A.
        apply H0.
        exists B'.
        split; Col.
      apply(col_transitivity_1 _ B); Col.
      intro.
      subst B.
      apply H0.
      exists A'.
      split; Col.
    assert(exists X : Tpoint, Col X B' C' /\ Col X O C).
      apply cop_npar__inter_exists.
        assert_diffs; apply coplanar_perm_13, col_cop__cop with B; Col; Cop.
      apply par_not_par with B C; Par.
      intro.
      induction H6.
        apply H6.
        exists C.
        split; Col.
      spliter.
      apply H2.
      exists B'.
      split;Col.
      apply col_permutation_2.
      apply (col_transitivity_1 _ O); Col.
      intro.
      subst O.
      apply H0.
      exists A'.
      split; Col.
    ex_and H6 C''.
    induction(col_dec O C C').
      auto.
    apply False_ind.
    assert(Par C' C'' B C ).
      apply (par_col_par_2 _ B').
        intro.
        subst C''.
        Col.
        Col.
      apply par_left_comm.
      left.
      Par.
    assert(Par_strict C' C'' B C).
      induction H9.
        auto.
      spliter.
      apply False_ind.
      apply H8.
      apply col_permutation_2.
      apply (col_transitivity_1 _ C'').
        intro.
        subst C''.
        apply H2.
        exists C.
        split; Col.
        apply (col_transitivity_1 _ B); Col.
      Col.
    assert(~Col O B C).
      intro.
      apply H10.
      exists B'.
      split; Col.
      apply col_permutation_2.
      apply (col_transitivity_1 _ O); Col.
      intro.
      subst B.
      apply H5.
      Col.
    assert(Par B' C'' B C).
      apply (par_col_par_2 _ C') ; Col.
        intro.
        subst B'.
        apply H11.
        apply(col_transitivity_1 _ C''); Col.
        intro.
        subst C''.
        apply H0.
        exists A.
        split; Col.
      left.
      Par.
    assert(Par_strict B' C'' B C).
      induction H12.
        auto.
      spliter.
      apply False_ind.
      apply H11.
      apply col_permutation_2.
      apply (col_transitivity_1 _ B'); Col.
      intro.
      subst B'.
      apply H2.
      exists B.
      split; Col.
    assert(Par A C A' C'').
      apply(l13_15 B A C B' A' C'' O); Par; Col.
      assert_diffs; apply coplanar_perm_3, coplanar_trans_1 with C'; Col.
        apply coplanar_perm_4, col_cop__cop with A'; Col; Cop.
        apply coplanar_perm_4, col_cop__cop with B'; Col; Cop.
    assert(Par A' C' A' C'').
      apply (par_trans _ _ A C).
        left.
        Par.
      Par.
    induction H15.
      apply H15.
      exists A'.
      split; Col.
    spliter.
    assert(~ Col A' B' C').
      intro.
      apply H.
      apply(col_par_par_col A' B' C' A B C H19); left; Par.
    assert( C' = C'').
      apply(l6_21 A' C' B' C'); Col.
      intro.
      subst C'.
      apply H19.
      Col.
    subst C''.
    Col.
Qed.

Lemma l13_18_3 : forall A B C A' B' C', ~Col A B C
                               -> Par_strict A B A' B'
                               -> Par_strict A C A' C'
                               -> (Par_strict B C B' C' /\ Par A A' B B')
                               -> (Par C C' A A' /\ Par C C' B B').
Proof.
    intros.
    spliter.
    assert(Par C C' A A').
      apply par_distincts in H3.
      spliter.
      assert(HH:= parallel_existence1 B B' C H5).
      ex_and HH P.
      induction(par_dec C P B C).
        induction H7.
          apply False_ind.
          apply H7.
          exists C.
          split; Col.
        spliter.
        assert(Col P B' C).
          induction H6.
            apply False_ind.
            apply H6.
            exists B.
            split; Col.
          spliter.
          Col.
        assert(Col C B B').
          apply (col_transitivity_1 _ P); Col.
        apply False_ind.
        apply H2.
        exists B'.
        split; Col.
      assert(~ Par C P B' C').
        intro.
        apply H7.
        apply(par_trans _ _ B' C'); Par.
      assert(Coplanar C P B' C').
        apply coplanar_perm_2, coplanar_trans_1 with B; [|Cop..].
        apply not_col_permutation_1, par_not_col with B' C'; Par; Col.
      assert(HH:=cop_npar__inter_exists C P B' C' H9 H8).
      ex_and HH C''.
      induction(eq_dec_points B' C'').
        subst C''.
        apply False_ind.
        induction H6.
          apply H6.
          exists B'.
          split; Col.
        spliter; apply H2.
        exists B'.
        split; Col.
        apply col_permutation_1.
        apply(col_transitivity_1 _ P); Col.
      assert(Par C C'' B B' ).
        apply (par_col_par_2 _ P); Col.
          intro.
          subst C''.
          apply H2.
          exists C.
          split; Col.
        Par.
      assert(Par B' C'' B C).
        apply (par_col_par_2 _ C'); Col.
        left.
        Par.
      assert(~ Col A' B' C').
        intro.
        apply H.
        assert(Par C' A' B C).
          apply (par_col_par_2 _ B').
            apply par_strict_distinct in H1.
            spliter.
            auto.
            Col.
          apply par_left_comm.
          left.
          Par.
        assert(Par B C A C).
          apply (par_trans _ _ A' C'); Par.
        induction H17.
          apply False_ind.
          apply H17.
          exists C.
          split; Col.
        spliter; Col.
      assert(Par A C A' C'').
        apply(l13_15_par B A C B' A' C'').
          intro.
          apply H.
          Col.
          apply par_strict_comm.
          Par.
          induction H14.
            Par.
          spliter.
          apply False_ind.
          apply H2.
          exists B'.
          split; Col.
          Par.
        Par.
      assert(C' = C'').
        apply (l6_21 C' A' B' C'); Col.
          intro.
          subst C'.
          apply H15.
          Col.
          eapply (col_par_par_col A C A); Col.
            apply par_right_comm.
            left.
            Par.
          Par.
      subst C''.
      apply (par_trans _ _ B B'); Par.
    split.
      Par.
    apply (par_trans _ _ A A'); Par.
Qed.

Lemma l13_18 :  forall A B C A' B' C' O, ~Col A B C /\ Par_strict A B A' B' /\  Par_strict A C A' C'
                                        ->(Par_strict B C B' C' /\ Col O A A' /\ Col O B B' -> Col O C C')
                                          /\ ((Par_strict B C B' C' /\ Par A A' B B') -> (Par C C' A A' /\ Par C C' B B'))
                                          /\ (Par A A' B B' /\ Par A A' C C' -> Par B C B' C').
Proof.
    intros.
    spliter.
    split.
      intros.
      apply (l13_18_2 A B C A' B' C' O); auto.
    split.
      intros.
      spliter.
      apply l13_18_3; auto.
    intros.
    spliter.
    apply (l13_15_par A B C A' B' C'); auto.
Qed.

Lemma l13_19_aux : forall A B C D A' B' C' D' O, ~Col O A B -> A <> A' -> A <> C
                                          -> O <> A -> O <> A' -> O <> C -> O <> C'
                                          -> O <> B -> O <> B' -> O <> D -> O <> D'
                                          -> Col O A C -> Col O A A' -> Col O A C'
                                          -> Col O B D -> Col O B B' -> Col O B D'
                                          -> ~Par A B C D
                                          -> Par A B A' B' -> Par A D A' D' -> Par B C B' C'
                                          -> Par C D C' D'.
Proof.
    intros.
    assert(Coplanar A B C D) by (exists O; right; left; split; Col).
    assert(HH:= cop_npar__inter_exists A B C D H20 H16).
    ex_and HH E.
    assert(~Par A' B' O E).
      intro.
      assert(Par A B O E).
        apply (par_trans _ _ A' B'); Par.
      induction H24.
        apply H24.
        exists E.
        split; Col.
      spliter.
      apply H.
      apply (col_transitivity_1 _ E); Col.
    assert(Coplanar A' B' O E).
      apply coplanar_pseudo_trans with O A B; Cop.
    assert(HH:= cop_npar__inter_exists A' B' O E H24 H23).
    ex_and HH E'.
    assert(C <> E).
      intro.
      subst E.
      apply H.
      apply col_permutation_2.
      apply (col_transitivity_1 _ C); Col.
    induction(col_dec A D E).
      assert(B = D).
        apply(l6_21 O B A E); Col.
        intro.
        subst E.
        apply H.
        assert(Col A O D).
          apply (col_transitivity_1 _ C); Col.
        apply (col_transitivity_1 _ D); Col.
      subst D.
      assert(Par A' B' A' D').
        apply (par_trans _ _ A B); Par.
      induction H29.
        apply False_ind.
        apply H29.
        exists A'.
        split; Col.
      spliter.
      assert(B' = D').
        eapply(l6_21 A' B' O B'); Col.
        intro.
        apply H.
        apply (col_transitivity_1 _ A'); Col.
        apply (col_transitivity_1 _ B'); Col.
        apply (col_transitivity_1 _ B); Col.
      subst D'.
      Par.
    assert(B <> B').
      intro.
      subst B'.
      induction H17.
        apply H17.
        exists B.
        split; Col.
      spliter.
      apply H.
      apply col_permutation_2.
      apply (col_transitivity_1 _ A'); Col.
    assert(Par D E D' E').
      apply (l13_15 A _ _ A' _ _ O); Col.
        exists B; left; split; Col.
        induction H18.
          auto.
        spliter.
        apply False_ind.
        assert(Col A' A D).
          apply (col_transitivity_1 _ D'); Col.
        assert(Col A O D).
          apply (col_transitivity_1 _ A'); Col.
        apply H.
        apply (col_transitivity_1 _ D); Col.
        assert(Par A E A' E').
          apply(par_col_par_2 _ B); Col.
            intro.
            subst E.
            apply H28.
            Col.
          apply par_symmetry.
          apply(par_col_par_2 _ B'); Col.
            intro.
            subst E'.
            assert(Col O A E).
              apply(col_transitivity_1 _ A'); Col.
            apply H.
            apply col_permutation_2.
            apply(col_transitivity_1 _ E); Col.
            intro.
            subst E.
            apply H28.
            Col.
          Par.
        induction H30.
          auto.
        spliter.
        apply False_ind.
        assert(Col A' A E).
          apply(col_transitivity_1 _ E'); Col.
        assert(Col A O E).
          apply(col_transitivity_1 _ A'); Col.
        apply H.
        apply col_permutation_2.
        apply(col_transitivity_1 _ E); Col.
      apply(col_transitivity_1 _ B); Col.
    apply par_comm.
    induction(col_dec B C E).
      assert(B = D).
        apply(l6_21 O B C E); Col.
        intro.
        apply H.
        apply (col_transitivity_1 _ C); Col.
      subst D.
      assert(Par A' B' A' D').
        apply (par_trans _ _ A B); Par.
      induction H32.
        apply False_ind.
        apply H32.
        exists A'.
        split; Col.
      spliter.
      assert(B' = D').
        eapply(l6_21 A' B' O B'); Col.
          Col5.
        ColR.
      subst D'.
      Par.
    assert(Par C E C' E').
      apply (l13_15 B _ _ B' _ _ O); Col.
        exists D; right; left; split; Col.
        induction H19.
          auto.
        spliter.
        apply False_ind.
        apply H.
        assert(Col B O C').
          apply (col_transitivity_1 _ B'); Col.
        apply (col_transitivity_1 _ C'); Col.
        assert(Par B E B' E').
          apply (par_col_par_2 _ A); Col.
            intro.
            subst E.
            apply H31.
            Col.
          apply par_symmetry.
          apply (par_col_par_2 _ A'); Col.
            intro.
            subst E'.
            assert(Col O B E).
              apply (col_transitivity_1 _ B'); Col.
            apply H.
            apply col_permutation_1.
            apply (col_transitivity_1 _ E); Col.
            intro.
            subst E.
            apply H31.
            Col.
          Par.
        induction H32.
          auto.
        spliter.
        apply False_ind.
        apply H.
        assert(Col O B' E').
          apply col_permutation_2.
          apply (col_transitivity_1 _ B); Col.
        assert(Col B' A' O).
          apply (col_transitivity_1 _ E'); Col.
        apply (col_transitivity_1 _ A'); Col.
        apply (col_transitivity_1 _ B'); Col.
      apply (col_transitivity_1 _ A); Col.
    apply(par_col_par_2 _ E); Col.
      intro.
      subst D.
      apply H.
      apply(col_transitivity_1 _ C); Col.
    apply par_symmetry.
    apply(par_col_par_2 _ E'); Col.
      intro.
      subst D'.
      apply H.
      apply(col_transitivity_1 _ C'); Col.
      apply (col_par_par_col D E C); Par.
      Col.
    Par.
Qed.


Lemma l13_19 : forall A B C D A' B' C' D' O, ~Col O A B
                                          -> O <> A -> O <> A' -> O <> C -> O <> C'
                                          -> O <> B -> O <> B' -> O <> D -> O <> D'
                                          -> Col O A C -> Col O A A' -> Col O A C'
                                          -> Col O B D -> Col O B B' -> Col O B D'
                                          -> Par A B A' B' -> Par A D A' D' -> Par B C B' C'
                                          -> Par C D C' D'.
Proof.
    intros.
    induction (eq_dec_points A A').
      subst A'.
      assert(B = B').
        apply(l6_21 A B O B); Col.
        induction H14.
          apply False_ind.
          apply H14.
          exists A.
          split; Col.
        spliter.
        Col.
      subst B'.
      assert(D = D').
        apply(l6_21 A D O B); Col.
          intro.
          apply H.
          apply (col_transitivity_1 _ D); Col.
          induction H15.
            apply False_ind.
            apply H15.
            exists A.
            split; Col.
          spliter.
          Col.
      subst D'.
      assert(C = C').
        apply(l6_21 B C O A); Col.
          intro.
          apply H.
          apply (col_transitivity_1 _ C); Col.
          induction H16.
            apply False_ind.
            apply H16.
            exists B.
            split; Col.
          spliter.
          Col.
      subst C'.
      apply par_reflexivity.
      intro.
      subst D.
      apply H.
      apply (col_transitivity_1 _ C); Col.
    induction(eq_dec_points A C).
      subst C.
      assert(A' = C').
        assert(Par A' B' B' C').
          apply (par_trans _ _ A B); Par.
        induction H18.
          apply False_ind.
          apply H18.
          exists B'.
          split; Col.
        spliter.
        eapply (l6_21 B' C' O A); Col.
        intro.
        apply H.
        apply (col_transitivity_1 _ B'); Col.
        apply (col_transitivity_1 _ C'); Col.
      subst C'.
      auto.
    induction(eq_dec_points A' C').
      subst C'.
      assert(A = C).
        assert(Par A B B C).
          apply (par_trans _ _ A' B'); Par.
        induction H19.
          apply False_ind.
          apply H19.
          exists B.
          split; Col.
        spliter.
        eapply (l6_21 B C O A'); Col.
          intro.
          apply H.
          apply (col_transitivity_1 _ C); Col.
          apply (col_transitivity_1 _ A); Col.
      contradiction.
    induction(par_dec C D C' D').
      auto.
    assert(HH:=not_par_one_not_par C D C' D' A' B' H20).
    induction HH.
      assert(~ Par C D A B).
        intro.
        apply H21.
        apply (par_trans _ _ A B); Par.
      (*assert(HH:= not_par_inter C D C' D' A B H19).
      ex_and HH E.
      induction H21.*)
      apply (l13_19_aux A B C D A' B' C' D' O); Col.
      intro.
      apply H21.
      apply (par_trans _ _ A B); Par.
    apply par_symmetry.
    apply (l13_19_aux A' B' C' D' A B C D O); Par.
      intro.
      apply H.
      apply (col_transitivity_1 _ A'); Col.
      apply (col_transitivity_1 _ B'); Col.
      apply (col_transitivity_1 _ A); Col.
      Col.
      apply (col_transitivity_1 _ A); Col.
      apply (col_transitivity_1 _ B); Col.
      Col.
    apply (col_transitivity_1 _ B); Col.
Qed.


Lemma l13_19_par_aux : forall A B C D A' B' C' D' X Y,
                                             X <> A -> X <> A' -> X <> C -> X <> C'
                                          -> Y <> B -> Y <> B' -> Y <> D -> Y <> D'
                                          -> Col X A C -> Col X A A' -> Col X A C'
                                          -> Col Y B D -> Col Y B B' -> Col Y B D'
                                          -> A <> C -> B <> D -> A <> A'
                                          -> Par_strict X A Y B
                                          -> ~Par A B C D
                                          -> Par A B A' B' -> Par A D A' D' -> Par B C B' C'
                                          -> Par C D C' D'.
Proof.
    intros.
    assert(Coplanar A B C D).
      apply coplanar_perm_2, col_cop__cop with Y; Col.
      apply coplanar_perm_16, col_cop__cop with X; Col; Cop.
    assert(HH := cop_npar__inter_exists A B C D H21 H17).
    ex_and HH E.
    assert(HH:= parallel_existence1 X A E H).
    ex_and HH Z.
    assert(~Par A B E Z).
      intro.
      assert(Par Y B E Z).
        apply (par_trans _ _ X A); Par.
      induction H25.
        apply H25.
        exists E.
        split; Col.
      spliter.
      induction H24.
        apply H24.
        exists A.
        split; Col.
      spliter.
      induction H26.
        apply H26.
        exists B.
        split; Col.
      spliter.
      apply H16.
      exists E.
      split;ColR.
    assert(~Par A' B' E Z).
      intro.
      apply H25.
      apply (par_trans _ _ A' B'); Par.
    assert(Coplanar A' B' E Z).
      induction H24.
        CopR.
      spliter.
      exfalso.
      apply H25.
      right.
      assert_diffs.
      repeat split; auto.
      assert (A <> E).
        intro.
        subst E.
        apply H16.
        exists D; split; ColR.
      ColR.
    assert(HH:= cop_npar__inter_exists A' B' E Z H27 H26).
    ex_and HH E'.
    assert(~Col A D E).
      intro.
      induction (eq_dec_points A E).
        subst E.
        apply H13.
        apply (l6_21 X A D A); Col.
          intro.
          apply H16.
          exists D.
          split; Col.
        apply par_distincts in H19.
        spliter.
        auto.
      assert(Col A B D) by ColR.
      apply H16.
      exists A.
      split; Col.
      ColR.
    assert(Par_strict X A E Z).
      induction H24.
        Par.
      spliter.
      apply False_ind.
      assert(Col E X A) by ColR.
      assert(Col A C E) by ColR.
      apply H13.
      apply (l6_21 A E D C); Col.
        intro.
        subst D.
        contradiction.
        apply col_permutation_2.
        apply (col_transitivity_1  _ E); Col.
        intro.
        subst E.
        clean_trivial_hyps.
        apply H16.
        exists B.
        split; Col.
        apply col_permutation_1.
        apply (col_transitivity_1  _ C); Col.
    assert(Par Y B E Z).
      apply (par_trans _ _ X A); Par.
    assert(Par_strict Y B E Z).
      induction H32.
        Par.
      spliter.
      apply False_ind.
      assert(Col E Y B) by ColR.
      assert(Col B D E) by ColR.
      apply H14.
      apply (l6_21 B E C D); Col.
        intro.
        apply H16.
        exists C.
        split; Col.
        apply col_permutation_1.
        apply (col_transitivity_1  _ E); Col.
        intro.
        subst E.
        apply H16.
        exists C.
        split; Col.
        clean_trivial_hyps.
        apply col_permutation_1.
        apply (col_transitivity_1  _ D); Col.
      intro.
      subst D.
      apply H16.
      exists C.
      split; Col.
      ColR.
    assert(~Col A' D' E').
      intro.
      assert(Col A' B' D').
        apply (col_transitivity_1  _ E'); Col.
        intro.
        subst E'.
        apply H31.
        exists A'.
        split; Col.
      apply H16.
      exists A'.
      split; Col.
      assert(Col Y B' D').
        apply (col_transitivity_1  _ B); Col.
      assert(Col B' A' Y).
        apply (col_transitivity_1  _ D'); Col.
        intro.
        subst D'.
        assert(Par A D A B).
          apply(par_trans _ _ A' B'); Par.
        induction H37.
          apply H37.
          exists A.
          split; Col.
        spliter.
        apply H16.
        exists A.
        split; Col.
        apply col_permutation_1.
        apply (col_transitivity_1  _ D); Col.
      apply col_permutation_2.
      apply (col_transitivity_1  _ B'); Col.
    assert(~ Col X A B).
      intro.
      apply H16.
      exists B.
      split; Col.
    assert(~ Col Y A B).
      intro.
      apply H16.
      exists A.
      split; Col.
    assert(B <> B').
      intro.
      subst B'.
      apply H15.
      apply(l6_21 X A B A); Col.
        intro.
        subst B.
        apply H35.
        Col.
        induction H18.
          apply False_ind.
          apply H18.
          exists B.
          split; Col.
        spliter.
        Col.
    assert(C <> C').
      intro.
      subst C'.
      induction H20.
        apply H20.
        exists C.
        split; Col.
      spliter.
      apply H16.
      exists C.
      split; Col.
      apply col_permutation_1.
      apply (col_transitivity_1  _ B'); Col.
    assert(D <> D').
      intro.
      subst D'.
      induction H19.
        apply H19.
        exists D.
        split; Col.
      spliter.
      apply H16.
      exists D.
      split; Col.
      apply col_permutation_1.
      apply (col_transitivity_1  _ A'); Col.
    assert(A' <> C').
      intro.
      subst C'.
      assert(Par B C A B).
        apply (par_trans _ _ A' B'); Par.
      induction H40.
        apply H40.
        exists B.
        split; Col.
      spliter.
      apply H16.
      exists B.
      split; ColR.
    assert(B' <> D').
      intro.
      subst D'.
      assert(Par A D A B).
        apply (par_trans _ _ A' B'); Par.
      induction H41.
        apply H41.
        exists A.
        split; Col.
      spliter.
      apply H16.
      exists A.
      split; Col.
      apply col_permutation_1.
      apply (col_transitivity_1  _ D); Col.
    assert(A <> E).
      intro.
      subst E.
      apply H30.
      Col.
    assert(A' <> E').
      intro.
      subst E'.
      apply H34.
      Col.
    assert(B <> E).
      intro.
      subst E.
      apply H33.
      exists B.
      split; Col.
    assert(B' <> E').
      intro.
      subst E'.
      apply H33.
      exists B'.
      split; Col.
    (*-------------------*)
    assert(Par A E A' E').
      apply (par_col_par_2 _ B); Col.
      apply par_symmetry.
      apply (par_col_par_2 _ B'); Col.
      Par.
    assert(Par_strict A E A' E').
      induction H46.
        Par.
      spliter.
      apply False_ind.
      apply H47.
      apply (l6_21 X A' B' E'); Col.
        intro.
        apply H16.
        exists B'.
        split; Col.
        apply col_permutation_2.
        apply (col_transitivity_1  _ A'); Col.
      apply col_permutation_2.
      apply (col_transitivity_1  _ A); Col.
    assert(Par D E D' E').
      apply(l13_15_par A D E A' D' E'); Par.
        induction H19.
          Par.
        spliter.
        apply False_ind.
        apply H16.
        exists D.
        split; Col.
        apply col_permutation_1.
        apply (col_transitivity_1  _ A'); Col.
        apply col_permutation_2.
        apply (col_transitivity_1  _ D'); Col.
        apply (par_col_par_2 _ X); Col.
        apply par_symmetry.
        apply (par_col_par_2 _ Y); Col.
          apply col_permutation_2.
          apply (col_transitivity_1  _ B); Col.
        apply par_comm.
        apply (par_col_par_2 _ B); Col.
        apply (par_trans _ _ E Z); Par.
      apply (par_col_par_2 _ X); Par; Col.
      apply par_symmetry.
      apply (par_col_par_2 _ Z); Col.
        intro.
        subst E'.
        apply H47.
        exists E.
        split; Col.
      Par.
    assert(Par C E C' E').
      eapply(l13_15_par B C E B' C' E'); Par.
        intro.
        assert(Col B A C) by ColR.
        apply H16.
        exists B.
        split; ColR.
        induction H20.
          Par.
        spliter.
        apply False_ind.
        apply H16.
        exists B'.
        split; Col.
        assert(Col X C C').
          apply (col_transitivity_1  _ A); Col.
        assert(Col C B' X).
          apply (col_transitivity_1  _ C'); Col.
        apply col_permutation_2.
        apply (col_transitivity_1  _ C); Col.
        assert(Par B E B' E').
          apply (par_col_par_2 _ A); Col.
          apply par_symmetry.
          apply (par_col_par_2 _ A'); Col.
          Par.
        induction H49.
          Par.
        spliter.
        apply False_ind.
        assert(Col B' A' B) by ColR.
        apply H16.
        exists A'.
        split; ColR.
        apply (par_col_par_2 _ Y); Col.
        apply par_symmetry.
        apply (par_col_par_2 _ X); Col.
          apply col_permutation_2.
          apply (col_transitivity_1  _ A); Col.
        apply par_left_comm.
        apply (par_col_par_2 _ A); Col.
        apply (par_trans _ _ E Z); Par.
      apply (par_col_par_2 _ Y); Col.
      apply par_symmetry.
      apply (par_col_par_2 _ Z); Col.
        intro.
        subst E'.
        apply H47.
        exists E.
        split; Col.
      Par.
    apply (par_col_par_2 _ E); Col.
      intro.
      subst D.
      apply H16.
      exists C.
      split; Col.
    apply par_symmetry.
    apply (par_col_par_2 _ E'); Col.
      intro.
      subst D'.
      apply H16.
      exists C'.
      split; Col.
      apply (col_par_par_col C E D); Col ; Par.
    Par.
Qed.


Lemma l13_19_par : forall A B C D A' B' C' D' X Y,
 X <> A -> X <> A' -> X <> C -> X <> C'-> Y <> B -> Y <> B' -> Y <> D -> Y <> D' ->
 Col X A C -> Col X A A' -> Col X A C' -> Col Y B D -> Col Y B B' -> Col Y B D' ->
 Par_strict X A Y B -> Par A B A' B' -> Par A D A' D' -> Par B C B' C' ->
 Par C D C' D'.
Proof.
    intros.
    induction(eq_dec_points A C).
      subst C.
      assert(Par A' B' B' C').
        apply(par_trans _ _ A B); Par.
      induction H17.
        apply False_ind.
        apply H17.
        exists B'.
        split; Col.
      spliter.
      assert(A' = C').
        apply (l6_21 X A B' A'); Col.
        intro.
        apply H13.
        exists B'.
        split; Col.
      subst C'.
      Par.
    induction(eq_dec_points B D).
      subst D.
      assert(Par A' B' A' D').
        apply(par_trans _ _ A B); Par.
      induction H18.
        apply False_ind.
        apply H18.
        exists A'.
        split; Col.
      spliter.
      assert(B' = D').
        apply (l6_21 Y B A' B'); Col.
        intro.
        apply H13.
        exists A'.
        split; Col.
      subst D'.
      Par.
    induction(eq_dec_points A A').
      subst A'.
      induction H14.
        apply False_ind.
        apply H14.
        exists A.
        split; Col.
      spliter.
      assert(B = B').
        apply (l6_21 Y B A B); Col.
        intro.
        apply H13.
        exists A.
        split; Col.
      subst B'.
      assert(C = C').
        induction H16.
          apply False_ind.
          apply H16.
          exists B.
          split; Col.
        spliter.
        apply (l6_21 X A B C); Col.
        intro.
        apply H13.
        exists B.
        split; Col.
      subst C'.
      assert(D = D').
        induction H15.
          apply False_ind.
          apply H15.
          exists A.
          split; Col.
        spliter.
        apply (l6_21 Y B A D); Col.
        intro.
        apply H13.
        exists A.
        split; Col.
      subst D'.
      auto.
      apply par_reflexivity.
      intro.
      subst D.
      clean_trivial_hyps.
      apply H13.
      exists C.
      split; Col.
    induction(par_dec C D C' D').
      auto.
    assert(HH:=not_par_one_not_par C D C' D' A B H20).
    induction HH.
      eapply (l13_19_par_aux A B C D A' B' C' D' X Y); Col.
      intro.
      apply H21.
      Par.
    apply par_distincts in H14.
    spliter.
    apply par_symmetry.
    eapply (l13_19_par_aux A' B' C' D' A B C D X Y); finish; [ColR..| | | |].
      intro.
      subst C'.
      apply H17.
      apply (l6_21 X A B A); Col.
        intro.
        apply H13.
        exists B.
        split; Col.
        assert(Par B C B A).
          apply(par_trans _ _ A' B'); Par.
        induction H24.
          apply False_ind.
          apply H24.
          exists B.
          split; Col.
        spliter.
        Col.
      intro.
      apply H18.
      subst D'.
      assert(Par A D A B).
        apply(par_trans _ _ A' B'); Par.
      apply (l6_21 Y B A B); Col.
        intro.
        apply H13.
        exists A.
        split; Col.
        induction H24.
          apply False_ind.
          apply H24.
          exists A.
          split; Col.
        spliter.
        Col.
      unfold Par_strict in H13.
      spliter.
      unfold Par_strict.
      split.
        apply coplanar_perm_16, col_cop__cop with A; Col.
        apply coplanar_perm_16, col_cop__cop with B; Col.
      intro.
      apply H24.
      ex_and H25 P.
      exists P.
      split.
        ColR.
      ColR.
    intro.
    apply H21.
    apply (par_trans _ _ A' B'); Par.
Qed.

End Desargues_Hessenberg.