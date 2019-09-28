(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *   INRIA, CNRS and contributors - Copyright 1999-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(*
 Tactic msatz: patched version of nsatz with an improved reification
 
*)

Require Import Reals Omega.
Require Export Nsatz.

Ltac reify_goal l le lb:=
  match le with
     nil => idtac
   | ?e::?le1 => 
        match lb with
         ?b::?lb1 => (* idtac "b="; idtac b;*)
           let x := fresh "B" in
           set (x:= b) at 1;
           replace x with (interpret3 e l) by apply refl_equal; 
           clear x;
           reify_goal l le1 lb1
        end
  end.

Ltac get_lpol g :=
  match g with
  (interpret3 ?p _) == _ => constr:(p::nil)
  | (interpret3 ?p _) == _ -> ?g =>
       let l := get_lpol g in constr:(p::l)     
  end.

Ltac msatz_generic radicalmax info lparam lvar :=
 let nparam := eval compute in (Z.of_nat (List.length lparam)) in
 match goal with
  |- ?g => let lb := lterm_goal g in 
     match (match lvar with
              |(@nil _) =>
                 match lparam with
                   |(@nil _) =>
                     let r := eval red in (list_reifyl (lterm:=lb)) in r
                   |_ =>
                     match eval red in (list_reifyl (lterm:=lb)) with
                       |(?fv, ?le) =>
                         let fv := parametres_en_tete fv lparam in
                           (* we reify a second time, with the good order
                              for variables *)
                         let r := eval red in 
                                  (list_reifyl (lterm:=lb) (lvar:=fv)) in r
                     end
                  end
              |_ => 
                let fv := parametres_en_tete lvar lparam in
                let r := eval red in (list_reifyl (lterm:=lb) (lvar:=fv)) in r
            end) with
          |(?fv, ?le) => 
            reify_goal fv le lb ;
            match goal with 
                   |- ?g => 
                       let lp := get_lpol g in 
                       let lpol := eval compute in (List.rev lp) in
                       intros;

  let SplitPolyList kont :=
    match lpol with
    | ?p2::?lp2 => kont p2 lp2
    | _ => idtac "polynomial not in the ideal"
    end in 

  SplitPolyList ltac:(fun p lp =>
    let p21 := fresh "p21" in
    let lp21 := fresh "lp21" in
    set (p21:=p) ;
    set (lp21:=lp);
(*    idtac "nparam:"; idtac nparam; idtac "p:"; idtac p; idtac "lp:"; idtac lp; *)
    nsatz_call radicalmax info nparam p lp ltac:(fun c r lq lci => 
      let q := fresh "q" in
      set (q := PEmul c (PEpow p21 r)); 
      let Hg := fresh "Hg" in 
      assert (Hg:check lp21 q (lci,lq) = true); 
      [ (vm_compute;reflexivity) || idtac "invalid nsatz certificate"
      | let Hg2 := fresh "Hg" in 
            assert (Hg2: (interpret3 q fv) == 0);
        [ (*simpl*) idtac; 
          generalize (@check_correct _ _ _ _ _ _ _ _ _ _ _ fv lp21 q (lci,lq) Hg);
          let cc := fresh "H" in
             (*simpl*) idtac; intro cc; apply cc; clear cc;
          (*simpl*) idtac;
          repeat (split;[assumption|idtac]); exact I
        | (*simpl in Hg2;*) (*simpl*) idtac; 
          apply Rintegral_domain_pow with (interpret3 c fv) (N.to_nat r);
          (*simpl*) idtac;
            try apply integral_domain_one_zero;
            try apply integral_domain_minus_one_zero;
            try trivial;
            try exact integral_domain_one_zero;
            try exact integral_domain_minus_one_zero
          || (solve [simpl; unfold R2, equality, eq_notation, addition, add_notation,
                     one, one_notation, multiplication, mul_notation, zero, zero_notation;
                     discrR || omega]) 
          || ((*simpl*) idtac) || idtac "could not prove discrimination result"
        ]
      ]
) 
)
end end end .

Ltac msatz_default:=
  intros;
  try apply (@psos_r1b _ _ _ _ _ _ _ _ _ _ _);
  match goal with |- (@equality ?r _ _ _) =>
    repeat equalities_to_goal;
    msatz_generic 6%N 1%Z (@nil r) (@nil r)
  end.

Tactic Notation "msatz" := msatz_default.
