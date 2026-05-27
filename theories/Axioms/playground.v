Require Import GeoCoq.Axioms.tarski_axioms.
Require Import GeoCoq.Axioms.adg_definitions.

(* Used by orchestrator/pipeline.py to demo Rocq MCP -> LLM -> Lean. *)
Lemma neq_sym : forall (A : Type) (a b : A), a <> b -> b <> a.
Proof.
  intros A a b H Hba.
  apply H. symmetry. exact Hba.
Qed.

Section Playground.
Context {Tn : Tarski_neutral_dimensionless}.

Lemma betweenNonStrict_iff_Bet : forall A B C,
  betweenNonStrict A B C <-> Bet A B C.
Proof.
Admitted.

End Playground.

(* Toy experiment lemmas: top-level so rocq-mcp can extract them. *)

(* Level 1: introduces the primitive type Tpoint. *)
Lemma point_eq_sym {Tn : Tarski_neutral_dimensionless} :
  forall (A B : Tpoint), A = B -> B = A.
Proof. intros A B H; symmetry; assumption. Qed.

(* Level 2: uses the primitive relation Cong. *)
Lemma cong_sym_stmt {Tn : Tarski_neutral_dimensionless} :
  forall (A B C D : Tpoint), Cong A B C D -> Cong C D A B.
Proof. Admitted.

(* Level 3: combines Bet and Cong primitives. *)
Lemma bet_cong_stmt {Tn : Tarski_neutral_dimensionless} :
  forall (A B C : Tpoint), Bet A B C -> Cong A C A C.
Proof. Admitted.
