Require Import Utf8 List utils basics.
Import EqNotations.
Set Implicit Arguments.


(* Testing using parts of book by David Marker "Model theory: an introduction" (2002). *)

Module LanguageOfRings.
  Inductive F := plus | minus | mult | zero | one.
  Inductive R := .

  Definition L: Language F R.
  Proof.
    refine (Build_Language _ _).
    + exact (λ f, match f with
                  | plus => 2
                  | minus => 2
                  | mult => 2
                  | zero => 0
                  | one => 0
                  end).
    + intro r. destruct r.
  Defined.

  Definition dec := PeanoNat.Nat.eq_dec.

  (* Test terms *)
  (* v1 * (v3 - 1) *)
  Definition t0: Term nat L.
  Proof.
    refine (function_term mult _); simpl. refine [ variable 1 ; _ ].
    refine (function_term minus _); simpl. refine [ variable 2 ; _ ].
    refine (function_term one _); simpl. exact [ ].
  Defined.

  (* (v1 + v2) * (v3 + 1) *)
  Definition t1: Term nat L.
  Proof.
    refine (function_term mult _); simpl. refine [ _; _ ].
    + refine (function_term plus _); simpl. exact [ variable 1; variable 2 ].
    + refine (function_term plus _); simpl. refine [ variable 3; _ ].
      refine (function_term one _); simpl. exact [ ].
  Defined.

  Definition t2 (n: nat): Term nat L.
  Proof.
    destruct n.
    + refine (function_term zero _); simpl. exact [ ].
    + induction n.
      - refine (function_term one _); simpl. exact [ ].
      - refine (function_term plus _); simpl. refine [ _; IHn ].
        refine (function_term one _); simpl. exact [ ].
  Defined.

  (* NB! This structure isn't actually a ring. *)
  (* But still good enough to test term interpretation. *)
  Definition M: Structure L.
  Proof.
    refine (@Build_Structure _ _ L nat _ _).
    set (exist (λ i, i < 2) 0 (ltac:(auto):(0<2))) as n0_2.
    set (exist (λ i, i < 2) 1 (ltac:(auto):(1<2))) as n1_2.
    + exact (λ f, match f with
                  | plus => λ v, vector.nth v n0_2 + vector.nth v n1_2
                  | minus => λ v, vector.nth v n0_2 - vector.nth v n1_2
                  | mult => λ v, vector.nth v n0_2 * vector.nth v n1_2
                  | zero => λ _, 0
                  | one => λ _, 1
                  end).
    + intro r. destruct r.
  Defined.

  Eval compute in (interpreted_term M id t0).
  Eval compute in (interpreted_term M id t1).
  Eval compute in (interpreted_term M id (t2 4)).
End LanguageOfRings.

Module LanguageOfOrderedRings.
  Inductive F := plus | minus | mult | zero | one.
  Inductive R := lt.

  Definition L: Language F R.
  Proof.
    refine (Build_Language _ _).
    + exact (λ f, match f with
                  | plus => 2
                  | minus => 2
                  | mult => 2
                  | zero => 0
                  | one => 0
                  end).
    + exact (λ r, match r with lt => 2 end).
  Defined.

  (* NB! The same as previously - this structure isn't actually a ring. *)
  (* But still good enough to test formula interpretation. *)

  Definition M: Structure L.
  Proof.
    set (exist (λ i, i < 2) 0 (ltac:(auto):(0<2))) as n0_2.
    set (exist (λ i, i < 2) 1 (ltac:(auto):(1<2))) as n1_2.
    refine (@Build_Structure _ _ L nat _ _).
    + exact (λ f, match f with
                  | plus => λ v, vector.nth v n0_2 + vector.nth v n1_2
                  | minus => λ v, vector.nth v n0_2 - vector.nth v n1_2
                  | mult => λ v, vector.nth v n0_2 * vector.nth v n1_2
                  | zero => λ _, 0
                  | one => λ _, 1
                  end).
    + intro r. destruct r. simpl. exact (λ v, vector.nth v n0_2 < vector.nth v n1_2).
  Defined.

  (* v1 = 0 \/ 0 < v1 *)
  Definition f0: Formula nat L.
  Proof.
    refine (disjunction _ _).
    + refine (equality (variable 1) _).
      refine (function_term zero _); simpl. exact [ ].
    + refine (atomic_formula lt _); simpl.
      refine [ _; variable 1 ].
      refine (function_term zero _); simpl. exact [ ].
  Defined.

  (* ∃ v2, v2 * v2 = v1 *)
  Definition f1: Formula nat L.
  Proof.
    refine (existence_quantifier 2 (equality _ (variable 1))).
    refine (function_term mult _); simpl.
    refine [ variable 2; variable 2 ].
  Defined.

  (* ∀ v1, (v1 = 0 ∨ ∃ v2, v2 * v1 = 1) *)
  Definition f2: Formula nat L.
  Proof.
    refine (universal_quantifier 1 (disjunction _ _)).
    + refine (equality (variable 1) (function_term zero _)); simpl. exact [ ].
    + refine (existence_quantifier 2 (equality (function_term mult _) (function_term one _))); simpl.
      - exact [ variable 2; variable 1 ].
      - exact [ ].
  Defined.

  Definition dec := PeanoNat.Nat.eq_dec.
  Definition assignment := @id nat.
  Eval simpl in (interpreted_formula dec M f0 assignment).
  Eval simpl in (interpreted_formula dec M f1 assignment).
  Eval simpl in (interpreted_formula dec M f2 assignment).
End LanguageOfOrderedRings.

Module LanguageOfPureSets.
  Inductive F := .
  Inductive R := true_prop.

  Definition L: Language F R.
  Proof.
    refine (Build_Language _ _).
    + intro f. destruct f.
    + exact (λ r, 0).
  Defined.

  Definition descart_product A B (La: list A) (Lb: list B): list (A * B) := flat_map (λ x, map (λ y, (x, y)) Lb) La.
  Definition only_lt_pairs n :=
    filter (λ p, if Compare_dec.lt_dec (fst p) (snd p) then true else false) (descart_product (seq 0 n) (seq 0 n)).

  Definition fun_for_fold (p: nat * nat) (A: Formula nat L): Formula nat L.
  Proof.
    destruct p as [x y]. refine (conjunction (negation (equality (variable x) (variable y))) A).
  Defined.

  Definition a0: Formula nat L.
  Proof.
    refine (atomic_formula true_prop _); simpl. exact [ ].
  Defined.

  Definition big_conjunction n: Formula nat L := fold_right fun_for_fold a0 (only_lt_pairs n).
  Fixpoint add_ex_quantifiers n (A: Formula nat L): Formula nat L :=
    match n with
    | O => A
    | S m => existence_quantifier m (add_ex_quantifiers m A)
    end.

  Definition resulting_formula n := add_ex_quantifiers n (big_conjunction n).

  Definition M: Structure L.
  Proof.
    refine (@Build_Structure _ _ L nat _ _).
    + intro f. destruct f.
    + intro r. destruct r. simpl. intro v. exact True.
  Defined.

  Definition dec := PeanoNat.Nat.eq_dec.

  Eval simpl in (interpreted_formula dec M (resulting_formula 4) id).
End LanguageOfPureSets.

Module LanguageOfGraphs.
  Inductive F := .
  Inductive R := connected.

  Definition L: Language F R.
  Proof.
    refine (Build_Language _ _).
    + intro f. destruct f.
    + exact (λ r, match r with connected => 2 end).
  Defined.
End LanguageOfGraphs.

Module Groups.
  Inductive F := e | mult.
  Inductive R := .

  Definition L: Language F R.
  Proof.
    refine (Build_Language _ _).
    + exact (λ f, match f with e => 0 | mult => 2 end).
    + intro r. destruct r.
  Defined.

  Definition M: Structure L.
  Proof.
    refine (@Build_Structure _ _ L nat _ _).
    + set (exist (λ i, i < 2) 0 (ltac:(auto):(0<2))) as n0_2.
      set (exist (λ i, i < 2) 1 (ltac:(auto):(1<2))) as n1_2.
      refine (λ f, match f with
                  | e => λ _, 1
                  | mult => _
                  end); simpl.
      exact (λ v, vector.nth v n0_2 + vector.nth v n1_2).
    + intro r. destruct r.
  Defined.
End Groups.
