From mathcomp Require Import all_ssreflect.
Require Import Utf8.
Import EqNotations.
Set Implicit Arguments.

Require Import basics.

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

  (* Test terms *)
  (* v1 * (v3 - 1) *)
  Definition t0: Term nat_eqType L.
  Proof.
    refine (function_term mult [ffun x => match nat_of_ord x with 0 => _ | _ => _ end]); clear x.
    + exact (variable _ _ 1).
    + refine (function_term minus [ffun x => match nat_of_ord x with 0 => variable _ _ 3 | _ => _ end]); clear x.
      refine (function_term one (ffun0 _)). apply card_ord.
  Defined.

  (* (v1 + v2) * (v3 + 1) *)
  Definition t1: Term nat_eqType L.
  Proof.
    refine (function_term mult [ffun x => match nat_of_ord x with 0 => _ | _ => _ end]); clear x.
    + exact (function_term plus [ffun x => match nat_of_ord x with 0 => variable _ _ 1 | _ => variable _ _ 2 end]).
    + refine (function_term plus [ffun x => match nat_of_ord x with 0 => variable _ _ 3 | _ => _ end]); clear x.
      refine (function_term one (ffun0 _)). apply card_ord.
  Defined.

  Definition t2 (n: nat): Term nat_eqType L.
  Proof.
    destruct n.
    + refine (function_term zero (ffun0 _)). apply card_ord.
    + induction n.
      - refine (function_term one (ffun0 _)). apply card_ord.
      - refine (function_term plus [ffun x => match nat_of_ord x with 0 => _ | _ => IHn end]); clear x.
        refine (function_term one (ffun0 _)). apply card_ord.
  Defined.

  (* NB! This structure isn't actually a ring. *)
  (* But still good enough to test term interpretation. *)
  Definition M: Structure L.
  Proof.
    refine (@Build_Structure _ _ L nat _ _).
    + intro f. set (ord0 (n':=1)) as ord0_2. set (Ordinal (ltac:(auto):(1<2))) as ord1_2.
      refine (match f with plus => _ | minus => _ | mult => _ | zero => _ | one => _ end); simpl.
      - intro v. exact (v ord0_2 + v ord1_2).
      - intro v. exact (v ord0_2 - v ord1_2).
      - intro v. exact (v ord0_2 * v ord1_2).
      - exact (λ _, 0).
      - exact (λ _, 1).
    + intro r. destruct r.
  Defined.

  Definition assignment: nat → nat := id.

  Eval compute in (interpreted_term M assignment t0).
  (* Error! It doesn't compute to the number 2, as it should theoretically. *)
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
End LanguageOfOrderedRings.

Module LanguageOfPureSets.
  Inductive F := .
  Inductive R := .

  Definition L: Language F R.
  Proof.
    refine (Build_Language _ _).
    + intro f. destruct f.
    + intro r. destruct r.
  Defined.
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
    + intro f. refine (match f with e => _ | mult => _ end).
      - simpl. exact (λ _, 1).
      - simpl. intro v. set (ord0 (n':=1)) as n0_2.
        set (Ordinal (ltac:(auto):(1<2))) as n1_2.
        exact (v n0_2 + v n1_2).
    + intro r. destruct r.
  Defined.
End Groups.

