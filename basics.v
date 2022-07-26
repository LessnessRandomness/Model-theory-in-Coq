From mathcomp Require Import all_ssreflect.
Require Import Utf8.
Import EqNotations.
Set Implicit Arguments.

(* useful stuff *)

Definition vmap A B n (f: A → B) (v: A^n): B^n := finfun (f \o v).

(* Language, Term, Formula *)

Structure Language F R := {
  function_arity: F → nat;
  relation_arity: R → nat
}.

Definition Function A n := A^n → A.
Definition Relation A n := A^n → Prop.

Inductive Term {F R} (V: eqType) (L: Language F R) :=
  | variable: V → Term V L
  | function_term: ∀ (f: F), (Term V L)^(function_arity L f) → Term V L.

Definition Term_induction F R (V: eqType) (L: Language F R) (P: Term V L -> Prop):
  (∀ (s: V), P (variable V L s)) →
  (∀ (f: F) (T: Term V L ^ function_arity L f), (forall (x: 'I_(function_arity L f)), P (T x)) → P (function_term f T)) →
  ∀ T, P T.
Proof.
  intros H H0. refine (fix IHt (t: Term V L) := match t with variable v => H v | function_term f T => _ end).
  refine (H0 _ T _). intros. apply IHt.
Defined.

Inductive Formula F R (V: eqType) (L: Language F R) :=
  | equality: Term V L → Term V L → Formula V L
  | atomic_formula: ∀ (r: R), (Term V L)^(relation_arity L r) → Formula V L
  | negation: Formula V L → Formula V L
  | disjunction: Formula V L → Formula V L → Formula V L
  | conjunction: Formula V L → Formula V L → Formula V L
  | existence_quantifier: V → Formula V L → Formula V L
  | universal_quantifier: V → Formula V L → Formula V L.

Fixpoint term_has_variable F R (V: eqType) (L: Language F R) (i: V) (t: Term V L) {struct t}: bool :=
  match t with
  | variable x => (i == x)
  | function_term f t' => has (eqb true) (codom (term_has_variable i \o t'))
  end.

Fixpoint formula_has_free_variable F R V (L: Language F R) (A: Formula V L) (i: V): Prop :=
  match A with
  | equality t1 t2 => term_has_variable i t1 ∨ term_has_variable i t2
  | atomic_formula r v => has (term_has_variable i) (codom v)
  | negation f => formula_has_free_variable f i
  | disjunction f1 f2 => formula_has_free_variable f1 i ∨ formula_has_free_variable f2 i
  | conjunction f1 f2 => formula_has_free_variable f1 i ∨ formula_has_free_variable f2 i
  | existence_quantifier v f => v != i ∧ formula_has_free_variable f i
  | universal_quantifier v f => v != i ∧ formula_has_free_variable f i
  end.

Definition has_n_free_variables F R V (L: Language F R) (A: Formula V L) (n: nat) :=
  ∃ (v: V ^ n), uniq (codom v) ∧ (∀ (x: V), formula_has_free_variable A x ↔ x \in codom v).

Structure Sentence F R V (L: Language F R) := {
  sentenceFormula:> Formula V L;
  sentenceProperty: ∀ i, ¬ formula_has_free_variable sentenceFormula i
}.

(* Structure, Interpretation *)

Structure Structure {F R} (L: Language F R) := {
  domain: Type;
  function: ∀ (f: F), Function domain (function_arity L f);
  relation: ∀ (r: R), Relation domain (relation_arity L r)
}.

Fixpoint interpreted_term F R (V: eqType) (L: Language F R) (M: Structure L) (assignment: V → domain M) (T: Term V L): domain M :=
  match T with
  | variable x => assignment x
  | function_term f v => function M f (finfun (interpreted_term M assignment \o v))
  end.

Fixpoint satisfies F R (V: eqType) (L: Language F R) (M: Structure L) (A: Formula V L) (assignment: V → domain M): Prop :=
  match A with
  | equality t1 t2 => interpreted_term M assignment t1 = interpreted_term M assignment t2
  | atomic_formula r v => relation M r (vmap (interpreted_term M assignment) v)
  | negation f => ¬ satisfies M f assignment
  | disjunction f1 f2 => satisfies M f1 assignment ∨ satisfies M f2 assignment
  | conjunction f1 f2 => satisfies M f1 assignment ∧ satisfies M f2 assignment
  | existence_quantifier v f => ∃ i, satisfies M f (λ x, if v == x then i else assignment x)
  | universal_quantifier v f => ∀ i, satisfies M f (λ x, if v == x then i else assignment x) 
  end.

Definition model_of_sentence F R V (L: Language F R) (M: Structure L) (A: Sentence V L) :=
  ∀ a, satisfies M A a.

Definition model F R V (L: Language F R) (M: Structure L) (A: Sentence V L → Prop) :=
  ∀ a, A a → model_of_sentence M a.

(* Embedding, Isomorphism, Automorphism *)

Structure Embedding Fm Rm Fn Rn (Lm: Language Fm Rm) (Ln: Language Fn Rn) (M: Structure Lm) (N: Structure Ln) := {
  domain_map: domain M → domain N;
  function_map: Fm → Fn;
  relation_map: Rm → Rn;
  domain_map_property: injective domain_map;
  function_arity_preserved: ∀ f, function_arity Lm f = function_arity Ln (function_map f);
  relation_arity_preserved: ∀ r, relation_arity Lm r = relation_arity Ln (relation_map r);
  embedding_function_property: ∀ f v, domain_map (function M f v) =
    function N (function_map f) (vmap domain_map (rew [λ W, (domain M ^ W)%type] (function_arity_preserved f) in v));
  embedding_relation_property: ∀ r v, relation M r v ↔
    relation N (relation_map r) (vmap domain_map (rew [λ W, (domain M ^ W)%type] (relation_arity_preserved r) in v));
}.

Structure Isomorphism Fm Rm Fn Rn (Lm: Language Fm Rm) (Ln: Language Fn Rn) (M: Structure Lm) (N: Structure Ln) := {
  isomorphism_emb: Embedding M N;
  isomorphism_emb_inv: Embedding N M;
  isomorphism_property_1: ∀ x, domain_map isomorphism_emb (domain_map isomorphism_emb_inv x) = x;
  isomorphism_property_2: ∀ x, domain_map isomorphism_emb_inv (domain_map isomorphism_emb x) = x
}.

Definition Auomorphism F R (L: Language F R) (M: Structure L) := Isomorphism M M.

(* Definable set *)

Definition replace_variables {V: eqType} M n (v: V ^ n) (m: M ^ n) (assignment: V → M): V → M.
Proof.
  intro x. remember (x \in codom v) as W. destruct W.
  + refine (m _). exists (index x (codom v)). 
    assert (size (codom v) = n) by abstract(rewrite size_codom; simpl; apply card_ord).
    assert (index x (codom v) < size (codom v)) by abstract(rewrite index_mem; auto).
    abstract (rewrite H in H0; auto).
  + exact (assignment x).
Defined.

Definition definable F R (L: Language F R) (M: Structure L) n (X: domain M ^ n → Prop) :=
  ∃ (V: eqType) (A: Formula V L), has_n_free_variables A n ∧
     ∀ (a: V → domain M) (v: V ^ n), (∀ (m: domain M ^ n), X m ↔ satisfies M A (replace_variables v m a)).

(* Theory, Entailment, Satisfiable, Deductively closed *)

Definition Theory F R V (L: Language F R) (C: Structure L → Prop): Sentence V L → Prop :=
  λ (A: Sentence V L), ∀ (M: Structure L), C M → model_of_sentence M A.

Definition satisfiable_theory F R (L: Language F R) (C: Structure L → Prop) :=
  ∃ V (M: Structure L), model M (Theory C) (V:=V).

Definition entailment F R V (L: Language F R) (S: Sentence V L → Prop) (A: Sentence V L) :=
  ∀ (M: Structure L), model M S → model_of_sentence M A.

Definition deductively_closed F R V (L: Language F R) (S: Sentence V L → Prop) :=
  ∀ (A: Sentence V L), entailment S A.

Definition deductive_closure F R V (L: Language F R) (S: Sentence V L → Prop): Sentence V L → Prop :=
  λ (A: Sentence V L), entailment S A.

(* Completeness *)

Theorem negation_of_sentence_as_sentence F R V (L: Language F R) (A: Sentence V L): Sentence V L.
Proof.
  refine (Build_Sentence (negation A) _). abstract (destruct A; simpl in *; auto).
Defined.

Definition complete F R V (L: Language F R) (S: Sentence V L → Prop) :=
  ∀ (A: Sentence V L), entailment S A ∨ entailment S (negation_of_sentence_as_sentence A).

(* Elementary equivalence *)

Definition elementary_equivalence F R (L: Language F R) (M N: Structure L) :=
  ∀ V (A: Sentence V L), model_of_sentence M A ↔ model_of_sentence N A.

