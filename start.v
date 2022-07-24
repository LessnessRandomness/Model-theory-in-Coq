From mathcomp Require Import all_ssreflect.
Require Import Utf8.
Import EqNotations.
Set Implicit Arguments.


Tactic Notation "transparent" "assert" "(" ident(H) ":" open_constr(type) ")" :=
  refine (let H := (_ : type) in _).

Definition vmap A B n (f: A → B) (v: A^n): B^n := finfun (f \o v).


Structure Language F R := {
  function_arity: F → nat;
  relation_arity: R → nat
}.

Definition Function A n := A^n → A.
Definition Relation A n := A^n → Prop.

Structure Structure {F R} (L: Language F R) := {
  domain: Type;
  function: ∀ (f: F), Function domain (function_arity L f);
  relation: ∀ (r: R), Relation domain (relation_arity L r)
}.

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
  | atomic_formula r v => has (term_has_variable i) (codom v)
  | negation f => formula_has_free_variable f i
  | disjunction f1 f2 => formula_has_free_variable f1 i ∨ formula_has_free_variable f2 i
  | conjunction f1 f2 => formula_has_free_variable f1 i ∨ formula_has_free_variable f2 i
  | existence_quantifier v f => v ≠ i ∧ formula_has_free_variable f i
  | universal_quantifier v f => v ≠ i ∧ formula_has_free_variable f i
  end.

Structure Sentence F R V (L: Language F R) := {
  sentenceFormula:> Formula V L;
  sentenceProperty: ∀ i, ¬ formula_has_free_variable sentenceFormula i
}.

Fixpoint interpreted_term F R (V: eqType) (L: Language F R) (M: Structure L) (assignment: V → domain M) (T: Term V L): domain M :=
  match T with
  | variable x => assignment x
  | function_term f v => function M f (finfun (interpreted_term M assignment \o v))
  end.

Fixpoint satisfies F R (V: eqType) (L: Language F R) (M: Structure L) (A: Formula V L) (assignment: V → domain M): Prop :=
  match A with
  | atomic_formula r v => relation M r (vmap (interpreted_term M assignment) v)
  | negation f => ¬ satisfies M f assignment
  | disjunction f1 f2 => satisfies M f1 assignment ∨ satisfies M f2 assignment
  | conjunction f1 f2 => satisfies M f1 assignment ∧ satisfies M f2 assignment
  | existence_quantifier v f => ∃ i, satisfies M f (λ x, if v == x then i else assignment x)
  | universal_quantifier v f => ∀ i, satisfies M f (λ x, if v == x then i else assignment x) 
  end.

Definition sentence_satisfies F R V (L: Language F R) (M: Structure L) (A: Sentence V L) :=
  ∀ a, satisfies M A a.


Structure Embedding Fm Rm Fn Rn (Lm: Language Fm Rm) (Ln: Language Fn Rn) (M: Structure Lm) (N: Structure Ln) := {
  domain_map: domain M → domain N;
  function_map: Fm → Fn;
  relation_map: Rm → Rn;
  function_arity_preserved: ∀ f, function_arity Lm f = function_arity Ln (function_map f);
  relation_arity_preserved: ∀ r, relation_arity Lm r = relation_arity Ln (relation_map r);
  embedding_function_property: ∀ f v, domain_map (function M f v) =
    function N (function_map f) (vmap domain_map (rew [λ W, (domain M ^ W)%type] (function_arity_preserved f) in v));
  embedding_relation_property: ∀ r v, relation M r v ↔
    relation N (relation_map r) (vmap domain_map (rew [λ W, (domain M ^ W)%type] (relation_arity_preserved r) in v));
}.

Definition injective A B (f: A → B) := ∀ a b, f a = f b → a = b.
Definition bijective A B (f: A → B) := forall (y: B), exists ! (x: A), f x = y.

Definition embedding_is_isomorphism Fm Rm Fn Rn (Lm: Language Fm Rm) (Ln: Language Fn Rn)
  (M: Structure Lm) (N: Structure Ln) (E: Embedding M N) :=
  bijective (domain_map E) ∧ bijective (function_map E) ∧ bijective (relation_map E).
(* Is the definition correct? *)

Definition embedding_is_substructure F R (L: Language F R) (M: Structure L) (N: Structure L) (E: Embedding M N) :=
  injective (domain_map E) ∧ (function_map E =1 id) ∧ (relation_map E =1 id).


Fixpoint quantifier_free_formula F R (V: eqType) (L: Language F R) (A: Formula V L): Prop :=
  match A with
  | existence_quantifier v f => False
  | universal_quantifier v f => False
  | atomic_formula r v => True
  | negation f => quantifier_free_formula f
  | disjunction f1 f2 | conjunction f1 f2 => quantifier_free_formula f1 /\ quantifier_free_formula f2
  end.

Theorem T1_1_8 F R (V: eqType) (L: Language F R) (M N: Structure L) (E: Embedding M N)
  (Hfun: function_map E =1 id) (Hrel: relation_map E =1 id) (assignment: V → domain M)
  (A: Formula V L) (H1: quantifier_free_formula A):
  satisfies M A assignment ↔ satisfies N A (domain_map E \o assignment).
Proof.
  destruct E. simpl in *.
  assert (∀ (f: F) (v: domain M ^ function_arity L f), domain_map0 (function M f v) = function N f (vmap domain_map0 v)).
  { intros. rewrite embedding_function_property0. pose (Hfun f). simpl in e. revert e.
    generalize (function_arity_preserved0 f). simpl. rewrite Hfun. intros.
    rewrite (eq_irrelevance e erefl). simpl. auto. }
  clear embedding_function_property0.
  assert (∀ (r: R) (v: domain M ^ relation_arity L r), relation M r v ↔ relation N r (vmap domain_map0 v)).
  { intros. rewrite embedding_relation_property0. pose (Hrel r). simpl in e. revert e.
    generalize (relation_arity_preserved0 r). simpl. rewrite Hrel. intros.
    rewrite (eq_irrelevance e erefl). simpl. tauto. }
  clear embedding_relation_property0.
  revert H1. induction A; simpl in *; intros.
  + rewrite H0. unfold vmap, comp in *.
    assert ([ffun x => domain_map0 ([ffun x0 => interpreted_term M assignment (f x0)] x)] =
            [ffun x => interpreted_term N (λ x0, domain_map0 (assignment x0)) (f x)]).
    { apply eq_ffun. intro. simpl in x. rewrite ffunE. generalize (f x).
      apply Term_induction.
      + intros. simpl. auto.
      + intros. simpl in *. unfold comp. rewrite H. f_equal. apply eq_dffun. intros. simpl in *.
        rewrite <- H2. rewrite ffunE. auto. }
    rewrite H2. tauto.
  + rewrite IHA; tauto; auto.
  + destruct H1. rewrite IHA1. rewrite IHA2. tauto. auto. auto.
  + destruct H1. rewrite IHA1. rewrite IHA2. tauto. auto. auto.
  + elim H1.
  + elim H1.
Qed.

Definition elementary_equivalent F R V (L: Language F R) (M N: Structure L) :=
  ∀ (A: Sentence V L), sentence_satisfies M A ↔ sentence_satisfies N A.

Definition full_theory F R V (L: Language F R) (M: Structure L) :=
  λ (A: Sentence V L), sentence_satisfies M A.

Theorem full_theory_thm00 F R (V: eqType) (L: Language F R) (M N: Structure L):
  (∀ x, @full_theory _ _ V _ M x ↔ @full_theory _ _ V _ N x) ↔ elementary_equivalent V M N.
Proof.
  unfold full_theory, elementary_equivalent. tauto.
Qed.

(* Theorem T1_1_10. Suppose that j: M → N is an isomorphism. Then, elementary_equivalent M N. *)


Definition Theory F R V (L: Language F R) := Sentence V L → Prop.

Definition Model F R V (L: Language F R) (Th: Theory V L) (M: Structure L) :=
  ∀ (A: Sentence V L), Th A → sentence_satisfies M A. 

Definition satisfiable F R V (L: Language F R) (Th: Theory V L) := ∃ (M: Structure L), Model Th M.

Definition elementary_class F R V (L: Language F R) (K: Structure L → Prop) := ∃ (Th: Theory V L), (∀ x, K x ↔ Model Th x).

Definition logical_consequence F R V (L: Language F R) (Th: Theory V L) (A: Sentence V L) :=
  ∀ (M: Structure L), Model Th M → sentence_satisfies M A.
