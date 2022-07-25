From mathcomp Require Import all_ssreflect.
Require Import Utf8.
Import EqNotations.
Set Implicit Arguments.

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
  | equality: ∀ (T1 T2: Term V L), Formula V L
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
  | equality t1 t2 => interpreted_term M assignment t1 = interpreted_term M assignment t2
  | atomic_formula r v => relation M r (vmap (interpreted_term M assignment) v)
  | negation f => ¬ satisfies M f assignment
  | disjunction f1 f2 => satisfies M f1 assignment ∨ satisfies M f2 assignment
  | conjunction f1 f2 => satisfies M f1 assignment ∧ satisfies M f2 assignment
  | existence_quantifier v f => ∃ i, satisfies M f (λ x, if v == x then i else assignment x)
  | universal_quantifier v f => ∀ i, satisfies M f (λ x, if v == x then i else assignment x) 
  end.

Definition sentence_satisfies F R V (L: Language F R) (M: Structure L) (A: Sentence V L) :=
  ∀ a, satisfies M A a.

Definition injective A B (f: A → B) := ∀ a b, f a = f b → a = b.

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


Definition has_n_free_variables F R V (L: Language F R) (A: Formula V L) (n: nat) :=
  ∃ (v: V ^ n), uniq (codom v) ∧ (∀ (x: V), formula_has_free_variable A x ↔ x \in codom v).

Definition replace_variables {V: eqType} M n (v: V ^ n) (m: M ^ n) (assignment: V → M): V → M.
Proof.
  intro x. remember (x \in codom v) as W. destruct W.
  + refine (m _). exists (index x (codom v)). 
    assert (size (codom v) = n). { rewrite size_codom. simpl. apply card_ord. }
    assert (index x (codom v) < size (codom v)). { rewrite index_mem. auto. }
    rewrite H in H0. auto.
  + exact (assignment x).
Defined.

Definition definable F R (L: Language F R) (M: Structure L) n (X: domain M ^ n → Prop) :=
  ∃ (V: eqType) (A: Formula V L), has_n_free_variables A n ∧
     ∀ (a: V → domain M) (v: V ^ n), (∀ (m: domain M ^ n), X m ↔ satisfies M A (replace_variables v m a)).


