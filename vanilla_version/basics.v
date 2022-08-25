Require Import Utf8 List Arith utils.
Import EqNotations.
Set Implicit Arguments.

(* Language, Term, Formula *)

Structure Language F R := {
  function_arity: F → nat;
  relation_arity: R → nat
}.

Inductive preTerm F R V (L: Language F R): Type :=
  | variable: V → preTerm V L
  | function_term: ∀ (f: F), list (preTerm V L) → preTerm V L.
Arguments variable {_} {_} {_} {L}. (*?*)

Definition preTerm_induction F R V (L: Language F R) (P: preTerm V L → Prop):
  (∀ (s: V), P (variable s)) →
  (∀ (f: F) (v: list (preTerm V L)), Forall P v → P (function_term f v)) →
  ∀ T, P T.
Proof.
  intros H H0. refine (fix IHt (t: preTerm V L) := match t with variable v => H v | function_term f T => _ end).
  refine (H0 _ T _). induction T; constructor; auto.
Defined.

Definition preTerm_recursion F R V (L: Language F R) (P: preTerm V L → Type):
  (∀ v: V, P (variable v)) →
  (∀ (f: F) (v: list (preTerm V L)), hlist P v → P (function_term f v)) →
  ∀ t, P t.
Proof.
  intros H H0. refine (fix IHt (t: preTerm V L) := match t with variable v => H v | function_term f T => _ end).
  refine (H0 _ T _). induction T.
  + constructor.
  + constructor. apply IHt. exact IHT.
Defined.

Fixpoint term_correct F R V (L: Language F R) (T: preTerm V L): bool :=
  match T with
  | variable v => true
  | function_term f x => andb (Nat.eqb (length x) (function_arity L f)) (forallb (@term_correct F R V L) x)
  end.

Definition Term F R V (L: Language F R) := { T: preTerm V L | term_correct T = true }.
Coercion Term_proj1 F R V (L: Language F R) (T: Term V L) := proj1_sig T.

Inductive preFormula F R V (L: Language F R): Type :=
  | equality: preTerm V L → preTerm V L → preFormula V L
  | atomic_formula: ∀ (r: R), list (preTerm V L) → preFormula V L
  | negation: preFormula V L → preFormula V L
  | disjunction: preFormula V L → preFormula V L → preFormula V L
  | conjunction: preFormula V L → preFormula V L → preFormula V L
  | existence_quantifier: V → preFormula V L → preFormula V L
  | universal_quantifier: V → preFormula V L → preFormula V L.

Definition formula_correct F R V (L: Language F R) (A: preFormula V L): bool.
Proof.
  induction A.
  + exact (andb (term_correct p) (term_correct p0)).
  + exact (andb (Nat.eqb (length l) (relation_arity L r)) (forallb (@term_correct F R V L) l)).
  + exact IHA.
  + exact (andb IHA1 IHA2).
  + exact (andb IHA1 IHA2).
  + exact IHA.
  + exact IHA.
Defined.

Definition Formula F R V (L: Language F R) := { A: preFormula V L | formula_correct A = true }.
Coercion Formula_proj1 F R V (L: Language F R) (A: Formula V L) := proj1_sig A.

Definition preterm_has_variable F R V (L: Language F R) (i: V) (T: preTerm V L): Prop.
Proof.
  induction T using preTerm_recursion.
  + exact (i = v).
  + induction X. exact False. exact (f0 ∨ IHX).
Defined.

Definition preformula_has_free_variable F R V (L: Language F R) (i: V) (A: preFormula V L): Prop.
Proof.
  induction A.
  + exact (preterm_has_variable i p ∨ preterm_has_variable i p0).
  + exact (Exists (preterm_has_variable i) l).
  + exact IHA.
  + exact (IHA1 ∨ IHA2).
  + exact (IHA1 ∨ IHA2).
  + exact (v ≠ i ∧ IHA).
  + exact (v ≠ i ∧ IHA).
Defined.

Definition has_n_free_variables F R V (L: Language F R) (A: preFormula V L) (n: nat) :=
  ∃ (v: list V), NoDup v ∧ length v = n ∧ (∀ (x: V), preformula_has_free_variable x A ↔ In x v).

Structure Sentence F R V (L: Language F R) := {
  sentenceFormula:> Formula V L;
  sentenceProperty: ∀ i, ¬ preformula_has_free_variable i sentenceFormula
}.

(* Structure, Interpretation *)

Structure Structure {F R} (L: Language F R) := {
  domain: Type;
  function: ∀ (f: F) (x: list domain) (H: length x = function_arity L f), domain;
  relation: ∀ (r: R) (x: list domain) (H: length x = relation_arity L r), Prop
}.

Definition interpreted_term F R V (L: Language F R) (M: Structure L) (assignment: V → domain M) (T: Term V L): domain M.
Proof.
  destruct T as [T H]. induction T using preTerm_recursion.
  + exact (assignment v).
  + simpl in *. apply andb_prop in H. destruct H. apply beq_nat_true in H. rewrite forallb_forall in H0.
    assert { x: list (domain M) | length x = length v } as D.
    { clear H. induction v; simpl in *.
      + exists nil; auto.
      + inversion X; subst; clear X. assert (term_correct a = true).
        { apply H0; auto. }
        assert (∀ x, In x v → term_correct x = true).
        { intros. apply H0. auto. }
        destruct (IHv X1 H1). exists (X0 H :: x). simpl. auto. }
    destruct D. rewrite H in e. exact (function M f x e).
Defined.

Definition interpreted_formula F R V (dec: eq_dec V) (L: Language F R) (M: Structure L) (assignment: V → domain M)
  (A: Formula V L): Prop.
Proof.
  destruct A as [A H]. induction A; simpl in *.
  + apply andb_prop in H. destruct H.
    exact (interpreted_term M assignment (exist _ p H) = interpreted_term M assignment (exist _ p0 H0)).
  + apply andb_prop in H. destruct H. apply beq_nat_true in H. rewrite forallb_forall in H0.
    assert { x : list (domain M) | length x = length l } as D.
    { clear H. induction l; simpl in *.
      + exists nil; auto.
      + assert (∀ x, In x l → term_correct x = true).
        { intros. apply H0. auto. }
        assert (term_correct a = true).
        { apply H0. auto. }
        destruct (IHl H). exists (interpreted_term M assignment (exist _ a H1) :: x). simpl. auto. }
    destruct D. rewrite H in e. exact (relation M r x e).
  + exact (IHA H).
  + apply andb_prop in H. destruct H. exact (IHA1 H ∧ IHA2 H0).
  + apply andb_prop in H. destruct H. exact (IHA1 H ∧ IHA2 H0).
  + exact (IHA H).
  + exact (IHA H).
Defined.

Definition model_of_sentence F R V (dec: eq_dec V) (L: Language F R) (M: Structure L) (A: Sentence V L) :=
  ∀ a, interpreted_formula dec M a A.

Definition model F R V (dec: eq_dec V) (L: Language F R) (M: Structure L) (A: Sentence V L → Prop) :=
  ∀ a, A a → model_of_sentence dec M a.

(* Embedding, Isomorphism, Automorphism *)

Structure Embedding Fm Rm Fn Rn (Lm: Language Fm Rm) (Ln: Language Fn Rn) (M: Structure Lm) (N: Structure Ln) := {
  domain_map: domain M → domain N;
  function_map: Fm → Fn;
  relation_map: Rm → Rn;
  domain_map_property: injective domain_map;
  function_arity_preserved: ∀ f, function_arity Lm f = function_arity Ln (function_map f);
  relation_arity_preserved: ∀ r, relation_arity Lm r = relation_arity Ln (relation_map r);
  embedding_function_property: ∀ f v H, domain_map (function M f v (H: length v = function_arity Lm f)) =
    function N (function_map f) (map domain_map v)
    (eq_trans (eq_trans (map_length domain_map v) H) (function_arity_preserved f));
  embedding_relation_property: ∀ r v H, relation M r v H ↔
    relation N (relation_map r) (map domain_map v)
    (eq_trans (eq_trans (map_length domain_map v) H) (relation_arity_preserved r))
 }.

Structure Isomorphism Fm Rm Fn Rn (Lm: Language Fm Rm) (Ln: Language Fn Rn) (M: Structure Lm) (N: Structure Ln) := {
  isomorphism_emb: Embedding M N;
  isomorphism_emb_inv: Embedding N M;
  isomorphism_property_1: ∀ x, domain_map isomorphism_emb (domain_map isomorphism_emb_inv x) = x;
  isomorphism_property_2: ∀ x, domain_map isomorphism_emb_inv (domain_map isomorphism_emb x) = x
}.

Definition Automorphism F R (L: Language F R) (M: Structure L) := Isomorphism M M.

(* Definable set *)

Definition replace_variables V (dec: eq_dec V) M (v: list V) (m: list M) n (H: length v = n) (H0: length m = n)
  (assignment: V → M): V → M.
Proof.
  intro x. destruct (In_dec dec x v).
  + refine (nth m H0 (index dec v H x i)).
  + exact (assignment x).
Defined.

Definition definable F R (L: Language F R) (M: Structure L) n (X: ∀ l, length l = n → Prop) :=
  ∃ V (dec: eq_dec V) (A: Formula V L), has_n_free_variables A n ∧
    ∀ (a: V → domain M) (v: list V) (H: length v = n), (∀ (m: list (domain M)) (H0: length m = n),
      X m H0 ↔ interpreted_formula dec M (replace_variables dec v m H H0 a) A).

(* Theory, Entailment, Satisfiable, Deductively closed *)

Definition Theory F R V (dec: eq_dec V) (L: Language F R) (C: Structure L → Prop): Sentence V L → Prop :=
  λ (A: Sentence V L), ∀ (M: Structure L), C M → model_of_sentence dec M A.

Definition satisfiable_theory F R (L: Language F R) (C: Structure L → Prop) :=
  ∃ V (dec: eq_dec V) (M: Structure L), model dec M (Theory dec C).

Definition entailment F R V (dec: eq_dec V) (L: Language F R) (S: Sentence V L → Prop) (A: Sentence V L) :=
  ∀ (M: Structure L), model dec M S → model_of_sentence dec M A.

Definition deductively_closed F R V (dec: eq_dec V) (L: Language F R) (S: Sentence V L → Prop) :=
  ∀ (A: Sentence V L), entailment dec S A.

Definition deductive_closure F R V (dec: eq_dec V) (L: Language F R) (S: Sentence V L → Prop): Sentence V L → Prop :=
  λ (A: Sentence V L), entailment dec S A.

(* Completeness *)

Theorem negation_of_sentence_as_sentence F R V (L: Language F R) (A: Sentence V L): Sentence V L.
Proof.
  destruct A. destruct sentenceFormula0. refine (let X: Formula V L := _ in _). Unshelve.
  2:{ exists (negation x). simpl. auto. }
  refine (Build_Sentence X _). simpl in *. auto.
Defined.

Definition complete F R V (dec: eq_dec V) (L: Language F R) (S: Sentence V L → Prop) :=
  ∀ (A: Sentence V L), entailment dec S A ∨ entailment dec S (negation_of_sentence_as_sentence A).

(* Elementary equivalence *)

Definition elementary_equivalence F R (L: Language F R) (M N: Structure L) :=
  ∀ V (dec: eq_dec V) (A: Sentence V L), model_of_sentence dec M A ↔ model_of_sentence dec N A.

