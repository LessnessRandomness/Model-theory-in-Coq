Require Import Lia Utf8.
Import EqNotations.
Set Implicit Arguments.

Definition eq_dec A := ∀ (x y: A), { x = y } + { x ≠ y }.

Definition fin n := { i | i < n }.

Inductive vector A: nat → Type :=
  | vnil: vector A 0
  | vcons: ∀ (n: nat), A → vector A n → vector A (S n).
Arguments vnil {A}.

Notation "A ^ n" := (vector A n): vector_scope.
Notation "[ ]" := (vnil) (format "[ ]"): vector_scope.
Notation "[ x ]" := (vcons x nil): vector_scope.
Notation "[ x ; y ; .. ; z ]" := (vcons x (vcons y .. (vcons z vnil) ..)): vector_scope.

Open Scope vector_scope.

Inductive hvector A (F: A → Type): ∀ n, A^n → Type :=
  | Hnil: hvector F vnil
  | Hcons: ∀ n x v, F x → hvector F v → hvector F (@vcons _ n x v).

Module vector.
  Fixpoint In A n i (v: A^n): Prop :=
    match v with
    | vnil => False
    | vcons x t => i = x ∨ In i t
    end.

  Definition In_dec A (dec: eq_dec A) i n (v: A^n): { In i v } + { ¬ In i v }.
  Proof.
    induction v; simpl; auto. destruct IHv.
    + left. auto.
    + destruct (dec i a).
      - left. auto.
      - right. tauto.
  Defined.

  Definition index A (dec: eq_dec A) i n (v: A^n) (H: In i v): fin n.
  Proof.
    induction v.
    + elim H.
    + simpl in H. destruct (dec i a).
      - exists 0. intuition.
      - assert (In i v) by tauto. destruct (IHv H0). exists (S x). intuition.
  Defined.

  Definition nth A n (v: A^n) (i: fin n): A.
  Proof.
    induction v.
    + destruct i. abstract lia.
    + destruct i. destruct x.
      - exact a.
      - assert (x < n) by intuition. apply IHv. exists x. auto.
  Defined.

  Fixpoint map A B n (f: A → B) (v: A^n): B^n :=
    match v with
    | vnil => vnil
    | vcons x t => vcons (f x) (map f t)
    end.

  Fixpoint fold_right A B (f: B → A → A) (a0: A) n (v: B^n): A :=
  match v with
  | vnil => a0
  | vcons x t => f x (fold_right f a0 t)
  end.
  Definition Forall A (P: A → Prop) n (v: A^n) := fold_right (λ x, and (P x)) True v.
  Definition Exists A (P: A → Prop) n (v: A^n) := fold_right (λ x, or (P x)) False v.

  Inductive NoDup A: ∀ n, A^n → Prop :=
  | NoDup_nil: NoDup vnil
  | NoDup_cons: ∀ x n (v: A^n), ¬ In x v → NoDup v → NoDup (vcons x v).
End vector.

Definition injective A B (f: A → B) := ∀ x y, f x = f y → x = y.

Module nonconstructive.
  (* Indefinite description *)
  Definition ID := ∀ A (P: A → Prop), (∃ x, P x) → { x | P x }.
  (* Law of excluded middle *)
  Definition LEM := ∀ (P: Prop), P ∨ ¬ P.

  (* Disjunction to sumbool. *)
  Theorem D2S: ID → ∀ (A B: Prop), (A ∨ B) → {A} + {B}.
  Proof.
    intros H A B. intro. assert (ex (fun _: A + B => True)).
    { destruct H0.
      + exists (inl H0). auto.
      + exists (inr H0). auto. }
    apply H in H1. destruct H1. destruct x; auto.
  Qed.
End nonconstructive.
