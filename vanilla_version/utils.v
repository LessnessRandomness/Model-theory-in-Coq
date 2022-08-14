Require Import Utf8 Lia List.
Import EqNotations.
Set Implicit Arguments.

Definition injective A B (f: A → B) := ∀ x y, f x = f y → x = y.

Definition eq_dec A := ∀ (x y: A), { x = y } + { x ≠ y }.

Definition fin n := { i | i < n }.

Definition index A (dec: eq_dec A) (l: list A) n (H: length l = n) (x: A) (H0: In x l): fin n.
Proof.
  revert n H. induction l; simpl in *; intros.
  + elim H0.
  + destruct (dec a x).
    - exists 0. abstract lia.
    - assert (In x l) by tauto. assert (length l = n - 1) by lia.
      destruct (IHl H1 _ H2). exists (S x0). abstract lia.
Defined.

Definition nth A n (l: list A) (H: length l = n) (i: fin n): A.
Proof.
  revert n H i. induction l; simpl in *; intros.
  + destruct i. abstract lia.
  + destruct i. destruct x.
    - exact a.
    - assert (x < n - 1) by abstract lia. apply (IHl (n - 1)); try abstract lia.
      exists x; auto.
Defined.

Inductive hlist A (F: A → Type): list A → Type :=
  | Hnil: hlist F nil
  | Hcons: ∀ x v, F x → hlist F v → hlist F (@cons _ x v).

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
