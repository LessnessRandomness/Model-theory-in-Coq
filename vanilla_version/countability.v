Require Import Utf8 Lia Arith Nat Setoid Morphisms Recdef utils basics.
Set Implicit Arguments.

(* Cantor pairing function *)

Definition Cantor_pairing p := match p with (x, y) => ((x + y + 1) * (x + y)) / 2 + y end.
Definition Cantor_pairing_inv (z: nat): nat * nat.
Proof.
  set ((sqrt (8 * z + 1) - 1) / 2) as w. set (div (w * w + w) 2) as t.
  set (z - t) as y. set (w - y) as x. exact (x, y).
Defined.

Theorem Cantor_pairing_inv_thm z p: Cantor_pairing p = z -> p = Cantor_pairing_inv z.
Proof.
  intros. destruct p as (x, y). unfold Cantor_pairing in H.
  remember (x + y) as w. remember ((w + 1) * w / 2) as t.
  assert (2 * t = w * w + w).
  { rewrite Heqt. clear Heqt Heqw. induction w; auto.
    replace ((S w + 1) * S w) with ((w + 1) * w + (w + 1) * 2) by ring.
    rewrite Nat.div_add; try lia. }
  assert ((2 * w + 1) * (2 * w + 1) <= 8 * z + 1) by lia.
  assert (8 * z + 1 < (2 * S w + 1) * (2 * S w + 1)) by lia.
  assert (2 * w + 1 <= sqrt (8 * z + 1)).
  { apply Nat.sqrt_le_square in H1. auto. }
  assert (sqrt (8 * z + 1) < 2 * S w + 1).
  { apply Nat.sqrt_lt_square in H2. auto. }
  assert (2 * w <= sqrt (8 * z + 1) - 1 < 2 * S w) by lia.
  assert (w <= (sqrt (8 * z + 1) - 1) / 2).
  { apply Nat.div_le_lower_bound; lia. }
  assert ((sqrt (8 * z + 1) - 1) / 2 < S w).
  { apply Nat.div_lt_upper_bound; lia. }
  assert (w = (sqrt (8 * z + 1) - 1) / 2) by lia.
  assert (y = z - t) by lia. assert (x = w - y) by lia.
  unfold Cantor_pairing_inv. rewrite <- H8, <- H0. replace (2 * t) with (t * 2) by ring.
  rewrite Nat.div_mul; try lia. f_equal; lia.
Qed.

(*-------*)

Definition injective A B Ra Rb (Ea: @Equivalence A Ra) (Eb: @Equivalence B Rb) f (Hf: Proper (Ra ==> Rb) f) :=
  ∀ x y, Rb (f x) (f y) → Ra x y.
Definition bijective A B Ra Rb (Ea: @Equivalence A Ra) (Eb: @Equivalence B Rb)
  f g (Hf: Proper (Ra ==> Rb) f) (Hg: Proper (Rb ==> Ra) g) :=
  injective Ea Eb Hf ∧ injective Eb Ea Hg.
Definition countable A R (E: @Equivalence A R) :=
  ∃ f (Hf: Proper (R ==> eq) f), injective E (@eq_equivalence nat) Hf.

Definition compose A B C Ra Rb Rc (Ea: @Equivalence A Ra) (Eb: @Equivalence B Rb) (Ec: @Equivalence C Rc)
  f g (Hf: Proper (Ra ==> Rb) f) (Hg: Proper (Rb ==> Rc) g):
  Proper (Ra ==> Rc) (λ x, g (f x)).
Proof.
  intros ? ? ?. apply Hg. apply Hf. auto.
Qed.

Definition compose_injective A B C Ra Rb Rc (Ea: @Equivalence A Ra) (Eb: @Equivalence B Rb) (Ec: @Equivalence C Rc)
  f g (Hf: Proper (Ra ==> Rb) f) (Hg: Proper (Rb ==> Rc) g) (H: injective _ _ Hf) (H0: injective _ _ Hg):
  injective Ea Ec (compose _ _ _ Hf Hg).
Proof.
  intros ? ? ?. apply H, H0. auto.
Qed.

Definition smaller_than_countable A B Ra Rb (Ea: @Equivalence A Ra) (Eb: @Equivalence B Rb)
  f (Hf: Proper (Ra ==> Rb) f) (H: injective _ _ Hf) (H0: countable Eb):
  countable Ea.
Proof.
  destruct H0 as [g [Hg H0]]. unfold countable. exists (Basics.compose g f), (compose _ _ _ Hf Hg).
  apply (compose_injective H H0).
Qed.

Definition pair_eq A B (Ra: A → A → Prop) (Rb: B → B → Prop) :=
  λ p1 p2, match p1, p2 with (x1, y1), (x2, y2) => Ra x1 x2 ∧ Rb y1 y2 end.
Definition pair_Equivalence A B Ra Rb (Ea: @Equivalence A Ra) (Eb: @Equivalence B Rb):
  @Equivalence _ (pair_eq Ra Rb).
Proof.
  split.
  + intros ?. destruct x; simpl. split. apply Ea. apply Eb.
  + intros ? ? ?. destruct x, y; simpl. destruct H; split. apply Ea. auto. apply Eb. auto.
  + intros ? ? ? ? ?. destruct x, y, z; simpl. destruct H, H0; split. etransitivity; eauto. etransitivity; eauto.
Qed.

Definition prod_countable A B Ra Rb (Ea: @Equivalence A Ra) (Eb: @Equivalence B Rb)
  (Ha: countable Ea) (Hb: countable Eb):
  countable (pair_Equivalence Ea Eb).
Proof.
  destruct Ha as [fa [Ha H0]], Hb as [fb [Hb H1]].
  set (fun p => match p with (x, y) => Cantor_pairing (fa x, fb y) end) as f.
  assert (Proper (pair_eq Ra Rb ==> eq) f).
  { intros ? ? ?. destruct x, y. unfold f, pair_eq in *. destruct H.
    f_equal. f_equal. apply Ha. auto. apply Hb. auto. }
  exists f, H. intros ? ? ?. destruct x, y; simpl. unfold f in *.
  assert ((fa a, fb b) = Cantor_pairing_inv (Cantor_pairing (fa a0, fb b0))).
  { apply Cantor_pairing_inv_thm. auto. }
  assert ((fa a0, fb b0) = Cantor_pairing_inv (Cantor_pairing (fa a0, fb b0))).
  { apply Cantor_pairing_inv_thm. auto. }
  assert (fa a = fa a0) by congruence. assert (fb b = fb b0) by congruence.
  apply H0 in H5. apply H1 in H6. auto.
Qed.

Definition list_Equivalence A R (E: @Equivalence A R): Equivalence (List.Forall2 R).
Proof.
  split.
  + intros ?. induction x; auto. constructor. reflexivity. auto.
  + intros ?. induction x; intros.
    - inversion H; subst; clear H. constructor.
    - inversion H; subst; clear H. constructor. apply E; auto. eauto.
  + intros ?. induction x; intros.
    - inversion H; subst; clear H. inversion H0; subst; clear H0. constructor.
    - inversion H; subst; clear H. inversion H0; subst; clear H0. constructor.
      etransitivity; eauto. eapply IHx; eauto.
Qed.

Theorem half_bijection_an_injection A B Ra Rb (Ea: @Equivalence A Ra) (Eb: @Equivalence B Rb)
  f g (Hf: Proper (Ra ==> Rb) f) (Hg: Proper (Rb ==> Ra) g):
  (∀ x, Ra (g (f x)) x) → injective Ea Eb Hf.
Proof.
  intros H. unfold injective. intros x y H1. apply Hg in H1. do 2 rewrite H in H1. auto.
Qed.


Definition code (L: list nat) := List.fold_right (λ n m, (2 ^ n) * (S (m * 2))) 0 L.

Function get_2_power (n: nat) { measure (λ x, x) } :=
  match n with
  | O => O
  | _ => match (n mod 2) with
         | O => S (get_2_power (n / 2))
         | _ => O
         end
  end.
Proof.
  intros. apply Nat.div_lt; lia.
Defined.

Function decode (n: nat) { measure (λ x, x) } :=
  match n with
  | O => nil
  | S m => let w := get_2_power n in
           cons w (decode (n / (2 ^ S w)))
  end.
Proof.
  intros. rewrite <- teq. rewrite Nat.pow_succ_r'. rewrite <- Nat.div_div; try lia.
  assert (n / 2 < n). { apply Nat.div_lt; lia. }
  assert (∀ m n, m / n <= m).
  { intros. destruct n0; [simpl; lia|]. destruct m0; [simpl; auto|]. destruct n0.
    + rewrite Nat.div_1_r. auto.
    + assert (S m0 / S (S n0) < S m0) by (apply Nat.div_lt; lia). lia. }
  pose proof (H0 (n / 2) (2 ^ get_2_power n)%nat). lia.
  { destruct (get_2_power n); [simpl; lia|].
    assert (1 < 2 ^ S n0) by (apply Nat.pow_gt_1; lia). lia. }
Defined.

Theorem decode_code_thm (L: list nat): decode (code L) = L.
Proof.
  assert (∀ a w, get_2_power (2 ^ a * S (w * 2)) = a).
  { intros. induction a.
    + simpl. rewrite get_2_power_equation. replace (S (w * 2 + 0)) with (1 + w * 2) by lia.
      rewrite Nat.mod_add; try lia. replace (1 mod 2) with (S O) by auto. auto.
    + rewrite get_2_power_equation. assert (1 < 2 ^ S a). { apply Nat.pow_gt_1; lia. }
      replace (_ * _) with (S (2 ^ S a * S (w * 2) - 1)) by lia.
      replace (S (_ * _ - 1)) with (2 ^ S a * S (w * 2)) by lia.
      rewrite Nat.pow_succ_r'. replace (2 * _ * _) with (2 ^ a * S (w * 2) * 2) by lia.
      rewrite Nat.mod_mul; try lia. rewrite Nat.div_mul; try lia. }
  induction L; simpl; rewrite decode_equation; auto. destruct a.
  + replace (2 ^ 0 * S (code L * 2)) with (S (code L * 2)) by (simpl; lia). f_equal.
    - replace (S (code L * 2)) with (2 ^ 0 * S (code L * 2)) by (simpl; lia). rewrite H. auto.
    - replace (S (code L * 2)) with (2 ^ 0 * S (code L * 2)) by (simpl; lia). rewrite H.
      simpl (2 ^ 0)%nat. simpl (2 ^ 1)%nat. replace (1 * _) with (1 + code L * 2) by lia.
      rewrite Nat.div_add; try lia. simpl. auto.
  + rewrite H. assert (1 < 2 ^ S a). { apply Nat.pow_gt_1; lia. }
    replace (2 ^ S a * S (code L * 2)) with (S (2 ^ S a * S (code L * 2) - 1)) by lia. f_equal.
    replace (S (_ - 1)) with (2 ^ S a * S (code L * 2)) by lia.
    repeat rewrite Nat.pow_succ_r'. replace (2 * (2 * 2 ^ a)) with (2 ^ a * 2 * 2) by lia.
    repeat rewrite <- Nat.div_div; try lia. replace (_ * _ * _) with (S (code L * 2) * 2 * 2 ^ a) by lia.
    repeat rewrite Nat.div_mul; try lia. replace (S _) with (1 + code L * 2) by lia.
    rewrite Nat.div_add; try lia. simpl. auto.
    { clear H0. induction a; simpl; try lia. }
    { clear H0. induction a; simpl; try lia. }
    { clear H0. induction a; simpl; try lia. }
Qed.

Definition lists_countable A R (E: @Equivalence A R) (H: countable E): countable (list_Equivalence E).
Proof.
  destruct H as [f [Hf H]]. set (λ L, code (List.map f L)) as F.
  assert (Proper (List.Forall2 R ==> eq) F).
  { intros ?. unfold F. induction x; simpl; intros.
    + inversion H0; subst; clear H0. reflexivity.
    + inversion H0; subst; clear H0. simpl. replace (f a) with (f y0).
      rewrite (IHx l' H5). reflexivity. apply Hf; symmetry; auto. }
  exists F, H0. intros ? ? ?. unfold F in *.
  revert y H1. induction x; simpl; intros.
  + assert (decode 0 = decode (code (List.map f y))) by congruence.
    assert (decode 0 = nil) by (compute; auto). rewrite decode_code_thm in H2. rewrite H3 in H2.
    symmetry in H2. apply List.map_eq_nil in H2. subst. constructor.
  + destruct y.
    - simpl in H1. assert (∀ w, 0 < 2 ^ w). { induction w; simpl; try lia. }
      pose (H2 (f a)). lia.
    - simpl in H1. assert (f a = f a0).
      { revert H1. generalize (f a) as w1, (f a0) as w2. induction w1; simpl; intros.
        + destruct w2; auto. simpl in H1. lia.
        + destruct w2.
          - simpl in H1. lia.
          - simpl in H1. f_equal. apply IHw1. lia. }
      constructor.
      * apply H. auto.
      * rewrite H2 in H1. apply Nat.mul_cancel_l in H1.
        ++ apply IHx. lia.
        ++ generalize (f a0) as w. induction w; simpl; lia.
Qed.

