Require Import Utf8 List Lia Arith Nat Recdef utils basics.
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

Definition countable A := ∃ (f: A → nat), injective f.

Definition prod_countable A B (Ha: countable A) (Hb: countable B): countable (A * B)%type.
Proof.
  destruct Ha as [fa Ha], Hb as [fb Hb].
  set (fun p => match p with (x, y) => Cantor_pairing (fa x, fb y) end) as f.
  exists f. intros ? ? ?. destruct x, y; simpl. unfold f in *.
  assert ((fa a, fb b) = Cantor_pairing_inv (Cantor_pairing (fa a0, fb b0))).
  { apply Cantor_pairing_inv_thm. auto. }
  assert ((fa a0, fb b0) = Cantor_pairing_inv (Cantor_pairing (fa a0, fb b0))).
  { apply Cantor_pairing_inv_thm. auto. }
  assert (fa a = fa a0) by congruence. assert (fb b = fb b0) by congruence.
  apply Ha in H2. apply Hb in H3. congruence.
Qed.

Definition sum_eq A B (Ra: A → A → Prop) (Rb: B → B → Prop): A + B → A + B → Prop.
Proof.
  intros x y. destruct x as [xa | xb], y as [ya | yb].
  + exact (Ra xa ya).
  + exact False.
  + exact False.
  + exact (Rb xb yb).
Defined.

Definition sum_countable A B (Ha: countable A) (Hb: countable B): countable (A + B).
Proof.
  destruct Ha as [fa Ha], Hb as [fb Hb]. unfold countable.
  refine (let f: A + B → nat := _ in _). Unshelve.
  2:{ intro. destruct X. exact (fa a * 2). exact (S (fb b * 2)). }
  exists f. intros ? ? ?. unfold f in *. destruct x, y; simpl in *.
  + assert (fa a = fa a0) by lia. apply Ha in H0. congruence.
  + lia.
  + lia.
  + assert (fb b = fb b0) by lia. apply Hb in H0. congruence.
Qed.

Theorem half_bijection_an_injection A B (f: A → B) (g: B → A): (∀ x, g (f x) = x) → injective f.
Proof.
  intros H. unfold injective. intros x y H0. congruence.
Qed.


Definition encode_list (L: list nat) := List.fold_right (λ n m, (2 ^ n) * (S (m * 2))) 0 L.

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

Function decode_list (n: nat) { measure (λ x, x) } :=
  match n with
  | O => nil
  | S m => let w := get_2_power n in
           cons w (decode_list (n / (2 ^ S w)))
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

Theorem decode_encode_list_thm (L: list nat): decode_list (encode_list L) = L.
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
  induction L; simpl; rewrite decode_list_equation; auto. destruct a.
  + replace (2 ^ 0 * S (encode_list L * 2)) with (S (encode_list L * 2)) by (simpl; lia). f_equal.
    - replace (S (encode_list L * 2)) with (2 ^ 0 * S (encode_list L * 2)) by (simpl; lia). rewrite H. auto.
    - replace (S (encode_list L * 2)) with (2 ^ 0 * S (encode_list L * 2)) by (simpl; lia). rewrite H.
      simpl (2 ^ 0)%nat. simpl (2 ^ 1)%nat. replace (1 * _) with (1 + encode_list L * 2) by lia.
      rewrite Nat.div_add; try lia. simpl. auto.
  + rewrite H. assert (1 < 2 ^ S a). { apply Nat.pow_gt_1; lia. }
    replace (2 ^ S a * S (encode_list L * 2)) with (S (2 ^ S a * S (encode_list L * 2) - 1)) by lia. f_equal.
    replace (S (_ - 1)) with (2 ^ S a * S (encode_list L * 2)) by lia.
    repeat rewrite Nat.pow_succ_r'. replace (2 * (2 * 2 ^ a)) with (2 ^ a * 2 * 2) by lia.
    repeat rewrite <- Nat.div_div; try lia. replace (_ * _ * _) with (S (encode_list L * 2) * 2 * 2 ^ a) by lia.
    repeat rewrite Nat.div_mul; try lia. replace (S _) with (1 + encode_list L * 2) by lia.
    rewrite Nat.div_add; try lia. simpl. auto.
    { clear H0. induction a; simpl; try lia. }
    { clear H0. induction a; simpl; try lia. }
    { clear H0. induction a; simpl; try lia. }
Qed.

Definition lists_countable A (H: countable A): countable (list A).
Proof.
  destruct H as [f Hf]. set (λ L, encode_list (map f L)) as F.
  exists F. intros ? ? ?. unfold F in *.
  revert y H. induction x; simpl; intros.
  + assert (decode_list 0 = decode_list (encode_list (List.map f y))) by congruence.
    assert (decode_list 0 = nil) by (compute; auto). rewrite decode_encode_list_thm in H0. rewrite H1 in H0.
    symmetry in H0. apply List.map_eq_nil in H0. subst. auto.
  + destruct y.
    - simpl in H. assert (∀ w, 0 < 2 ^ w). { induction w; simpl; try lia. }
      pose (H0 (f a)). lia.
    - simpl in H. assert (f a = f a0).
      { revert H. generalize (f a) as w1, (f a0) as w2. induction w1; simpl; intros.
        + destruct w2; auto. simpl in H. lia.
        + destruct w2.
          - simpl in H. lia.
          - simpl in H. f_equal. apply IHw1. lia. }
      f_equal.
      * apply Hf. auto.
      * rewrite H0 in H. apply Nat.mul_cancel_l in H.
        ++ apply IHx. lia.
        ++ generalize (f a0) as w. induction w; simpl; lia.
Qed.


Definition encode_Term F R V (L: Language F R) (T: Term V L): list (F + V).
Proof.
  destruct T. clear e. induction x using preTerm_recursion; simpl in *.
  + exact (inr v :: nil).
  + refine (inl f :: _). induction v.
    - exact nil.
    - inversion X; subst; clear X. exact (IHv X1 ++ X0).
Defined.

