/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# IMO 2009 C2

For each $n ∈ ℕ$, find the largest integer $k$ such that there exist $k$ triples
  $(a_1, b_1, c_1), …, (a_k, b_k, c_k)$ with the following properties:
* $a_i + b_i + c_i$ for all $i ≤ k$;
* for any $i ≠ j$, we have $a_i ≠ a_j$, $b_i ≠ b_j$, and $c_i ≠ c_j$.

### Answer

$⌊2n/3⌋ + 1$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
-/

namespace IMOSL
namespace IMO2009C2

open Finset

/-! ### Extra lemmas -/

/-- For any finite set `S ⊆ ℕ`, the sum of all elements of `S` is at least `C(#S, 2)`. -/
theorem card_choose_le_nat_sum (S : Finset ℕ) : Nat.choose #S 2 ≤ ∑ s ∈ S, s := by
  ---- Induction on `S` via inserting greater elements; the base case is trivial.
  induction S using Finset.induction_on_max with | h0 => rfl | step m S hmS hS => ?_
  ---- Since `m` is greater than all elements of `S`, we have `#S ≤ m`.
  have hmS0 : #S ≤ m := calc
    #S ≤ #(range m) := card_le_card λ k hk ↦ mem_range.mpr (hmS k hk)
    _ = m := card_range m
  replace hmS : m ∉ S := λ h ↦ Nat.lt_irrefl m (hmS _ h)
  ---- Now just do the calculations.
  calc Nat.choose #(insert m S) 2
    _ = Nat.choose (#S + 1) 2 := by rw [card_insert_of_notMem hmS]
    _ = #S + Nat.choose #S 2 := by
      rw [Nat.choose_succ_left _ _ Nat.two_pos, Nat.choose_one_right]
    _ ≤ m + ∑ s ∈ S, s := Nat.add_le_add hmS0 hS
    _ = ∑ s ∈ insert m S, s := (sum_insert hmS (f := id)).symm

/-- If `f : ι → ℕ` is injective, thenf or any finite set `I ⊆ ι`,
  the sum of `f(i)` across all `i ∈ I` is at least `C(#I, 2)`. -/
theorem card_choose_le_sum_of_inj {f : ι → ℕ} (hf : f.Injective) (I : Finset ι) :
    Nat.choose #I 2 ≤ ∑ i ∈ I, f i := calc
  _ = Nat.choose #(I.image f) 2 := by rw [card_image_of_injective I hf]
  _ ≤ ∑ i ∈ I.image f, i := card_choose_le_nat_sum (I.image f)
  _ = ∑ i ∈ I, f i := sum_image λ _ _ _ _ h ↦ hf h

/-- The map `f : Fin k → ℕ` defined by `f(i) = 2(k - i - 1)` is injective. -/
theorem fin_cast_sub_two_mul_injective (k : ℕ) :
    (λ i : Fin k ↦ 2 * (k - 1 - i.val)).Injective := by
  match k with | 0 => exact λ x _ ↦ x.elim0 | k + 1 => ?_
  have h : 2 ≠ 0 := Nat.succ_ne_zero 1
  intro a b h0; rw [Nat.add_sub_cancel, Nat.mul_right_inj h] at h0
  rw [Fin.ext_iff, ← Nat.add_right_inj (n := k - a.val),
    Nat.sub_add_cancel a.is_le, h0, Nat.sub_add_cancel b.is_le]





/-! ### Start of the problem -/

/-- A collection `((x_{0i}, x_{1i}, x_{2i}))_{i ∈ ι}` of triples is called `n`-*good*
  if `x_{ji} ≠ x_{ji'}` whenever `i ≠ i'` and `x_{0i} + x_{1i} + x_{2i} = n` for all `i`. -/
structure GoodTripleFn (n : ℕ) (ι : Type*) where
  toFun : Fin 3 → ι → ℕ
  toFun_inj : ∀ j, (toFun j).Injective
  toFun_sum : ∀ i, ∑ j : Fin 3, toFun j i = n


namespace GoodTripleFn

/-- Subcollection of an `n`-good collection, which is also an `n`-good collection. -/
def ofEmbedding (f : κ ↪ ι) (X : GoodTripleFn n ι) : GoodTripleFn n κ where
  toFun := λ j k ↦ X.toFun j (f k)
  toFun_inj := λ j ↦ (X.toFun_inj j).comp f.injective
  toFun_sum := λ k ↦ X.toFun_sum (f k)

/-- If there is an `ι`-indexed `n`-good collection and `|κ| ≤ |ι|`,
  then there is also a `κ`-indexed `n`-good collection. -/
theorem nonempty_of_card_le [Fintype ι] [Fintype κ]
    (hι : Nonempty (GoodTripleFn n ι)) (h : Fintype.card κ ≤ Fintype.card ι) :
    Nonempty (GoodTripleFn n κ) :=
  (Function.Embedding.nonempty_of_card_le h).elim λ f ↦ hι.elim λ X ↦ ⟨ofEmbedding f X⟩

/-- If there is an `ι`-indexed `n`-good collection, then `|ι| ≤ 2n/3 + 1`. -/
theorem card_bound [Fintype ι] (X : GoodTripleFn n ι) :
    Fintype.card ι ≤ 2 * n / 3 + 1 := by
  ---- Denote `k := |ι|`.
  let k : ℕ := Fintype.card ι
  ---- Prove `3 k(k - 1)/2 ≤ kn` by counting.
  have h : 3 * Nat.choose k 2 ≤ k * n := calc
    _ = ∑ _ : Fin 3, Nat.choose #(univ : Finset ι) 2 := (sum_const _).symm
    _ ≤ ∑ j : Fin 3, ∑ i : ι, X.toFun j i :=
      sum_le_sum λ j _ ↦ card_choose_le_sum_of_inj (X.toFun_inj j) _
    _ = ∑ i : ι, ∑ j : Fin 3, X.toFun j i := sum_comm
    _ = ∑ _ : ι, n := Fintype.sum_congr _ _ X.toFun_sum
    _ = k * n := sum_const _
  ---- In code, it is more convenient to use `3k(k - 1) ≤ 2kn`.
  replace h : k * ((k - 1) * 3) ≤ k * (2 * n) := calc
    _ = 3 * (k * (k - 1)) := by rw [← Nat.mul_assoc, Nat.mul_comm]
    _ = 3 * Nat.choose k 2 * 2 := by
      have h0 : (k * (k - 1)) / 2 * 2 = k * (k - 1) :=
        Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.even_mul_pred_self k))
      rw [Nat.choose_two_right, Nat.mul_assoc, h0]
    _ ≤ k * n * 2 := Nat.mul_le_mul_right 2 h
    _ = k * (2 * n) := by rw [Nat.mul_assoc, Nat.mul_comm n 2]
  ---- Solve the case `k = 0`, then solve the case `k > 0`.
  obtain h0 | h0 : k = 0 ∨ 0 < k := Nat.eq_zero_or_pos _
  · exact h0.trans_le (Nat.zero_le _)
  · refine Nat.le_add_of_sub_le ((Nat.le_div_iff_mul_le (Nat.succ_pos 2)).mpr ?_)
    exact Nat.le_of_mul_le_mul_left h h0

/-- Creating a new `n`-good collection by adding a fixed value to a fixed coordinate. -/
def add_val (X : GoodTripleFn n ι) (j₀ : Fin 3) (v : ℕ) : GoodTripleFn (n + v) ι where
  toFun := λ j i ↦ X.toFun j i + if j = j₀ then v else 0
  toFun_inj := λ j a b h ↦ X.toFun_inj j (Nat.add_right_cancel h)
  toFun_sum := λ j ↦ by rw [sum_add_distrib, X.toFun_sum, Fintype.sum_ite_eq']

/-- Construction of a `3k`-good collection of `2k + 1` triples. -/
def default_of_0mod3 (k) : GoodTripleFn (3 * k) (Fin (k + 1) ⊕ Fin k) where
  toFun j := match j with
    | 0 => Sum.elim (λ i ↦ i) (λ i ↦ k + 1 + i)
    | 1 => Sum.elim (λ i ↦ k + i) (λ i ↦ i)
    | 2 => Sum.elim (λ i ↦ 2 * (k - i)) (λ i ↦ 2 * (k - 1 - i) + 1)
  toFun_inj j := match j with
    | 0 => Function.Injective.sumElim
        Fin.val_injective
        (λ _ _ h ↦ Fin.val_injective (Nat.add_left_cancel h))
        (λ a b ↦ (Nat.lt_add_right _ a.is_lt).ne)
    | 1 => Function.Injective.sumElim
        (λ _ _ h ↦ Fin.val_injective (Nat.add_left_cancel h))
        Fin.val_injective
        (λ a b ↦ (Nat.lt_add_right _ b.is_lt).ne.symm)
    | 2 => Function.Injective.sumElim
        (fin_cast_sub_two_mul_injective (k + 1))
        (λ _ _ h0 ↦ fin_cast_sub_two_mul_injective k (Nat.add_right_cancel h0))
        (λ _ _ ↦ Nat.two_mul_ne_two_mul_add_one)
  toFun_sum i := match i with
    | Sum.inl i => calc
        _ = i + (k + i) + 2 * (k - i) := Fin.sum_univ_three _
        _ = k + 2 * i + 2 * (k - i) := by rw [Nat.add_left_comm, ← Nat.two_mul]
        _ = k + 2 * k := by rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' i.is_le]
        _ = 3 * k := by rw [Nat.add_comm, ← Nat.succ_mul]
    | Sum.inr i => calc
        _ = k + 1 + i + i + (2 * (k - 1 - i) + 1) := Fin.sum_univ_three _
        _ = k + 2 * ((k - 1 - i) + (i + 1)) := by
          rw [Nat.add_right_comm k, Nat.add_assoc k, Nat.add_assoc, Nat.add_left_comm i,
            Nat.add_add_add_comm, ← Nat.two_mul, Nat.add_assoc, ← Nat.mul_add]
        _ = k + 2 * k := by rw [Nat.sub_sub, Nat.add_comm 1, Nat.sub_add_cancel i.is_lt]
        _ = 3 * k := by rw [Nat.add_comm, ← Nat.succ_mul]

/-- Construction of a `3k + 1`-good collection of `2k + 1` triples. -/
def default_of_1mod3 (k) : GoodTripleFn (3 * k + 1) (Fin (k + 1) ⊕ Fin k) :=
  (default_of_0mod3 k).add_val 2 1

/-- Construction of a `3k + 2`-good collection of `2k + 2` triples. -/
def default_of_2mod3 (k) : GoodTripleFn (3 * k + 2) (Fin (k + 1) ⊕ Fin (k + 1)) where
  toFun := λ j ↦ match j with
    | 0 => Sum.elim (λ i ↦ i) (λ i ↦ k + 1 + i)
    | 1 => Sum.elim (λ i ↦ k + 2 + i) (λ i ↦ i)
    | 2 => Sum.elim (λ i ↦ 2 * (k - i)) (λ i ↦ 2 * (k - i) + 1)
  toFun_inj := λ j ↦ match j with
    | 0 => Function.Injective.sumElim
        Fin.val_injective
        (λ _ _ h ↦ Fin.val_injective (Nat.add_left_cancel h))
        (λ a b ↦ (Nat.lt_add_right _ a.is_lt).ne)
    | 1 => Function.Injective.sumElim
        (λ _ _ h ↦ Fin.val_injective (Nat.add_left_cancel h))
        Fin.val_injective
        (λ a b ↦ (Nat.lt_add_right a.val (Nat.lt_succ_of_lt b.is_lt)).ne.symm)
    | 2 =>
        let h := fin_cast_sub_two_mul_injective (k + 1)
        Function.Injective.sumElim h
          (λ _ _ h0 ↦ h (Nat.add_right_cancel h0))
          (λ _ _ ↦ Nat.two_mul_ne_two_mul_add_one)
  toFun_sum i := match i with
    | Sum.inl i => calc
        _ = i + (k + 2 + i) + 2 * (k - i) := Fin.sum_univ_three _
        _ = k + 2 + 2 * i + 2 * (k - i) := by rw [Nat.add_left_comm, ← Nat.two_mul]
        _ = k + 2 + 2 * k := by
          rw [Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' i.is_le]
        _ = 3 * k + 2 := by rw [Nat.add_right_comm, Nat.add_comm k, ← Nat.succ_mul]
    | Sum.inr i => calc
        _ = k + 1 + i + i + (2 * (k - i) + 1) := Fin.sum_univ_three _
        _ = k + 1 + 2 * i + (2 * (k - i) + 1) := by
          rw [Nat.add_assoc (k + 1), ← Nat.two_mul]
        _ = k + 1 + (2 * k + 1) := by
          rw [Nat.add_assoc, ← Nat.add_assoc (2 * i),
            ← Nat.mul_add, Nat.add_sub_cancel' i.is_le]
        _ = 3 * k + 2 := by rw [Nat.add_add_add_comm, Nat.add_comm k, ← Nat.succ_mul]

/-- If `|ι| ≤ 2n/3 + 1`, then there is an `ι`-indexed `n`-good collection. -/
theorem nonempty_of_le_bound [Fintype ι] (h : Fintype.card ι ≤ 2 * n / 3 + 1) :
    Nonempty (GoodTripleFn n ι) := by
  have three_pos : 0 < 3 := Nat.succ_pos 2
  ---- First write `n = 3k + r` where `r < 3`.
  obtain ⟨k, r, hr, rfl⟩ : ∃ k, ∃ r < 3, n = 3 * k + r :=
    ⟨n / 3, n % 3, Nat.mod_lt n three_pos, (n.div_add_mod 3).symm⟩
  ---- Now split into three cases.
  have fin_sum_fin_card (a b) : Fintype.card (Fin a ⊕ Fin b) = a + b := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  replace hr : (r = 0 ∨ r = 1) ∨ r = 2 := by
    rwa [Nat.lt_succ_iff, Nat.le_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one] at hr
  rcases hr with (rfl | rfl) | rfl
  ---- Case 1: `r = 0`.
  · refine nonempty_of_card_le ⟨default_of_0mod3 k⟩ (h.trans_eq ?_)
    rw [fin_sum_fin_card, Nat.add_right_comm, ← Nat.two_mul, Nat.add_zero (3 * k),
      Nat.mul_left_comm, Nat.mul_div_cancel_left _ three_pos]
  ---- Case 2: `r = 1`.
  · refine nonempty_of_card_le ⟨default_of_1mod3 k⟩ (h.trans_eq ?_)
    rw [fin_sum_fin_card, Nat.add_right_comm, ← Nat.two_mul,
      Nat.mul_succ, Nat.mul_left_comm, Nat.mul_add_div three_pos]
  ---- Case 3: `r = 2`.
  · refine nonempty_of_card_le ⟨default_of_2mod3 k⟩ (h.trans_eq ?_)
    rw [fin_sum_fin_card, ← Nat.two_mul, Nat.mul_add, Nat.mul_left_comm,
      Nat.mul_add_div three_pos, Nat.add_assoc, Nat.mul_succ 2 k]

/-- There exists an `ι`-indexed `n`-good collection if and only if `ι ≤ ⌊2n/3⌋ + 1`. -/
theorem nonempty_iff [Fintype ι] :
    Nonempty (GoodTripleFn n ι) ↔ Fintype.card ι ≤ 2 * n / 3 + 1 :=
  ⟨λ h ↦ h.elim λ X ↦ X.card_bound, GoodTripleFn.nonempty_of_le_bound⟩

end GoodTripleFn


/-- Final solution -/
theorem final_solution :
    IsGreatest {k | Nonempty (GoodTripleFn n (Fin k))} (2 * n / 3 + 1) := by
  conv => left; right; ext k; rw [GoodTripleFn.nonempty_iff, Fintype.card_fin]
  exact ⟨Nat.le_refl _, λ _ ↦ id⟩
