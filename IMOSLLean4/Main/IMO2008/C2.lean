/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic

/-!
# IMO 2008 C2

Let $n$ be a positive integer.
Determine the number $N_n$ of permutations $σ$ from $\{0, 1, …, n - 1\}$ to itself
  such that $k$ divides $2(σ(0) + σ(1) + … + σ(k - 1))$ for each integer $k ≤ n$.

### Answer

We have $N_n = n!$ for $n < 3$ and $N_n = 6 \cdot 2^{n - 3}$ for all $n ≥ 3$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2008SL.pdf).
Just like in the official solution, the desired permutations are called **nice**.
Note that the original version asks for permutations of $\{1, 2, …, n\}$.
It is easy to see that these two versions are equivalent.
We modify the official solution accordingly.
-/

namespace IMOSL
namespace IMO2008C2

open Finset Fin.NatCast

/-! ### Extra lemmas -/

section

open Function

/-- If `σ : Fin n → Fin n` is a permutation, then `2 ∑_i σ(i) = n(n - 1)`. -/
theorem two_mul_sum_equiv_fin [NeZero n] (σ : Equiv.Perm (Fin n)) :
    2 * ∑ i ∈ range n, (σ i : ℕ) = n * (n - 1) := by
  have h : ∑ i ∈ range n, (σ i : ℕ) = ∑ i ∈ range n, i := calc
    _ = ∑ i : Fin n, (σ (i : ℕ) : ℕ) := (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ i : Fin n, (σ i : ℕ) := by simp_rw [Fin.cast_val_eq_self]
    _ = ∑ i : Fin n, (i : ℕ) := Equiv.sum_comp _ _
    _ = ∑ i ∈ range n, i := Fin.sum_univ_eq_sum_range id _
  rw [h, Nat.mul_comm, sum_range_id_mul_two]

/-- If `σ : Fin (n + 1) → Fin (n + 1)` is a permutation, then `2 ∑_i σ(i) = (n + 1)n`. -/
theorem two_mul_sum_equiv_fin_succ (σ : Equiv.Perm (Fin (n + 1))) :
    2 * ∑ i ∈ range (n + 1), (σ i : ℕ) = (n + 1) * n := by
  rw [two_mul_sum_equiv_fin, Nat.add_sub_cancel]

/-- Let `f, g : Fin n → Fin n` with `f ∘ g = id`.
  Define `f₀, g₀ : Fin (n + 1) → Fin (n + 1)` by `f₀(i) = f(i), g₀(i) = g(i)`
    for `i < n` and `f₀(n) = g₀(n) = n`. Then `f₀ ∘ g₀ = id`. -/
theorem snoc_castSucc_inverse {f g : Fin n → Fin n} (h : ∀ j, f (g j) = j) (i) :
    Fin.snoc (α := λ _ ↦ Fin (n + 1)) (Fin.castSucc ∘ f) (Fin.last n)
      (Fin.snoc (α := λ _ ↦ Fin (n + 1)) (Fin.castSucc ∘ g) (Fin.last n) i) = i := by
  obtain ⟨j, rfl⟩ | rfl : (∃ j : Fin n, i = j.castSucc) ∨ i = Fin.last n :=
    i.eq_castSucc_or_eq_last
  · rw [Fin.snoc_castSucc, comp_apply, Fin.snoc_castSucc, comp_apply, h]
  · rw [Fin.snoc_last, Fin.snoc_last]

/-- Let `f, g : Fin n → Fin n` with `f ∘ g = id`.
  Define `f₀, g₀ : Fin (n + 1) → Fin (n + 1)` by `f₀(i + 1) = f(i), g₀(i) = g(i) + 1`
    for `i < n` and `f₀(0) = n, g₀(n) = 0`. Then `f₀ ∘ g₀ = id`. -/
theorem cons_last_snoc_zero_inverse {f g : Fin n → Fin n} (h : ∀ j, f (g j) = j) (i) :
    Fin.cons (α := λ _ ↦ Fin (n + 1)) (Fin.last n) (Fin.castSucc ∘ f)
      (Fin.snoc (α := λ _ ↦ Fin (n + 1)) (Fin.succ ∘ g) 0 i) = i := by
  obtain ⟨j, rfl⟩ | rfl : (∃ j : Fin n, i = j.castSucc) ∨ i = Fin.last n :=
    i.eq_castSucc_or_eq_last
  · rw [Fin.snoc_castSucc, comp_apply, Fin.cons_succ, comp_apply, h]
  · rw [Fin.snoc_last, Fin.cons_zero]

/-- Let `f, g : Fin n → Fin n` with `f ∘ g = id`.
  Define `f₀, g₀ : Fin (n + 1) → Fin (n + 1)` by `f₀(i) = f(i) + 1, g₀(i + 1) = g(i)`
    for `i < n` and `f₀(n) = 0, g₀(0) = n`. Then `f₀ ∘ g₀ = id`. -/
theorem snoc_zero_cons_last_inverse {f g : Fin n → Fin n} (h : ∀ j, f (g j) = j) (i) :
    Fin.snoc (α := λ _ ↦ Fin (n + 1)) (Fin.succ ∘ f) 0
      (Fin.cons (α := λ _ ↦ Fin (n + 1)) (Fin.last n) (Fin.castSucc ∘ g) i) = i := by
  obtain rfl | ⟨j, rfl⟩ : i = 0 ∨ ∃ j : Fin n, i = j.succ := i.eq_zero_or_eq_succ
  · rw [Fin.cons_zero, Fin.snoc_last]
  · rw [Fin.cons_succ, comp_apply, Fin.snoc_castSucc, comp_apply, h]

/-- Let `σ : Fin (n + 1) → Fin (n + 1)` and `j = σ(0)`.
  Then `σ(i + 1) ≠ j` for any `i : Fin n`. -/
theorem equiv_map_castSucc_ne_of_map_zero
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : σ 0 = j) (i : Fin n) : (σ i.succ) ≠ j :=
  λ h ↦ Fin.succ_ne_zero i (σ.injective (h.trans hσ.symm))

/-- Let `σ : Fin (n + 1) → Fin (n + 1)` and `j = σ(n)`.
  Then `σ(i) ≠ j` for any `i : Fin n`. -/
theorem equiv_map_castSucc_ne_of_map_last
    {σ : Equiv.Perm (Fin (n + 1))} (hσ : σ (Fin.last n) = j) (i : Fin n) :
    (σ i.castSucc) ≠ j :=
  λ h ↦ Fin.castSucc_ne_last i (σ.injective (h.trans hσ.symm))


end





/-! ### Appending new element to a permutation on `Fin` -/

/-- Obtaining a permutation on `Fin (n + 1)` from a permutation on `Fin n`
  by appending `0` on the back and incrementing the other elements. -/
def snoc_zero_equiv (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.snoc (Fin.succ ∘ σ) 0
  invFun := Fin.cons (Fin.last n) (Fin.castSucc ∘ σ.symm)
  left_inv := cons_last_snoc_zero_inverse σ.symm_apply_apply
  right_inv := snoc_zero_cons_last_inverse σ.apply_symm_apply

/-- Obtaining a permutation on `Fin (n + 1)` from a
  permutation on `Fin n` by appending `n` on the back. -/
def snoc_last_equiv (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) where
  toFun := Fin.snoc (Fin.castSucc ∘ σ) (Fin.last n)
  invFun := Fin.snoc (Fin.castSucc ∘ σ.symm) (Fin.last n)
  left_inv := snoc_castSucc_inverse σ.symm_apply_apply
  right_inv := snoc_castSucc_inverse σ.apply_symm_apply

/-- Obtaining a permutation on `Fin (n + 1)` from a permutation on `Fin n` by
  appending `0` (when the boolean is set to `false`) or `n` (otherwise) on the back. -/
def snoc_equiv (p : Bool × Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  bif p.1 then snoc_last_equiv p.2 else snoc_zero_equiv p.2

/-- For any `i : Fin n`, we have `snoc_last_equiv σ i = σ(i) + 1`. -/
theorem snoc_zero_equiv_apply_castSucc (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    snoc_zero_equiv σ i.castSucc = (σ i).succ :=
  Fin.snoc_castSucc (α := λ _ ↦ Fin (n + 1)) _ _ i

/-- For any `i : Fin n`, we have `snoc_last_equiv σ i = σ(i)`. -/
theorem snoc_last_equiv_apply_castSucc (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    snoc_last_equiv σ i.castSucc = (σ i).castSucc :=
  Fin.snoc_castSucc (α := λ _ ↦ Fin (n + 1)) _ _ i

/-- We have `snoc_zero_equiv σ n = n`. -/
theorem snoc_zero_equiv_apply_last (σ : Equiv.Perm (Fin n)) :
    snoc_zero_equiv σ (Fin.last n) = 0 :=
  Fin.snoc_last (α := λ _ ↦ Fin (n + 1)) _ _

/-- We have `snoc_last_equiv σ n = n`. -/
theorem snoc_last_equiv_apply_last (σ : Equiv.Perm (Fin n)) :
    snoc_last_equiv σ (Fin.last n) = Fin.last n :=
  Fin.snoc_last (α := λ _ ↦ Fin (n + 1)) _ _

/-- We have `snoc_equiv (b, σ) n` equal to `0` if `b = false` and `n` if `b = true`. -/
theorem snoc_equiv_apply_last (p : Bool × Equiv.Perm (Fin n)) :
    snoc_equiv p (Fin.last n) = bif p.1 then Fin.last n else 0 :=
  match p with
  | (false, σ) => snoc_zero_equiv_apply_last σ
  | (true, σ) => snoc_last_equiv_apply_last σ

/-- The function `snoc_zero_equiv` is injective. -/
theorem snoc_zero_equiv_injective {n} : (snoc_zero_equiv (n := n)).Injective := by
  intro σ τ h; refine Equiv.ext λ i ↦ ?_
  rw [← Fin.succ_inj, ← snoc_zero_equiv_apply_castSucc, h, snoc_zero_equiv_apply_castSucc]

/-- The function `snoc_last_equiv` is injective. -/
theorem snoc_last_equiv_injective {n} : (snoc_last_equiv (n := n)).Injective := by
  intro σ τ h; refine Equiv.ext λ i ↦ ?_
  rw [← Fin.castSucc_inj, ← snoc_last_equiv_apply_castSucc,
    h, snoc_last_equiv_apply_castSucc]

/-- The function `snoc_equiv` is injective. -/
theorem snoc_equiv_injective [NeZero n] : (snoc_equiv (n := n)).Injective := by
  rintro ⟨b, σ⟩ ⟨c, τ⟩ h
  have h0 : Fin.last n ≠ 0 := mt Fin.last_eq_zero_iff.mp (NeZero.ne n)
  match b, c with
  | false, false => exact Prod.mk_right_inj.mpr (snoc_zero_equiv_injective h)
  | false, true =>
      refine absurd (Equiv.congr_fun h (Fin.last n)) ?_
      simpa only [snoc_equiv_apply_last] using h0.symm
  | true, false =>
      refine absurd (Equiv.congr_fun h (Fin.last n)) ?_
      simpa only [snoc_equiv_apply_last] using h0
  | true, true => exact Prod.mk_right_inj.mpr (snoc_last_equiv_injective h)


section

variable {σ : Equiv.Perm (Fin (n + 1))} (hσ : σ (Fin.last n) = 0)
include hσ

/-- The inverse function for `snoc_zero_equiv`. -/
def snoc_zero_inverse : Equiv.Perm (Fin n) where
  toFun i := (σ i.castSucc).pred (equiv_map_castSucc_ne_of_map_last hσ i)
  invFun i := (σ.symm i.succ).castPred
    (equiv_map_castSucc_ne_of_map_zero (σ.symm_apply_eq.mpr hσ.symm) i)
  left_inv i := by simp_rw [Fin.succ_pred, Equiv.symm_apply_apply, Fin.castPred_castSucc]
  right_inv i := by simp_rw [Fin.castSucc_castPred, Equiv.apply_symm_apply, Fin.pred_succ]

/-- The function `snoc_zero_inverse` is the right inverse for `snoc_zero_equiv`. -/
theorem snoc_zero_equiv_inverse : snoc_zero_equiv (snoc_zero_inverse hσ) = σ := by
  ext i; obtain ⟨j, rfl⟩ | rfl : (∃ j : Fin n, i = j.castSucc) ∨ i = Fin.last n :=
    i.eq_castSucc_or_eq_last
  · rw [snoc_zero_equiv_apply_castSucc, snoc_zero_inverse, Equiv.coe_fn_mk, Fin.succ_pred]
  · rw [snoc_zero_equiv_apply_last, hσ]

end


section

variable {σ : Equiv.Perm (Fin (n + 1))} (hσ : σ (Fin.last n) = Fin.last n)

/-- The inverse function for `snoc_last_equiv`. -/
def snoc_last_inverse : Equiv.Perm (Fin n) where
  toFun i := (σ i.castSucc).castPred (equiv_map_castSucc_ne_of_map_last hσ i)
  invFun i := (σ.symm i.castSucc).castPred
    (equiv_map_castSucc_ne_of_map_last (σ.symm_apply_eq.mpr hσ.symm) i)
  left_inv i := by simp_rw [Fin.castSucc_castPred, σ.symm_apply_apply, Fin.castPred_castSucc]
  right_inv i := by simp_rw [Fin.castSucc_castPred, σ.apply_symm_apply, Fin.castPred_castSucc]

/-- The function `snoc_last_inverse` is the right inverse for `snoc_last_equiv`. -/
theorem snoc_last_equiv_inverse : snoc_last_equiv (snoc_last_inverse hσ) = σ := by
  ext i; obtain ⟨j, rfl⟩ | rfl : (∃ j : Fin n, i = j.castSucc) ∨ i = Fin.last n :=
    i.eq_castSucc_or_eq_last
  · rw [snoc_last_equiv_apply_castSucc, snoc_last_inverse,
      Equiv.coe_fn_mk, Fin.castSucc_castPred]
  · rw [snoc_last_equiv_apply_last, hσ]

end


/-- The image of `snoc_zero_equiv` is the set of `σ` with` σ(n) = 0`. -/
theorem eq_snoc_zero_equiv_iff {σ : Equiv.Perm (Fin (n + 1))} :
    (∃ τ, snoc_zero_equiv τ = σ) ↔ σ (Fin.last n) = 0 :=
  ⟨λ ⟨τ, hτ⟩ ↦ hτ ▸ snoc_zero_equiv_apply_last τ,
  λ hσ ↦ ⟨snoc_zero_inverse hσ, snoc_zero_equiv_inverse hσ⟩⟩

/-- The image of `snoc_last_equiv` is the set of `σ` with` σ(n) = n`. -/
theorem eq_snoc_last_equiv_iff {σ : Equiv.Perm (Fin (n + 1))} :
    (∃ τ, snoc_last_equiv τ = σ) ↔ σ (Fin.last n) = Fin.last n :=
  ⟨λ ⟨τ, hτ⟩ ↦ hτ ▸ snoc_last_equiv_apply_last τ,
  λ hσ ↦ ⟨snoc_last_inverse hσ, snoc_last_equiv_inverse hσ⟩⟩

/-- The image of the sum of `snoc_zero_equiv` and `snoc_last_equiv`
  is the set of `σ` with `σ(n) ∈ {0, n}`. -/
theorem eq_snoc_equiv_iff {σ : Equiv.Perm (Fin (n + 1))} :
    (∃ p, snoc_equiv p = σ) ↔ σ (Fin.last n) = 0 ∨ σ (Fin.last n) = Fin.last n := by
  rw [Prod.exists, Bool.exists_bool]
  exact or_congr eq_snoc_zero_equiv_iff eq_snoc_last_equiv_iff





/-! ### Start of the problem -/

/-- A permutation `σ : Fin n → Fin n` is called nice if for any `k ≤ n`,
  `k` divides `2(σ(0) + σ(1) + … + σ(k - 1))`. -/
def nice (σ : Equiv.Perm (Fin n)) :=
  match n with
  | 0 => True
  | _ + 1 => ∀ k ≤ n, k ∣ 2 * ∑ i ∈ range k, (σ i : ℕ)

/-- A permutation on `Fin 0` is nice. -/
theorem perm_zero_is_nice (σ : Equiv.Perm (Fin 0)) : nice σ :=
  trivial

/-- Definition of a nice permutation on `Fin n` for `n ≠ 0`. -/
theorem nice_def [NeZero n] {σ : Equiv.Perm (Fin n)} :
    nice σ ↔ ∀ k ≤ n, k ∣ 2 * ∑ i ∈ range k, (σ i : ℕ) := by
  cases n with | zero => exact absurd rfl (NeZero.ne 0) | succ n => rfl

/-- The property `nice` is decidable. -/
instance : DecidablePred (nice (n := n)) :=
  λ _ ↦ match n with | 0 => isTrue trivial | _ + 1 => Nat.decidableBallLE _ _

/-- The construction `snoc_zero_equiv` preserves niceness. -/
theorem snoc_zero_equiv_nice_iff_nice {σ : Equiv.Perm (Fin n)} :
    nice (snoc_zero_equiv σ) ↔ nice σ := by
  cases n with | zero => decide +revert | succ m => ?_
  let n := m + 1
  ---- The sum condition at `k = n + 1` is automatic.
  set τ : Equiv.Perm (Fin (m + 2)) := snoc_zero_equiv σ
  simp_rw [nice_def, Nat.le_add_one_iff (n := m + 1), or_imp, forall_and, forall_eq]
  refine (and_iff_left ⟨n, two_mul_sum_equiv_fin_succ _⟩).trans
    (forall_congr' λ k ↦ imp_congr_right λ hk ↦ ?_)
  ---- Thus we only need to check that `Σ_{i < k} τ(i) = Σ_{i < k} σ(i) + 2k` for `k ≤ n`.
  suffices ∀ i ∈ range k, (τ i : ℕ) = σ i + 1 by
    rw [sum_congr rfl this, sum_add_distrib, sum_const, nsmul_one, Nat.cast_id,
      card_range, Nat.mul_add, Nat.dvd_add_left (Nat.dvd_mul_left k 2)]
  intro i hi; replace hi : i < n := Nat.lt_of_lt_of_le (mem_range.mp hi) hk
  lift i to Fin n using hi
  rw [Fin.coe_eq_castSucc, Fin.cast_val_eq_self, snoc_zero_equiv_apply_castSucc]; rfl

/-- The construction `snoc_last_equiv` preserves niceness. -/
theorem snoc_last_equiv_nice_iff_nice {σ : Equiv.Perm (Fin n)} :
    nice (snoc_last_equiv σ) ↔ nice σ := by
  cases n with | zero => decide +revert | succ m => ?_
  let n := m + 1
  ---- The sum condition at `k = n + 1` is automatic.
  set τ : Equiv.Perm (Fin (n + 1)) := snoc_last_equiv σ
  unfold nice; simp_rw [Nat.le_add_one_iff (n := m + 1), or_imp, forall_and, forall_eq]
  refine (and_iff_left ⟨n, two_mul_sum_equiv_fin_succ _⟩).trans
    (forall_congr' λ k ↦ imp_congr_right λ hk ↦ ?_)
  ---- Thus we only need to check that `Σ_{i < k} τ(i) = Σ_{i < k} σ(i)` for `k ≤ n`.
  suffices ∀ i ∈ range k, (τ i : ℕ) = σ i by rw [sum_congr rfl this]
  intro i hi; replace hi : i < n := Nat.lt_of_lt_of_le (mem_range.mp hi) hk
  lift i to Fin n using hi
  rw [Fin.coe_eq_castSucc, Fin.cast_val_eq_self, snoc_last_equiv_apply_castSucc]; rfl

/-- The construction `snoc_equiv` preserves niceness. -/
theorem snoc_equiv_nice_iff_nice {p : Bool × Equiv.Perm (Fin n)} :
    nice (snoc_equiv p) ↔ nice p.2 :=
  match p with
  | (false, _) => snoc_zero_equiv_nice_iff_nice
  | (true, _) => snoc_last_equiv_nice_iff_nice


section

variable (hn : n ≥ 3)
include hn

/-- If `n ≥ 3`, then `σ(n) ∈ {0, n}` for any nice permutation `σ` on `Fin (n + 1)`. -/
theorem nice.map_last_eq_zero_or_last {σ : Equiv.Perm (Fin (n + 1))} (hσ : nice σ) :
    σ (Fin.last n) = 0 ∨ σ (Fin.last n) = Fin.last n := by
  have hn0 : 1 ≤ n := Nat.zero_lt_of_lt hn
  ---- First note that `n ∣ 2σ(n)`, and write `2σ(n) = kn`.
  obtain ⟨k, h⟩ : n ∣ 2 * σ (Fin.last n) := by
    rw [← Fin.natCast_eq_last, Nat.dvd_add_iff_right (hσ n (Nat.le_succ n)),
      ← Nat.mul_add, ← sum_range_succ, two_mul_sum_equiv_fin_succ]
    exact ⟨n + 1, Nat.mul_comm _ _⟩
  ---- Now we show that `k ∈ {0, 1, 2}`.
  obtain rfl | rfl | rfl : k = 0 ∨ k = 2 ∨ k = 1 := by
    suffices k ≤ 2 by
      rwa [or_left_comm, ← Nat.le_one_iff_eq_zero_or_eq_one, ← Nat.le_succ_iff_eq_or_le]
    refine Nat.le_of_mul_le_mul_right ?_ hn0
    rw [Nat.mul_comm, ← h]
    exact Nat.mul_le_mul_left 2 (Fin.is_le _)
  ---- If `k = 0` then we are done.
  · rw [Nat.mul_zero, Nat.mul_eq_zero, or_iff_right (Nat.succ_ne_zero 1)] at h
    left; exact Fin.val_eq_zero_iff.mp h
  ---- If `k = 2` then we are also done.
  · rw [Nat.mul_comm, Nat.mul_left_inj (Nat.succ_ne_zero 1)] at h
    right; exact Fin.eq_of_val_eq h
  ---- Now assume `k = 1` and `2σ(n) = n`, and start with `2 ∑_{i < n} σ(i) = n^2`.
  replace h : (2 : ℕ) * σ (Fin.last n) = n := h.trans (Nat.mul_one _)
  have h0 : 2 * ∑ i ∈ range n, (σ i : ℕ) = n * n := by
    refine Nat.add_right_cancel (m := 2 * σ (Fin.last n)) ?_
    calc 2 * ∑ i ∈ range n, (σ i : ℕ) + 2 * σ (Fin.last n)
      _ = 2 * ∑ i ∈ range (n + 1), (σ i : ℕ) := by
        rw [sum_range_succ, Fin.natCast_eq_last, Nat.mul_add]
      _ = (n + 1) * n := two_mul_sum_equiv_fin σ
      _ = n * n + 2 * σ (Fin.last n) := by rw [Nat.succ_mul, h]
  ---- Then the niceness condition implies `2σ(n - 1) ≡ n^2 ≡ 2σ(n) (mod n - 1)`.
  replace h0 : 2 * σ (n - 1 : ℕ) ≡ 2 * σ (Fin.last n) [MOD n - 1] := calc
    _ ≡ 2 * σ (n - 1 : ℕ) + 2 * ∑ i ∈ range (n - 1), (σ i : ℕ) [MOD n - 1] :=
      let h : n - 1 ≤ n + 1 := (Nat.sub_le n 1).trans (Nat.le_succ n)
      Nat.left_modEq_add_iff.mpr (hσ _ h)
    _ = 2 * ∑ i ∈ range n, (σ i : ℕ) := by
      rw [← Nat.mul_add, Nat.add_comm, ← sum_range_succ, Nat.sub_add_cancel hn0]
    _ = n * n := h0
    _ ≡ 1 * n [MOD n - 1] := (Nat.modEq_sub hn0).mul_right n
    _ = 2 * σ (Fin.last n) := by rw [Nat.one_mul, h]
  ---- But `n` is even, so we actually have `σ(n - 1) ≡ σ(n) (mod n - 1)`.
  replace h0 : (σ (n - 1 : ℕ) : ℕ) ≡ σ (Fin.last n) [MOD n - 1] := by
    have h1 : Nat.gcd (n - 1) 2 = 1 := by
      rw [← Nat.Coprime, Nat.coprime_two_right, Nat.odd_sub' hn0]
      exact iff_of_true odd_one (even_iff_two_dvd.mpr ⟨σ (Fin.last n), h.symm⟩)
    exact h0.cancel_left_of_coprime h1
  ---- Before the next major step, we note that `n < 2(n - 1)` since `n ≥ 3`.
  exfalso; clear hσ
  have hn1 : n < 2 * (n - 1) := calc
    _ = n - 1 + 1 := (Nat.sub_add_cancel hn0).symm
    _ < n - 1 + (n - 1) := Nat.add_lt_add_left (Nat.lt_sub_of_add_lt hn) _
    _ = 2 * (n - 1) := (Nat.two_mul _).symm
  ---- Now we have either `σ(n - 1) < σ(n)`, `σ(n - 1) = σ(n)`, or `σ(n - 1) > σ(n)`.
  obtain h1 | h1 | h1 :
      (σ (n - 1 : ℕ) : ℕ) < σ (Fin.last n) ∨ (σ (n - 1 : ℕ) : ℕ) = σ (Fin.last n)
        ∨ (σ (n - 1 : ℕ) : ℕ) > σ (Fin.last n) :=
    Nat.lt_trichotomy _ _
  ---- If `σ(n - 1) < σ(n)`, then `n = 2σ(n) ≥ 2σ(n - 1) + 2(n - 1) ≥ 2(n - 1)`.
  · replace h0 : n - 1 ≤ σ (Fin.last n) := Nat.le_of_add_left_le (h0.add_le_of_lt h1)
    exact Nat.not_lt_of_le (Nat.mul_le_mul_left 2 h0) (hn1.trans_eq' h.symm)
  ---- If `σ(n - 1) = σ(n)`, then contradiction since `n - 1 ≠ n`.
  · rw [Fin.val_inj, σ.apply_eq_iff_eq, ← Fin.val_inj, Fin.val_natCast, Fin.val_last] at h1
    revert h1; exact Nat.ne_of_lt ((Nat.mod_le _ _).trans_lt (Nat.sub_one_lt_of_lt hn))
  ---- If `σ(n - 1) > σ(n)`, then `2σ(n - 1) ≥ 2σ(n) + 2(n - 1) > 2n`.
  · replace h0 : (σ (Fin.last n) : ℕ) + (n - 1) ≤ σ (n - 1 : ℕ) := h0.symm.add_le_of_lt h1
    refine Nat.not_lt_of_le (Nat.mul_le_mul_left 2 h0) ?_
    calc (2 : ℕ) * σ (n - 1 : ℕ)
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 (Fin.is_le _)
      _ = n + n := Nat.two_mul n
      _ < n + 2 * (n - 1) := Nat.add_lt_add_left hn1 n
      _ = 2 * (σ (Fin.last n) + (n - 1)) := by rw [Nat.mul_add, h]

/-- For `n ≥ 3`, a permutation `σ : Fin (n + 1) → Fin (n + 1)` is nice if and only if
  it equals `snoc_equiv (b, τ)` with `τ : Fin n → Fin n` being a nice permutation. -/
theorem nice_iff_exists_snoc_equiv_nice {σ : Equiv.Perm (Fin (n + 1))} :
    nice σ ↔ ∃ p : Bool × Equiv.Perm (Fin n), nice p.2 ∧ snoc_equiv p = σ := by
  refine ⟨λ hσ ↦ ?_, λ hσ ↦ ?_⟩
  ---- The `→` direction.
  · obtain ⟨p, rfl⟩ : ∃ p, snoc_equiv p = σ :=
      eq_snoc_equiv_iff.mpr (hσ.map_last_eq_zero_or_last hn)
    exact ⟨p, snoc_equiv_nice_iff_nice.mp hσ, rfl⟩
  ---- The `←` direction.
  · rcases hσ with ⟨p, hp, rfl⟩
    exact snoc_equiv_nice_iff_nice.mpr hp

/-- For `n ≥ 3`, the set of nice permutations on `Fin (n + 1)` is precisely the image of
  `snoc_equiv` on pairs `(b, σ)` where `σ` is a nice permutation on `Fin n`. -/
theorem filter_nice_eq_image_snoc_equiv :
    ({σ : Equiv.Perm (Fin (n + 1)) | nice σ} : Finset _)
      = (univ ×ˢ ({σ : Equiv.Perm (Fin n) | nice σ} : Finset _)).image snoc_equiv := by
  refine ext λ σ ↦ ?_
  rw [mem_filter_univ, nice_iff_exists_snoc_equiv_nice hn, mem_image]
  conv => right; right; ext τ
          rw [mem_product, and_iff_right (mem_univ _), mem_filter_univ]

/-- For `n ≥ 3`, the number of nice permutations on `Fin (n + 1)`
  is twice the number of nice permutations on `Fin n`. -/
theorem card_nice_perm_of_ge_three :
    #{σ : Equiv.Perm (Fin (n + 1)) | nice σ} = 2 * #{σ : Equiv.Perm (Fin n) | nice σ} := by
  haveI : NeZero n := NeZero.of_gt hn
  rw [filter_nice_eq_image_snoc_equiv hn, card_image_of_injective _ snoc_equiv_injective,
    card_product, card_univ, Fintype.card_bool]

end


/-- For every `m`, the number of nice permutations on `Fin (m + 3)` is `6 * 2^m`. -/
theorem card_nice_perm_add_three (m) :
    #{σ : Equiv.Perm (Fin (m + 3)) | nice σ} = 6 * 2 ^ m := by
  induction m with | zero => decide | succ m m_ih => ?_
  rw [card_nice_perm_of_ge_three (Nat.le_add_left 3 m),
    m_ih, Nat.mul_left_comm, Nat.pow_succ']

/-- Final solution -/
theorem final_solution (n) :
    #{σ : Equiv.Perm (Fin n) | nice σ} =
      match n with
      | 0 => 1
      | 1 => 1
      | 2 => 2
      | m + 3 => 6 * 2 ^ m := by
  match n with
  | 0 => decide
  | 1 => decide
  | 2 => decide
  | m + 3 => exact card_nice_perm_add_three m
