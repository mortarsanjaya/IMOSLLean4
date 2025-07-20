/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.IntLinearSolver
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Unbundled.Int

/-!
# IMO 2014 A4

Let $b$ and $c$ be integers with $|b| > 1$ and $c ≠ 0$.
Find all functions $f : ℤ → ℤ$ such that, for any $x, y ∈ ℤ$,
$$ f(y + f(x)) - f(y) = f(bx) - f(x) + c. $$
-/

namespace IMOSL
namespace IMO2014A4

/-! ### Extra lemmas -/

section

open Finset

/-- Given `b k : ℤ` with `k ≠ 0`, there exists `m < n` such that `b^m ≡ b^n (mod k)`. -/
theorem exists_ne_pow_eq (h : k ≠ 0) (b : ℤ) : ∃ m n, m ≠ n ∧ b ^ m % k = b ^ n % k := by
  suffices ∃ m ∈ range k.natAbs.succ, ∃ n ∈ range k.natAbs.succ,
      m ≠ n ∧ b ^ m % k = b ^ n % k by
    rcases this with ⟨m, -, n, -, h0⟩; exact ⟨m, n, h0⟩
  apply exists_ne_map_eq_of_card_lt_of_maps_to (t := image Nat.cast (range k.natAbs))
  · apply card_image_le.trans_lt
    rw [card_range, card_range]
    exact k.natAbs.lt_succ_self
  · rintro n -; simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio]
    have h0 := Int.natAbs_of_nonneg (Int.emod_nonneg (b ^ n) h)
    refine ⟨(b ^ n % k).natAbs, ?_, h0⟩
    rw [← Int.ofNat_lt, h0, Int.natCast_natAbs]
    exact (Int.emod_lt _ h).trans_eq k.natCast_natAbs

end





/-! ### Start of the problem -/

def good (b c : ℤ) (f : ℤ → ℤ) := ∀ x y : ℤ, f (y + f x) - f y = f (b * x) - f x + c

theorem linear_good (k m : ℤ) : good (k + 1) (k * m) (k * · + m) := λ x y ↦ by
  rw [add_sub_add_right_eq_sub, Int.mul_add, add_sub_cancel_left, Int.add_mul, Int.one_mul,
    add_sub_add_right_eq_sub, ← Int.mul_sub, add_sub_cancel_right, ← Int.mul_add]




section good_lemmas

variable (h : good b c f)
include h

theorem map_map_zero_add (y : ℤ) : f (y + f 0) = c + f y :=
  by rw [← sub_eq_iff_eq_add, h, Int.mul_zero, sub_self, zero_add]

theorem map_mul_map_zero_add (y k : ℤ) : f (y + f 0 * k) = c * k + f y := by
  have h0 n : f (y + f 0 * (n + 1)) = c + f (y + f 0 * n) := by
    rw [Int.mul_add, Int.mul_one, ← Int.add_assoc, map_map_zero_add h]
  replace h0 := Extra.LinearSolver.IntInt (f := λ n ↦ f (y + f 0 * n)) h0 k
  rwa [Int.mul_zero, Int.add_zero] at h0

theorem map_b_pow_mul_eq_of_map_eq (h0 : f x = f y) :
    ∀ k, f (b ^ k * x) = f (b ^ k * y) := by
  refine Nat.rec (by rwa [pow_zero, one_mul, one_mul]) λ k h1 ↦ ?_
  have h2 := h (b ^ k * y) 0
  rwa [← h1, h, add_left_inj, sub_left_inj, ← mul_assoc, ← mul_assoc, ← pow_succ'] at h2

variable (h0 : 1 < b.natAbs) (h1 : c ≠ 0)
include h0 h1

theorem map_is_linear : ∀ n : ℤ, f n = (b - 1) * n + f 0 := by
  ---- Solve the problem assuming `f` is injective
  suffices f.Injective from λ n ↦ by
    have h2 := eq_add_of_sub_eq' (h 0 (b * n))
    rw [Int.mul_zero, sub_self, zero_add, ← sub_left_inj (a := f n),
      add_sub_right_comm, ← h n n, sub_left_inj] at h2
    rw [Int.sub_mul, Int.one_mul, ← add_sub_right_comm, this h2, add_sub_cancel_left]
  ---- Some preliminary
  have h2 : f 0 ≠ 0 := λ h2 ↦ by
    have h3 := map_map_zero_add h 0
    rw [zero_add, h2, h2, add_zero] at h3
    exact h1 h3.symm
  obtain ⟨m, n, h3, h4⟩ := exists_ne_pow_eq h2 b
  rw [Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero] at h4
  rcases h4 with ⟨N, h4⟩
  ---- Prove that `f` is injective
  intro x y h5
  apply map_b_pow_mul_eq_of_map_eq h at h5
  have h6 := h5 m
  have h7 := map_mul_map_zero_add h
  rw [eq_add_of_sub_eq' h4, Int.add_mul, mul_assoc, h7, Int.add_mul,
    mul_assoc, h7, h5, add_left_inj, Int.mul_eq_mul_left_iff h1] at h6
  refine (Int.mul_eq_mul_left_iff λ h8 ↦ ?_).mp h6
  rw [h8, Int.mul_zero, sub_eq_zero] at h4
  exact h3 (Int.pow_right_injective h0 h4)

theorem c_eq_b_sub_one_mul_map_zero : c = (b - 1) * f 0 := by
  have h3 := h 0 0
  rwa [zero_add, Int.mul_zero, sub_self, zero_add,
    map_is_linear h h0 h1, add_sub_cancel_right, eq_comm] at h3

end good_lemmas





/-- Final solution -/
theorem final_solution {b c : ℤ} (h : 1 < b.natAbs) (h0 : c ≠ 0) :
    good b c f ↔ b - 1 ∣ c ∧ f = ((b - 1) * · + c / (b - 1)) := by
  refine ⟨λ hf ↦ ?_, λ hf ↦ ?_⟩
  ---- `→` direction
  · have h1 := c_eq_b_sub_one_mul_map_zero hf h h0
    refine ⟨⟨f 0, h1⟩, funext λ n ↦ ?_⟩
    rw [map_is_linear hf h h0, h1, add_right_inj]
    refine (Int.mul_ediv_cancel_left _ λ h2 ↦ h0 ?_).symm
    rw [h1, h2, Int.zero_mul]
  ---- `←` direction
  · rw [← sub_add_cancel b 1]
    rcases hf with ⟨⟨m, rfl⟩, rfl⟩
    refine (Int.mul_ediv_cancel_left m λ h1 ↦ h0 ?_).symm ▸ linear_good (b - 1) m
    rw [h1, Int.zero_mul]
