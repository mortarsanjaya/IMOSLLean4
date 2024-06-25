/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.IntLinearSolver
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Order.Lemmas

/-!
# IMO 2014 A4

Let $b$ and $c$ be integers with $|b| > 1$ and $c ≠ 0$.
Find all functions $f : ℤ → ℤ$ such that, for any $x, y ∈ ℤ$,
$$ f(y + f(x)) - f(y) = f(bx) - f(x) + c. $$
-/

namespace IMOSL
namespace IMO2014A4

/-- Given `b k : ℤ` with `k ≠ 0`, there exists `m < n` such that `b^m ≡ b^n (mod k)`. -/
theorem exists_ne_pow_eq (h : k ≠ 0) (b : ℤ) :
    ∃ m n : ℕ, m ≠ n ∧ b ^ m % k = b ^ n % k := by
  have h0 : Set.MapsTo (b ^ · % k) Set.univ (Finset.Ico 0 (|k|)) := λ x _ ↦ by
    rw [Finset.coe_Ico, Set.mem_Ico]
    exact ⟨(b ^ x).emod_nonneg h, (b ^ x).emod_lt h⟩
  obtain ⟨m, -, n, -, h, h0⟩ :=
    Set.infinite_univ.exists_ne_map_eq_of_mapsTo h0 (Set.toFinite _)
  exact ⟨m, n, h, h0⟩





/-! ## Start of the problem -/

def good (b c : ℤ) (f : ℤ → ℤ) :=
  ∀ x y : ℤ, f (y + f x) - f y = f (b * x) - f x + c

theorem linear_good (k m : ℤ) : good (k + 1) (k * m) (k * · + m) := λ x y ↦ by
  rw [add_sub_add_right_eq_sub, mul_add, add_sub_cancel_left, add_one_mul (α := ℤ),
    add_sub_add_right_eq_sub, ← mul_sub, add_sub_cancel_right, ← mul_add]




section good_lemmas

variable (h : good b c f)

theorem map_map_zero_add (y : ℤ) : f (y + f 0) = c + f y :=
  by rw [← sub_eq_iff_eq_add, h, mul_zero, sub_self, zero_add]

theorem map_mul_map_zero_add (y k : ℤ) : f (y + f 0 * k) = c * k + f y := by
  have h0 n : f (y + f 0 * (n + 1)) = c + f (y + f 0 * n) := by
    rw [mul_add_one (α := ℤ), ← add_assoc, map_map_zero_add h]
  replace h0 := Extra.IntIntLinearSolverAlt (f := λ n ↦ f (y + f 0 * n)) h0 k
  rwa [mul_zero, add_zero] at h0

theorem map_b_pow_mul_eq_of_map_eq (h0 : f x = f y) :
    ∀ k : ℕ, f (b ^ k * x) = f (b ^ k * y)
  | 0 => by rwa [pow_zero, one_mul, one_mul]
  | k + 1 => by
      rw [pow_succ', mul_assoc, mul_assoc]
      have h1 := h (b ^ k * y) 0
      rwa [← map_b_pow_mul_eq_of_map_eq h0 k, h, add_left_inj, sub_left_inj] at h1

variable (h0 : 1 < b.natAbs) (h1 : c ≠ 0)

theorem map_is_linear : ∀ n : ℤ, f n = (b - 1) * n + f 0 := by
  ---- Solve the problem assuming `f` is injective
  suffices f.Injective from λ n ↦ by
    have h2 := eq_add_of_sub_eq' (h 0 (b * n))
    rw [mul_zero, sub_self, zero_add, ← sub_left_inj (a := f n),
      add_sub_right_comm, ← h n n, sub_left_inj] at h2
    rw [sub_one_mul, ← add_sub_right_comm, this h2, add_sub_cancel_left]
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
  rw [eq_add_of_sub_eq' h4, add_mul, mul_assoc, h7, add_mul,
    mul_assoc, h7, h5, add_left_inj, Int.mul_eq_mul_left_iff h1] at h6
  refine (Int.mul_eq_mul_left_iff λ h8 ↦ ?_).mp h6
  rw [h8, mul_zero, sub_eq_zero] at h4
  exact h3 (Int.pow_right_injective h0 h4)

theorem c_eq_b_sub_one_mul_map_zero : c = (b - 1) * f 0 := by
  have h3 := h 0 0
  rwa [zero_add, mul_zero, sub_self, zero_add,
    map_is_linear h h0 h1, add_sub_cancel_right, eq_comm] at h3

end good_lemmas





/-! ## Final solution -/

/-- Final solution -/

theorem final_solution {b c : ℤ} (h : 1 < b.natAbs) (h0 : c ≠ 0) :
    good b c f ↔ b - 1 ∣ c ∧ f = ((b - 1) * · + c / (b - 1)) :=
  ---- `←` direction
  ⟨λ hf ↦ by
    have h1 := c_eq_b_sub_one_mul_map_zero hf h h0
    refine ⟨⟨f 0, h1⟩, funext λ n ↦ ?_⟩
    rw [map_is_linear hf h h0, h1, add_right_inj]
    refine (Int.mul_ediv_cancel_left _ ?_).symm
    rw [h1, mul_ne_zero_iff] at h0; exact h0.1,
  ---- `→` direction
  λ hf ↦ by
    rw [← sub_add_cancel b 1]
    rcases hf with ⟨⟨m, rfl⟩, rfl⟩
    rw [Int.mul_ediv_cancel_left _ (mul_ne_zero_iff.mp h0).1]
    exact linear_good (b - 1) m⟩


/-
variable {b c : ℤ} (h : 1 < b.natAbs) (h0 : c ≠ 0)

/-- Final solution, Case 1: `b - 1 ∤ c` -/
theorem final_solution_case1 (h1 : ¬b - 1 ∣ c) : ¬good b c f :=
  λ h2 ↦ h1 ⟨f 0, c_eq_b_sub_one_mul_map_zero h2 h h0⟩

/-- Final solution, Case 2: `b - 1 ∣ c` -/
theorem final_solution_case2 (h1 : b - 1 ∣ c) :
    good b c f ↔ f = ((b - 1) * · + c / (b - 1)) :=
  ⟨λ h2 ↦ by
    rcases h1 with ⟨k, rfl⟩
    have h1 := c_eq_b_sub_one_mul_map_zero h2 h h0
    have h3 := (mul_ne_zero_iff.mp h0).1
    rw [Int.mul_ediv_cancel_left _ h3]
    rw [mul_eq_mul_left_iff, or_iff_left h3] at h1
    rw [h1]; exact funext (map_is_linear h2 h h0),
  λ h2 ↦ h2.symm ▸ linear_good h1⟩
-/
