/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.IntLinearSolver

/-!
# IMO 2015 A2

Find all functions $f : ℤ → ℤ$ such that, for any $x, y ∈ ℤ$,
$$ f(x - f(y)) = f(f(x)) - f(y) - 1. $$

### Answer

$x ↦ -1$ and $x ↦ x + 1$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2015SL.pdf).
We simplify the computations when checking which linear functions work,
  by dividing into cases of whether the slope is zero or not.
If the slope is zero, then $f$ is constant, and $f(-f(f(0))) = -1$ yields $f = -1$.
If the slope is non-zero, then $f$ is injective, so $f(x + 1) = f(f(x))$ yields
  $f(x) = x + 1$ for all $x ∈ ℤ$.
-/

namespace IMOSL
namespace IMO2015A2

/-- Final solution -/
theorem final_solution {f : Int → Int} :
    (∀ x y, f (x - f y) = f (f x) - f y - 1) ↔ (f = λ _ ↦ -1) ∨ f = (· + 1) := by
  ---- The `←` direction is easier.
  refine Iff.symm ⟨λ hf x y ↦ ?_, λ hf ↦ ?_⟩
  · rcases hf with rfl | rfl
    · rfl
    · dsimp only; rw [← Int.sub_sub, Int.sub_add_cancel, Int.sub_sub, Int.add_assoc,
        Int.add_assoc, y.add_comm (1 + 1), ← Int.sub_sub, Int.add_sub_cancel]
  ---- For the `⁻→` direction, start with `f(z) = -1`, where `z = -f(f(0))`.
  have h : f (-f (f 0)) = -1 := by
    simpa only [Int.sub_self, Int.zero_sub] using hf 0 (f 0)
  ---- Now prove that `f(x + 1) = f(f(x))` for any integer `x`.
  have h0 (x) : f (x + 1) = f (f x) := by
    simpa only [Int.sub_neg, Int.add_sub_cancel, h] using hf x (-f (f 0))
  ---- Now prove that `f` is linear with slope `A = f(-1) + 1`.
  replace hf : ∀ n, f n = (f (-1) + 1) * n + f 0 := by
    refine Extra.LinearSolver.IntInt λ n ↦ ?_
    suffices f (n + 1) - f n - 1 = f (-1) by simpa only [Int.sub_eq_iff_eq_add]
    calc f (n + 1) - f n - 1
      _ = f (n - f n) := by rw [h0, hf]
      _ = f (f (n - f n - 1)) := by rw [← h0, Int.sub_add_cancel]
      _ = f (f (n - 1 - f n)) := by rw [Int.sub_sub, Int.sub_sub, Int.add_comm]
      _ = f (-1) := by rw [hf, ← h0, Int.sub_add_cancel, Int.sub_self, Int.zero_sub]
  ---- Split into two cases: `A = 0` and `A ≠ 0`.
  refine (Decidable.em (f (-1) + 1 = 0)).imp
    (λ h1 ↦ funext λ x ↦ ?_) (λ h1 ↦ funext λ x ↦ ?_)
  ---- If `A = 0`, then `f` is constant and `f(-f(f(0))) = -1` means the constant is `-1`.
  · simp only [h1, Int.zero_mul, Int.zero_add] at hf
    rw [hf, ← h, hf (-f _)]
  ---- If `A ≠ 0`, then `f` is injective, so `f(x + 1) = f(f(x))` implies `f(x) = x + 1`.
  · replace h0 : f (x + 1) = f (f x) := h0 x
    rwa [hf, hf (f x), Int.add_left_inj, Int.mul_eq_mul_left_iff h1, eq_comm] at h0
