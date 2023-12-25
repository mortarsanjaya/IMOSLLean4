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
-/

namespace IMOSL
namespace IMO2015A2

/-- Final solution -/
theorem final_solution {f : ℤ → ℤ} :
    (∀ x y : ℤ, f (x - f y) = f (f x) - f y - 1)
      ↔ (f = λ _ ↦ (-1 : ℤ)) ∨ f = (· + 1) := by
  refine Iff.symm ⟨λ h x y ↦ ?_, λ h ↦ ?_⟩
  ---- `←` direction
  · rcases h with rfl | rfl
    · rw [sub_sub, neg_add_self, sub_zero]
    · rw [sub_sub, add_sub_add_right_eq_sub, add_sub_right_comm]
  ---- `→` direction
  · -- First obtain `f(x + 1) = f(f(x))`
    have h0 := h 0 (f 0)
    rw [sub_self, zero_sub 1] at h0
    replace h0 x : f (x + 1) = f (f x) := by
      have h1 := h x (0 - f (f 0))
      rwa [h0, sub_neg_eq_add (f (f x)), add_sub_cancel] at h1
    -- Now prove that `f` is linear (with linear coefficient `f(-1) + 1`)
    have h1 : ∀ n, f n = (f (-1) + 1) * n + f 0 := by
      refine Extra.IntIntLinearSolverAlt λ n ↦ ?_
      have h1 := h0 (n - f n - 1)
      rw [sub_add_cancel, sub_right_comm, h, ← h0, h (n - 1), ← h0,
        sub_add_cancel, sub_self, zero_sub, sub_eq_iff_eq_add] at h1
      exact eq_add_of_sub_eq h1
    -- Finishing in two cases
    refine (eq_or_ne (f (-1) + 1) 0).imp
      (λ h2 ↦ funext λ x ↦ ?_) (λ h2 ↦ funext λ x ↦ ?_)
    · rw [h1, h2, zero_mul, zero_add, ← eq_neg_of_add_eq_zero_left h2]
      specialize h1 (-1)
      rw [h2, zero_mul, zero_add] at h1
      exact h1.symm
    · specialize h0 x
      rw [h1, h1 (f x), add_left_inj, Int.mul_eq_mul_left_iff h2] at h0
      exact h0.symm
