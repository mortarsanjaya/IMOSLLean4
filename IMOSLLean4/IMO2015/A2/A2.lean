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
theorem final_solution {f : Int → Int} :
    (∀ x y, f (x - f y) = f (f x) - f y - 1) ↔ (f = λ _ ↦ -1) ∨ f = (· + 1) :=
  ---- `→`
  ⟨λ h ↦ by
    have h0 := h 0 (f 0)
    rw [Int.sub_self, Int.zero_sub 1] at h0
    replace h0 x : f (x + 1) = f (f x) := by
      have h1 := h x (0 - f (f 0))
      rwa [h0, Int.sub_neg, Int.sub_neg, Int.add_sub_cancel] at h1
    -- Now prove that `f` is linear (with linear coefficient `f(-1) + 1`)
    have h1 : ∀ n, f n = (f (-1) + 1) * n + f 0 := by
      refine Extra.LinearSolver.IntInt λ n ↦ ?_
      have h1 : f (n - f n - 1) = -1 := by
        rw [Int.sub_sub, Int.add_comm, ← Int.sub_sub, h,
          ← h0, Int.sub_add_cancel, Int.sub_self, Int.zero_sub]
      have h2 := h0 (n - f n - 1)
      rw [h1, Int.sub_add_cancel, h, ← h0, Int.sub_sub, (f n).add_comm] at h2
      rw [← h2, Int.add_assoc, Int.sub_add_cancel]
    -- Finishing in two cases
    apply (Decidable.em (f (-1) + 1 = 0)).imp <;> refine λ h2 ↦ funext λ x ↦ ?_
    · simp only [h2, Int.zero_mul, Int.zero_add] at h1
      rw [h1, ← h1 (-1)]; exact Int.eq_of_sub_eq_zero h2
    · specialize h0 x
      rwa [h1, h1 (f x), Int.add_right_inj, Int.mul_eq_mul_left_iff h2, eq_comm] at h0,
  ---- `←`
  λ h x y ↦ by
    rcases h with rfl | rfl
    · rfl
    · simp only; rw [Int.sub_sub, Int.add_assoc, Int.add_assoc, y.add_comm (1 + 1),
        ← Int.sub_sub, Int.sub_add_cancel, ← Int.sub_sub, Int.add_sub_cancel]⟩
