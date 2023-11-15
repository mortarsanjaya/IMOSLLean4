/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.IntLinearSolver
import Mathlib.Algebra.Ring.Regular

/-! # IMO 2019 A1 (P1) -/

namespace IMOSL
namespace IMO2019A1

/-- Final solution -/
theorem final_solution (h : N ≠ 0) (f : ℤ → ℤ) :
    (∀ a b : ℤ, f (N * a) + N * f b = f (f (a + b))) ↔
      (f = 0) ∨ ∃ c : ℤ, f = (N * · + c) := by
  symm; refine ⟨λ h0 a b ↦ ?_, λ h0 ↦ ?_⟩
  ---- `←` direction
  · rcases h0 with rfl | ⟨c, rfl⟩
    · exact (N * 0).zero_add.trans N.mul_zero
    · rw [add_right_comm, ← mul_add, ← add_assoc, ← mul_add]
  ---- `→` direction
  · -- Prove that solutions are linear
    have h1 n : N * (f (n + 1) - f n) = f N - f 0 := by
      rw [mul_sub, sub_eq_iff_eq_add, ← add_sub_right_comm, eq_sub_iff_add_eq',
        ← N.mul_zero, h0, zero_add, n.add_comm, ← h0, mul_one]
    replace h1 n : f (n + 1) = (f 1 - f 0) + f n :=
      eq_add_of_sub_eq <| mul_left_cancel₀ h <| by rw [h1, ← h1 0, zero_add]
    -- Classify all linear functions satifying the FE
    generalize f 1 - f 0 = q at h1
    replace h1 := Extra.IntIntLinearSolverAlt h1
    refine (em' <| N = q).imp (λ h2 ↦ ?_) (λ h2 ↦ ⟨f 0, funext <| by rwa [h2]⟩)
    have h3 := h0 0 0
    rw [add_zero, N.mul_zero, h1 (f 0), add_comm, add_left_inj,
      mul_eq_mul_right_iff, or_iff_right h2] at h3
    specialize h0 0 1
    rw [N.mul_zero, zero_add, h1 (f 1), add_comm, add_left_inj,
      mul_eq_mul_right_iff, or_iff_right h2, h1, mul_one, h3, add_zero] at h0
    funext n
    rw [h1, h0, h3, n.zero_mul, add_zero, Pi.zero_apply]
