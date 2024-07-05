/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.IntLinearSolver
import Mathlib.Algebra.Group.Int

/-!
# IMO 2019 A1 (P1)

Fix an integer $N ≠ 0$.
Find all functions $f : ℤ → ℤ$ such that, for any $a, b ∈ ℤ$,
$$ f(Na) + N f(b) = f(f(a + b)). $$
-/

namespace IMOSL
namespace IMO2019A1

/-- Final solution -/
theorem final_solution (h : N ≠ 0) {f : Int → Int} :
    (∀ a b : Int, f (N * a) + N * f b = f (f (a + b)))
      ↔ (f = λ _ ↦ 0) ∨ ∃ c : Int, f = (N * · + c) :=
  ---- `→` direction
  ⟨λ h0 ↦ by
    -- Prove that solutions are linear
    have h1 n : N * (f (n + 1) - f n) = f N - f 0 := by
      rw [Int.mul_sub, sub_eq_iff_eq_add, ← add_sub_right_comm, eq_sub_iff_add_eq',
        ← N.mul_zero, h0, zero_add, n.add_comm, ← h0, mul_one]
    replace h1 n : f (n + 1) = (f 1 - f 0) + f n := by
      rw [← sub_eq_iff_eq_add, ← Int.mul_eq_mul_left_iff h, h1, ← Int.zero_add 1, h1]
    generalize f 1 - f 0 = q at h1
    replace h1 := Extra.LinearSolver.IntInt h1
    refine (eq_or_ne N q).symm.imp (λ h2 ↦ ?_) (λ h2 ↦ ⟨f 0, funext (by rwa [h2])⟩)
    have h3 := h0 0 0
    rw [add_zero, N.mul_zero, h1 (f 0), add_comm, add_left_inj, ← sub_eq_zero,
      ← Int.sub_mul, Int.mul_eq_zero, or_iff_right (sub_ne_zero_of_ne h2)] at h3
    specialize h0 0 1
    rw [N.mul_zero, zero_add, h1 (f 1), add_comm, add_left_inj, ← sub_eq_zero, ← Int.sub_mul,
      Int.mul_eq_zero, or_iff_right (sub_ne_zero_of_ne h2), h1, mul_one, h3, add_zero] at h0
    funext n; rw [h1, h0, h3, n.zero_mul, Int.add_zero],
  ---- `←` direction
  λ h0 a b ↦ by
    rcases h0 with rfl | ⟨c, rfl⟩
    · exact (N * 0).zero_add.trans N.mul_zero
    · rw [Int.add_right_comm, ← Int.mul_add, ← Int.add_assoc, ← Int.mul_add]⟩
