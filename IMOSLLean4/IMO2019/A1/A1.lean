/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.IntLinearSolver

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
      ↔ (f = λ _ ↦ 0) ∨ ∃ c : Int, f = (N * · + c) := by
  refine ⟨λ h0 ↦ ?_, λ h0 ↦ ?_⟩
  ---- `→` direction
  · have h1 n : N * (f (n + 1) - f n) = f N - f 0 := by
      rw [Int.mul_sub, ← Int.add_left_inj (k := N * f n + f 0), ← Int.add_assoc,
        Int.sub_add_cancel, (N * f n).add_comm, ← Int.add_assoc, Int.sub_add_cancel,
        ← N.mul_zero, Int.add_comm, h0, Int.zero_add, n.add_comm, ← h0, N.mul_one]
    replace h1 n : f (n + 1) = (f 1 - f 0) + f n := by
      rw [← Int.sub_left_inj (k := f n), Int.add_sub_cancel,
        ← Int.mul_eq_mul_left_iff h, h1, ← Int.zero_add 1, h1]
    generalize f 1 - f 0 = q at h1
    replace h1 := Extra.LinearSolver.IntInt h1
    obtain rfl | h2 : N = q ∨ N ≠ q := Decidable.em (N = q)
    · right; exact ⟨f 0, funext h1⟩
    · left; funext n; specialize h0 0 n
      rw [N.mul_zero, n.zero_add, h1 (f n), Int.add_comm, Int.add_left_inj,
        ← Int.sub_eq_zero, ← Int.sub_mul, Int.mul_eq_zero, Int.sub_eq_zero] at h0
      exact h0.resolve_left h2
  ---- `←` direction
  · rcases h0 with rfl | ⟨c, rfl⟩
    · intro _ _; exact (N * 0).zero_add.trans N.mul_zero
    · intro a b; rw [Int.add_right_comm, ← Int.mul_add, ← Int.add_assoc, ← Int.mul_add]
