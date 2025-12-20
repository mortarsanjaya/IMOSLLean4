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

### Answer

$f(n) = 0$ and $f(n) = Nn + c$ for some integer $c$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2019SL.pdf).
After obtaining linearity, we substitute $b = 0$ to the original functional equation.
-/

namespace IMOSL
namespace IMO2019A1

/-- Final solution -/
theorem final_solution (h : N ≠ 0) {f : Int → Int} :
    (∀ a b : Int, f (N * a) + N * f b = f (f (a + b)))
      ↔ (f = λ _ ↦ 0) ∨ ∃ c : Int, f = (N * · + c) := by
  ---- The `←` direction is easy.
  refine Iff.symm ⟨λ h0 a b ↦ ?_, λ h0 ↦ ?_⟩
  · rcases h0 with rfl | ⟨c, rfl⟩
    · exact (N * 0).zero_add.trans N.mul_zero
    · rw [Int.add_right_comm, ← Int.mul_add, ← Int.add_assoc, ← Int.mul_add]
  ---- For the `→` direction, start with `N(f(n + 1) - f(n)) = f(N) - f(0)`.
  have h1 (n) : N * (f (n + 1) - f n) = f N - f 0 := by
    rw [Int.mul_sub, ← Int.add_left_inj (k := N * f n + f 0), ← Int.add_assoc,
      Int.sub_add_cancel, (N * f n).add_comm, ← Int.add_assoc, Int.sub_add_cancel,
      ← N.mul_zero, Int.add_comm, h0, Int.zero_add, n.add_comm, ← h0, N.mul_one]
  ---- This already implies that `f` is linear, say `f(n) = qn + f(0)`.
  replace h1 (n) : f (n + 1) = (f 1 - f 0) + f n := by
    rw [← Int.sub_left_inj (k := f n), Int.add_sub_cancel,
      ← Int.mul_eq_mul_left_iff h, h1, ← Int.zero_add 1, h1]
  generalize f 1 - f 0 = q at h1
  replace h1 : ∀ n, f n = q * n + f 0 := Extra.LinearSolver.IntInt h1
  ---- If `q = N`, then `f(n) = Nn + c`.
  obtain rfl | h2 : q = N ∨ q ≠ N := Decidable.em _
  · right; exact ⟨f 0, funext h1⟩
  ---- If `q ≠ N`, then we prove that `q = 0` and `f(0) = 0`.
  left; funext n
  replace h0 : f (N * 0) + N * f n = f (f (0 + n)) := h0 0 n
  rw [N.mul_zero, n.zero_add, h1 (f n), Int.add_comm, Int.add_left_inj,
    ← Int.sub_eq_zero, ← Int.sub_mul, Int.mul_eq_zero, Int.sub_eq_zero] at h0
  exact h0.resolve_left h2.symm
