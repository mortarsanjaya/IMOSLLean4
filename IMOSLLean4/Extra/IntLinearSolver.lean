import Mathlib.Algebra.GroupPower.Lemmas

/-!
# Linear solver for functions `f : ℤ → G`

We describe the solution to the functional equation `f(n + 1) = g + f(n)`.
-/

namespace IMOSL
namespace Extra

theorem IntLinearSolver [AddGroup G] {f : ℤ → G}
    (h : ∀ n, f (n + 1) = g + f n) (n : ℤ) : f n = n • g + f 0 :=
  n.inductionOn' 0
    (by rw [zero_zsmul, zero_add])
    (λ k _ h1 ↦ by rw [h, h1, ← add_assoc, add_comm, one_add_zsmul])
    (λ k _ h1 ↦ by rwa [← add_right_inj g, ← h, sub_add_cancel,
                     ← add_assoc, ← one_add_zsmul, add_sub_cancel'_right])

theorem IntIntLinearSolverAlt {f : ℤ → ℤ}
    (h : ∀ n, f (n + 1) = g + f n) (n : ℤ) : f n = g * n + f 0 := by
  rw [IntLinearSolver h, smul_eq_mul, mul_comm]
