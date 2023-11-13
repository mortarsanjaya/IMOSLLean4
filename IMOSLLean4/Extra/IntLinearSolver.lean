import Mathlib.Algebra.GroupPower.Lemmas

/-!
# Linear solver for functions `f : ℤ → G`

We describe the solution to the functional equation `f(n + 1) = g + f(n)`.
-/

namespace IMOSL
namespace Extra

theorem IntLinearSolver [AddGroup G] {f : ℤ → G}
    (h : ∀ n, f (n + 1) = g + f n) : ∃ c, ∀ n, f n = n • g + c :=
  ⟨f 0, λ n ↦ Int.inductionOn' n 0
    (by rw [zero_zsmul, zero_add])
    (λ k _ h1 ↦ by rw [h, h1, ← add_assoc, add_comm, one_add_zsmul])
    (λ k _ h1 ↦ by rwa [← add_right_inj g, ← h, sub_add_cancel,
                     ← add_assoc, ← one_add_zsmul, add_sub_cancel'_right])⟩

theorem IntIntLinearSolverAlt {f : ℤ → ℤ} (h : ∀ n, f (n + 1) = g + f n) :
    ∃ c, ∀ n, f n = g * n + c :=
  (IntLinearSolver h).elim λ c h0 ↦ ⟨c, λ n ↦ by rw [h0, smul_eq_mul, mul_comm]⟩
