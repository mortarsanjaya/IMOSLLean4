/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Int

/-!
# Linear solver for functions $f : ℤ → G$

Let $G$ be an additive group, and fix an element $g \in G$.
We describe all functions $f : ℤ → G$ satisfying
  the functional equation $f(n + 1) = g + f(n)$.
-/

namespace IMOSL
namespace Extra

theorem IntLinearSolver [AddGroup G] {f : ℤ → G}
    (h : ∀ n, f (n + 1) = g + f n) (n : ℤ) : f n = n • g + f 0 :=
  n.inductionOn' 0
    (by rw [zero_zsmul, zero_add])
    (λ k _ h1 ↦ by rw [h, h1, ← add_assoc, add_comm, one_add_zsmul])
    (λ k _ h1 ↦ by rwa [← add_right_inj g, ← h, sub_add_cancel,
                     ← add_assoc, ← one_add_zsmul, add_sub_cancel])

theorem IntIntLinearSolverAlt {f : ℤ → ℤ}
    (h : ∀ n, f (n + 1) = g + f n) (n : ℤ) : f n = g * n + f 0 := by
  rw [IntLinearSolver h, smul_eq_mul, mul_comm]
