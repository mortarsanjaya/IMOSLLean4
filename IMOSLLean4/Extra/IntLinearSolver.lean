/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

/-!
# Linear solver for functions $f : ℕ → ℤ$ and $f : ℤ → ℤ$

Let $f : ℕ → ℤ$ be a function and $c ∈ ℤ$.
Suppose that $f(n + 1) = c + f(n)$ for all $n ∈ ℕ$.
Then $f(n) = cn + f(0)$ for all $n ∈ ℕ$.
We prove similar statement for $ℤ → ℤ$ and $ℕ → ℕ$.
-/

namespace IMOSL
namespace Extra
namespace LinearSolver

theorem NatNat {f : Nat → Nat} (h : ∀ n, f (n + 1) = c + f n) : ∀ n, f n = c * n + f 0
  | 0 => by rw [Nat.mul_zero, Nat.zero_add]
  | n + 1 => by rw [h, Nat.mul_succ, NatNat h, Nat.add_left_comm, Nat.add_assoc]

theorem NatInt {f : Nat → Int} (h : ∀ n, f (n + 1) = c + f n) : ∀ n, f n = c * n + f 0
  | 0 => by rw [Int.natCast_zero, c.mul_zero, Int.zero_add]
  | n + 1 => by rw [Int.natCast_add, Int.natCast_one, c.mul_add,
      c.mul_one, h, Int.add_comm _ c, NatInt h, Int.add_assoc]

theorem IntInt {f : Int → Int} (h : ∀ n, f (n + 1) = c + f n) : ∀ n, f n = c * n + f 0
  | Int.ofNat n => by
      revert n; apply NatInt (f := λ n ↦ f n)
      intro n; rw [Int.natCast_add, Int.natCast_one, h]
  | Int.negSucc n => by
      replace h (n) : f (n + -1) = -c + f n := by
        specialize h (n + -1); rw [Int.neg_add_cancel_right] at h
        rw [h, c.neg_add_cancel_left]
      rw [Int.negSucc_eq, Int.neg_add, Int.mul_add, Int.mul_neg_one,
        Int.add_assoc, ← h, Int.mul_neg, ← Int.neg_mul]
      revert n; refine NatInt λ n ↦ ?_
      rw [h, Int.natCast_add, Int.natCast_one, Int.neg_add]
