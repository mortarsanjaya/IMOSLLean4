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

/-- Linear solver for functions from `Nat` to `Nat`. -/
theorem NatNat {f : Nat → Nat} (hf : ∀ n, f (n + 1) = c + f n) : ∀ n, f n = c * n + f 0 :=
  Nat.rec (by rw [Nat.mul_zero, Nat.zero_add]) λ n hn ↦ by
    rw [hf, Nat.mul_succ, hn, Nat.add_left_comm, Nat.add_assoc]

/-- Linear solver for functions from `Nat` to `Int`. -/
theorem NatInt {f : Nat → Int} (hf : ∀ n, f (n + 1) = c + f n) : ∀ n, f n = c * n + f 0 :=
  Nat.rec (by rw [Int.natCast_zero, Int.mul_zero, Int.zero_add]) λ n hn ↦ by
    rw [Int.natCast_succ, Int.mul_add, Int.mul_one, hf, Int.add_comm _ c, hn, Int.add_assoc]

/-- Linear solver for functions from `Int` to `Int`. -/
theorem IntInt {f : Int → Int} (hf : ∀ n, f (n + 1) = c + f n) : ∀ n, f n = c * n + f 0 := by
  refine Int.rec ?_ ?_
  ---- Solve the case `n ≥ 0`.
  · refine NatInt λ n ↦ ?_
    rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, Int.natCast_succ, hf]
  ---- Solve the case `n < 0`.
  · -- First replace the given condition with a version we can apply `NatInt` on.
    replace hf (n : Nat) : f (-(n + 1 : Nat)) = -c + f (-n) := by
      rw [← Int.sub_eq_iff_eq_add'.mpr (hf _), Int.natCast_succ, Int.neg_add,
        Int.neg_add_cancel_right, Int.sub_eq_add_neg, Int.add_comm]
    -- Now do the calc using `NatInt`.
    intro n; rw [Int.negSucc_eq, ← Int.natCast_add_one, NatInt (f := λ n ↦ f (-n)) hf,
      Int.neg_mul, Int.mul_neg, Int.natCast_zero, Int.neg_zero]
