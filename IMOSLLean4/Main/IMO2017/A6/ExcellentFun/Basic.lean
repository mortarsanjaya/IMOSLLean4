/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2017.A6.ExcellentFun.Defs
import Mathlib.Algebra.Group.Basic

/-! # Additional lemmas about excellent functions -/

namespace IMOSL
namespace IMO2017A6

variable [NonAssocRing R] [AddCancelCommMonoid G]
  [FunLike F R G] [ExcellentFunClass F R G] (f : F)

lemma excellent_alt1 (x y : R) : f (x + y - x * y) + f (x * y) = f (x + y) := by
  rw [← add_left_inj, excellent_map_self_add_map_one_sub, add_right_comm,
    excellent_def, excellent_map_one_sub_add_map_self]

lemma excellent_alt2 (x y : R) : f (x * y + (x + y)) = f (x * y) + f (x + y) := by
  rw [← add_right_inj, excellent_map_neg_add_map_self, neg_add_rev,
    ← sub_eq_add_neg, neg_add, ← neg_mul_neg, ← add_assoc,
    excellent_alt1, ← neg_add, excellent_map_neg_add_map_self]

lemma excellent_map_add_one_mul_add_one (x y : R) :
    f ((x + 1) * (y + 1)) = f (x * y) + f (x + y) + f 1 := by
  rw [← excellent_alt2, ← excellent_map_add_one,
    add_one_mul, mul_add_one, ← add_assoc, ← add_assoc]

/-- TODO: Simplify the proof, if possible -/
lemma excellent_map_add_nat_mul_add_nat (x y : R) (n : ℕ) :
    f ((x + n) * (y + n)) = f (x * y) + n • f (x + y) + (n * n) • f 1 := by
  induction n with
  | zero => simp [zero_nsmul]
  | succ n n_ih => rw [Nat.cast_succ, ← add_assoc, ← add_assoc, Nat.mul_succ,
      excellent_map_add_one_mul_add_one, n_ih, add_add_add_comm, ← Nat.cast_add,
      excellent_map_add_nat, add_add_add_comm, add_assoc (f _), ← succ_nsmul, add_assoc,
      ← add_nsmul, ← Nat.add_assoc, ← Nat.succ_mul, ← succ_nsmul, Nat.add_assoc]

lemma excellent_map_mul_nat (x : R) (n : ℕ) : f (x * n) = n • f x := by
  have h := excellent_map_add_nat_mul_add_nat f (x - n) 0 n
  simp only [sub_add_cancel, zero_add, mul_zero, excellent_map_zero, add_zero] at h
  rwa [mul_nsmul, ← nsmul_add, ← excellent_map_add_nat, sub_add_cancel] at h

lemma excellent_map_nat_mul (n : ℕ) (x : R) : f (n * x) = n • f x := by
  have h := excellent_map_add_nat_mul_add_nat f 0 (x - n) n
  simp only [zero_add, sub_add_cancel, zero_mul, excellent_map_zero] at h
  rwa [mul_nsmul, ← nsmul_add, ← excellent_map_add_nat, sub_add_cancel] at h

/-- TODO: Simplify the proof, if possible -/
lemma excellent_linear_formula (x y : R) : 2 • f (3 * x + y) = 2 • (3 • f x + f y) := by
  have X (x : R) : f (2 * x) = 2 • f x := excellent_map_nat_mul f 2 x
  have h (x y : R) : f ((x + 2) * (y + 2)) = f (x * y) + 2 • f (x + y) + 4 • f 1 :=
    excellent_map_add_nat_mul_add_nat f x y 2
  have h0 (x y : R) : 2 • f ((x + 1) * (y + 2))
      = 2 • f (x * y) + 2 • (f (2 * x + y) + 2 • f 1) := by
    have h0 := h (2 * x) y
    rwa [← mul_add_one, two_mul, add_mul, ← two_mul, X, two_mul, add_mul x x,
      ← two_mul, X, ← two_mul, mul_nsmul _ 2 2, add_assoc, ← nsmul_add] at h0
  replace h (x y) : 2 • f ((x + 2) * (y + 1))
      = 2 • f (x * y) + 2 • (f (x + 2 * y) + 2 • f 1) := by
    have h1 := h x (2 * y)
    rwa [← mul_add_one, two_mul, mul_add, ← two_mul, X, two_mul, mul_add x,
      ← two_mul, X, ← two_mul, mul_nsmul _ 2 2, add_assoc, ← nsmul_add] at h1
  replace h (x y) : 2 • (f (2 * x + y) + f (x + 2 * y)) = 6 • f (x + y) := by
    specialize h (x + 1) (y + 2)
    rw [add_assoc, add_assoc, h0, ← Nat.cast_one, ← Nat.cast_two (R := R), ← Nat.cast_add,
      ← Nat.cast_add, excellent_map_add_nat_mul_add_nat, add_assoc, nsmul_add, nsmul_add,
      ← mul_nsmul, ← mul_nsmul, add_assoc, add_right_inj, ← nsmul_add, add_add_add_comm,
      ← add_nsmul, Nat.cast_two, Nat.cast_one, mul_add 2 y, add_add_add_comm x,
      two_mul 2, ← Nat.cast_two (R := R), ← Nat.cast_add, add_comm 1,
      ← Nat.cast_succ, excellent_map_add_nat, ← add_assoc, add_assoc,
      ← add_nsmul, nsmul_add, ← mul_nsmul, add_left_inj] at h
    exact h.symm
  clear h0; specialize h (x + (x + y)) (-(x + y))
  rw [mul_add, two_mul (x + y), ← add_assoc, add_neg_cancel_right,
    ← add_assoc, ← add_one_mul, two_mul, ← add_assoc,
    add_neg_cancel_right, neg_add, add_neg_cancel_left] at h
  rw [nsmul_add, ← mul_nsmul, ← h, ← nsmul_add, add_assoc,
    excellent_map_neg_add_map_self, add_zero, two_add_one_eq_three]

lemma excellent_linear_formula_weak (x y : R) : 6 • f (x + y) = 6 • (f x + f y) := by
  simpa only [mul_nsmul _ 3 2, ← excellent_map_nat_mul, Nat.cast_ofNat, mul_add, nsmul_add]
    using excellent_linear_formula f x (3 * y)
