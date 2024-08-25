/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Tactic.Set

/-!
# IMO 2015 A4 (P5)

Let $R$ be a ring.
Find all functions $f : R → R$ such that for any $x, y ∈ R$,
$$ f(x + f(x + y)) + f(xy) = x + f(x + y) + f(x) y. $$

### Extra notes

In the code comments below, we denote $A = 1 - f(0)$.
This is probably the most central element of $R$ used in the proof.
-/

namespace IMOSL
namespace IMO2015A4

variable [Ring R]

def good (f : R → R) := ∀ x y, f (x + f (x + y)) + f (x * y) = x + f (x + y) + f x * y

theorem answer_set {a : R} (ha : a ^ 2 = 1) : good (λ x ↦ a * (x - 1) + 1) := λ x y ↦ by
  simp only
  rw [add_sub_assoc, add_sub_cancel_right, mul_add, ← mul_assoc, ← sq, ha, one_mul,
    add_assoc (a * x), sub_add_cancel, add_left_comm _ x, add_assoc, add_assoc x,
    add_right_inj, add_right_comm _ 1, ← add_assoc, add_left_inj, add_one_mul _ y,
    ← add_assoc, add_right_comm, add_left_inj, ← mul_add, mul_assoc, ← mul_add]
  apply congrArg _
  rw [sub_one_mul, sub_add_sub_comm, add_right_comm, add_sub_add_right_eq_sub, add_sub_assoc]



namespace good

variable {f : R → R} (hf : good f)

lemma map_add_map_self (t : R) : f (t + f t) + f 0 = t + f t := by
  specialize hf t 0; rwa [add_zero, mul_zero, mul_zero, add_zero] at hf

lemma map_add_map_add_one (t : R) : f (t + f (t + 1)) = t + f (t + 1) := by
  specialize hf t 1; rwa [mul_one, mul_one, add_left_inj] at hf

lemma map_map_eq (t : R) : f (f t) = f t + f 0 * (t - 1) := by
  specialize hf 0 t; rw [zero_add, zero_add, zero_mul] at hf
  rwa [mul_sub_one, ← add_sub_assoc, eq_sub_iff_add_eq]

lemma map_map_zero : f (f 0) = 0 := by
  rw [hf.map_map_eq, zero_sub, mul_neg_one (f 0), add_right_neg]

lemma map_zero_annihilate (t : R) : f 0 * (t + f t - 2) = 0 := by
  have h := hf.map_add_map_add_one (t - 1)
  rw [sub_add_cancel] at h
  have h0 := hf.map_map_eq (t - 1 + f t)
  rwa [h, h, self_eq_add_right, ← add_sub_right_comm, sub_sub, one_add_one_eq_two] at h0

lemma A_sq_eq_one : (1 - f 0) ^ 2 = 1 := by
  have h := hf.map_zero_annihilate 0
  rw [zero_add, mul_sub, sub_eq_zero, mul_two] at h
  rw [sq, one_sub_mul, mul_one_sub, h, sub_add_cancel_right, sub_neg_eq_add, sub_add_cancel]

lemma map_neg_A : f (f 0 - 1) = f 0 - 1 := by
  have h := hf.map_add_map_add_one (-1); rwa [neg_add_self, neg_add_eq_sub] at h

lemma map_one_eq_one : f 1 = 1 := by
  ---- In this proof, let `B = f(1) - 1`. The goal is to prove that `B = 0`.
  apply eq_of_sub_eq_zero; set B := f 1 - 1
  -- First get `f(0) B = 0`
  have h : f 0 * B = 0 := by
    have h := hf.map_zero_annihilate 1
    rwa [← one_add_one_eq_two, add_sub_add_left_eq_sub] at h
  -- Now get `2B^2 = 0` with intermediate step `-BA = B(f(0) - 1) = B`
  have h0 : B * B + B * B = 0 := by
    have h0 := hf 1 (f 0 - 1)
    rw [add_sub_cancel, hf.map_map_zero, add_zero, one_mul, hf.map_neg_A,
      ← eq_sub_iff_add_eq, add_sub_assoc, ← sub_one_mul, ← sub_eq_iff_eq_add'] at h0
    replace h0 : B * B = B * (f 0 - 1) * B := congrArg (· * B) h0
    rwa [mul_assoc, sub_one_mul (f 0), h, zero_sub, mul_neg, eq_neg_iff_add_eq_zero] at h0
  -- Get `f(B + 1) = B + 1`
  have h1 : f (B + 1) = B + 1 := by
    rw [sub_add_cancel, hf.map_map_eq, sub_self, mul_zero, add_zero]
  -- Get `2 f(-B) B = B`
  have h2 : f (-B) * (2 * B) = B := by
    have h2 := hf (-B) (B + (B + 1))
    rwa [neg_add_cancel_left, h1, neg_add_cancel_left, ← add_assoc, mul_add_one (-B),
      neg_mul, mul_add, h0, neg_zero, zero_add, mul_add_one (f (-B)), ← add_assoc,
      add_left_inj, ← sub_eq_iff_eq_add', ← two_mul, eq_comm] at h2
  -- Replace `2B^2 = 0` with `B^2 = 0`
  replace h0 : B * B = 0 := by
    have h3 : _ * B = _ * B := congrArg (· * B) h2
    rwa [mul_assoc, mul_assoc, two_mul, h0, mul_zero, eq_comm] at h3
  save
  -- Get `f(-B) = f(0) - B` with intermediate step `f(2(B + 1)) = 2(B + 1) - f(0)`
  have h3 : f (-B) = f 0 - B := by
    have h3 : f (f 1 + f 1) = f 1 + f 1 - f 0 := by
      have h3 := hf.map_add_map_self (B + 1)
      rwa [h1, sub_add_cancel, ← eq_sub_iff_add_eq] at h3
    have h4 := hf (B + 1) (-B)
    rwa [add_neg_cancel_comm, h1, add_one_mul B, mul_neg, h0,
      neg_zero, zero_add, sub_add_cancel, h3, ← add_sub_right_comm,
      sub_eq_iff_eq_add', add_left_comm, add_right_inj, ← sub_eq_add_neg] at h4
  -- Finishing
  rwa [two_mul, mul_add, h3, sub_mul, h, h0, sub_self, add_zero, eq_comm] at h2

/- ... -/

theorem f_eq_A_mul_sub_one_conj (x : R) : f x = (1 - f 0) * (x - 1) + 1 := by
  have hf := hf
  sorry

theorem exists_A_f_eq : ∃ A, A ^ 2 = 1 ∧ f = λ x ↦ A * (x - 1) + 1 :=
  ⟨1 - f 0, hf.A_sq_eq_one, funext hf.f_eq_A_mul_sub_one_conj⟩

end good




/-- Final solution -/
theorem final_solution {f : R → R} : good f ↔ ∃ a, a ^ 2 = 1 ∧ f = λ x ↦ a * (x - 1) + 1 :=
  ⟨good.exists_A_f_eq, λ ⟨_, ha, hf⟩ ↦ hf ▸ answer_set ha⟩
