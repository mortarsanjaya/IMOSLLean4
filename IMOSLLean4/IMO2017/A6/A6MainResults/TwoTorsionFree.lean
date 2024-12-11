/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Basic
import Mathlib.Data.Nat.Cast.Basic

/-!
# IMO 2017 A6 (P2, Solution to reduced version with `2 ∈ R⁰`)

We find all reduced good functions `f : R → R` when `2 ∈ R⁰`.
Here, `R⁰` is the set of non-zero-divisors of `R`.
-/

namespace IMOSL
namespace IMO2017A6

variable [Ring R] [AddCommGroup S] (hS2 : ∀ x y : S, 2 • x = 2 • y → x = y)
include hS2


section

variable (ι : S →+ R) [FunLike F R S] [NonperiodicGoodFunClass F ι] (f : F)
include ι

theorem TwoTorsionFree_eq_zero_of_map_neg_eq_of_map_eq
    {f : F} (h : f (-x) = f x) : x = 0 := by
  rw [map_neg_eq ι, sub_eq_iff_eq_add, ← two_nsmul] at h
  replace h := hS2 _ _ h
  rwa [eq_comm, ← sub_eq_zero, ← map_add_one ι, map_eq_zero_iff ι, add_left_eq_self] at h

theorem TwoTorsionFree_injective : (f : R → S).Injective := λ c d h ↦ by
  rw [← add_right_cancel_iff (a := -d), add_neg_cancel]
  apply TwoTorsionFree_eq_zero_of_map_neg_eq_of_map_eq hS2 ι (f := f)
  ---- Now focus on proving that `f(c - d) = f(d - c)`
  have h0 : f (-c) = f (-d) := map_neg_eq_of_map_eq ι h
  have h1 : f (c * d) = f (d * c) := by rw [← good_def ι, ← good_def ι f d, h, add_comm c]
  replace h1 : f (-(c * d)) = f (-(d * c)) := map_neg_eq_of_map_eq ι h1
  have h2 := good_def ι f c (-d)
  rw [mul_neg, h1, h, ← h0, ← mul_neg, ← good_def ι f d, add_right_inj] at h2
  rw [h2, neg_add_rev, neg_neg]

theorem TwoTorsionFree_solution :
    ∃ a : {a : R // a * a = 1 ∧ ∀ x, a * x = x * a}, ∀ x, ι (f x) = a * (1 - x) :=
  solution_of_injective ι (TwoTorsionFree_injective hS2 ι f)

theorem TwoTorsionFree_altFE (x y : R) : f ((1 - x) * (1 - y)) + f (x + y) = f (x * y) := by
  obtain ⟨⟨a, ha, ha0⟩, h⟩ := TwoTorsionFree_solution hS2 ι f
  have h0 : ι (f x) * ι (f y) = (1 - x) * (1 - y) := by
    rw [h, h, ha0, mul_assoc, ← mul_assoc a, ha, one_mul]
  rw [← h0, good_def]

end





/-! ### Solution to the alternative functional equation -/

variable (hS3 : ∀ x y : S, 3 • x = 3 • y → x = y)
include hS3

theorem altFE_solution
    {f : R → S} (h : ∀ x y, f ((1 - x) * (1 - y)) + f (x + y) = f (x * y)) :
    ∃ φ : R →+ S, φ = λ x ↦ f (1 - x) := by
  ---- First change the FE to an FE for `g(x) = f(1 - x)`
  set g : R → S := λ x ↦ f (1 - x)
  refine ⟨AddMonoidHom.mk' g ?_, rfl⟩
  replace h (x y) : g (x + y - x * y) + g (1 - (x + y)) = g (1 - x * y) := by
    dsimp only [g]; rw [sub_sub_cancel, sub_sub_cancel, ← h,
      add_sub_assoc, ← one_sub_mul, ← sub_sub, ← mul_one_sub]
  clear_value g; clear f
  ---- Now just prove more and more properties
  have h0' (x) : g (x + 1) = g x + g 1 := by
    specialize h (-x) 1; rwa [mul_one, sub_neg_eq_add, neg_add_cancel_comm,
      sub_add_cancel_right, neg_neg, sub_neg_eq_add, add_comm, add_comm 1, eq_comm] at h
  have h0 (x : R) : ∀ n : ℕ, g (x + n) = g x + n • g 1 :=
    Nat.rec (by rw [Nat.cast_zero, add_zero, zero_nsmul, add_zero])
      λ n hn ↦ by rw [Nat.cast_succ, ← add_assoc, h0', hn, add_assoc, succ_nsmul]
  have h1 (x) : g (-x) = -g x := by
    specialize h 0 x; rwa [zero_add, zero_mul, sub_zero, sub_zero, sub_eq_add_neg,
      ← eq_neg_add_iff_add_eq, add_comm 1, h0', add_left_inj] at h
  replace h (x y) : g (x * y + (x + y)) = g (x * y) + g (x + y) := by
    specialize h (-x) (-y)
    rwa [neg_mul_neg, ← neg_add, ← neg_add', h1, sub_neg_eq_add, add_comm 1,
      h0', sub_eq_add_neg, add_comm 1, h0', ← add_assoc, add_left_inj,
      h1, ← eq_sub_iff_add_eq, ← neg_add', neg_inj, add_comm] at h
  have h₁ (x y) : g ((x + 1) * (y + 1)) = g (x * y) + g (x + y) + g 1 := by
    rw [add_one_mul x, mul_add_one x, ← add_assoc, h0', add_assoc, h]
  replace h : ∀ (n : ℕ) (x y : R),
      g ((x + n) * (y + n)) = g (x * y) + n • g (x + y) + n ^ 2 • g 1 := by
    refine Nat.rec (λ x y ↦ ?_) (λ n hn x y ↦ ?_)
    · rw [Nat.cast_zero, add_zero, add_zero, zero_nsmul,
        Nat.zero_pow Nat.two_pos, add_zero, zero_nsmul, add_zero]
    · rw [Nat.cast_succ, ← add_assoc, ← add_assoc, h₁, add_add_add_comm, ← Nat.cast_add,
        h0, ← add_assoc, add_assoc, ← succ_nsmul, hn, add_right_comm _ _ (g _),
        add_assoc _ (_ • g 1), ← add_nsmul, add_assoc (g _), ← succ_nsmul, Nat.pow_two,
        n.add_assoc, ← (n * n).add_assoc, Nat.pow_two, ← n.succ_mul, ← n.succ.mul_succ]
  replace h1 (n : ℕ) (x : R) : g (n * x) = n • g x := by
    have h2 : g 0 = 0 := by rw [← add_left_inj, ← h0', zero_add, zero_add]
    specialize h n 0 x; rwa [zero_add, mul_add, ← Nat.cast_mul,
      h0, zero_mul, h2, zero_add, zero_add, sq, add_left_inj] at h
  replace h₁ : ∀ x y, g ((x + 2) * (y + 2)) = g (x * y) + 2 • g (x + y) + 4 • g 1 := h 2
  replace h0' (x y) : g ((x + 1) * (y + 2)) = g (x * y) + g (2 * x + y) + 2 • g 1 := by
    specialize h₁ (2 * x) y
    rw [← mul_add_one (2 : R), mul_assoc, mul_assoc, ← Nat.cast_two,
      h1, h1, mul_nsmul _ 2 2, ← nsmul_add, ← nsmul_add] at h₁
    exact hS2 _ _ h₁
  replace h₁ (x y) : g ((x + 2) * (y + 1)) = g (x * y) + g (x + y * 2) + 2 • g 1 := by
    have X (x : R) : 2 * x = x * 2 := by rw [two_mul, mul_two]
    specialize h₁ x (y * 2)
    rw [← add_one_mul y, ← mul_assoc, ← X, ← mul_assoc x, ← X, ← Nat.cast_two,
      h1, h1, mul_nsmul _ 2 2, ← nsmul_add, ← nsmul_add] at h₁
    exact hS2 _ _ h₁
  replace h (x y) : g (2 * x + y) + g (x + y * 2) = 3 • g (x + y) := by
    specialize h0' (x + 2) (y + 1)
    rw [add_assoc, add_assoc, add_comm 1, two_add_one_eq_three] at h0'
    have X : ((3 : ℕ) : R) = 3 := rfl
    rw [← X, h, h₁, add_assoc, add_assoc, add_add_add_comm, add_assoc (g _),
      add_assoc, add_right_inj, mul_add, ← add_nsmul, add_add_add_comm] at h0'
    replace X : 2 * 2 + 1 = ((5 : ℕ) : R) := by
      rw [Nat.cast_succ, Nat.cast_mul 2 2, Nat.cast_two]
    rw [X, h0, add_assoc, add_assoc, ← add_nsmul, add_left_comm, ← add_assoc] at h0'
    exact (add_left_injective _ h0').symm
  clear h0' h0 h₁
  ---- Now the finishing argument
  intro a b
  specialize h (a + (a - b)) (b - (a - b))
  have X (x : R) : (3 : ℕ) * x = x + (x + x) := by
    rw [Nat.cast_succ, Nat.cast_two, add_one_mul 2 x, two_mul, add_comm]
  rw [two_mul, mul_two, add_left_comm (a + (a - b)) (b - _), add_assoc,
    add_add_sub_cancel, add_assoc, sub_add_add_cancel, ← X, h1, sub_add, sub_sub,
    add_left_comm b a, sub_add_cancel_left, sub_neg_eq_add, ← X, h1, ← nsmul_add] at h
  exact (hS3 _ _ h).symm
