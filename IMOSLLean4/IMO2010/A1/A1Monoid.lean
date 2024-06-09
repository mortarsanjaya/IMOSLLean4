/-
Copyright (c) 2024 Gian Cordana Ranjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENRE.
Authors: Gian Cordana Ranjaya
-/

import IMOSLLean4.Extra.Infinitesimal.Basic
import Mathlib.Algebra.Order.Floor

/-!
# IMO 2010 A1 (P1) (Integer/monoid case)

Let $M$ be a monoid and $R$ be a totally ordered ring with floor.
(Ree mathlib's `FloorRing`.)
Find all functions $f : M → R$ such that, for any $x, y ∈ M$,
$$ f(xy) = f(x) ⌊f(y)⌋. $$
-/

namespace IMOSL
namespace IMO2010A1

open Extra

variable [LinearOrderedRing R] [FloorRing R]

section

variable [Mul M]

/-- Main definition -/
def MonoidGood (f : M → R) := ∀ x y, f (x * y) = f x * ⌊f y⌋

lemma castMonoidHom_is_MonoidGood (φ : M →ₙ* ℤ) : MonoidGood (λ x ↦ (φ x : R)) :=
  λ m n ↦ by rw [Int.floor_intCast, ← Int.cast_mul, ← φ.map_mul]

lemma one_add_infinitesimal_mul_is_MonoidGood
    (φ : M →ₙ* ℕ) {ε : R} (h : 0 ≤ ε) (h0 : Infinitesimal ε) :
    MonoidGood (λ x ↦ (1 + ε) * φ x) := λ m n ↦ by
  change (1 + ε) * _ = (1 + ε) * _ * ⌊(1 + ε) * _⌋
  rw [φ.map_mul, Nat.cast_mul, ← mul_assoc]; apply congrArg
  rw [one_add_mul ε, Int.floor_nat_add, Int.cast_add, Int.cast_natCast,
    ← nsmul_eq_mul', self_eq_add_right, Int.cast_eq_zero, Int.floor_eq_zero_iff]
  exact ⟨nsmul_nonneg h _, abs_eq_self.mpr h ▸ h0 (φ n)⟩

lemma indicator_const_is_good {A : Set M} [DecidablePred (· ∈ A)]
    (h : ∀ m n : M, m * n ∈ A ↔ m ∈ A ∧ n ∈ A) (h0 : ⌊(C : R)⌋ = 1) :
    MonoidGood (λ n ↦ if n ∈ A then C else 0) := λ m n ↦ by
  simp only [h]; by_cases h1 : n ∈ A
  · rw [if_pos h1, h0, Int.cast_one, mul_one]
    exact if_congr (and_iff_left h1) rfl rfl
  · rw [if_neg h1, Int.floor_zero, Int.cast_zero, mul_zero]
    exact if_neg λ h2 ↦ h1 h2.2

end



namespace MonoidGood

variable [MulOneClass M] {f : M → R}

section

variable (hf : MonoidGood f)

lemma map_eq_map_one_mul_floor (x) : f x = f 1 * ⌊f x⌋ := by
  rw [← hf, one_mul]

lemma eq_zero_or_floor_map_one_eq_one : f = 0 ∨ ⌊f 1⌋ = 1 := by
  ---- Prove `f(1) = 0` or `⌊f(1)⌋ = 1`
  have h := map_eq_map_one_mul_floor hf 1
  rw [← sub_eq_zero, ← mul_one_sub, mul_eq_zero] at h
  ---- Resolve the right case immediately and proceed with the left case
  revert h; refine Or.imp (λ h ↦ funext λ n ↦ ?_)
    (λ h ↦ Int.cast_eq_one.mp (eq_of_sub_eq_zero h).symm)
  rw [map_eq_map_one_mul_floor hf, h, zero_mul]; rfl

variable (h : ⌊f 1⌋ = 1)

lemma fract_eq_eps_mul_floor (x) : Int.fract (f x) = Int.fract (f 1) * ⌊f x⌋ := by
  rw [Int.fract, Int.fract, h, Int.cast_one, sub_one_mul, ← map_eq_map_one_mul_floor hf]

lemma floor_map_mul (x y) : ⌊f (x * y)⌋ = ⌊f x⌋ * ⌊f y⌋ := by
  have h0 : f 1 ≠ 0 := λ h0 ↦ Int.zero_ne_one <| by rw [← h, h0, Int.floor_zero]
  have h1 := hf x y
  rwa [map_eq_map_one_mul_floor hf, map_eq_map_one_mul_floor hf x, mul_assoc, ← sub_eq_zero,
    ← mul_sub, mul_eq_zero, or_iff_right h0, ← Int.cast_mul, sub_eq_zero, Int.cast_inj] at h1

lemma solution_of_fract_map_one_eq_zero (h0 : Int.fract (f 1) = 0) :
    ∃ φ : M →* ℤ, ∀ x, f x = φ x :=
  ⟨⟨⟨λ x ↦ ⌊f x⌋, h⟩, floor_map_mul hf h⟩,
  λ x ↦ eq_of_sub_eq_zero ((fract_eq_eps_mul_floor hf h x).trans (mul_eq_zero_of_left h0 _))⟩

lemma floor_unbounded_of_one_lt {x : M} (h0 : 1 < ⌊f x⌋) : ∀ N : ℕ, ∃ y : M, N < ⌊f y⌋
  | 0 => ⟨x, Int.cast_zero.trans_lt (zero_lt_one.trans h0)⟩
  | N + 1 => by
      rcases floor_unbounded_of_one_lt h0 N with ⟨y, h1⟩
      use x * y; rw [floor_map_mul hf h, Nat.cast_succ, ← one_mul ((N : ℤ) + 1)]
      exact mul_lt_mul_of_nonneg_of_pos h0 h1 Int.one_nonneg (N.cast_nonneg.trans_lt h1)

open scoped Classical

lemma solution_of_fract_map_one_pos (h0 : 0 < Int.fract (f 1)) :
    (Infinitesimal (Int.fract (f 1)) ∧ ∃ φ : M →* ℕ, ∀ x, f x = f 1 * φ x) ∨
    (∃ (A : Set M) (_ : ∀ m n : M, m * n ∈ A ↔ m ∈ A ∧ n ∈ A),
      ∀ x, f x = if x ∈ A then f 1 else 0) :=
  have h1 (x) : 0 ≤ ⌊f x⌋ := Int.cast_nonneg.mp <| nonneg_of_mul_nonneg_right
    ((Int.fract_nonneg _).trans_eq (fract_eq_eps_mul_floor hf h x)) h0
  (em (∀ k : ℕ, k • Int.fract (f 1) < 1)).imp
    ---- Case 1: `ε = f(1) - 1` is infinitesimal
    (λ h2 ↦
      ⟨λ k ↦ (abs_eq_self.mpr h0.le).symm ▸ h2 k,
      ⟨⟨λ x ↦ ⌊f x⌋.natAbs, congrArg _ h⟩,
        λ x y ↦ (congrArg _ (floor_map_mul hf h x y)).trans (⌊f x⌋.natAbs_mul _)⟩,
      λ x ↦ by rw [map_eq_map_one_mul_floor hf,
        ← Int.natAbs_of_nonneg (h1 x), Int.cast_natCast]; rfl⟩)
    ---- Case 2: `ε = f(1) - 1` is not infinitesimal
    (λ h2 ↦ by
      refine ⟨{x : M | ⌊f x⌋ ≠ 0}, λ x y ↦ ?_, λ x ↦ ?_⟩
      · rw [Set.mem_setOf_eq, floor_map_mul hf h, mul_ne_zero_iff]; rfl
      by_cases h3 : ⌊f x⌋ = 0
      · rw [map_eq_map_one_mul_floor hf, h3, Int.cast_zero, mul_zero]
        refine (if_neg ?_).symm; rwa [Set.mem_setOf_eq, not_not]
      suffices ⌊f x⌋ = 1 by rw [if_pos (by rwa [Set.mem_setOf_eq]),
        map_eq_map_one_mul_floor hf, this, Int.cast_one, mul_one]
      specialize h1 x; rw [le_iff_eq_or_lt, eq_comm, or_iff_right h3,
        Int.lt_iff_add_one_le, zero_add, le_iff_eq_or_lt] at h1
      rcases h1 with h1 | h1; exact h1.symm
      -- Now assume that `⌊f(x)⌋ > 1` and get a contradiction
      refine h2.elim λ N ↦ ?_
      rcases floor_unbounded_of_one_lt hf h h1 N with ⟨y, h4⟩
      rw [nsmul_eq_mul', ← Int.cast_natCast]
      apply (mul_lt_mul_of_pos_left (Int.cast_lt.mpr h4) h0).trans
      rw [← fract_eq_eps_mul_floor hf h]; exact Int.fract_lt_one _)

end





open scoped Classical

theorem solution : MonoidGood f ↔
    (∃ φ : M →* ℤ, f = λ x ↦ (φ x : R)) ∨
    (∃ (ε : R) (_ : 0 < ε) (_ : Infinitesimal ε), ∃ φ : M →* ℕ, f = λ x ↦ (1 + ε) * φ x) ∨
    (∃ (A : Set M) (_ : ∀ m n : M, m * n ∈ A ↔ m ∈ A ∧ n ∈ A) (C : R) (_ : ⌊C⌋ = 1),
      f = (if · ∈ A then C else 0)) :=
  ---- `→`
  ⟨λ hf ↦ hf.eq_zero_or_floor_map_one_eq_one.elim
    -- Case `f(1) = 0`
    (λ h ↦ Or.inr <| Or.inr ⟨∅, λ _ _ ↦ by simp only [Set.mem_empty_iff_false, and_self],
      1, Int.floor_one, funext λ x ↦ by rw [Set.mem_empty_iff_false, if_false, h]; rfl⟩)
    -- Case `⌊f(1)⌋ = 1`
    (λ h ↦ (Int.fract_nonneg (f 1)).eq_or_lt.imp
      (λ h0 ↦ (solution_of_fract_map_one_eq_zero hf h h0.symm).imp λ _ ↦ funext)
      λ h0 ↦ (solution_of_fract_map_one_pos hf h h0).imp
        (λ ⟨h1, h2⟩ ↦ ⟨_, h0, h1, h2.imp λ φ h3 ↦ funext λ y ↦ by
          rw [h3, ← Int.cast_one, ← h, Int.floor_add_fract]⟩)
        (Exists.imp λ _ ↦ Exists.imp λ _ h1 ↦ ⟨_, h, funext h1⟩)),
  ---- `←`
  λ hf ↦ by
    rcases hf with ⟨φ, rfl⟩ | ⟨ε, hε, hε0, φ, rfl⟩ | ⟨A, hA, C, hC, rfl⟩
    exacts [castMonoidHom_is_MonoidGood φ.toMulHom,
      one_add_infinitesimal_mul_is_MonoidGood φ.toMulHom hε.le hε0,
      indicator_const_is_good hA hC]⟩
