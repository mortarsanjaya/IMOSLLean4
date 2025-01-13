/-
Copyright (c) 2024 Gian Cordana Ranjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENRE.
Authors: Gian Cordana Ranjaya
-/

import IMOSLLean4.Extra.Infinitesimal.Basic
import Mathlib.Algebra.Order.Floor

/-!
# IMO 2010 A1 (P1) (Integer/monoid case)

Let $M$ be a monoid and $R$ be a totally ordered ring with floor. (See `FloorRing`.)
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
    MonoidGood (λ x ↦ φ x • (1 + ε)) := λ m n ↦ by
  change _ • (1 + ε) = _ • (1 + ε) * ⌊_ • (1 + ε)⌋
  rw [φ.map_mul, nsmul_eq_mul', Nat.cast_mul, ← mul_assoc, nsmul_eq_mul']; apply congrArg
  rw [nsmul_add, nsmul_one, Int.floor_nat_add, Int.cast_add, Int.cast_natCast,
    self_eq_add_right, Int.cast_eq_zero, Int.floor_eq_zero_iff]
  exact ⟨nsmul_nonneg h _, abs_of_nonneg h ▸ h0 (φ n)⟩

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

/-! ### Transfer via homomorphisms -/

theorem ofMulHom [Mul M] [Mul N] (φ : N →ₙ* M) {f : M → R} (hf : MonoidGood f) :
    MonoidGood (f ∘ φ) :=
  λ x y ↦ (congrArg f (φ.map_mul x y)).trans (hf (φ x) (φ y))

theorem ofMonoidEquiv [MulOneClass M] [MulOneClass N] (φ : N ≃* M) {f : M → R} :
    MonoidGood f ↔ MonoidGood (f ∘ φ) :=
  ⟨ofMulHom φ.toMulHom, λ hf ↦ by
    replace hf : MonoidGood (f ∘ φ ∘ φ.symm) := ofMulHom φ.symm.toMulHom hf
    rwa [MulEquiv.self_comp_symm, Function.comp_id] at hf⟩


section

/-! ### Solution -/

variable [MulOneClass M] {f : M → R} (hf : MonoidGood f)
  (h : ⌊f 1⌋ = 1) (h0 : 0 < Int.fract (f 1))
include hf

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

include h

lemma fract_eq_eps_mul_floor (x) : Int.fract (f x) = Int.fract (f 1) * ⌊f x⌋ := by
  rw [Int.fract, Int.fract, h, Int.cast_one, sub_one_mul, ← map_eq_map_one_mul_floor hf]

lemma floor_map_mul (x y) : ⌊f (x * y)⌋ = ⌊f x⌋ * ⌊f y⌋ := by
  have h0 : f 1 ≠ 0 := λ h0 ↦ Int.zero_ne_one (by rw [← h, h0, Int.floor_zero])
  have h1 := hf x y
  rwa [map_eq_map_one_mul_floor hf, map_eq_map_one_mul_floor hf x, mul_assoc, ← sub_eq_zero,
    ← mul_sub, mul_eq_zero, or_iff_right h0, ← Int.cast_mul, sub_eq_zero, Int.cast_inj] at h1

lemma case_fract_map_one_eq_zero (h0 : Int.fract (f 1) = 0) :
    ∃ φ : M →* ℤ, f = λ x ↦ (φ x : R) :=
  ⟨⟨⟨λ x ↦ ⌊f x⌋, h⟩, floor_map_mul hf h⟩,
  funext λ x ↦ by rw [MonoidHom.coe_mk, OneHom.coe_mk, ← sub_eq_zero,
    ← Int.fract, fract_eq_eps_mul_floor hf h, h0, zero_mul]⟩

lemma floor_unbounded_of_one_lt {x : M} (h0 : 1 < ⌊f x⌋) : ∀ N : ℕ, ∃ y : M, N < ⌊f y⌋
  | 0 => ⟨x, Int.cast_zero.trans_lt (zero_lt_one.trans h0)⟩
  | N + 1 => by
      rcases floor_unbounded_of_one_lt h0 N with ⟨y, h1⟩
      use x * y; rw [floor_map_mul hf h, Nat.cast_succ, ← one_mul ((N : ℤ) + 1)]
      exact mul_lt_mul_of_nonneg_of_pos h0 h1 Int.one_nonneg (N.cast_nonneg.trans_lt h1)

include h0

lemma case_fract_map_one_pos : ∃ φ : M →* ℕ, ∀ x, f x = φ x • f 1 := by
  refine ⟨⟨⟨λ x ↦ ⌊f x⌋.natAbs, congrArg _ h⟩, λ x y ↦ ?_⟩, λ x ↦ ?_⟩
  · rw [← Int.natAbs_mul, ← floor_map_mul hf h]
  · have h1 : 0 ≤ ⌊f x⌋ := by
      have h1 := (Int.fract_nonneg _).trans_eq (fract_eq_eps_mul_floor hf h x)
      rwa [mul_nonneg_iff_of_pos_left h0, Int.cast_nonneg] at h1
    change f x = ↑⌊f x⌋.natAbs • f 1
    rw [nsmul_eq_mul', ← Int.cast_natCast,
      Int.natAbs_of_nonneg h1, ← map_eq_map_one_mul_floor hf]

open scoped Classical

lemma case_fract_map_one_big (h1 : ¬Infinitesimal (Int.fract (f 1))) :
    ∃ (A : Set M) (_ : ∀ m n : M, m * n ∈ A ↔ m ∈ A ∧ n ∈ A),
      f = (if · ∈ A then f 1 else 0) := by
  rcases case_fract_map_one_pos hf h h0 with ⟨φ, h2⟩
  refine ⟨{x | φ x ≠ 0}, λ x y ↦ by simp, ?_⟩
  ---- Reduce to showing that `φ` only takes value in `{0, 1}`
  suffices ∀ x, φ x = 0 ∨ φ x = 1 from funext λ x ↦ by
    rw [h2, Set.mem_setOf_eq]; rcases this x with h3 | h3
    · rw [h3, zero_nsmul, if_neg (· rfl)]
    · rw [h3, one_nsmul, if_pos Nat.one_ne_zero]
  ---- Next, change the hypothesis `h2`
  rw [Infinitesimal, abs_of_nonneg (Int.fract_nonneg _)] at h1
  replace h2 (x) : φ x • Int.fract (f 1) < 1 := by
    have h3 := (h2 x).symm.trans (map_eq_map_one_mul_floor hf x)
    rw [nsmul_eq_mul', ← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h3
    rcases h3 with h3 | h3
    · rw [h3, Int.fract_zero] at h0; exact absurd rfl h0.ne
    · rw [nsmul_eq_mul', h3, ← fract_eq_eps_mul_floor hf h]; exact Int.fract_lt_one (f x)
  ---- Go back to the main goal
  intro x; rw [← Nat.lt_one_iff, ← le_iff_lt_or_eq, ← not_lt]
  revert h1; refine mt λ h1 ↦ ?_
  replace h2 : ∀ k, φ x ^ k • Int.fract (f 1) < 1 :=
    suffices ∀ k, ∃ y, φ y = φ x ^ k from λ k ↦ (this k).elim λ y h3 ↦ h3 ▸ h2 y
    Nat.rec ⟨1, φ.map_one⟩ λ n ⟨y, h3⟩ ↦ ⟨y * x, by rw [φ.map_mul, h3, pow_succ]⟩
  intro k; exact (h2 k).trans' (nsmul_lt_nsmul_left h0 (Nat.lt_pow_self h1))

end





/-! ### Summary -/

open scoped Classical

variable [MulOneClass M]

inductive IsAnswer : (M → R) → Prop
  | MonoidHom_cast (φ : M →* ℤ) :
      IsAnswer (λ x ↦ (φ x : R))
  | one_add_ε (ε : R) (_ : 0 < ε) (_ : Infinitesimal ε) (φ : M →* ℕ) :
      IsAnswer (φ · • (1 + ε))
  | indicator (A : Set M) (_ : ∀ m n : M, m * n ∈ A ↔ m ∈ A ∧ n ∈ A) (C : R) (_ : ⌊C⌋ = 1) :
      IsAnswer (if · ∈ A then C else 0)

theorem of_IsAnswer {f : M → R} (hf : IsAnswer f) : MonoidGood f :=
  hf.recOn
    (λ φ ↦ castMonoidHom_is_MonoidGood φ.toMulHom)
    (λ _ h h0 φ ↦ one_add_infinitesimal_mul_is_MonoidGood φ.toMulHom h.le h0)
    (λ _ hA _ hC ↦ indicator_const_is_good hA hC)

theorem to_IsAnswer {f : M → R} (hf : MonoidGood f) : IsAnswer f := by
  obtain (rfl | h) : f = 0 ∨ ⌊f 1⌋ = 1 := eq_zero_or_floor_map_one_eq_one hf
  · have h := IsAnswer.indicator (∅ : Set M) (λ _ _ ↦ and_self_iff.symm) (1 : R) Int.floor_one
    simp only [Set.mem_empty_iff_false, if_false] at h; exact h
  obtain (h0 | h0) : 0 = Int.fract (f 1) ∨ 0 < Int.fract (f 1) := (Int.fract_nonneg _).eq_or_lt
  · rcases case_fract_map_one_eq_zero hf h h0.symm with ⟨φ, rfl⟩
    exact IsAnswer.MonoidHom_cast (R := R) φ
  obtain (h1 | h1) := em (Infinitesimal (Int.fract (f 1)))
  · rcases case_fract_map_one_pos hf h h0 with ⟨φ, h2⟩
    generalize f 1 = C at h h0 h1 h2
    obtain rfl : f = (φ · • C) := funext h2
    rw [← Int.floor_add_fract C, h, Int.cast_one]
    exact IsAnswer.one_add_ε _ h0 h1 φ
  · rcases case_fract_map_one_big hf h h0 h1 with ⟨A, hA, h2⟩
    generalize f 1 = C at h h0 h1 h2; subst h2
    exact IsAnswer.indicator A hA C h

/-- Solution for `MonoidGood` -/
theorem solution {f : M → R} : MonoidGood f ↔ IsAnswer f :=
  ⟨to_IsAnswer, of_IsAnswer⟩
