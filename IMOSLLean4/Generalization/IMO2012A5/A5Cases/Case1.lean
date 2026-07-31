/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.SubOneMap
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.F3Map1
public import Mathlib.Algebra.Ring.Equiv
public import Mathlib.Data.Int.Cast.Basic

/-!
# IMO 2012 A5 (Case 1: `f(-1) ≠ 0`)

We solve the case where `f` is reduced good and `f(-1) ≠ 0`.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization
namespace Case1

variable [NonAssocRing R] [NonAssocRing S] [NoZeroDivisors S]



section

variable {f : R → S} (hf : NontrivialGood f) (h : f (-1) ≠ 0)
include hf h

omit [NoZeroDivisors S] h in
/-- (1.1) -/
theorem Eq1 (x : R) : f (-x) = f (x + 1) * f (-1) + f x := by
  have h0 := hf.is_good (x + 1) (-1)
  rwa [add_neg_cancel_right, mul_neg_one (x + 1), neg_add, neg_add_cancel_right] at h0

/-- (1.2) -/
theorem Eq2 (x : R) : f (-x) = -f (x + 2) := by
  replace hf := Eq1 hf
  have h0 := hf (-(x + 1))
  rw [neg_neg, hf (x + 1), neg_add, neg_add_cancel_right, ← add_assoc, right_eq_add,
    ← add_mul, mul_eq_zero, or_iff_left h, add_assoc, one_add_one_eq_two] at h0
  exact eq_neg_of_add_eq_zero_left h0

lemma map_two : f 2 = 1 := by
  rw [← zero_add 2, ← neg_inj, ← Eq2 hf h, neg_zero, hf.map_zero]

omit [NoZeroDivisors S] h in
/-- (1.3) -/
theorem Eq3 (x y : R) : f (-x) * f (-y) + f (-(x + y)) = f x * f y + f (x + y) := by
  rw [neg_add, ← hf.is_good, neg_mul_neg, hf.is_good]

/-- (1.4) -/
theorem Eq4 (x : R) : f (2 * x + 1) = f x - f (-x) := by
  rw [hf.is_good, map_two hf h, one_mul, add_comm 2, Eq2 hf h, sub_neg_eq_add]

/-- (1.5) -/
theorem Eq5 (x : R) : f (x + 1) = 0 ∨ f x + f (-x) = f (-1) := by
  ---- First factorize `f(x)^2 - f(-x)^2`
  have h0 : f x * f x - f (-x) * f (-x) = (f x - f (-x)) * (f x + f (-x)) := by
    have h0 : x * -x = -x * x := by rw [mul_neg, neg_mul]
    rw [sub_mul, mul_add, mul_add, map_commute_of_commute hf.is_good h0,
      add_comm, add_sub_add_left_eq_sub]
  ---- Now consider `Eq3 x x` and use `Eq1` and `Eq4` to simplify things
  have h1 := Eq3 hf x x
  rw [add_comm, ← sub_eq_sub_iff_add_eq_add, h0, Eq1 hf, add_sub_cancel_right,
    ← two_mul, Eq4 hf h, ← sub_eq_zero, ← mul_sub, mul_eq_zero] at h1
  refine h1.imp (λ h1 ↦ ?_) (λ h1 ↦ (eq_of_sub_eq_zero h1).symm)
  rw [Eq1 hf, sub_add_cancel_right, neg_eq_zero, mul_eq_zero] at h1
  exact h1.resolve_right h

/-- (1.6) -/
theorem Eq6 {x : R} (h0 : f (x + 1) = 0) : f x = -1 := by
  ---- `f(-x) = f(x)`
  have h1 := Eq1 hf x
  rw [h0, zero_mul, zero_add] at h1
  ---- First use `Eq3` with `y = -(x + 1)`
  have h2 := Eq3 hf x (-(x + 1))
  rw [neg_neg, h0, mul_zero, zero_add, ← sub_eq_add_neg,
    sub_add_cancel_left, neg_neg, hf.map_one] at h2
  ---- Now use `Eq3` with `y = x + 1`
  have h3 := Eq3 hf x (x + 1)
  rw [h0, mul_zero, zero_add, ← add_assoc, ← two_mul,
    Eq4 hf h, h1, sub_self, h2, add_right_inj] at h3
  ---- Finally get `f(-2x - 1) = -f(-x) f(-1)` and finish
  replace h2 := Eq4 hf h (-x - 1)
  rw [two_mul, add_assoc, sub_add_cancel, ← add_sub_right_comm, ← two_mul, mul_neg,
    ← neg_add', h3, eq_comm, Eq1 hf, sub_add_cancel_right, sub_add_cancel,
    neg_eq_iff_add_eq_zero, h1, ← add_one_mul (f x), mul_eq_zero] at h2
  exact eq_neg_of_add_eq_zero_left (h2.resolve_right h)

lemma map_neg_one_cases : f (-1) = -2 ∨ f (-1) = 1 := by
  rw [← sub_eq_zero (b := 1), eq_neg_iff_add_eq_zero, ← mul_eq_zero,
    mul_sub_one, add_mul, two_mul, add_sub_assoc, add_sub_add_left_eq_sub]
  have h0 := Eq5 hf h (-1 + -1)
  rw [neg_add_cancel_right, or_iff_right h, ← eq_sub_iff_add_eq] at h0
  have h1 := hf.is_good (-1) (-1)
  rwa [h0, neg_mul_neg, one_mul, ← neg_add, neg_neg, one_add_one_eq_two, map_two hf h,
    eq_comm, ← sub_eq_zero, add_sub_assoc, sub_sub, one_add_one_eq_two] at h1



/-! ### Subcase 1.1: `f(-1) = -2`, `char(S) ∤ 2` -/

theorem Subcase11_solution (h0 : f (-1) = -2) :
    ∃ φ : R →+* S, ∀ x, f x = φ (x - 1) :=
  sub_one_solver hf λ x ↦ by
    rcases Eq5 hf h x with h2 | h2
    -- Case 1: `f(x + 1) = 0`
    · rw [Eq6 hf h h2, h2, neg_add_cancel]
    -- Case 2: `f(x) + f(-x) = f(-1)`
    · rw [Eq1 hf, h0, add_left_comm, ← mul_two, mul_neg, ← neg_mul, ← add_mul,
        eq_neg_iff_add_eq_zero, ← add_one_mul _ (2 : S), mul_eq_zero, add_assoc] at h2
      exact neg_add_eq_zero.mp (h2.resolve_right (neg_ne_zero.mp (h0.symm.trans_ne h)))

end



/-! ### Subcase 1.2: `f(-1) = 1`, `char(S) ∤ 3` -/

structure GoodSubcase12 (f : R → S) : Prop extends ReducedGood f where
  map_neg_one : f (-1) = 1
  Schar : (3 : S) ≠ 0

namespace GoodSubcase12

variable {f : R → S} (hf : GoodSubcase12 f)
include hf

omit [NoZeroDivisors S] in
lemma map_neg_one_ne_zero : f (-1) ≠ 0 :=
  λ h ↦ hf.Schar <| by rw [← mul_one (3 : S), ← hf.map_neg_one, h, mul_zero]

lemma eq_zero_of_map_add_one (h : f (x + 1) = 0) : x = 0 := by
  have h0 (x) : f (-x) = f (x + 1) + f x := by
    rw [Eq1 hf.toNontrivialGood, hf.map_neg_one, mul_one]
  have h1 : f (-x) = f x := by rw [h0, h, zero_add]
  refine hf.period_imp_zero λ y ↦ ?_
  ---- Apply `Eqn1` with `x = y - 1`, then bash
  have h2 := Eq3 hf.toNontrivialGood x (y - 1)
  rwa [h1, Case1.Eq6 hf.toNontrivialGood (map_neg_one_ne_zero hf) h, neg_one_mul,
    neg_one_mul, h0, h0 (x + _), add_assoc, sub_add_cancel, ← add_assoc, add_left_inj,
    neg_add_rev, add_assoc, add_eq_left, neg_add_eq_zero, eq_comm, add_comm] at h2

lemma eq_zero_or_map_neg_add_self (x) : x = 0 ∨ f x + f (-x) = 1 :=
  (Case1.Eq5 hf.toNontrivialGood (map_neg_one_ne_zero hf) x).imp
    (λ h ↦ eq_zero_of_map_add_one hf h) (λ h ↦ h.trans hf.map_neg_one)

lemma triple_sum_eq_zero (x) : f x + f (x + 1) + f (x + 2) = 0 := by
  have h := Eq1 hf.toNontrivialGood x
  rwa [Case1.Eq2 hf.toNontrivialGood (map_neg_one_ne_zero hf), hf.map_neg_one,
    mul_one, neg_eq_iff_add_eq_zero, add_comm, add_comm (f _)] at h

lemma Rchar : (3 : R) = 0 := by
  refine hf.period_imp_zero λ x ↦ ?_
  have h := triple_sum_eq_zero hf
  have h0 := h (x + 1)
  rwa [add_assoc x, one_add_one_eq_two, ← add_rotate, ← h x, add_left_inj,
    add_left_inj, add_assoc, add_comm 1, two_add_one_eq_three] at h0

lemma value_bash (x : R) : x = 0 ∨ x = 1 ∨ x = -1 := by
  ---- Assume that `f(y) + f(-y) = 1` for all `y = x, x - 1, x + 1`; else done
  have h := eq_zero_or_map_neg_add_self hf
  refine (h x).imp_right λ h0 ↦ (h (x - 1)).imp eq_of_sub_eq_zero
    λ h1 ↦ eq_neg_of_add_eq_zero_left <| (h (x + 1)).resolve_right λ h2 ↦ ?_
  ---- Change `triple_sum_eq_zero` to `f(x) + f(x + 1) + f(x - 1) = 0`
  replace h (x) : f x + f (x + 1) + f (x - 1) = 0 := by
    have h3 : (2 : R) = -1 := by
      rw [eq_neg_iff_add_eq_zero, two_add_one_eq_three, Rchar hf]
    rw [sub_eq_add_neg, ← h3, triple_sum_eq_zero hf]
  ---- Now get `f(x) + f(x + 1) + f(x - 1) + f(-x) + f(-x + 1) + f(-x - 1) = 0`
  replace h : _ + (f (-x) + _ + _) = 0 + 0 := congrArg₂ (· + ·) (h x) (h (-x))
  rw [add_zero, ← neg_add', add_right_comm (f _), add_add_add_comm,
    add_add_add_comm (f _), h0, h2, neg_add_eq_sub, ← neg_sub x, h1,
    one_add_one_eq_two, two_add_one_eq_three] at h
  exact hf.Schar h

theorem solution : ∃ φ : R →+* 𝔽₃, ∀ x, f x = 𝔽₃Map1 (φ x) :=
  have h : (𝔽₃.cast : 𝔽₃ → R).Bijective :=
    ⟨𝔽₃.castRingHom_injective (Rchar hf)
      λ h ↦ map_neg_one_ne_zero hf (by rw [h, neg_zero, ← h, hf.map_one]),
    λ x ↦ (value_bash hf x).elim (λ h ↦ ⟨𝔽₃.𝔽₃0, h.symm⟩)
      λ h ↦ h.elim (λ h ↦ ⟨𝔽₃.𝔽₃1, h.symm⟩) (λ h ↦ ⟨𝔽₃.𝔽₃2, h.symm⟩)⟩
  have h0 : ∀ x, f (𝔽₃.cast x) = 𝔽₃Map1 x
    | 𝔽₃.𝔽₃0 => by
        change f 0 = ((-1 : ℤ) : S)
        rw [hf.map_zero, Int.cast_neg, Int.cast_one]
    | 𝔽₃.𝔽₃1 => (hf.map_one).trans Int.cast_zero.symm
    | 𝔽₃.𝔽₃2 => hf.map_neg_one.trans Int.cast_one.symm
  let ρ := RingEquiv.ofBijective (𝔽₃.castRingHom (Rchar hf)) h
  ⟨ρ.symm, λ x ↦ h0 _ ▸ congrArg f (Equiv.apply_symm_apply ρ.toEquiv _).symm⟩

end GoodSubcase12



/-! ### Summary -/

theorem solution {f : R → S} (hf : ReducedGood f) (h : f (-1) ≠ 0) :
    (∃ φ : R →+* S, ∀ x, f x = φ (x - 1)) ∨
    (∃ φ : R →+* 𝔽₃, ∀ x, f x = 𝔽₃Map1 (φ x)) :=
  let hf' := hf.toNontrivialGood
  (em (f (-1) = -2)).imp
    (Subcase11_solution hf' h)
    (λ h0 ↦ GoodSubcase12.solution <|
      have h1 := (map_neg_one_cases hf' h).resolve_left h0
      ⟨hf, h1, by rwa [← two_add_one_eq_three, Ne,
        ← neg_eq_iff_add_eq_zero, ← h1, eq_comm]⟩)
