/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.A5Answers.SqSubOneMap
import IMOSLLean4.IMO2012.A5.A5Answers.F3Map2
import IMOSLLean4.IMO2012.A5.A5Answers.Z4Map
import IMOSLLean4.IMO2012.A5.A5General.A5CommLift
import Mathlib.Algebra.Ring.Equiv

/-!
# IMO 2012 A5 (Case 2: `f(-1) = 0`, `char(R) ∤ 2`)

We solve the case where `f` is reduced good, `f(-1) = 0`, and `char(R) ∤ 2`.
Actually, `f(-1) = 0` implies that `f` is even, so the latter is assumed instead.
-/

namespace IMOSL
namespace IMO2012A5
namespace Case2

/-- Extra lemma -/
theorem map_sub_comm [AddGroup G] {f : G → α} (h : ∀ x, f (-x) = f x) (x y) :
    f (x - y) = f (y - x) := by
  rw [← neg_sub, h]

theorem map_even_of_map_one [NonAssocRing R] [NonAssocSemiring S]
    {f : R → S} (hf : good f) (h : f (-1) = 0) (x) : f (-x) = f x := by
  specialize hf (x + 1) (-1)
  rwa [h, mul_zero, zero_add, add_neg_cancel_right,
    mul_neg_one, neg_add, neg_add_cancel_right] at hf


section

variable [NonAssocRing R] [NonAssocSemiring S]
  {f : R → S} (hf : NontrivialGood f) (h : ∀ x, f (-x) = f x)

/-- (2.1) -/
theorem Eq1 (x y) : f (x * y - 1) = f x * f y + f (x - y) := by
  rw [← h y, sub_eq_add_neg x, ← hf.is_good, mul_neg, neg_add_eq_sub, ← neg_sub, h]

/-- (2.2) -/
theorem Eq2 (x) : f x * f 2 + f (x + 2) = f (x + 1) * f 2 + f (x - 1) := by
  have h0 := Eq1 hf h (x + 1) (1 + 1)
  rwa [add_sub_add_right_eq_sub, one_add_one_eq_two, mul_two, add_sub_assoc,
    add_sub_cancel_right, add_right_comm, ← mul_two, hf.is_good] at h0

/-- (2.5) -/
theorem Eq5 {x} (h0 : f x = 0) (h1 : f (x + 1) = 0) : ∀ y, f (y + (2 * x + 1)) = f y := by
  suffices ∀ y, f (x + y + 1) = f (x - y) from λ y ↦ by
    rw [two_mul, ← add_assoc, add_left_comm, this, sub_add_cancel_right, h]
  intro y
  have h2 : f (x * ((x + 1) * y) + 1) = f ((x + 1) * (x * y) + 1) := by
    rw [add_one_mul x, mul_add, add_one_mul x]
  have h3 : x + (x + 1) * y = (x + 1) * (y + 1) - 1 := by
    rw [mul_add_one _ y, add_sub_assoc, add_sub_cancel_right, add_comm]
  rwa [hf.is_good, h3, Eq1 hf h, hf.is_good, ← add_rotate, ← mul_add_one x,
    hf.is_good, h0, h1, zero_mul, zero_add, zero_mul, zero_add, zero_add,
    zero_mul, zero_add, add_sub_add_right_eq_sub, ← add_assoc, eq_comm] at h2

end


/-- (2.3), commutative ring version -/
theorem CommCase.Eq3 [CommRing R] [CommRing S] {f : R → S}
    (hf : NontrivialGood f) (h : ∀ x, f (-x) = f x) (x) :
    f x * (f (x - 1) * f 2 + f (x + 1)) =
      (f (x - 1) + 1) * (f (x + 1) * f 2 + f (x - 1)) := by
  have h0 : x * (x + 1) - 1 = (x - 1) * (x + 2) + 1 := by ring
  have h1 : (x - 1) + (x + 2) = x * 2 + 1 := by ring
  have h2 := Eq2 hf h x
  apply congrArg f at h0
  rw [Eq1 hf h, hf.is_good, sub_add_cancel_left, h, hf.map_one, add_zero,
    h1, hf.is_good, h2, eq_sub_of_add_eq' h2, ← sub_eq_zero] at h0
  rw [← sub_eq_zero, ← h0]; ring

/-- (2.3) -/
theorem Eq3 [Ring R] [Ring S] {f : R → S}
    (hf : NontrivialGood f) (h : ∀ x, f (-x) = f x) (x) :
    f x * (f (x - 1) * f 2 + f (x + 1)) =
      (f (x - 1) + 1) * (f (x + 1) * f 2 + f (x - 1)) := by
  rcases CommSubring.oneVarCommLift_exists hf x with
    ⟨R', R'comm, φ, -, ⟨x, rfl⟩, S', S'comm, ρ, hρ, f', h0, hf'⟩
  have h1 : φ 2 = 2 := by
    rw [← one_add_one_eq_two, φ.map_add, φ.map_one, one_add_one_eq_two]
  rw [h0, ← φ.map_one, ← φ.map_sub, ← φ.map_add, h0, h0, ← h1, h0, ← ρ.map_one]
  simp only [← ρ.map_add, ← ρ.map_mul]
  exact congrArg ρ (CommCase.Eq3 hf' (λ _ ↦ hρ <| by rw [← h0, ← h0, φ.map_neg, h]) x)

/-- If `f(2) = -1`, then `f` is `2`-periodic -/
theorem two_periodic_of_map_two [Ring R] [Ring S] [NoZeroDivisors S]
    {f : R → S} (hf : NontrivialGood f) (h : ∀ x, f (-x) = f x) (h0 : f 2 = -1) :
    ∀ x, f (x + 2) = f x := by
  suffices ∀ x, f (x + 1) = f (x - 1) from λ x ↦ by
    rw [← one_add_one_eq_two, ← add_assoc, this, add_sub_cancel_right]
  ---- First prove that either `f(x) + f(x - 1) = -1` or `f(x + 1) = f(x - 1)`
  have h1 (x : R) : f x + f (x - 1) = -1 ∨ f (x - 1) = f (x + 1) := by
    have h1 := Eq3 hf h x
    rw [h0, mul_neg_one, mul_neg_one, neg_add_eq_sub, neg_add_eq_sub, ← neg_sub,
      mul_neg, neg_eq_iff_add_eq_zero, ← add_mul, mul_eq_zero, ← add_assoc] at h1
    exact h1.imp eq_neg_of_add_eq_zero_left eq_of_sub_eq_zero
  ---- Now prove `f(x + 1) = f(x - 1)` for all `x`
  intro x; refine (h1 x).elim (λ h2 ↦ (h1 (-x)).elim (λ h3 ↦ ?_) (λ h3 ↦ ?_)) Eq.symm
  · rwa [← h2, h, add_right_inj, ← neg_add', h] at h3
  · rwa [← neg_add', h, neg_add_eq_sub, ← neg_sub, h] at h3





/-! ### Main part of the case -/

structure GoodCase2 [NonAssocRing R] [NonAssocRing S] (f : R → S)
    extends NontrivialGood f : Prop where
  map_even : ∀ x, f (-x) = f x
  map_two_ne_neg_one : f 2 ≠ -1

structure RGoodCase2 [NonAssocRing R] [NonAssocRing S] (f : R → S)
    extends ReducedGood f, GoodCase2 f


namespace GoodCase2

/-- One-variable lift for the current case -/
theorem oneVarLift_exists {R : Type u} {S : Type v} [Ring R] [Ring S]
    [NoZeroDivisors S] {f : R → S} (hf : GoodCase2 f) (c : R) :
    ∃ (R' : Type u) (_ : CommRing R')
        (φ : R' →+* R) (_ : Function.Injective φ) (_ : c ∈ Set.range φ)
      (S' : Type v) (_ : CommRing S') (_ : NoZeroDivisors S')
        (ρ : S' →+* S) (_ : Function.Injective ρ)
      (f' : R' → S') (_ : ∀ a, f (φ a) = ρ (f' a)), GoodCase2 f' := by
  rcases CommSubring.oneVarCommLiftDomain_exists hf.toNontrivialGood c with
    ⟨R', R'comm, φ, hφ, ⟨x, rfl⟩, S', S'comm, S'nzd, ρ, hρ, f', h0, hf'⟩
  refine ⟨R', R'comm, φ, hφ, ⟨x, rfl⟩, S', S'comm, S'nzd, ρ, hρ, f', h0, hf', ?_, ?_⟩
  -- `f'` is also even
  · intro x; apply hρ
    rw [← h0, ← h0, φ.map_neg, hf.map_even]
  --` f'(2) ≠ -1`
  · intro h1; apply hf.map_two_ne_neg_one
    rw [← one_add_one_eq_two, ← φ.map_one, ← φ.map_add,
      h0, one_add_one_eq_two, h1, ρ.map_neg, ρ.map_one]

theorem Eq4_ring_id [CommRing S] (a b c d : S) :
    a * (c * d + b) - (c + 1) * (b * d + c) - (a * (b * d + c) - (b + 1) * (c * d + b))
      = (b + c - (d - 1) * (a + 1)) * (b - c) := by ring

/-- (2.4), commutative case -/
theorem CommCase.Eq4 [Ring R] [CommRing S] [NoZeroDivisors S]
    {f : R → S} (hf : GoodCase2 f) :
    ∀ x, f (x + 1) + f (x - 1) = (f 2 - 1) * (f x + 1) := by
  have h := Case2.Eq3 hf.toNontrivialGood hf.map_even
  ---- First, either the goal holds or `f(x + 1) = f(x - 1)`
  have h0 (x) : f (x + 1) + f (x - 1) = (f 2 - 1) * (f x + 1) ∨ f (x + 1) = f (x - 1) := by
    have h0 := h (-x)
    rw [hf.map_even, ← neg_add', hf.map_even, neg_add_eq_sub, ← neg_sub, hf.map_even,
      ← sub_eq_zero, ← sub_eq_zero.mpr (h x), eq_comm, ← sub_eq_zero, Eq4_ring_id] at h0
    exact (mul_eq_zero.mp h0).imp eq_of_sub_eq_zero eq_of_sub_eq_zero
  save
  ---- Continue
  intro x; refine (h0 x).elim id λ h1 ↦ ?_
  specialize h0 (x + 1)
  rw [add_sub_cancel_right, add_assoc, one_add_one_eq_two] at h0
  have h2 := Eq2 hf.toNontrivialGood hf.map_even x
  rcases h0 with h0 | h0
  · have h3 : _ - _ = _ - _ := congrArg₂ (· - ·) h2 h0
    rwa [add_comm, add_sub_add_left_eq_sub, ← mul_sub_one, add_sub_right_comm, mul_comm,
      mul_comm (f _), mul_add_one (f 2 - 1), ← sub_sub, ← sub_mul, sub_sub_cancel, one_mul,
      ← add_sub_right_comm, eq_sub_iff_add_eq, ← mul_add_one (f 2 - 1), eq_comm] at h3
  · have X : f 2 + 1 ≠ 0 := λ h3 ↦ hf.map_two_ne_neg_one (eq_neg_of_add_eq_zero_left h3)
    rw [h0, ← mul_add_one (f x), h1, ← mul_add_one (f _), ← sub_eq_zero,
      ← sub_mul, mul_eq_zero, sub_eq_zero, or_iff_left X] at h2
    replace h0 := h x
    rw [h1, ← h2, add_one_mul (f x), self_eq_add_right,
      ← mul_add_one (f x), mul_eq_zero, or_iff_left X] at h0
    rw [h0, eq_comm] at h2; rw [h2] at h1
    replace h (x) := Eq5 hf.toNontrivialGood hf.map_even (x := x)
    have h3 := h (x - 1) h2 ((congrArg f (sub_add_cancel x 1)).trans h0) 2
    rw [← add_assoc, ← mul_one_add 2 (x - 1), add_sub_cancel, ← zero_add (2 * x + 1),
      h x h0 h1, hf.map_zero, neg_eq_iff_add_eq_zero, add_comm] at h3
    exact absurd h3 X

/-- (2.4) -/
theorem Eq4 [Ring R] [Ring S] [NoZeroDivisors S] {f : R → S} (hf : GoodCase2 f) (x) :
    f (x + 1) + f (x - 1) = (f 2 - 1) * (f x + 1) := by
  rcases oneVarLift_exists hf x with
    ⟨R', R'comm, φ, -, ⟨x, rfl⟩, S', S'comm, S'nzd, ρ, -, f', h0, hf'⟩
  have h1 : φ 2 = 2 := by
    rw [← one_add_one_eq_two, φ.map_add, φ.map_one, one_add_one_eq_two]
  rw [h0, ← φ.map_one, ← φ.map_sub, ← φ.map_add, h0, h0, ← h1, h0,
    ← ρ.map_one, ← ρ.map_add, ← ρ.map_add, ← ρ.map_sub, ← ρ.map_mul]
  exact congrArg ρ (CommCase.Eq4 hf' x)

end GoodCase2

/- ... -/





theorem RGoodCase2.solution {R : Type u} [Ring R] [Ring S] [NoZeroDivisors S]
    {f : R → S} (hf : RGoodCase2 f) :
    (∃ (R' : Type u) (_ : CommRing R') (φ : R →+* R')
      (ι : Subring.closure (Set.range λ x : R' ↦ x ^ 2) →+* S),
      ∀ x, f x = ι (RestrictedSqSubOne (φ x))) ∨
    (∃ φ : R →+* 𝔽₃, ∀ x, f x = 𝔽₃Map2 (φ x)) ∨
    (∃ φ : R →+* ℤ₄, ∀ x, f x = ℤ₄Map (φ x)) :=
  have hf := hf
  sorry









/-! ### Summary -/

section

variable {R : Type u} [Ring R] [Ring S] [NoZeroDivisors S] {f : R → S}

/-- Refer to Case 3 if `f(2) = -1` -/
theorem CharTwo'_of_map_two (hf : ReducedGood f)
    (h : f (-1) = 0) (h0 : f 2 = -1) : (2 : R) = 0 :=
  hf.period_imp_zero <| two_periodic_of_map_two
    hf.toNontrivialGood (map_even_of_map_one hf.is_good h) h0

theorem solution (hf : ReducedGood f) (h : f (-1) = 0) (h0 : f 2 ≠ -1) :
    (∃ (R' : Type u) (_ : CommRing R') (φ : R →+* R')
      (ι : Subring.closure (Set.range λ x : R' ↦ x ^ 2) →+* S),
      ∀ x, f x = ι (RestrictedSqSubOne (φ x))) ∨
    (∃ φ : R →+* 𝔽₃, ∀ x, f x = 𝔽₃Map2 (φ x)) ∨
    (∃ φ : R →+* ℤ₄, ∀ x, f x = ℤ₄Map (φ x)) :=
  RGoodCase2.solution ⟨hf, map_even_of_map_one hf.is_good h, h0⟩
