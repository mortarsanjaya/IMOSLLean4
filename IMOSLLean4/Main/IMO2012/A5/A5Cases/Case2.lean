/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2012.A5.A5Answers.SqSubOneMap
import IMOSLLean4.Main.IMO2012.A5.A5Answers.F3Map2
import IMOSLLean4.Main.IMO2012.A5.A5Answers.Z4Map
import IMOSLLean4.Main.IMO2012.A5.A5General.A5CommLift
import IMOSLLean4.Main.IMO2012.A5.A5General.A5QuasiPeriodic
import IMOSLLean4.Extra.SquareLike

/-!
# IMO 2012 A5 (Case 2: `f(-1) = 0`, `char(R) ∤ 2`)

We solve the case where `f` is reduced good, `f(-1) = 0`, and `char(R) ∤ 2`.
Actually, `f(-1) = 0` implies that `f` is even, so the latter is assumed instead.
-/

namespace IMOSL
namespace IMO2012A5
namespace Case2

/-! ### General lemmas -/

section

variable [NonAssocRing R] [NonAssocSemiring S] {f : R → S}

theorem map_even_of_map_one (hf : good f) (h : f (-1) = 0) (x) : f (-x) = f x := by
  specialize hf (x + 1) (-1)
  rwa [h, mul_zero, zero_add, add_neg_cancel_right,
    mul_neg_one, neg_add, neg_add_cancel_right] at hf

variable (hf : NontrivialGood f) (h : ∀ x, f (-x) = f x)
include hf h

/-- (2.1) -/
theorem Eq1 (x y) : f (x * y - 1) = f x * f y + f (x - y) := by
  rw [← h y, sub_eq_add_neg x, ← hf.is_good, mul_neg, neg_add_eq_sub, ← neg_sub, h]

omit h in
/-- (2.2) -/
theorem Eq2 (x) : f (x * 2 - 1) = f (x - 1) * f 2 + f (x + 1) := by
  have h0 := hf.is_good (x - 1) (1 + 1)
  rwa [sub_add_add_cancel, one_add_one_eq_two, mul_two, add_assoc,
    sub_add_cancel, ← add_sub_right_comm, ← mul_two] at h0

/-- (2.3) -/
theorem Eq3 (x) : f (x * 2 + 1) = f (x + 1) * f 2 + f (x - 1) := by
  have h0 := Eq2 hf (-x)
  rwa [neg_mul, ← neg_add', h, ← neg_add', h, neg_add_eq_sub, ← neg_sub, h] at h0

/-- (2.5) -/
theorem Eq5 {x} (h0 : f x = 0) (h1 : f (x + 1) = 0) : ∀ y, f (y + (2 * x + 1)) = f y :=
  suffices ∀ y, f (x + y + 1) = f (x - y) from λ y ↦ by
    rw [two_mul, ← add_assoc, add_left_comm, this, sub_add_cancel_right, h]
  λ y ↦ by
    have h2 : f (x * ((x + 1) * y) + 1) = f ((x + 1) * (x * y) + 1) := by
      rw [add_one_mul x, mul_add, add_one_mul x]
    have h3 : x + (x + 1) * y = (x + 1) * (y + 1) - 1 := by
      rw [mul_add_one _ y, add_sub_assoc, add_sub_cancel_right, add_comm]
    rwa [hf.is_good, h3, Eq1 hf h, hf.is_good, ← add_rotate, ← mul_add_one x,
      hf.is_good, h0, h1, zero_mul, zero_add, zero_mul, zero_add, zero_add,
      zero_mul, zero_add, add_sub_add_right_eq_sub, ← add_assoc, eq_comm] at h2

end


namespace CommCase

variable [Ring R] [CommRing S] [NoZeroDivisors S] {f : R → S}
  (hf : NontrivialGood f) (h : ∀ x, f (-x) = f x)
include hf h

omit [NoZeroDivisors S] in
/-- (2.4) (commutative version only) -/
theorem Eq4 (x) : f x * f (x * 2 - 1) = (f (x - 1) + 1) * f (x * 2 + 1) := by
  have h0 : x * (x + 1) - 1 = (x - 1) * (x + 1 + 1) + 1 := by
    rw [mul_add_one (x - 1), add_assoc, sub_add_cancel, sub_one_mul,
      ← add_sub_right_comm, add_comm, add_sub_add_right_eq_sub]
  apply congrArg f at h0
  rw [Eq1 hf h, hf.is_good, sub_add_cancel_left, h, hf.map_one, sub_add_add_cancel,
    add_zero, add_assoc, one_add_one_eq_two, ← add_assoc, ← mul_two] at h0
  rw [Eq2 hf, mul_add, h0, ← add_assoc, add_one_mul (f _),
    add_left_inj, mul_left_comm, ← mul_add, ← hf.is_good]

omit [NoZeroDivisors S] in
/-- (2.4), alternate version -/
theorem Eq4_alt (x) : f x * f (x * 2 + 1) = (f (x + 1) + 1) * f (x * 2 - 1) := by
  have h0 := Eq4 hf h (-x)
  rwa [h, neg_mul, ← neg_add', h, ← neg_add', h, neg_add_eq_sub, ← neg_sub, h] at h0

/-- `R` has characteristic `2` if `f(2) = -1` -/
theorem two_periodic_of_map_two (h0 : f 2 = -1) : ∀ x, f (x + 2) = f x :=
  have h1 (x) : f (x * 2 + 1) = f (x + 2) - f x := by
    rw [hf.is_good, h0, mul_neg_one, neg_add_eq_sub]
  have h2 (x) : f (x * 2 + 1) = -f (x * 2 - 1) := by
    rw [Eq2 hf, Eq3 hf h, h0, mul_neg_one, mul_neg_one, neg_add_rev, neg_neg]
  ---- First get the main ineq
  have h3 (x) : f x + f (x + 1) = -1 ∨ f (x * 2 - 1) = 0 := by
    have h3 := Eq4_alt hf h x
    rw [h2, mul_neg, neg_eq_iff_add_eq_zero, ← add_mul, mul_eq_zero, ← add_assoc] at h3
    exact h3.imp_left eq_neg_of_add_eq_zero_left
  ---- Now
  λ x ↦ (h3 (x + 1)).symm.elim
    (λ h4 ↦ by rwa [mul_two, add_sub_assoc, add_sub_cancel_right,
      add_right_comm, ← mul_two, h1, sub_eq_zero] at h4)
    λ h4 ↦ (h3 x).symm.elim
      (λ h5 ↦ by rwa [← neg_eq_zero, ← h2, h1, sub_eq_zero] at h5)
      (λ h5 ↦ by rwa [← h5, add_comm, add_left_inj, add_assoc, one_add_one_eq_two] at h4)

omit [CommRing S] [NoZeroDivisors S] hf h in
theorem Eq6_ring_id {S} [CommRing S] (a b c d : S) :
    a * (c * d + b) - a * (b * d + c) - ((c + 1) * (b * d + c) - (b + 1) * (c * d + b))
      = (b + c - (a + 1) * (d - 1)) * (b - c) := by ring

/-- (2.6), commutative case -/
theorem Eq6 (h0 : f 2 ≠ -1) : ∀ x, f (x + 1) + f (x - 1) = (f x + 1) * (f 2 - 1) := by
  ---- First, either the goal holds or `f(x + 1) = f(x - 1)`
  have h1 (x) : f (x + 1) + f (x - 1) = (f x + 1) * (f 2 - 1) ∨ f (x + 1) = f (x - 1) := by
    have h1 : _ - _ = _ - _ := congrArg₂ (· - ·) (Eq4 hf h x) (Eq4_alt hf h x)
    rw [Eq2 hf, Eq3 hf h, ← sub_eq_zero, Eq6_ring_id, mul_eq_zero] at h1
    exact h1.imp eq_of_sub_eq_zero eq_of_sub_eq_zero
  ---- Continue
  intro x; refine (h1 x).elim id λ h2 ↦ ?_
  specialize h1 (x + 1)
  rw [add_sub_cancel_right, add_assoc, one_add_one_eq_two] at h1
  rcases h1 with h1 | h1
  · have h2 := Eq3 hf h x
    rw [hf.is_good, eq_sub_of_add_eq h1, add_sub_left_comm, ← mul_sub_one,
      add_one_mul (f _), add_assoc, ← one_add_mul (f x), mul_sub_one,
      ← add_sub_right_comm, add_sub_assoc, add_right_inj, add_comm] at h2
    exact (eq_add_of_sub_eq' h2).symm
  · have h0 : f 2 + 1 ≠ 0 := λ X ↦ h0 (eq_neg_of_add_eq_zero_left X)
    have h3 := Eq3 hf h x
    rw [← h2, hf.is_good, h1, ← mul_add_one (f x), ← mul_add_one (f _),
      ← sub_eq_zero, ← sub_mul, mul_eq_zero, or_iff_left h0, sub_eq_zero] at h3
    have h4 := Eq4 hf h x
    rw [Eq3 hf h, Eq2 hf, ← h2, ← h3, ← sub_eq_zero, ← sub_mul, sub_add_cancel_left,
      neg_one_mul, neg_eq_zero, ← mul_add_one (f x), mul_eq_zero, or_iff_left h0] at h4
    rw [eq_comm, h4] at h3; rw [eq_comm, h3] at h2
    have h5 := Eq5 hf h h4 h3 0
    rw [zero_add, hf.is_good, add_comm 2 x, h1, h4, mul_zero,
      add_zero, hf.map_zero, eq_comm, neg_eq_zero] at h5
    rw [← sub_eq_zero, ← one_mul (_ - _), h5, zero_mul]

/-- (2.7), commutative case -/
theorem Eq7 (h0 : f 2 ≠ -1) (h1 : f 2 ≠ 1) (x) :
    (f (x + 1) + 1) * (f (x - 1) + 1) = f x ^ 2 := by
  ---- Reduce to the case where `f(2x + 1) = f(2x - 1) = 0`
  have h2 : _ * _ = _ * _ := congrArg (f x * ·) (Eq4_alt hf h x)
  rw [← mul_assoc, ← sq, mul_left_comm, Eq4 hf h,
    ← mul_assoc, ← sub_eq_zero, ← sub_mul, mul_eq_zero] at h2
  rcases h2 with h2 | h2; exact (eq_of_sub_eq_zero h2).symm
  have h3 : _ * _ = _ * _ := congrArg (f x * ·) (Eq4 hf h x)
  rw [← mul_assoc, ← sq, mul_left_comm, Eq4_alt hf h,
    ← mul_assoc, ← sub_eq_zero, ← sub_mul, mul_eq_zero] at h3
  rcases h3 with h3 | h3; rwa [sub_eq_zero, eq_comm, mul_comm] at h3
  ---- Solve the case where `f(2x + 1) = f(2x - 1) = 0`
  rw [Eq3 hf h] at h2
  replace h3 : _ + _ = _ + _ := congrArg₂ (· + ·) h2 h3
  rw [Eq2 hf, add_add_add_comm, add_zero, ← add_mul,
    add_comm (f _), ← mul_add_one (α := S), mul_eq_zero,
    or_iff_left (h0 ∘ eq_neg_of_add_eq_zero_left), ← eq_neg_iff_add_eq_zero] at h3
  have X : f 2 - 1 ≠ 0 := h1 ∘ eq_of_sub_eq_zero
  rw [h3, ← sub_eq_add_neg, ← mul_sub_one, mul_eq_zero, or_iff_left X] at h2
  rw [h2, neg_zero] at h3
  have h4 := Eq6 hf h h0 x
  rw [h2, h3, add_zero, zero_eq_mul, or_iff_left X] at h4
  rw [h2, h3, zero_add, one_mul, eq_neg_of_add_eq_zero_left h4, neg_one_sq]

end CommCase








/-! ### Restriction to the case `f(2) ≠ -1` -/

structure GoodCase2 [NonAssocRing R] [NonAssocRing S] (f : R → S)
    extends NontrivialGood f : Prop where
  map_even : ∀ x, f (-x) = f x
  map_two_ne_neg_one : f 2 ≠ -1

structure RGoodCase2 [NonAssocRing R] [NonAssocRing S] (f : R → S)
    extends ReducedGood f, GoodCase2 f : Prop


namespace GoodCase2

variable {R : Type u} {S : Type v} [Ring R] [Ring S] {f : R → S} (hf : GoodCase2 f)
include hf

theorem Rtwo_ne_zero : (2 : R) ≠ 0 :=
  λ h ↦ hf.map_two_ne_neg_one <| by rw [h, hf.map_zero]

/-- One-variable lift for the current case -/
theorem oneVarLift_exists [NoZeroDivisors S] (c : R) :
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
    rw [← map_ofNat φ 2, h0, h1, ρ.map_neg, ρ.map_one]

theorem Eq1 : ∀ x y, f (x * y - 1) = f x * f y + f (x - y) :=
  Case2.Eq1 hf.toNontrivialGood hf.map_even

/-- (2.2) -/
theorem Eq2 : ∀ x, f (x * 2 - 1) = f (x - 1) * f 2 + f (x + 1) :=
  Case2.Eq2 hf.toNontrivialGood

/-- (2.3) -/
theorem Eq3 : ∀ x, f (x * 2 + 1) = f (x + 1) * f 2 + f (x - 1) :=
  Case2.Eq3 hf.toNontrivialGood hf.map_even

variable [NoZeroDivisors S]

/-- (2.6) -/
theorem Eq6 (x) : f (x + 1) + f (x - 1) = (f x + 1) * (f 2 - 1) := by
  rcases oneVarLift_exists hf x with
    ⟨R', R'comm, φ, -, ⟨x, rfl⟩, S', S'comm, S'nzd, ρ, -, f', h0, hf'⟩
  rw [h0, ← φ.map_one, ← φ.map_sub, ← φ.map_add, h0, h0, ← map_ofNat φ 2, h0,
    ← ρ.map_one, ← ρ.map_add, ← ρ.map_add, ← ρ.map_sub, ← ρ.map_mul]
  exact congrArg ρ
    (CommCase.Eq6 hf'.toNontrivialGood hf'.map_even hf'.map_two_ne_neg_one x)

/-- (2.7) -/
theorem Eq7 (h1 : f 2 ≠ 1) (x) : (f (x + 1) + 1) * (f (x - 1) + 1) = f x ^ 2 := by
  rcases oneVarLift_exists hf x with
    ⟨R', R'comm, φ, -, ⟨x, rfl⟩, S', S'comm, S'nzd, ρ, -, f', h0, hf'⟩
  have h2 : f' 2 ≠ 1 := λ h2 ↦ h1 <| by rw [← map_ofNat φ 2, h0, h2, ρ.map_one]
  rw [h0, ← φ.map_one, ← φ.map_sub, ← φ.map_add, h0, h0, ← ρ.map_one,
    ← ρ.map_add, ← ρ.map_add, ← ρ.map_mul, ← ρ.map_pow]
  exact congrArg ρ
    (CommCase.Eq7 hf'.toNontrivialGood hf'.map_even hf'.map_two_ne_neg_one h2 x)

theorem map_two_cases : f 2 = 1 ∨ f 2 = 0 ∨ f 2 = 3 := by
  have h := Eq1 hf (2 + 1) 2
  rw [add_sub_cancel_left, hf.map_one, add_zero,
    mul_two, add_sub_assoc, add_sub_cancel_right] at h
  have h0 := Eq6 hf (2 + 1 + 1)
  rw [add_sub_cancel_right, add_assoc, one_add_one_eq_two, h, ← mul_add_one (f _)] at h0
  replace h := Eq6 hf (2 + 1)
  rw [add_sub_cancel_right, add_one_mul (α := S), add_sub_left_comm,
    add_comm, add_right_inj, eq_sub_iff_add_eq] at h
  rw [h, mul_assoc, eq_comm, ← sub_eq_zero, ← mul_sub, mul_eq_zero] at h0
  clear h; revert h0; refine Or.imp (λ h ↦ ?_) (λ h ↦ ?_)
  · have h0 := Eq1 hf 2 (1 + 1)
    rw [two_mul, ← add_assoc, add_sub_cancel_right, one_add_one_eq_two, sub_self,
      hf.map_zero, h, eq_comm, add_neg_eq_zero, mul_self_eq_one_iff] at h0
    exact h0.resolve_right hf.map_two_ne_neg_one
  · rw [mul_sub_one, sub_one_mul, sub_sub, sub_add_add_cancel, ← two_mul,
      sub_sub, ← one_add_mul 2 (f 2), ← sub_mul, mul_eq_zero, add_comm] at h
    exact h.symm.imp_right λ h ↦ (eq_of_sub_eq_zero h).trans two_add_one_eq_three

end GoodCase2





/-! ### Subcase 2.1: `f(2) = 1`, `char(S) ∤ 2` -/

theorem RGoodSubcase21.solution [Ring R] [Ring S] [NoZeroDivisors S]
    {f : R → S} (hf : RGoodCase2 f) (h : f 2 = 1) :
    ∃ φ : R →+* ℤ₄, ∀ x, f x = ℤ₄Map (φ x) :=
  have h0 (x) : f (x + 2) = -f x := by
    have h0 := hf.toGoodCase2.Eq6 (x + 1)
    rw [h, sub_self, mul_zero, add_sub_cancel_right, add_assoc, one_add_one_eq_two] at h0
    exact eq_neg_iff_add_eq_zero.mpr h0
  have h1 : (4 : R) = 0 := hf.period_imp_zero λ x ↦ by
    have h1 : (2 : R) + 2 = 4 := by norm_num
    rw [← h1, ← add_assoc, h0, h0, neg_neg]
  have hInj : (ℤ₄.cast : ℤ₄ → R).Injective :=
    ℤ₄.castRingHom_injective h1 hf.toGoodCase2.Rtwo_ne_zero
  have hSurj : (ℤ₄.cast : ℤ₄ → R).Surjective :=
    have h2 : QuasiPeriodic f 2 := (QuasiPeriodic.iff_right hf.toNontrivialGood).mpr
      λ x ↦ by rw [h0, h, mul_neg_one]
    have X : (2 : R) + 1 = -1 := by
      rwa [two_add_one_eq_three, eq_neg_iff_add_eq_zero, three_add_one_eq_four]
    λ x ↦ (h2.reduced_main_cases hf.toReducedGood hf.toGoodCase2.Rtwo_ne_zero x).elim
      (λ h3 ↦ h3.elim (λ h3 ↦ ⟨ℤ₄.ℤ₄0, h3.symm⟩) (λ h3 ↦ ⟨ℤ₄.ℤ₄2, h3.symm⟩))
      (λ h3 ↦ h3.elim (λ h3 ↦ ⟨ℤ₄.ℤ₄1, h3.symm⟩) (λ h3 ↦ ⟨ℤ₄.ℤ₄3, (h3.trans X).symm⟩))
  have h2 : (ℤ₄.cast : ℤ₄ → R).Bijective := ⟨hInj, hSurj⟩
  have h3 : ∀ x, f (ℤ₄.cast x) = ℤ₄Map x
    | ℤ₄.ℤ₄0 => by
        change f 0 = ((-1 : ℤ) : S)
        rw [hf.map_zero, Int.cast_neg, Int.cast_one]
    | ℤ₄.ℤ₄1 => hf.map_one.trans Int.cast_zero.symm
    | ℤ₄.ℤ₄2 => h.trans Int.cast_one.symm
    | ℤ₄.ℤ₄3 => (hf.map_even _).trans (hf.map_one.trans Int.cast_zero.symm)
  let ρ := RingEquiv.ofBijective (ℤ₄.castRingHom h1) h2
  ⟨ρ.symm, λ x ↦ h3 _ ▸ congrArg f (Equiv.apply_symm_apply ρ.toEquiv _).symm⟩





/-! ### Subcase 2.2: `f(2) = 0`, `char(S) ∤ 3` -/

namespace RGoodSubcase22

variable [Ring R] [Ring S] [NoZeroDivisors S] {f : R → S} (hf : RGoodCase2 f) (h : f 2 = 0)
include hf h

/-- (2.2.1) -/
theorem Eq1 (x) : f (x + 1) + f (x - 1) + f x = -1 := by
  rw [hf.toGoodCase2.Eq6, h, zero_sub, mul_neg_one, neg_add_rev, neg_add_cancel_right]

theorem Rchar : (3 : R) = 0 := by
  rw [← two_add_one_eq_three, ← eq_neg_iff_add_eq_zero]
  refine hf.period_imp_eq _ _ λ x ↦ ?_
  have h0 := Eq1 hf h (x + 1)
  rwa [add_sub_cancel_right, add_assoc x, one_add_one_eq_two, ← Eq1 hf h x,
    ← add_rotate, add_left_inj, add_right_inj, sub_eq_add_neg] at h0

theorem Rchar' : (2 : R) = -1 := by
  rw [eq_neg_iff_add_eq_zero, two_add_one_eq_three, Rchar hf h]

/-- (2.2.2) -/
theorem Eq2 (x) : f (x + 1) * f (x - 1) = (f x + 1) * f x := by
  have h0 : f 2 ≠ 1 := λ h0 ↦ hf.map_two_ne_neg_one <| by rw [h, zero_eq_neg, ← h, ← h0]
  rw [add_one_mul (f x), ← sq, ← hf.toGoodCase2.Eq7 h0, add_one_mul (f _),
    mul_add_one (f _), add_assoc, add_assoc, self_eq_add_right,
    add_right_comm, ← add_assoc, ← add_assoc, Eq1 hf h, neg_add_cancel]

theorem map_eq_neg_one_imp (h0 : f x = -1) : x = 0 := by
  have h1 : f (x + 1) = 0 ∧ f (x - 1) = 0 := by
    have h1 : f (x + 1) + f (x - 1) = 0 := by
      rw [eq_sub_of_add_eq (Eq1 hf h x), h0, sub_self]
    obtain h2 | h2 : f (x + 1) = 0 ∨ f (x - 1) = 0 := by
      rw [← mul_eq_zero, Eq2 hf h, h0, neg_add_cancel, zero_mul]
    · rw [h2, zero_add] at h1; exact ⟨h2, h1⟩
    · rw [h2, add_zero] at h1; exact ⟨h1, h2⟩
  ---- Grind the rest
  rw [sub_eq_add_neg, ← Rchar' hf h, ← one_add_one_eq_two, ← add_assoc] at h1
  replace h1 := hf.toReducedGood.period_imp_zero
    (Eq5 hf.toNontrivialGood hf.map_even h1.1 h1.2)
  rwa [Rchar' hf h, neg_one_mul, neg_add_rev, neg_add_cancel_comm, neg_eq_zero] at h1

theorem map_eq_neg_one_or_zero (h0 : (3 : S) ≠ 0) (x) : f x = -1 ∨ f x = 0 := by
  have Rchar' := Rchar' hf h
  ---- Get `f(x^2 + 1)`, `f(x^2 - 1)`, and `f(x^2)`
  have h1 : f (x * x + 1) = (f x + 1) * f x := by
    rw [hf.is_good, ← two_mul, Rchar', neg_one_mul, hf.map_even, add_one_mul (f x)]
  have h2 : f (x * x - 1) = f x * f x - 1 := by
    rw [Case2.Eq1 hf.toNontrivialGood hf.map_even, sub_self, hf.map_zero, sub_eq_add_neg]
  have h3 : f (x * x) = (f x + 1 + 1) * f x := by
    have h2 := hf.is_good (x + 1) (x - 1)
    rw [Eq2 hf h, add_one_mul x, mul_sub_one, sub_add_sub_cancel, sub_add_cancel,
      add_add_sub_cancel, ← two_mul, Rchar', neg_one_mul, hf.map_even] at h2
    exact h2.trans (add_one_mul _ (f x)).symm
  ---- Add all three equations and grind
  have h4 := Eq1 hf h (x * x)
  rw [h1, h2, h3, ← add_sub_assoc, ← add_mul, ← add_sub_right_comm,
    sub_eq_neg_self, ← add_mul, mul_eq_zero, add_add_add_comm] at h4
  clear h1 h2 h3; revert h4; refine Or.imp_left λ h1 ↦ ?_
  rw [← two_mul, ← add_one_mul 2 (f x + 1), mul_eq_zero, two_add_one_eq_three] at h1
  exact eq_neg_of_add_eq_zero_left (h1.resolve_left h0)

theorem value_bash (h0 : (3 : S) ≠ 0) (x : R) : x = 0 ∨ x = 1 ∨ x = -1 := by
  have h1 (x) : x = 0 ∨ f x = 0 :=
    (map_eq_neg_one_or_zero hf h h0 x).imp_left (map_eq_neg_one_imp hf h)
  refine (h1 x).imp_right λ h2 ↦ (h1 (x - 1)).imp eq_of_sub_eq_zero λ h3 ↦
    (h1 (x + 1)).elim eq_neg_of_add_eq_zero_left λ h4 ↦ ?_
  have h5 := Eq1 hf h x
  rw [h2, h3, h4, add_zero, add_zero, eq_comm, neg_eq_zero] at h5
  rw [← mul_one 3, h5, mul_zero] at h0
  exact absurd rfl h0

theorem solution (h0 : (3 : S) ≠ 0) : ∃ φ : R →+* 𝔽₃, ∀ x, f x = 𝔽₃Map2 (φ x) :=
  have h1 : (𝔽₃.cast : 𝔽₃ → R).Bijective :=
    ⟨𝔽₃.castRingHom_injective (Rchar hf h) λ h ↦ h0 <| by
      have h0 := hf.map_one; rw [h, hf.map_zero, neg_eq_zero] at h0
      rw [← mul_one 3, h0, mul_zero],
    λ x ↦ (value_bash hf h h0 x).elim (λ h ↦ ⟨𝔽₃.𝔽₃0, h.symm⟩)
      λ h ↦ h.elim (λ h ↦ ⟨𝔽₃.𝔽₃1, h.symm⟩) (λ h ↦ ⟨𝔽₃.𝔽₃2, h.symm⟩)⟩
  have h2 : ∀ x, f (𝔽₃.cast x) = 𝔽₃Map2 x
    | 𝔽₃.𝔽₃0 => by
        change f 0 = ((-1 : ℤ) : S)
        rw [hf.map_zero, Int.cast_neg, Int.cast_one]
    | 𝔽₃.𝔽₃1 => (hf.map_one).trans Int.cast_zero.symm
    | 𝔽₃.𝔽₃2 => (hf.map_even _).trans ((hf.map_one).trans Int.cast_zero.symm)
  let ρ := RingEquiv.ofBijective (𝔽₃.castRingHom (Rchar hf h)) h1
  ⟨ρ.symm, λ x ↦ h2 _ ▸ congrArg f (Equiv.apply_symm_apply ρ.toEquiv _).symm⟩

end RGoodSubcase22





/-! ### Structure for Subcase 2.3: `f(2) = 3`, `char(S) ∤ 2` -/

/-- Structure expressing that `g - 1` is good and `(g - 1)(2) = 3` -/
structure ShiftGood23 [NonAssocRing R] [NonAssocRing S] (g : R → S) : Prop where
  shift_good : GoodCase2 (g - 1)
  map_two : g 2 = 4

namespace ShiftGood23

/-- One-variable lift for the current case -/
theorem oneVarLift_exists {R : Type u} {S : Type v} [Ring R] [Ring S]
    [NoZeroDivisors S] {g : R → S} (hg : ShiftGood23 g) (c : R) :
    ∃ (R' : Type u) (_ : CommRing R')
        (φ : R' →+* R) (_ : Function.Injective φ) (_ : c ∈ Set.range φ)
      (S' : Type v) (_ : CommRing S') (_ : NoZeroDivisors S')
        (ρ : S' →+* S) (_ : Function.Injective ρ)
      (g' : R' → S') (_ : ∀ a, g (φ a) = ρ (g' a)), ShiftGood23 g' := by
  rcases hg.shift_good.oneVarLift_exists c with
    ⟨R', R'comm, φ, hφ, ⟨x, rfl⟩, S', S'comm, S'nzd, ρ, hρ, f', h0, hf'⟩
  refine ⟨R', R'comm, φ, hφ, ⟨x, rfl⟩, S', S'comm, S'nzd, ρ, hρ, f' + 1, ?_, ?_⟩
  -- Homomorphism transfer
  · intro x; rw [Pi.add_apply, Pi.one_apply, ρ.map_add, ← h0, ρ.map_one]
    exact (sub_add_cancel _ _).symm
  -- `ShiftGood`
  · refine ⟨by rwa [add_sub_cancel_right], hρ ?_⟩
    rw [Pi.add_apply, Pi.one_apply, ρ.map_add, ρ.map_one, ← h0, map_ofNat,
      map_ofNat, Pi.sub_apply, Pi.one_apply, hg.map_two, sub_add_cancel]


section

variable [NonAssocRing R] [NonAssocRing S]

lemma mk_iff {g : R → S} : ShiftGood23 g ↔ GoodCase2 (g - 1) ∧ g 2 = 4 :=
  ⟨λ ⟨h, h0⟩ ↦ ⟨h, h0⟩, λ ⟨h, h0⟩ ↦ ⟨h, h0⟩⟩

lemma shift_mk_iff {f : R → S} : ShiftGood23 (f + 1) ↔ GoodCase2 f ∧ f 2 = 3 := by
  rw [mk_iff, add_sub_cancel_right, ← three_add_one_eq_four]
  exact and_congr_right' (add_left_inj _)

variable {g : R → S} (hg : ShiftGood23 g)
include hg

lemma map_zero : g 0 = 0 :=
  sub_eq_neg_self.mp hg.shift_good.map_zero

lemma map_one : g 1 = 1 :=
  eq_of_sub_eq_zero hg.shift_good.map_one

lemma map_even (x) : g (-x) = g x :=
  sub_left_injective (hg.shift_good.map_even x)

lemma Schar_ne_two : (2 : S) ≠ 0 :=
  λ h ↦ hg.shift_good.map_two_ne_neg_one <| by
    rw [Pi.sub_apply, Pi.one_apply, sub_eq_neg_self, hg.map_two, ← three_add_one_eq_four,
      ← two_add_one_eq_three, h, zero_add, one_add_one_eq_two, h]

lemma is_good (x y) : g (x * y + 1) = (g x - 1) * (g y - 1) + g (x + y) := by
  have h := hg.shift_good.is_good x y
  simp only [Pi.sub_apply, Pi.one_apply] at h
  rwa [← add_sub_assoc, sub_left_inj] at h

lemma alt_good (x y) : g (x * y - 1) = (g x - 1) * (g y - 1) + g (x - y) := by
  have h := hg.is_good x (-y)
  rwa [hg.map_even, mul_neg, neg_add_eq_sub, ← neg_sub, hg.map_even, ← sub_eq_add_neg] at h

end


section

variable [Ring R] [Ring S] [NoZeroDivisors S] {g : R → S} (hg : ShiftGood23 g)
include hg

/-- (2.3.1) -/
lemma Eq1 (x) : g (x + 1) + g (x - 1) = 2 * (g x + 1) := by
  have h := hg.shift_good.Eq6 x; simp only [Pi.sub_apply, Pi.one_apply] at h
  rwa [sub_add_cancel, hg.map_two, sub_eq_of_eq_add (G := S) three_add_one_eq_four.symm,
    sub_eq_of_eq_add (G := S) two_add_one_eq_three.symm, sub_add_sub_comm, mul_two,
    sub_eq_iff_eq_add, one_add_one_eq_two, ← two_mul, ← mul_add_one] at h

omit [NoZeroDivisors S] in
/-- (2.3.2) -/
lemma Eq2 (x y) : g (x * y + 1) - g (x * y - 1) = g (x + y) - g (x - y) := by
  rw [hg.is_good, hg.alt_good, add_sub_add_left_eq_sub]

lemma Eq3_1 (x) : g (x + 1) * g (x - 1) = (g x - 1) ^ 2 := by
  have h : (g - 1) 2 ≠ 1 := λ h0 ↦ by
    rw [Pi.sub_apply, hg.map_two, sub_eq_of_eq_add three_add_one_eq_four.symm,
      ← two_add_one_eq_three, add_left_eq_self] at h0
    exact hg.Schar_ne_two h0
  replace h := hg.shift_good.Eq7 h x
  simp only [Pi.sub_apply, Pi.one_apply, sub_add_cancel] at h; exact h

omit [Ring S] [NoZeroDivisors S] hg in
lemma CommCase.Eq3_2 {S} [CommRing S] [NoZeroDivisors S]
    {g : R → S} (hg : ShiftGood23 g) (x) :
    (g (x + 1) - g (x - 1)) ^ 2 = 2 ^ 4 * g x := by
  rw [sub_sq', ← sub_eq_of_eq_add (add_sq' (g _) _),
    Eq1 hg, mul_assoc, Eq3_1 hg]
  ring

lemma Eq3_2 (x) : (g (x + 1) - g (x - 1)) ^ 2 = 2 ^ 4 * g x := by
  rcases oneVarLift_exists hg x with
    ⟨R', R'comm, φ, -, ⟨x, rfl⟩, S', S'comm, S'nzd, ρ, -, g', h0, hg'⟩
  rw [← φ.map_one, ← φ.map_add, ← φ.map_sub, h0, h0, ← ρ.map_sub, ← ρ.map_pow,
    CommCase.Eq3_2 hg', h0, ρ.map_mul, ρ.map_pow, map_ofNat]

/-- (2.3.3) -/
lemma Eq3 (x y) : (g (x + y) - g (x - y)) ^ 2 = 2 ^ 4 * g (x * y) :=
  Eq2 hg x y ▸ Eq3_2 hg _

/-- (2.3.4) -/
lemma Eq4 (x y) : 2 * (g (x * y) - g x * g y) =
    g (x + y) + g (x - y) - 2 * (g x + g y) := by
  have h : _ + _ = _ + _ := congrArg₂ (· + ·) (hg.is_good x y) (hg.alt_good x y)
  rw [Eq1 hg, add_add_add_comm, ← two_mul, ← sub_eq_iff_eq_add', ← mul_sub] at h
  rw [← h, ← mul_sub, sub_sub, sub_one_mul, mul_sub_one, sub_sub, sub_add,
    ← add_sub_assoc, sub_sub_cancel_left, sub_neg_eq_add, add_sub_add_right_eq_sub]

/-- (2.3.5) -/
lemma Eq5 (x) : g (x * 2) = g x * 4 := by
  have h : _ + _ = _ + _ := congrArg₂ (· + ·) (hg.shift_good.Eq3 x) (hg.shift_good.Eq2 x)
  simp only [Pi.sub_apply, Pi.one_apply] at h
  rw [← add_sub_add_comm, Eq1 hg, add_add_add_comm, ← add_mul,
    add_comm (g (x - 1) - 1), mul_sub_one, sub_add_cancel, ← add_sub_add_comm,
    Eq1 hg, one_add_one_eq_two, mul_add_one (α := S), add_sub_cancel_right,
    mul_add_one (α := S), add_sub_cancel_right, hg.map_two, mul_assoc,
    ← sub_eq_zero, ← mul_sub, mul_eq_zero] at h
  exact eq_of_sub_eq_zero (h.resolve_left hg.Schar_ne_two)

end

end ShiftGood23




structure RShiftGood23 [NonAssocRing R] [NonAssocRing S] (g : R → S)
  extends RGoodCase2 (g - 1), ShiftGood23 g : Prop

namespace RShiftGood23

section

variable [NonAssocRing R] [NonAssocRing S]

lemma mk_iff {g : R → S} : RShiftGood23 g ↔ RGoodCase2 (g - 1) ∧ g 2 = 4 :=
  ⟨λ ⟨h, h0⟩ ↦ ⟨h, (ShiftGood23.mk_iff.mp h0).2⟩, λ ⟨h, h0⟩ ↦ ⟨h, h.toGoodCase2, h0⟩⟩

lemma shift_mk_iff {f : R → S} : RShiftGood23 (f + 1) ↔ RGoodCase2 f ∧ f 2 = 3 := by
  rw [mk_iff, add_sub_cancel_right, ← three_add_one_eq_four]
  exact and_congr_right' (add_left_inj _)

variable {g : R → S} (hg : RShiftGood23 g)
include hg

lemma period_imp_eq₀ (c d) (h : ∀ x, g (x + c) = g (x + d)) : c = d :=
  hg.period_imp_eq c d λ x ↦ congrArg₂ (· - ·) (h x) rfl

lemma period_imp_zero₀ {c} (h : ∀ x, g (x + c) = g x) : c = 0 :=
  hg.period_imp_eq₀ c 0 λ x ↦ by rw [h, add_zero]

end


section

variable {R : Type u} [Ring R] [Ring S] [NoZeroDivisors S] {g : R → S} (hg : RShiftGood23 g)
include hg

/-- (2.3.6) -/
lemma Eq6 {x} (h : g x = 0) : x = 0 := by
  ---- First get `g(x + 1) = g(x - 1) = 1`
  have h0 := hg.Eq3 x 1
  rw [mul_one, h, mul_zero, sq_eq_zero_iff, sub_eq_zero] at h0
  have h1 := hg.Eq1 x
  rw [h, zero_add, h0, ← two_mul, ← sub_eq_zero, ← mul_sub,
    mul_eq_zero, or_iff_right hg.Schar_ne_two, sub_eq_zero] at h1
  rw [h1] at h0
  ---- Now prove the equality `g(y - x) + 2 g(y) = 3 g(y + x)`
  have h2 (y) : g (y - x) + 2 * g y = (2 + 1) * g (y + x) := by
    have h2 : g (x + (x + 1) * (y - 1)) = g (x + 1 - y) := by
      rw [mul_sub_one, add_sub_left_comm, sub_add_cancel_left, ← sub_eq_add_neg,
        hg.toShiftGood23.alt_good, h0, sub_self, zero_mul, zero_add]
    have h3 := hg.toShiftGood23.is_good (x + 1) (x * (y - 1))
    rw [h0, sub_self, zero_mul, zero_add, ← add_rotate, ← mul_add_one x, sub_add_cancel,
      ← mul_assoc, add_one_mul x, ← mul_add_one x, mul_assoc, hg.toShiftGood23.is_good,
      h2, hg.toShiftGood23.is_good, h, zero_sub, neg_one_mul, neg_one_mul, neg_sub,
      neg_sub, sub_add, sub_add, sub_right_inj, sub_eq_iff_eq_add] at h3
    replace h2 := hg.Eq4 (x + 1) (y - 1)
    rw [h0, one_mul, mul_sub, mul_one_add (α := S), ← sub_sub, sub_left_inj,
      eq_sub_iff_add_eq, h3, mul_add, add_assoc, ← mul_add_one (α := S),
      add_add_sub_cancel, ← hg.Eq1, ← sub_add, ← add_assoc, ← add_rotate,
      add_left_inj, sub_sub, add_sub_add_right_eq_sub, ← neg_sub, mul_sub,
      hg.toShiftGood23.map_even, ← add_sub_assoc, sub_eq_iff_eq_add'] at h2
    rw [h2, add_one_mul (α := S), add_comm x]
  ---- Finish
  refine hg.period_imp_zero₀ λ y ↦ ?_
  have h3 := h2 (-y)
  rw [← neg_add', hg.toShiftGood23.map_even, hg.toShiftGood23.map_even,
    neg_add_eq_sub, ← neg_sub, hg.toShiftGood23.map_even] at h3
  replace h2 : _ - _ = _ - _ := congrArg₂ (· - ·) h3 (h2 y)
  rw [add_sub_add_right_eq_sub, ← mul_sub, ← neg_sub, neg_eq_iff_add_eq_zero,
    ← one_add_mul (α := S), mul_eq_zero, add_left_comm, one_add_one_eq_two,
    ← two_mul, mul_self_eq_zero, or_iff_right hg.Schar_ne_two, sub_eq_zero] at h2
  rwa [h2, add_one_mul (α := S), add_comm, add_left_inj, ← sub_eq_zero, ← mul_sub,
    mul_eq_zero, or_iff_right hg.Schar_ne_two, sub_eq_zero, eq_comm] at h3

/-- `R` is commutative -/
lemma Rcomm : ∀ x y : R, x * y = y * x := by
  ---- First get `(x^2 - y^2)(xy - yx) = 0` for all `x y : R`
  have X : (2 : S) ^ 4 ≠ 0 := pow_ne_zero 4 hg.Schar_ne_two
  have h (x y) : g (x * y) = g (y * x) := by
    have h := hg.Eq3 x y
    rw [add_comm, ← neg_sub y, hg.toShiftGood23.map_even, hg.Eq3,
      ← sub_eq_zero, ← mul_sub, mul_eq_zero, or_iff_right X] at h
    exact (eq_of_sub_eq_zero h).symm
  replace h (x y : R) : (x * x - y * y) * (x * y - y * x) = 0 := hg.Eq6 <| by
    have h0 := hg.Eq3 (x * x - y * y) (x * y - y * x)
    rwa [sub_add_sub_comm, ← mul_add, ← mul_add, add_comm y, ← sub_mul, h,
      sub_sub_sub_comm, ← mul_sub, ← mul_sub, ← neg_sub x, mul_neg, sub_neg_eq_add,
      add_mul, sub_self, sq, zero_mul, zero_eq_mul, or_iff_right X] at h0
  ---- Now reduce repeatedly
  have h0 (x y : R) : (x + 1) * y - y * (x + 1) = x * y - y * x := by
    rw [add_one_mul x, mul_add_one y, add_sub_add_right_eq_sub]
  replace h (x y : R) : (x * 2 + 1) * (x * y - y * x) = 0 := by
    have h1 := h (x + 1) y
    rwa [h0, add_one_mul x, mul_add_one x, add_assoc, add_sub_right_comm,
      add_mul, h, zero_add, ← add_assoc, ← mul_two] at h1
  intro x y; have h1 := h (x + 1) y
  rw [h0, add_one_mul x, add_right_comm, add_mul, h, zero_add] at h1
  specialize h x y
  rwa [add_one_mul (α := R), mul_assoc, h1, mul_zero, zero_add, sub_eq_zero] at h

/-- (2.3.7) -/
lemma Eq7 : ∀ x y, g (x * y) = g x * g y := by
  ---- First get `g(xy^2) = g(xy) g(y)` for any `x y : R`
  have h (x y) : g (x * y * y) = g (x * y) * g y := by
    suffices g (x * y + y) + g (x * y - y) = 2 * (g (x * y) + g y) by
      rw [← sub_eq_zero, ← hg.Eq4, mul_eq_zero] at this
      exact eq_of_sub_eq_zero (this.resolve_left hg.Schar_ne_two)
    have h : _ + _ = _ + _ := congrArg₂ (· + ·) (hg.Eq4 (x + 1) y) (hg.Eq4 (x - 1) y)
    rwa [← mul_add, sub_add_sub_comm, ← add_mul, sub_add_sub_comm, add_add_add_comm,
      hg.Eq1, add_right_comm x, ← add_sub_right_comm x y, hg.Eq1, add_sub_right_comm x,
      sub_right_comm, hg.Eq1, ← mul_add, ← mul_add, ← mul_sub, add_add_add_comm,
      add_add_add_comm (g _) (g y), hg.Eq1, ← sub_eq_zero, ← mul_sub, mul_eq_zero,
      or_iff_right hg.Schar_ne_two, sub_eq_zero, sub_eq_iff_eq_add, one_add_one_eq_two,
      mul_add_one (α := S), ← two_mul, add_right_comm (2 * g x), add_sub_add_right_eq_sub,
      ← mul_add, ← hg.Eq4, ← mul_add_one (α := S), mul_assoc, ← mul_add, add_one_mul (g x),
      add_comm _ (g y), sub_add_add_cancel, add_one_mul x, sub_one_mul] at h
  ---- Now get either `xy = 0` or `g(xy) = g(x) g(y)`
  replace h (x y) : x * y = 0 ∨ g (x * y) = g x * g y := by
    have h0 := h 1 (x * y)
    rw [one_mul, ← mul_assoc, hg.Rcomm _ x, ← mul_assoc, h, mul_assoc, hg.Rcomm x,
      hg.Rcomm x, h, mul_assoc, hg.Rcomm y, ← sub_eq_zero, ← mul_sub, mul_eq_zero] at h0
    exact h0.imp hg.Eq6 (λ h0 ↦ (eq_of_sub_eq_zero h0).symm)
  ---- Finally, bash again
  intro x y; refine (h x y).elim (λ h0 ↦ ?_) id
  refine (h (x + 1) y).elim (λ h1 ↦ ?_) (λ h1 ↦ ?_)
  · rw [add_one_mul x, h0, zero_add] at h1
    rw [h1, mul_zero, hg.toShiftGood23.map_zero, mul_zero]
  refine (h (x - 1) y).elim (λ h2 ↦ ?_) (λ h2 ↦ ?_)
  · rw [sub_one_mul x, h0, zero_sub, neg_eq_zero] at h2
    rw [h2, mul_zero, hg.toShiftGood23.map_zero, mul_zero]
  rw [add_one_mul x, h0, zero_add] at h1
  rw [sub_one_mul, h0, zero_sub, hg.toShiftGood23.map_even] at h2
  have h3 : _ + _ = _ + _ := congrArg₂ (· + ·) h1 h2
  rw [← two_mul, ← add_mul, hg.Eq1, mul_add_one (α := S), add_mul, self_eq_add_left,
    mul_assoc, mul_eq_zero, or_iff_right hg.Schar_ne_two] at h3
  rw [h0, hg.toShiftGood23.map_zero, h3]

/-- (2.3.8) -/
lemma Eq8 (x y) : g (x + y) + g (x - y) = 2 • (g x + g y) := by
  rw [two_nsmul, ← two_mul, ← sub_eq_zero, ← hg.Eq4, hg.Eq7, sub_self, mul_zero]


open Extra.SquareLike


theorem solution :
    ∃ (R' : Type u) (_ : CommRing R') (φ : R →+* R') (ι : SqSubring R' →+* S),
      ∀ x, g x = ι (RestrictedSq (φ x)) := by
  let hR := CommRing.mk hg.Rcomm
  refine ⟨R, hR, RingHom.id R, ?_⟩
  have hS (x y : S) (h : 2 • x = 2 • y) : x = y := by
    rwa [two_nsmul, ← two_mul, two_nsmul, ← two_mul, ← sub_eq_zero, ← mul_sub,
      mul_eq_zero, or_iff_right hg.Schar_ne_two, sub_eq_zero] at h
  let φ := BilinMap hS hg.Eq8
  let ρ := φ 1
  ---- Collect basic properties of `φ`
  have h : ∀ x, φ x x = 2 • g x := BilinMap_eq_two_nsmul _ _
  have h0 (x y) : φ x y = ρ (x * y) :=
    hS _ _ <| by rw [two_nsmul_BilinMap_eq, two_nsmul_BilinMap_eq,
      ← hg.Eq2, add_comm, ← neg_sub (x * y), hg.toShiftGood23.map_even]
  ---- Construct `ι` as an additive hom
  let R₂ := AddSubgroup.closure (Set.range λ x : R ↦ x ^ 2)
  obtain ⟨ι, h1⟩ : ∃ ι : SqSubring R →+ S, ∀ a : SqSubring R, ρ a = 2 • ι a :=
    suffices ∃ ι : SqSubring R → S, ∀ a : SqSubring R, ρ a = 2 • ι a by
      rcases this with ⟨ι, h1⟩
      have h3 (x y) : ι (x + y) = ι x + ι y := hS _ _ <| by
        rw [← h1, Subring.coe_add, ρ.map_add, h1, h1, nsmul_add]
      exact ⟨AddMonoidHom.mk' ι h3, h1⟩
    suffices ∀ r ∈ R₂, ∃ s, ρ r = 2 • s
      from Classical.axiomOfChoice λ (a : SqSubring R) ↦ this a.1 a.2
    λ r ↦ AddSubgroup.closure_induction
      (λ y ⟨x, h3⟩ ↦ ⟨g x, by rw [← h, h0 x, ← sq, ← h3]⟩)
      ⟨0, by rw [ρ.map_zero, nsmul_zero]⟩
      (λ x y _ _ ⟨s, hs⟩ ⟨t, ht⟩ ↦ ⟨s + t, by rw [ρ.map_add, hs, ht, nsmul_add]⟩)
      (λ x _ ⟨s, hs⟩ ↦ ⟨-s, by rw [ρ.map_neg, hs, nsmul_eq_mul, ← mul_neg, nsmul_eq_mul]⟩)
  ---- Reduce to multiplicativity of `ι`, then prove it
  suffices ∀ x y, ι (x * y) = ι x * ι y by
    have h2 : ι 1 = 1 := hS _ _ <| by
      rw [← h1, Subring.coe_one, h, hg.toShiftGood23.map_one]
    refine ⟨⟨⟨⟨ι, h2⟩, this⟩, ι.map_zero, ι.map_add⟩, λ x ↦ hS _ _ ?_⟩
    change 2 • g x = 2 • ι (RestrictedSq x)
    rw [← h, ← h1, RestrictedSq_coe, sq, h0]
  ---- Prove that `ι` is multiplicative
  have X (x y : S) : (2 • x) * (2 • y) = 2 • 2 • (x * y) := by
    rw [two_nsmul, two_nsmul, add_mul, mul_add, ← two_nsmul, ← two_nsmul]
  suffices ∀ a b, a ∈ R₂ → b ∈ R₂ → 2 • ρ (a * b) = ρ a * ρ b
    from λ x y ↦ hS _ _ <| hS _ _ <| by
      rw [← h1, Subring.coe_mul, this _ _ x.2 y.2, h1, h1, X]
  replace h (x) : ρ (x ^ 2) = 2 • g x := by rw [← h, sq, ← h0]
  intro a b; refine AddSubgroup.closure_induction₂ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro _ _ ⟨c, rfl⟩ ⟨d, rfl⟩; rw [← mul_pow, h, h, h, X, hg.Eq7]
  · rintro x -; rw [zero_mul, ρ.map_zero, zero_mul, nsmul_zero]
  · rintro x -; rw [mul_zero, ρ.map_zero, mul_zero, nsmul_zero]
  · rintro x₁ x₂ y - - - hx₁ hx₂
    rw [add_mul, ρ.map_add, nsmul_add, hx₁, hx₂, ρ.map_add, add_mul]
  · rintro x y₁ y₂ - - - hy₁ hy₂
    rw [mul_add, ρ.map_add, nsmul_add, hy₁, hy₂, ρ.map_add, mul_add]
  · rintro x y - - h2; rw [neg_mul, ρ.map_neg, ρ.map_neg, neg_mul, ← h2]
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_neg]
  · rintro x y - - h2; rw [mul_neg, ρ.map_neg, ρ.map_neg, mul_neg, ← h2]
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_neg]

end

end RShiftGood23





/-! ### Summary -/

section

variable {R : Type u} [Ring R] [Ring S] [NoZeroDivisors S] {f : R → S}

theorem RGoodSubcase23.solution (hf : RGoodCase2 f) (h : f 2 = 3) :
    ∃ (R' : Type u) (_ : CommRing R') (φ : R →+* R') (ι : SqSubring R' →+* S),
      ∀ x, f x = ι (RestrictedSq (φ x) - 1) := by
  rcases (RShiftGood23.shift_mk_iff.mpr ⟨hf, h⟩).solution with ⟨R', _, φ, ι, h0⟩
  refine ⟨R', _, φ, ι, λ x ↦ ?_⟩
  rw [ι.map_sub, ← h0, ι.map_one]
  exact (add_sub_cancel_right _ _).symm

theorem RGoodCase2.solution (hf : RGoodCase2 f) :
    (∃ (R' : Type u) (_ : CommRing R') (φ : R →+* R') (ι : SqSubring R' →+* S),
      ∀ x, f x = ι (RestrictedSq (φ x) - 1)) ∨
    (∃ φ : R →+* ℤ₄, ∀ x, f x = ℤ₄Map (φ x)) ∨
    (∃ φ : R →+* 𝔽₃, ∀ x, f x = 𝔽₃Map2 (φ x)) :=
  (em (f 2 = 3)).imp (RGoodSubcase23.solution hf) λ h ↦
    hf.toGoodCase2.map_two_cases.imp (RGoodSubcase21.solution hf) λ h0 ↦
      have h0 := h0.resolve_right h
      RGoodSubcase22.solution hf h0 (h0.symm.trans_ne h).symm

/-- Refer to Case 3 if `f(2) = -1` -/
theorem CharTwo'_of_map_two (hf : ReducedGood f)
    (h : f (-1) = 0) (h0 : f 2 = -1) : (2 : R) = 0 := by
  refine hf.period_imp_zero λ x ↦ ?_
  rcases CommSubring.oneVarCommLiftDomain_exists hf.toNontrivialGood x with
    ⟨R', R'comm, φ, -, ⟨x, rfl⟩, S', S'comm, S'nzd, ρ, hρ, f', h1, hf'⟩
  rw [← map_ofNat φ 2, ← φ.map_add, h1, h1, CommCase.two_periodic_of_map_two hf']
  · refine map_even_of_map_one hf'.is_good (hρ ?_)
    rw [← h1, φ.map_neg, φ.map_one, h, ρ.map_zero]
  · apply hρ; rw [← h1, map_ofNat, h0, ρ.map_neg, ρ.map_one]

theorem solution (hf : ReducedGood f) (h : f (-1) = 0) (h0 : f 2 ≠ -1) :
    (∃ (R' : Type u) (_ : CommRing R') (φ : R →+* R') (ι : SqSubring R' →+* S),
      ∀ x, f x = ι (RestrictedSq (φ x) - 1)) ∨
    (∃ φ : R →+* ℤ₄, ∀ x, f x = ℤ₄Map (φ x)) ∨
    (∃ φ : R →+* 𝔽₃, ∀ x, f x = 𝔽₃Map2 (φ x)) :=
  RGoodCase2.solution ⟨hf, map_even_of_map_one hf.is_good h, h0⟩
