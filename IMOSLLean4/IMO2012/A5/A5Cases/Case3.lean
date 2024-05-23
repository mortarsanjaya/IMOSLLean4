/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.A5Answers.SubOneMap
import IMOSLLean4.IMO2012.A5.A5Answers.F2Map
import IMOSLLean4.IMO2012.A5.A5Answers.F2eMap
import IMOSLLean4.IMO2012.A5.A5Answers.F4Map
import IMOSLLean4.IMO2012.A5.A5General.A5CommLift
import IMOSLLean4.IMO2012.A5.A5General.A5QuasiPeriodic
import IMOSLLean4.Extra.CharTwo.Ring.Lemmas
import IMOSLLean4.Extra.CharTwo.Hom
import Mathlib.Algebra.Ring.Equiv

/-!
# IMO 2012 A5 (Case 3: `char(R) ∣ 2`)

We solve the case where `f` is reduced good and `char(R) ∣ 2`.
-/

namespace IMOSL
namespace IMO2012A5
namespace Case3

open Extra Extra.CharTwo
/-
/-! ### Classification of elements of `R` with respect to `f` -/

section

variable [AddMonoidWithOne R] [NonAssocRing S] (f : R → S) (x : R)

structure 𝔽₂_zero : Prop where
  map_self : f x = -1
  map_add_one : f (x + 1) = 0

structure 𝔽₄_prim : Prop where
  add : f x + f (x + 1) = 1
  mul : f x * f (x + 1) = -1

lemma 𝔽₄_prim.map_mul_self_eq {f : R → S} {x : R} (h : 𝔽₄_prim f x) :
    f x * f x = f x + 1 := by
  rw [← add_neg_eq_iff_eq_add, ← eq_sub_iff_add_eq',
    ← mul_one_sub, ← h.mul, ← h.add, add_sub_cancel_left]

end
-/





/-! ### General lemmas -/

section

variable [Semiring R] [CharTwo R] [Ring S] [NoZeroDivisors S]
   {f : R → S} (hf : NontrivialGood f)

/-- (3.1) -/
lemma Eq1 (x) : f (x * (x + 1) + 1) = f x * f (x + 1) := by
  rw [hf.is_good, add_add_cancel_left, hf.map_one, add_zero]

/-- (3.2) -/
lemma Eq2 (x) : f (x * x + 1) = f x ^ 2 - 1 := by
  rw [sq, hf.is_good, add_self_eq_zero, hf.map_zero, sub_eq_add_neg]

lemma Eq2_v2 (x) : f (x * x) = f (x + 1) ^ 2 - 1 := by
  rw [← Eq2 hf, add_one_mul_self, add_add_cancel_right]

/-- (3.3) -/
lemma Eq3 (x) : f x * f (x * x + x) =
    (f (x + 1) ^ 2 - 1) * (f (x + 1) - 1) + f x * f (x + 1) := by
  have h : x * (x + 1) = x * x + x := mul_add_one x x
  rw [← Eq2_v2 hf, ← Eq1 hf, mul_sub_one, ← add_sub_right_comm, h, add_assoc,
    ← hf.is_good, mul_assoc, hf.is_good, h, add_add_cancel_middle₁, add_sub_cancel_right]

lemma Eq3_v2 (x) : f (x + 1) * f (x * x + x) =
    (f x ^ 2 - 1) * (f x - 1) + f (x + 1) * f x := by
  have h := Eq3 hf (x + 1)
  rwa [add_add_cancel_right, add_one_mul_self, add_add_add_cancel_right] at h

end





/-! ### Lemmas in commutative case -/

namespace CommCase

variable [CommSemiring R] [CharTwo R] [CommRing S] [NoZeroDivisors S]
  {f : R → S} (hf : NontrivialGood f)

/-- Big ring identity 1 used in `Thm1` -/
lemma Thm1_ring_id1 (a b : S) :
    a * ((a ^ 2 - 1) * (a - 1) + b * a) - b * ((b ^ 2 - 1) * (b - 1) + a * b)
      = (a ^ 2 + b ^ 2 - 1) * (a + b - 1) * (a - b) := by ring

/-- Big ring identity 2 used in `Thm1` -/
lemma Thm1_ring_id2 (a : S) :
    a ^ 2 * ((a ^ 2 - 1) ^ 2 + 1) - ((a ^ 2 - 1) * (a - 1) + a * a) ^ 2
      = (1 - 2 * a) * (a ^ 2 - 1) := by ring

/-- (3.4) -/
theorem Thm1 (x) : f x ^ 2 + f (x + 1) ^ 2 = 1 ∨ f x + f (x + 1) = 1 := by
  ---- Step 1: Either the above holds or `f(x) = f(x + 1)`, then assume the latter
  have h := Thm1_ring_id1 (f x) (f (x + 1))
  rw [← Eq3 hf, ← Eq3_v2 hf, mul_left_comm, sub_self, zero_eq_mul,
    mul_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero] at h
  cases h with | inl h => exact h | inr h => ?_
  right; save
  ---- Step 2: Prove either `2 f(x) = 1` or `f(x)^2 - 1 = 0`, then assume the latter
  rw [← h, ← two_mul]
  have h0 : _ ^ 2 = _ ^ 2 := congrArg (λ x ↦ x ^ 2) (Eq3 hf x)
  rw [mul_pow, ← add_eq_of_eq_sub (Eq2 hf (x * x + x)), ← h, add_mul_self,
    ← mul_add_one (x * x), Eq1 hf, Eq2 hf, Eq2_v2 hf, ← h,
    ← sub_eq_zero, ← sq, Thm1_ring_id2, mul_eq_zero] at h0
  cases h0 with | inl h0 => exact (eq_of_sub_eq_zero h0).symm | inr h0 => ?_
  save
  ---- Step 3: Resolve the case `f(x)^2 - 1 = 0`
  have h1 : f (x * x) = 0 := by rw [Eq2_v2 hf, ← h, h0]
  replace h := Eq3_v2 hf (x * x)
  rw [h1, mul_zero, add_zero, sq, zero_mul, zero_sub,
    neg_mul_neg, one_mul, Eq2 hf, h0, zero_mul] at h
  rw [← mul_one (2 * f x), ← h, mul_zero]
  save

/-- Main theorem 1: We are (almost!) done if `char(S) ∣ 2` -/
theorem SCharTwo_map_add_one [CharTwo S] (x) : f (x + 1) = f x + 1 := by
  have h := Thm1 hf x
  rwa [← CharTwo.add_sq, CharTwo.sq_eq_one_iff, or_self, add_eq_iff_eq_add''] at h

lemma pow_four_Eq1 (x) : f ((x ^ 2) ^ 2) = (f x ^ 2 - 1) ^ 2 - 1 := by
  rw [← add_add_cancel_right (x ^ 2) 1, add_one_sq, sq, sq, Eq2 hf, Eq2 hf]

lemma pow_four_Eq2 (x) : f ((x ^ 2) ^ 2 + 1) = (f (x + 1) ^ 2 - 1) ^ 2 - 1 := by
  rw [← pow_four_Eq1 hf, add_one_sq, add_one_sq]

/-- Big ring identity used in `SCharNeTwo_main` -/
lemma SCharNeTwo_main_ring_id (a b : S) :
    ((a - 1) ^ 2 - 1) * ((b - 1) ^ 2 - 1) - ((a * b - 1) ^ 2 - 1)
      = 2 * ((a * b) * ((2 + 1) - (a + b))) := by ring

/-- Main theorem 2: Case division when `char(S) ∤ 2` -/
theorem SCharNeTwo_cases (h : (2 : S) ≠ 0) (x) :
    (f x = 0 ∨ f (x + 1) = 0) ∨ (f x + f (x + 1) = 1 ∧ f x * f (x + 1) = -1) := by
  ---- Step 1: `f(x) f(x + 1) = 0` or `f(x)^2 + f(x + 1)^2 = 3`
  have h0 := pow_four_Eq2 hf (x * (x + 1))
  rw [Eq1 hf, mul_pow, mul_pow, add_one_sq, add_one_sq, Eq1 hf, pow_four_Eq1 hf,
    pow_four_Eq2 hf, ← sub_eq_zero, mul_pow, SCharNeTwo_main_ring_id, mul_eq_zero,
    or_iff_right h, mul_eq_zero, ← mul_pow, sq_eq_zero_iff] at h0
  revert h0; refine Or.imp mul_eq_zero.mp λ h0 ↦ ?_
  rw [sub_eq_zero, eq_comm] at h0
  ---- Step 2: If `f(x)^2 + f(x + 1)^2 = 3`, then `x` is 𝔽₄-primitive.
  refine (Thm1 hf x).elim (λ h1 ↦ Not.elim h ?_) (λ h1 ↦ ⟨h1, ?_⟩)
  · rwa [h0, add_left_eq_self] at h1
  apply congrArg (λ y ↦ y ^ 2) at h1
  rw [one_pow, add_sq', h0, add_right_comm, add_left_eq_self,
     mul_assoc, ← mul_one_add (2 : S), mul_eq_zero] at h1
  exact eq_neg_of_add_eq_zero_right (h1.resolve_left h)

end CommCase





/-! ### Transferring results from commutative case -/

variable [Ring R] [CharTwo R] [Ring S] [NoZeroDivisors S]

/-- Solution for `char(S) ∣ 2` -/
theorem SCharTwo.solution [CharTwo S] {f : R → S} (hf : NontrivialGood f) :
    ∃ φ : R →+* S, ∀ x, f x = φ (x - 1) :=
  sub_one_solver hf λ x ↦ by
    rcases CommSubring.oneVarCommLiftDomain_exists hf x with
      ⟨R', R'comm, φ, hφ, ⟨x, rfl⟩, S', S'comm, S'nzd, ρ, hρ, f', h, hf'⟩
    have R'char := pullback_of_inj φ.toAddMonoidHom hφ
    have S'char := pullback_of_inj ρ.toAddMonoidHom hρ
    rw [h, ← φ.map_one, ← φ.map_add, h, ← ρ.map_one, ← ρ.map_add]
    exact ρ.congr_arg (CommCase.SCharTwo_map_add_one hf' x)


namespace SCharNeTwo

section

variable (hS : (2 : S) ≠ 0) {f : R → S} (hf : NontrivialGood f)

/-- (3.5) -/
lemma main_cases (x) :
    (f x = 0 ∨ f (x + 1) = 0) ∨ (f x + f (x + 1) = 1 ∧ f x * f (x + 1) = -1) := by
  rcases CommSubring.oneVarCommLiftDomain_exists hf x with
    ⟨R', R'comm, φ, hφ, ⟨x, rfl⟩, S', S'comm, S'nzd, ρ, -, f', h, hf'⟩
  have R'char := pullback_of_inj φ.toAddMonoidHom hφ
  have S'char : (2 : S') ≠ 0 := λ h1 ↦ hS <| by rw [← map_ofNat ρ 2, h1, ρ.map_zero]
  rw [h, ← φ.map_one, ← φ.map_add, h, ← ρ.map_zero]
  refine (CommCase.SCharNeTwo_cases hf' S'char x).imp
    (Or.imp ρ.congr_arg ρ.congr_arg) (And.imp (λ h0 ↦ ?_) (λ h0 ↦ ?_))
  · rw [← ρ.map_add, h0, ρ.map_one]
  · rw [← ρ.map_mul, h0, ρ.map_neg, ρ.map_one]

lemma map_add_one_eq_zero_iff_map_eq {x} : f (x + 1) = 0 ↔ f x ^ 2 = 1 := by
  refine ⟨λ h0 ↦ ?_, λ h0 ↦ ?_⟩
  · have h1 := Eq3_v2 hf x
    rw [h0, zero_mul, zero_mul, add_zero, zero_eq_mul] at h1
    exact h1.elim eq_of_sub_eq_zero λ h1 ↦ eq_of_sub_eq_zero h1 ▸ one_pow 2
  · rcases main_cases hS hf x with (h1 | h1) | ⟨h1, h2⟩
    · rw [h1, sq, zero_mul] at h0
      rw [← mul_one (f _), ← h0, mul_zero]
    · exact h1
    · apply congrArg (f x * ·) at h2
      rw [← mul_assoc, ← sq, h0, one_mul, mul_neg_one] at h2
      rw [h2, add_neg_self] at h1
      rw [← mul_one (f _), ← h1, mul_zero]

lemma map_eq_neg_one_imp_map_add_one {x} (h : f x = -1) : f (x + 1) = 0 :=
  (map_add_one_eq_zero_iff_map_eq hS hf).mpr (h ▸ neg_one_sq)





/-! ### Reduction lemmas for 𝔽₂-zeroes -/

namespace ReductionLemmas

variable (h : f r = -1)

lemma Lem1 : f (r * r) = -1 := by
  rw [Eq2_v2 hf, map_eq_neg_one_imp_map_add_one hS hf h, sq, zero_mul, zero_sub]

lemma Lem2 : f (r * r + r) = -1 := by
  have h0 := Eq3 hf r
  rwa [map_eq_neg_one_imp_map_add_one hS hf h, mul_zero, add_zero,
    sq, mul_zero, zero_sub, mul_neg_one, h, neg_one_mul, neg_inj] at h0

lemma Lem3 (x) : f (r * x + 1) = f (r + x) - f x := by
  rw [hf.is_good, h, neg_one_mul, neg_add_eq_sub]

lemma Lem4 {x} (h0 : ∃ y, x = r * y + 1) : f (r * r + x) = -f x := by
  rcases h0 with ⟨x, rfl⟩
  rw [Lem3 hf h, ← add_assoc, ← mul_add, Lem3 hf h, add_add_cancel_left, neg_sub]

lemma Lem5 {x} (h0 : ∃ y, x = r * r * y + 1) :
    f ((r * r + r) * (r * r + r) + x) = f x := by
  rcases h0 with ⟨x, rfl⟩
  have h1 : Commute (r * r) r := mul_assoc r r r
  rw [add_mul_self_of_Commute h1, add_assoc, Lem4 hf (Lem1 hS hf h), Lem4 hf h, neg_neg]
  exacts [⟨r * x, by rw [mul_assoc]⟩, ⟨1 + x, by rw [← add_assoc, mul_one_add (r * r)]⟩]

lemma Lem6 : QuasiPeriodic f (r * r * (r + 1)) :=
  (QuasiPeriodic.iff_left2 hf).mpr λ x ↦ by
    ---- `f(r^4 + r^2 + r^2 (r + 1) x + 1) = f(r^2 (r + 1) x + 1)`
    have h0 : ∃ y, r * r * (r + 1) * x + 1 = r * r * y + 1 :=
      ⟨(r + 1) * x, by rw [← mul_assoc]⟩
    apply Lem5 hS hf h at h0
    ---- `f(r^4 + r^2 + r^2 (r + 1) x + 1) = -f(r^2 (r + 1) x + 1)`
    have h1 : ∃ y, r * r * (r + 1) * x + 1 = (r * r + r) * y + 1 :=
      ⟨r * x, by rw [← mul_assoc, add_mul, mul_add_one (r * r)]⟩
    apply Lem4 hf (Lem2 hS hf h) at h1
    ---- Finish
    rw [h1, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero] at h0
    exact h0.resolve_left hS

end ReductionLemmas

end






/-! ### Rest of the solution -/

variable (hS : (2 : S) ≠ 0) {f : R → S} (hf : ReducedGood f)

theorem map_neg_one_reduced_imp (h : f r = -1) : r = 0 := by
  let hf' := hf.toNontrivialGood
  ---- First show that `r^4 + r^2 = 0`
  have h0 : (r * r + r) * (r * r + r) = 0 := by
    refine (QuasiPeriodic.reduced_eq_zero_iff hf ?_).mpr
      (ReductionLemmas.Lem1 hS hf' (ReductionLemmas.Lem2 hS hf' h))
    have h0 : Commute (r * r) r := mul_assoc r r r
    rw [add_mul_self_of_Commute h0, ← mul_add_one (r * r), ← add_one_mul_self, ← mul_assoc]
    exact (ReductionLemmas.Lem6 hS hf' h).mul_right hf' (r + 1)
  ---- Next show that `r^2 + r = 0`
  replace h0 : r * r + r = 0 := by
    refine (QuasiPeriodic.reduced_eq_zero_iff hf <|
      (QuasiPeriodic.iff_left2 hf').mpr λ x ↦ ?_).mpr (ReductionLemmas.Lem2 hS hf' h)
    have h1 := ReductionLemmas.Lem4 hf' (ReductionLemmas.Lem2 hS hf' h) ⟨x, rfl⟩
    rw [h0, zero_add, eq_neg_iff_add_eq_zero, ← two_mul, mul_eq_zero] at h1
    exact h1.resolve_left hS
  ---- Now go for the final goal
  refine (QuasiPeriodic.reduced_eq_zero_iff hf <|
    (QuasiPeriodic.iff_left2 hf').mpr λ x ↦ ?_).mpr h
  have h1 := hf.is_good (r + 1) (r * (x - 1))
  rwa [map_eq_neg_one_imp_map_add_one hS hf' h, zero_mul, zero_add,
    ← mul_assoc, add_one_mul r, h0, zero_mul, zero_add, hf.map_one,
    ← add_rotate, ← mul_add_one r, sub_add_cancel, eq_comm] at h1

lemma map_add_one_eq_zero_imp (h : f (x + 1) = 0) : x * x = 0 :=
  map_neg_one_reduced_imp hS hf <| by
    rw [Eq2_v2 hf.toNontrivialGood, h, sq, zero_mul, zero_sub]

/- ... -/

theorem solution :
    (∃ φ : R →+* 𝔽₂, ∀ x, f x = 𝔽₂Map (φ x)) ∨
    (∃ φ : R →+* 𝔽₂ε, ∀ x, f x = 𝔽₂εMap (φ x)) ∨
    (∃ (φ : R →+* 𝔽₄) (ι : ℤφ →+* S), ∀ x, f x = ι (𝔽₄Map (φ x))) := by
  have hS := hS
  have hf := hf
  ---- Remove the above once the proof is complete
  sorry

end SCharNeTwo





/-! ### Summary -/

theorem solution {f : R → S} (hf : ReducedGood f) :
    (∃ φ : R →+* S, ∀ x, f x = φ (x - 1)) ∨
    (∃ φ : R →+* 𝔽₂, ∀ x, f x = 𝔽₂Map (φ x)) ∨
    (∃ φ : R →+* 𝔽₂ε, ∀ x, f x = 𝔽₂εMap (φ x)) ∨
    (∃ (φ : R →+* 𝔽₄) (ι : ℤφ →+* S), ∀ x, f x = ι (𝔽₄Map (φ x))) :=
  (em ((2 : S) = 0)).imp
    (λ h ↦ haveI : CharTwo S := CharTwo.Semiring_of_two_eq_zero h
           SCharTwo.solution hf.toNontrivialGood)
    (λ h ↦ SCharNeTwo.solution h hf)
