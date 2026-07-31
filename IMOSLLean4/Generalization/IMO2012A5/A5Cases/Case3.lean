/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.SubOneMap
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.F2Map
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.F2eMap
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.F4Map
public import IMOSLLean4.Generalization.IMO2012A5.A5General.A5CommLift
public import IMOSLLean4.Generalization.IMO2012A5.A5General.A5QuasiPeriodic
public import IMOSLLean4.Extra.CharTwo.Ring
public import IMOSLLean4.Extra.CharTwo.Hom
public import Mathlib.Algebra.Ring.Equiv

/-!
# IMO 2012 A5 (Case 3: `char(R) ∣ 2`)

We solve the case where `f` is reduced good and `char(R) ∣ 2`.

TODO: Optimize/clean up the proofs if possible, starting from `R_elts_claim1`.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization
namespace Case3

open Extra Extra.CharTwo

/-! ### General lemmas -/

section

variable [Semiring R] [CharTwo R] [Ring S] {f : R → S} (hf : NontrivialGood f)
include hf

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

variable [CommSemiring R] [CharTwo R] [CommRing S]

/-- Big ring identity 1 used in `Thm1` -/
lemma Thm1_ring_id1 (a b : S) :
    a * ((a ^ 2 - 1) * (a - 1) + b * a) - b * ((b ^ 2 - 1) * (b - 1) + a * b)
      = (a ^ 2 + b ^ 2 - 1) * (a + b - 1) * (a - b) := by ring

/-- Big ring identity 2 used in `Thm1` -/
lemma Thm1_ring_id2 (a : S) :
    a ^ 2 * ((a ^ 2 - 1) ^ 2 + 1) - ((a ^ 2 - 1) * (a - 1) + a * a) ^ 2
      = (1 - 2 * a) * (a ^ 2 - 1) := by ring

variable [NoZeroDivisors S] {f : R → S} (hf : NontrivialGood f)
include hf

/-- (3.4) -/
theorem Thm1 (x) : f x ^ 2 + f (x + 1) ^ 2 = 1 ∨ f x + f (x + 1) = 1 := by
  ---- Step 1: Either the above holds or `f(x) = f(x + 1)`, then assume the latter
  have h := Thm1_ring_id1 (f x) (f (x + 1))
  rw [← Eq3 hf, ← Eq3_v2 hf, mul_left_comm, sub_self, zero_eq_mul,
    mul_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero] at h
  cases h with | inl h => exact h | inr h => ?_
  right
  ---- Step 2: Prove either `2 f(x) = 1` or `f(x)^2 - 1 = 0`, then assume the latter
  rw [← h, ← two_mul]
  have h0 : _ ^ 2 = _ ^ 2 := congrArg (λ x ↦ x ^ 2) (Eq3 hf x)
  rw [mul_pow, ← add_eq_of_eq_sub (Eq2 hf (x * x + x)), ← h, add_mul_self,
    ← mul_add_one (x * x), Eq1 hf, Eq2 hf, Eq2_v2 hf, ← h,
    ← sub_eq_zero, ← sq, Thm1_ring_id2, mul_eq_zero] at h0
  cases h0 with | inl h0 => exact (eq_of_sub_eq_zero h0).symm | inr h0 => ?_
  ---- Step 3: Resolve the case `f(x)^2 - 1 = 0`
  have h1 : f (x * x) = 0 := by rw [Eq2_v2 hf, ← h, h0]
  replace h := Eq3_v2 hf (x * x)
  rw [h1, mul_zero, add_zero, sq, zero_mul, zero_sub,
    neg_mul_neg, one_mul, Eq2 hf, h0, zero_mul] at h
  rw [← mul_one (2 * f x), ← h, mul_zero]

/-- Main theorem 1: We are (almost!) done if `char(S) ∣ 2` -/
theorem SCharTwo_map_add_one [CharTwo S] (x) : f (x + 1) = f x + 1 := by
  have h := Thm1 hf x
  rwa [← CharTwo.add_sq, CharTwo.sq_eq_one_iff, or_self, add_eq_iff_eq_add''] at h

omit [NoZeroDivisors S] in
lemma pow_four_Eq1 (x) : f ((x ^ 2) ^ 2) = (f x ^ 2 - 1) ^ 2 - 1 := by
  rw [← add_add_cancel_right (x ^ 2) 1, add_one_sq, sq, sq, Eq2 hf, Eq2 hf]

omit [NoZeroDivisors S] in
lemma pow_four_Eq2 (x) : f ((x ^ 2) ^ 2 + 1) = (f (x + 1) ^ 2 - 1) ^ 2 - 1 := by
  rw [← pow_four_Eq1 hf, add_one_sq, add_one_sq]

omit [CommSemiring R] [CharTwo R] hf [NoZeroDivisors S] in
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
  · rwa [h0, add_eq_right] at h1
  apply congrArg (λ y ↦ y ^ 2) at h1
  rw [one_pow, add_sq', h0, add_right_comm, add_eq_right,
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
include hS hf

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
    refine h1.elim eq_of_sub_eq_zero λ h1 ↦ ?_
    rw [eq_of_sub_eq_zero h1, one_pow]
  · rcases main_cases hS hf x with (h1 | h1) | ⟨h1, h2⟩
    · rw [h1, sq, zero_mul] at h0
      rw [← mul_one (f _), ← h0, mul_zero]
    · exact h1
    · apply congrArg (f x * ·) at h2
      rw [← mul_assoc, ← sq, h0, one_mul, mul_neg_one] at h2
      rw [h2, add_neg_cancel] at h1
      rw [← mul_one (f _), ← h1, mul_zero]

lemma map_eq_neg_one_imp_map_add_one {x} (h : f x = -1) : f (x + 1) = 0 :=
  (map_add_one_eq_zero_iff_map_eq hS hf).mpr (h ▸ neg_one_sq)





/-! ### Reduction lemmas for 𝔽₂-zeroes -/

namespace ReductionLemmas

variable (h : f r = -1)
include h

lemma Lem1 : f (r * r) = -1 := by
  rw [Eq2_v2 hf, map_eq_neg_one_imp_map_add_one hS hf h, sq, zero_mul, zero_sub]

lemma Lem2 : f (r * r + r) = -1 := by
  have h0 := Eq3 hf r
  rwa [map_eq_neg_one_imp_map_add_one hS hf h, mul_zero, add_zero,
    sq, mul_zero, zero_sub, mul_neg_one, h, neg_one_mul, neg_inj] at h0

omit [CharTwo R] [NoZeroDivisors S] hS in
lemma Lem3 (x) : f (r * x + 1) = f (r + x) - f x := by
  rw [hf.is_good, h, neg_one_mul, neg_add_eq_sub]

 omit [NoZeroDivisors S] hS in
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






/-! ### Characterization of elements of `R` -/

variable (hS : (2 : S) ≠ 0) {f : R → S} (hf : ReducedGood f)
include hS hf

theorem map_eq_neg_one_reduced_imp (h : f r = -1) : r = 0 := by
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
  map_eq_neg_one_reduced_imp hS hf <| by
    rw [Eq2_v2 hf.toNontrivialGood, h, sq, zero_mul, zero_sub]

theorem reduced_eq_zero_iff : r = 0 ↔ f r = -1 :=
  ⟨λ h ↦ h ▸ hf.map_zero, map_eq_neg_one_reduced_imp hS hf⟩

theorem reduced_𝔽₂ε_iff : r * r = 0 ↔ f (r + 1) = 0 := by
  rw [reduced_eq_zero_iff hS hf, Eq2_v2 hf.toNontrivialGood,
    sub_eq_neg_self, sq_eq_zero_iff]

theorem reduced_𝔽₄_iff :
    r * (r + 1) + 1 = 0 ↔ (f r + f (r + 1) = 1 ∧ f r * f (r + 1) = -1) := by
  rw [reduced_eq_zero_iff hS hf, Eq1 hf.toNontrivialGood, iff_and_self]
  intro h; refine (main_cases hS hf.toNontrivialGood r).elim (λ h0 ↦ ?_) And.left
  rw [← mul_eq_zero, h, neg_eq_zero] at h0
  rw [← mul_one (_ + _), h0, mul_zero]

theorem R_elts_cases (r : R) :
    ((r + 1) * (r + 1) = 0 ∨ r * r = 0) ∨ r * (r + 1) + 1 = 0 := by
  rw [reduced_𝔽₂ε_iff hS hf, reduced_𝔽₂ε_iff hS hf,
    reduced_𝔽₄_iff hS hf, add_add_cancel_right]
  exact main_cases hS hf.toNontrivialGood r

theorem R_elts_claim1 {r s : R} (hr : r * r = 0) (hs : s * s = 0) :
    r = 0 ∨ s = 0 ∨ r = s := by
  ---- First show that `(rs)^2 = 0`
  have h : (r * s) * (r * s) = 0 := by
    have h : (r + s) * (r + s) = r * s + s * r := by
      rw [add_mul, mul_add, hr, zero_add, mul_add, hs, add_zero]
    rcases R_elts_cases hS hf (r + s) with (h0 | h0) | h0
    · rw [add_one_mul_self, h, add_eq_zero_iff_eq] at h0
      have h1 : (r * s) * (r * s) = r * s := by
        apply congrArg (λ x ↦ r * x * s) at h0
        rwa [mul_add, ← mul_assoc, hr, zero_mul, zero_add,
          mul_one, mul_assoc, mul_assoc, ← mul_assoc] at h0
      rcases R_elts_cases hS hf (r * s) with (h2 | h2) | h2
      · rw [add_one_mul_self, h1, add_eq_zero_iff_eq] at h2
        rw [h2, add_eq_left] at h0
        apply congrArg (r * ·) at h0
        rw [mul_zero, ← mul_assoc, h2, one_mul] at h0
        rw [h0, zero_mul, zero_mul]
      · exact h2
      · rw [mul_add_one (r * s), h1, add_self_eq_zero, zero_add] at h2
        rw [← mul_one (r * s * _), h2, mul_zero]
    · rw [h, add_eq_zero_iff_eq] at h0
      rw [← mul_assoc, mul_assoc r, ← h0, mul_assoc, mul_assoc, hs, mul_zero, mul_zero]
    · rw [mul_add_one (r + s), h] at h0
      replace h : r * _ = r * 0 := congrArg (r * ·) h0
      rw [mul_zero, mul_add_one r, mul_add, mul_add, ← mul_assoc,
        mul_add, hr, zero_mul, zero_add, zero_add, ← mul_assoc] at h
      have h1 : _ * r = 0 * r := congrArg (· * r) h
      rw [zero_mul, add_mul, add_mul, mul_assoc, hr, add_zero, mul_zero, zero_add] at h1
      rw [h1, zero_add, add_eq_zero_iff_eq] at h
      rw [h, hr]
  ---- Now plug in back to the functional equation
  rw [reduced_𝔽₂ε_iff hS hf, hf.is_good] at h
  rw [reduced_𝔽₂ε_iff hS hf, map_add_one_eq_zero_iff_map_eq hS hf.toNontrivialGood,
    _root_.sq_eq_one_iff, or_comm] at hr hs
  have h0 {x} : f x = -1 → x = 0 := map_eq_neg_one_reduced_imp hS hf
  revert hr; refine Or.imp h0 λ hr ↦ ?_
  revert hs; refine Or.imp h0 λ hs ↦ ?_
  rw [hr, hs, mul_one, ← neg_eq_iff_add_eq_zero, eq_comm] at h
  exact add_eq_zero_iff_eq.mp (h0 h)

theorem R_elts_claim2 {r s : R} (hr : r * r = 0) (hs : s * (s + 1) + 1 = 0) : r = 0 := by
  rcases R_elts_cases hS hf (r + s) with (h | h) | h
  ---- Case 1: `(r + s + 1)^2 = 0`
  · rcases R_elts_claim1 hS hf hr h with hr | h | h0
    · exact hr
    · rw [add_assoc, add_eq_zero_iff_eq] at h
      rw [h, add_one_mul s, add_eq_zero_iff_eq] at hr
      rw [hr, add_add_cancel_right] at hs
      rwa [← h, hs, zero_mul, eq_comm] at hr
    · rw [add_assoc, left_eq_add] at h0
      rw [h0, mul_zero, zero_add] at hs
      rw [← mul_one r, hs, mul_zero]
  ---- Case 2: `(r + s)^2 = 0`
  · rcases R_elts_claim1 hS hf hr h with hr | h | h0
    · exact hr
    · rw [← add_eq_zero_iff_eq.mp h, mul_add_one r, hr, zero_add] at hs
      rw [add_eq_zero_iff_eq.mp hs, mul_one] at hr
      rwa [hr, add_zero] at hs
    · rw [left_eq_add] at h0
      rw [h0, zero_mul, zero_add] at hs
      rw [← mul_one r, hs, mul_zero]
  ---- Case 3: `(r + s)^2 = (r + s) + 1`
  · rw [add_assoc, mul_add, add_mul, hr, zero_add,
      add_mul, ← add_assoc, add_assoc, hs, add_zero] at h
    have h0 : r * _ * s = r * 0 * s := congrArg (r * · * s) h
    rw [mul_zero, zero_mul, mul_add, ← mul_assoc,
      ← mul_assoc, hr, zero_mul, add_zero, mul_assoc] at h0
    rcases R_elts_claim1 hS hf hr h0 with hr | h0 | h0
    · exact hr
    · apply congrArg (· * (s + 1)) at h0
      rwa [zero_mul, mul_assoc, add_eq_zero_iff_eq.mp hs, mul_one] at h0
    · apply congrArg (r * ·) at hs
      rwa [mul_zero, mul_add_one r, ← mul_assoc, ← h0,
        mul_add_one r, ← h0, add_add_cancel_right] at hs

omit [NoZeroDivisors S] in
theorem 𝔽₂_solution (hR : ∀ r : R, r = 0 ∨ r = 1) :
    ∃ φ : R →+* 𝔽₂, ∀ x, f x = 𝔽₂Map (φ x) :=
  have h : (𝔽₂.cast : 𝔽₂ → R).Bijective :=
    ⟨𝔽₂.castRingHom_injective λ h ↦ hS <| by
      apply congrArg f at h; rw [hf.map_one, hf.map_zero, zero_eq_neg] at h
      rw [← mul_one 2, h, mul_zero],
    λ x ↦ (hR x).elim (λ h ↦ ⟨𝔽₂.O, h.symm⟩) (λ h ↦ ⟨𝔽₂.I, h.symm⟩)⟩
  have h0 : ∀ x, f (𝔽₂.cast x) = 𝔽₂Map x
    | 𝔽₂.O => by
        change f 0 = ((-1 : ℤ) : S)
        rw [hf.map_zero, Int.cast_neg, Int.cast_one]
    | 𝔽₂.I => (hf.map_one).trans Int.cast_zero.symm
  let ρ := RingEquiv.ofBijective 𝔽₂.castRingHom h
  ⟨ρ.symm, λ x ↦ h0 _ ▸ congrArg f (Equiv.apply_symm_apply ρ.toEquiv _).symm⟩

theorem 𝔽₂ε_solution {r : R} (hr : r ≠ 0) (hr0 : r * r = 0) :
    ∃ φ : R →+* 𝔽₂ε, ∀ x, f x = 𝔽₂εMap (φ x) :=
  have h : (𝔽₂ε.cast r : 𝔽₂ε → R).Bijective := by
    refine ⟨𝔽₂ε.castRingHom_injective hr0 hr, λ x ↦ ?_⟩
    rcases R_elts_cases hS hf x with (h0 | h0) | h0
    · exact ((R_elts_claim1 hS hf hr0 h0).resolve_left hr).elim
        (λ h1 ↦ ⟨1, (add_eq_zero_iff_eq.mp h1).symm⟩)
        (λ h1 ↦ ⟨𝔽₂ε.Y, add_eq_iff_eq_add.mpr h1⟩)
    · exact ((R_elts_claim1 hS hf hr0 h0).resolve_left hr).elim
        (λ h1 ↦ ⟨0, h1.symm⟩) (λ h1 ↦ ⟨𝔽₂ε.X, h1⟩)
    · exact absurd (R_elts_claim2 hS hf hr0 h0) hr
  have h0 : ∀ x, f (𝔽₂ε.cast r x) = 𝔽₂εMap x
    | 𝔽₂ε.O => by
        change f 0 = ((-1 : ℤ) : S)
        rw [hf.map_zero, Int.cast_neg, Int.cast_one]
    | 𝔽₂ε.I => (hf.map_one).trans Int.cast_zero.symm
    | 𝔽₂ε.X => by
        change f r = ((1 : ℤ) : S)
        have h0 := Eq2 hf.toNontrivialGood r
        rw [hr0, zero_add, hf.map_one, eq_comm, sub_eq_zero, _root_.sq_eq_one_iff] at h0
        refine (h0.resolve_right λ h1 ↦ hr ?_).trans Int.cast_one.symm
        exact map_eq_neg_one_reduced_imp hS hf h1
    | 𝔽₂ε.Y => ((reduced_𝔽₂ε_iff hS hf).mp hr0).trans Int.cast_zero.symm
  let ρ := RingEquiv.ofBijective (𝔽₂ε.castRingHom hr0) h
  ⟨ρ.symm, λ x ↦ h0 _ ▸ congrArg f (Equiv.apply_symm_apply ρ.toEquiv _).symm⟩

theorem 𝔽₄_solution {r : R} (hr : r * (r + 1) + 1 = 0) :
    ∃ (φ : R →+* 𝔽₄) (ι : ℤφ →+* S), ∀ x, f x = ι (𝔽₄Map (φ x)) := by
  have X : (1 : R) ≠ 0 := λ X ↦ hS <| by
    apply congrArg f at X; rw [hf.map_one, hf.map_zero, zero_eq_neg] at X
    rw [← mul_one 2, X, mul_zero]
  obtain ⟨hr0, hr1⟩ := (reduced_𝔽₄_iff hS hf).mp hr
  have hr' : r * r + r = 1 := by rwa [← mul_add_one r, ← add_eq_zero_iff_eq]
  ---- Bijectivity of `R → 𝔽₄`
  have h : (𝔽₄.cast r : 𝔽₄ → R).Bijective := by
    refine ⟨𝔽₄.castRingHom_injective hr' X, λ x ↦ ?_⟩
    have h0 {x : R} (h0 : x * x = 0) : x = 0 := R_elts_claim2 hS hf h0 hr
    rcases R_elts_cases hS hf x with (h1 | h1) | h1
    · exact ⟨1, (add_eq_zero_iff_eq.mp (h0 h1)).symm⟩
    · exact ⟨0, (h0 h1).symm⟩
    rcases R_elts_cases hS hf (x + r) with (h2 | h2) | h2
    · exact ⟨𝔽₄.Y, (add_eq_zero_iff_eq.mp <| (add_assoc x r 1).symm.trans (h0 h2)).symm⟩
    · exact ⟨𝔽₄.X, (add_eq_zero_iff_eq.mp (h0 h2)).symm⟩
    rw [_root_.add_comm x r, add_assoc, mul_add, add_mul, add_mul, add_assoc, add_assoc,
      add_assoc, h1, add_zero, mul_add_one r, ← add_assoc (x * r), add_left_comm, hr'] at h2
    rcases R_elts_cases hS hf (x * r) with (h3 | h3) | h3
    · apply h0 at h3
      rw [add_right_comm, h3, zero_add] at h2
      apply congrArg (r * ·) at h3
      rw [mul_zero, mul_add_one r, ← mul_assoc, h2, zero_mul, zero_add] at h3
      rw [h3, zero_mul, zero_add] at hr
      exact absurd hr X
    · apply h0 at h3
      rw [h3, zero_add, add_eq_zero_iff_eq] at h2
      have h4 : r = 0 := by rw [← one_mul r, ← h2, mul_assoc, h3, mul_zero]
      rw [h4, zero_mul, zero_add] at hr
      exact absurd hr X
    · rw [add_right_comm, add_eq_zero_iff_eq] at h2
      rw [mul_add_one x, add_assoc, add_eq_zero_iff_eq] at h1
      rw [h2, ← mul_assoc, mul_assoc x, add_eq_iff_eq_add'.mp hr', mul_add_one x, add_mul,
        h1, add_assoc, add_add_cancel_right, ← add_one_mul _ x, h2, mul_assoc, h1] at h3
      apply congrArg (· * x) at h3
      rw [zero_mul, mul_assoc, add_one_mul x, h1, add_add_cancel_middle₂, mul_one] at h3
      rw [h3, zero_mul, zero_add] at hr
      exact absurd hr X
  ---- Value check
  rw [← eq_sub_iff_add_eq'] at hr0
  rw [hr0, ← neg_sub, mul_neg, neg_inj, mul_sub_one, sub_eq_iff_eq_add'] at hr1
  let ι := ℤφ.castRingHom hr1
  have h0 : ∀ x, f (𝔽₄.cast r x) = ι (𝔽₄Map x)
    | 𝔽₄.O => by change f 0 = ι (-1)
                 rw [hf.map_zero, ι.map_neg, ι.map_one]
    | 𝔽₄.I => (hf.map_one).trans ι.map_zero.symm
    | 𝔽₄.X => (ℤφ.cast_φ _).symm
    | 𝔽₄.Y => by change f (r + 1) = ((1 : ℤ) : S) + (-1 : ℤ) • f r
                 rw [Int.cast_one, neg_one_zsmul, hr0, sub_eq_add_neg]
  ---- Summary
  let ρ := RingEquiv.ofBijective (𝔽₄.castRingHom hr') h
  exact ⟨ρ.symm, ι, λ x ↦ h0 _ ▸ congrArg f (Equiv.apply_symm_apply ρ.toEquiv _).symm⟩

theorem solution :
    (∃ φ : R →+* 𝔽₂ε, ∀ x, f x = 𝔽₂εMap (φ x)) ∨
    (∃ (φ : R →+* 𝔽₄) (ι : ℤφ →+* S), ∀ x, f x = ι (𝔽₄Map (φ x))) ∨
    (∃ φ : R →+* 𝔽₂, ∀ x, f x = 𝔽₂Map (φ x)) :=
  (em (∃ r : R, r ≠ 0 ∧ r * r = 0)).imp
    (λ ⟨_, h, h0⟩ ↦ 𝔽₂ε_solution hS hf h h0)
  λ h ↦ (em (∃ r : R, r * (r + 1) + 1 = 0)).imp
    (λ ⟨_, h⟩ ↦ 𝔽₄_solution hS hf h)
  λ h0 ↦ 𝔽₂_solution hS hf λ r ↦
    ((R_elts_cases hS hf r).resolve_right λ h1 ↦ h0 ⟨r, h1⟩).symm.imp
      (λ h1 ↦ by_contra λ h2 ↦ h ⟨r, h2, h1⟩)
      (λ h1 ↦ add_eq_zero_iff_eq.mp <| by_contra λ h2 ↦ h ⟨r + 1, h2, h1⟩)

end SCharNeTwo





/-! ### Summary -/

theorem solution {f : R → S} (hf : ReducedGood f) :
    (∃ φ : R →+* S, ∀ x, f x = φ (x - 1)) ∨
    (∃ φ : R →+* 𝔽₂ε, ∀ x, f x = 𝔽₂εMap (φ x)) ∨
    (∃ (φ : R →+* 𝔽₄) (ι : ℤφ →+* S), ∀ x, f x = ι (𝔽₄Map (φ x))) ∨
    (∃ φ : R →+* 𝔽₂, ∀ x, f x = 𝔽₂Map (φ x)) :=
  (em ((2 : S) = 0)).imp
    (λ h ↦ haveI : CharTwo S := Semiring_of_two_eq_zero h
           SCharTwo.solution hf.toNontrivialGood)
    (λ h ↦ SCharNeTwo.solution h hf)
