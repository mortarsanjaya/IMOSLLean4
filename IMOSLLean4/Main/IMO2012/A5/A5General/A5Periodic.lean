/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2012.A5.A5General.A5QuasiPeriodic
import Mathlib.RingTheory.Congruence.Basic

/-!
# IMO 2012 A5 (Periodic elements)

Let `R` be a ring, `S` be a domain, and `f : R → S` be a non-trivial good function.
We prove that the set `I = {c | ∀ x, f(x + c) = f(x)}` is a two-sided ideal.
Then we prove that the induced map `R/I → S` is a reduced good function.

### Implementation details

Instead of using ideals explicitly, we use the `RingCon` API.
The `RingCon` relation is implemented as `PeriodEquiv`.
-/

namespace IMOSL
namespace IMO2012A5

/-- The equivalence relation representing the set `I`, as an `AddCon`. -/
def PeriodEquiv [AddCommSemigroup R] (f : R → S) : AddCon R where
  r := λ c d ↦ ∀ x, f (x + c) = f (x + d)
  iseqv := ⟨λ _ _ ↦ rfl, λ h x ↦ (h x).symm, λ h h0 x ↦ (h x).trans (h0 x)⟩
  add' := λ h h0 x ↦ by
    rw [← add_assoc, h0, add_right_comm, h, add_right_comm, add_assoc]



namespace PeriodEquiv

instance [AddCommSemigroup R] (f : R → S) : Setoid R := (PeriodEquiv f).toSetoid

lemma iff_def [AddCommSemigroup R] {f : R → S} {c d : R} :
    PeriodEquiv f c d ↔ ∀ x, f (x + c) = f (x + d) :=
  Eq.to_iff rfl

lemma apply_eq [AddCommMonoid R] {f : R → S} {c d : R} (h : PeriodEquiv f c d) :
    f c = f d := by
  rw [← zero_add c, h, zero_add]

lemma zero_right [AddCommMonoid R] {f : R → S} {c : R} :
    PeriodEquiv f c 0 ↔ ∀ x, f (x + c) = f x :=
  forall_congr' λ x ↦ by rw [add_zero]

lemma zero_right' [AddCommMonoid R] {f : R → S} {c : R} :
    PeriodEquiv f c 0 ↔ ∀ x, f (c + x) = f x :=
  zero_right.trans <| forall_congr' λ x ↦ by rw [add_comm]

lemma iff_sub [AddCommGroup R] {f : R → S} {c d : R} :
    PeriodEquiv f c d ↔ PeriodEquiv f (c - d) 0 :=
  ⟨λ h x ↦ by rw [← add_comm_sub, h, sub_add_cancel, add_zero],
  λ h x ↦ by rw [← add_add_sub_cancel x c d, h, add_zero]⟩



variable [Ring R] [NonAssocRing S] [NoZeroDivisors S] {f : R → S} (hf : NontrivialGood f)
include hf

theorem equiv_zero_iff : PeriodEquiv f c 0 ↔ QuasiPeriodic f c ∧ f c = -1 := by
  rw [zero_right, QuasiPeriodic.iff_right hf]
  refine ⟨λ h ↦ ?_, λ h x ↦ by rw [h.1, h.2, neg_neg, mul_one]⟩
  ---- `←` solved above, `→` remains
  have h0 : f c = -1 := by rw [← zero_add c, h, hf.map_zero]
  refine ⟨λ x ↦ ?_, h0⟩
  rw [h0, neg_neg, mul_one, h]

theorem mul_left_equiv_zero (h : PeriodEquiv f c 0) : ∀ d, PeriodEquiv f (d * c) 0 := by
  ---- Some general results
  have h0 (d) : QuasiPeriodic f (d * c) :=
    ((equiv_zero_iff hf).mp h).1.mul_left hf d
  have h1 := zero_right'.mp h
  have h2 (d x) : f (d * c) = -1 ∨ f (d * x + 1) = 0 := by
    rw [eq_neg_iff_add_eq_zero, ← mul_eq_zero, add_one_mul (f _),
      ← neg_eq_iff_add_eq_zero, ← neg_mul, ← (h0 d).imp_left hf,
      ← add_assoc, ← mul_add, hf.is_good, hf.is_good, h1, add_left_comm, h1]
  ---- Reduce to `f(dc) = -1`, and assume `f(-d^2 + 1) = 0`
  refine λ d ↦ (equiv_zero_iff hf).mpr ⟨h0 d, (h2 d (-d)).elim id λ h3 ↦ ?_⟩
  ---- Split into `f((d - 1) c) = -1` and `f(d) = 0`
  refine (h2 (d - 1) 1).elim (λ h4 ↦ ?_) (λ h4 ↦ ?_)
  · rwa [← h1, ← one_add_mul _ c, add_sub_cancel] at h4
  · rw [mul_one, sub_add_cancel] at h4
    rw [hf.is_good, h4, zero_mul, zero_add, add_neg_cancel, hf.map_zero] at h3
    rw [h3, ← neg_neg (f _), ← neg_one_mul, h3, zero_mul]

theorem mul_right_equiv_zero (h : PeriodEquiv f c 0) : ∀ d, PeriodEquiv f (c * d) 0 := by
  ---- Some general results
  have h0 (d) : QuasiPeriodic f (c * d) :=
    ((equiv_zero_iff hf).mp h).1.mul_right hf d
  have h1 := zero_right.mp h
  have h2 (d x) : f (c * d) = -1 ∨ f (x * d + 1) = 0 := by
    rw [eq_neg_iff_add_eq_zero, or_comm, ← mul_eq_zero, mul_add_one (f _),
      ← neg_eq_iff_add_eq_zero, ← mul_neg, ← (h0 d).imp_right hf,
      add_right_comm, ← add_mul, hf.is_good, hf.is_good, h1, add_right_comm, h1]
  ---- Reduce to `f(cd) = -1`, and assume `f(-d^2 + 1) = 0`
  refine λ d ↦ (equiv_zero_iff hf).mpr ⟨h0 d, (h2 d (-d)).elim id λ h3 ↦ ?_⟩
  ---- Split into `f(c (d - 1)) = -1` and `f(d) = 0`
  refine (h2 (d - 1) 1).elim (λ h4 ↦ ?_) (λ h4 ↦ ?_)
  · rwa [← h1, ← mul_add_one c, sub_add_cancel] at h4
  · rw [one_mul, sub_add_cancel] at h4
    rw [hf.is_good, h4, mul_zero, zero_add, neg_add_cancel, hf.map_zero] at h3
    rw [h3, ← neg_neg (f _), ← neg_one_mul, h3, zero_mul]

theorem mul_left_equiv (h : PeriodEquiv f c d) (a) :
    PeriodEquiv f (a * c) (a * d) := by
  rw [iff_sub, ← mul_sub]
  exact mul_left_equiv_zero hf (iff_sub.mp h) a

theorem mul_right_equiv (h : PeriodEquiv f c d) (a) :
    PeriodEquiv f (c * a) (d * a) := by
  rw [iff_sub, ← sub_mul]
  exact mul_right_equiv_zero hf (iff_sub.mp h) a

theorem mul_equiv (h : PeriodEquiv f a b) (h0 : PeriodEquiv f c d) :
    PeriodEquiv f (a * c) (b * d) :=
  λ x ↦ (mul_left_equiv hf h0 a x).trans (mul_right_equiv hf h d x)

def toRingCon : RingCon R :=
  { PeriodEquiv f with mul' := mul_equiv hf }

def toQuotientMap : (toRingCon hf).Quotient → S :=
  Quotient.lift f λ _ _ ↦ apply_eq

lemma toQuotientMap_good : good (toQuotientMap hf) :=
  Quotient.ind₂ hf.is_good

lemma toQuotientMap_NonTrivialGood : NontrivialGood (toQuotientMap hf) :=
  ⟨toQuotientMap_good hf, hf.map_zero_add_one⟩

/-- The induced map `R/I → S` is a reduced good map. -/
lemma toQuotientMap_ReducedGood : ReducedGood (toQuotientMap hf) :=
  ⟨toQuotientMap_NonTrivialGood hf, Quotient.ind₂ λ _ _ h ↦ Quot.sound λ x ↦ h x⟩

/-- `f` factors out through a ring homomorphism and the induced map. -/
lemma toQuotientMap_factor : f = toQuotientMap hf ∘ (toRingCon hf).mk' := rfl
