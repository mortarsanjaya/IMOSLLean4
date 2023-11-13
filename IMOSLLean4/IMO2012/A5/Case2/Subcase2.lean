import IMOSLLean4.IMO2012.A5.Case2.Basic
import IMOSLLean4.IMO2012.A5.A5Quotient

/-!
# IMO 2012 A5, Subcase 2.2: `f(-1) = 0` and `f(2) = 1 ≠ -1`

This file solves Subcase 2.2.
-/

namespace IMOSL
namespace IMO2012A5

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 2 = 1) (h2 : f 2 ≠ -1)

/-- (8.1) -/
theorem case2_2_lem1 (x : R) : f (x + 2) + f x = f (x + 1) + f (x - 1) := by
  rw [case2_map_add_two_eq h h0, h1, one_mul, add_assoc, sub_add_add_cancel]

/-- `2 + 2 ∈ I` -/
theorem case2_2_lem2 : 2 + 2 ∈ periodIdeal h := λ x ↦ by
  have h2 := case2_2_lem1 h h0 h1
  have h3 := (h2 (x + 1 + 1)).symm
  rwa [add_sub_cancel, add_assoc, one_add_one_eq_two, h2, add_sub_cancel, add_comm,
    add_left_inj, add_assoc x, one_add_one_eq_two, add_rotate, eq_comm] at h3

theorem case2_2_lem3 : 2 ∈ quasiPeriodIdeal h := λ x ↦ by
  -- First get `f(2x + 1) = f(2x - 1)`
  have h3 := eq_add_of_sub_eq' (h (x - 1) (1 + 1))
  rw [sub_add_add_cancel, sub_one_mul, ← sub_sub, one_add_one_eq_two,
    sub_add_cancel, h1, mul_one, ← case2_2_lem1 h h0 h1,
    ← mul_one (f x), ← h1, ← eq_add_of_sub_eq' (h x 2)] at h3
  -- Now use `f(4x + 1) = 0` to obtain `f(2x + 1) = f(2x - 1) = 0`
  have h4 := eq_add_of_sub_eq (case2_good_alt h h0 (x * 2 + 1) (1 + 1))
  rw [add_sub_add_right_eq_sub, add_one_mul (x * 2), ← add_assoc, add_sub_cancel,
    h3, one_add_one_eq_two, h1, mul_one, ← two_mul, mul_rotate, two_mul,
    period_imp_quasi_period h (case2_2_lem2 h h0 h1), zero_eq_mul, mul_comm] at h4
  refine h4.resolve_left λ h4 ↦ h2 ?_
  rwa [h1, eq_neg_iff_add_eq_zero, one_add_one_eq_two]

theorem case2_2_lem4 : f 0 = -1 :=
  Not.imp_symm (eq_zero_of_map_zero_ne_neg_one h)
    (λ h3 ↦ one_ne_zero <| h1.symm.trans <| congr_fun h3 2)

/-- The main lemma for the subcase -/
theorem case2_2_lem5 (h3 : ∀ c ∈ periodIdeal h, c = 0) (x : R) :
    (x = 0 ∨ x = 2) ∨ x = 1 ∨ x = -1 := by
  have h4 := h3 (2 + 2) (case2_2_lem2 h h0 h1)
  rw [← one_add_one_eq_two, ← add_assoc] at h4
  rw [← eq_neg_iff_add_eq_zero.mpr h4, one_add_one_eq_two]
  replace h4 := case2_2_lem4 h h1
  exact cases_of_nonperiod_quasi_period h h3 h4
    (case2_2_lem3 h h0 h1 h2) (λ h5 ↦ h2 <| h5.symm ▸ h4) x

/-- Solution for the current subcase (`ℤ₄Map`) -/
theorem case2_2_quot_IsAnswer (h3 : ∀ c ∈ periodIdeal h, c = 0) : IsAnswer f :=
  have h4 : (4 : R) = 0 := by
    rw [← Nat.cast_eq_ofNat, Nat.cast_add 2 2]
    exact h3 _ (case2_2_lem2 h h0 h1)
  -- `ℤ₄ → R/I` is bijective
  have X : Function.Bijective (ℤ₄.castHom h4) :=
    ⟨ℤ₄.castHom_injective _ λ h5 ↦ h2 <| h5.symm ▸ case2_2_lem4 h h1,
    λ x ↦ by rcases case2_2_lem5 h h0 h1 h2 h3 x with (h5 | h5) | (h5 | h5)
             exacts [⟨0, h5.symm⟩, ⟨2, h5.symm⟩, ⟨1, h5.symm⟩, ⟨3, h5.symm⟩]⟩
  -- Factor `f` out as `ℤ₄Map ∘ π`
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = ℤ₄Map S ∘ π.toFun
    from this.symm ▸ IsAnswer.ℤ₄_map_comp π.toRingHom π.surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <| funext λ x ↦
    match x with
      | ℤ₄.ℤ₄0 => case2_2_lem4 h h1
      | ℤ₄.ℤ₄1 => good_map_one h
      | ℤ₄.ℤ₄2 => h1
      | ℤ₄.ℤ₄3 => h0
