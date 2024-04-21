/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.A5Basic
import Mathlib.RingTheory.Ideal.Quotient

/-!
# IMO 2012 A5 (Ring quotient)

Let $R$ be a commutative ring and $S$ be an integral domain.
Given a *good* function $f : R → S$, the set
$$I = \\{c ∈ R : ∀ x ∈ R, f(c + x) = f(x)\\}$$
  is an ideal of $R$, and the induced map $\tilde{f} : R/I → S$ is good.
The set
$$J = \\{c ∈ R : ∀ x ∈ R, f(cx + 1) = 0\\}$$
  is also an ideal of $R$.
We prove this fact and prove more facts about $J$.
-/

namespace IMOSL
namespace IMO2012A5

variable [CommRing R] [Ring S] [IsDomain S] {f : R → S} (h : good f)

theorem quasi_period_iff :
    (∀ x, f (c + x) = -f c * f x) ↔ ∀ x, f (c * x + 1) = 0 :=
  forall_congr' λ x ↦ by rw [neg_mul, ← h, neg_sub, eq_comm, sub_eq_self]

theorem quasi_period_add
    (h0 : ∀ x, f (c * x + 1) = 0) (h1 : ∀ x, f (d * x + 1) = 0) :
    ∀ x, f ((c + d) * x + 1) = 0 := by
  rw [← quasi_period_iff h] at h0 h1 ⊢
  intro x; rw [add_assoc, h0, h1, ← mul_assoc, mul_neg, ← h0]

theorem map_quasi_period (h0 : f 0 = -1) (h1 : ∀ x, f (c + x) = -f c * f x) :
    f c = 1 ∨ f c = -1 := by
  -- First prove `f(-c) = f(c)`
  have h2 := map_neg_sub_map2 h c
  rw [h1, good_map_one h, mul_zero, zero_mul, sub_eq_zero] at h2
  -- Now show that `f(c)^2 = 1`
  replace h1 := h1 (-c)
  rwa [add_neg_self, h0, h2, neg_mul, neg_inj, eq_comm, mul_self_eq_one_iff] at h1

/-- (2.1) The ideal of quasi-periods -/
def quasiPeriodIdeal : Ideal R where
  carrier := {c | ∀ x, f (c * x + 1) = 0}
  add_mem' := quasi_period_add h
  zero_mem' x := by rw [zero_mul, zero_add, good_map_one h]
  smul_mem' a b h1 x := by rw [smul_eq_mul, mul_assoc, mul_left_comm, h1]

theorem period_iff :
    (∀ x, f (c + x) = f x) ↔ (∀ x, f (c + x) = -f c * f x) ∧ f c = f 0 :=
  have h1 := neg_map_zero_mul h
  ⟨λ h0 ↦ have h2 : f c = f 0 := add_zero c ▸ h0 0
    ⟨λ x ↦ by rw [h0, h2, h1], h2⟩,
  λ h0 x ↦ by rw [h0.1, h0.2, h1]⟩

theorem period_imp_quasi_period (h0 : ∀ x, f (c + x) = f x) :
    c ∈ quasiPeriodIdeal h :=
  (quasi_period_iff h).mp ((period_iff h).mp h0).1

theorem period_mul (h0 : ∀ x, f (c + x) = f x) (d : R) :
    ∀ x : R, f (d * c + x) = f x := by
  -- Eliminate the case `f = 0` first
  rcases ne_or_eq (f 0) (-1) with h1 | h1
  · intros x; rw [eq_zero_of_map_zero_ne_neg_one h h1]; rfl
  -- Now assume `f(0) = 1`. Reduce the goal to the case `d ∉ quasiPeriodIdeal`
  suffices h2 : ∀ d ∉ quasiPeriodIdeal h, ∀ x, f (d * c + x) = f x by
    by_cases h3 : d ∈ quasiPeriodIdeal h
    on_goal 2 => exact h2 d h3
    have h4 : 1 ∉ quasiPeriodIdeal h := λ h4 ↦ by
      specialize h4 (-1)
      rw [one_mul, neg_add_self, h1, neg_eq_zero] at h4
      exact one_ne_zero h4
    have h5 : d + 1 ∉ quasiPeriodIdeal h := λ h5 ↦
      h4 <| (Ideal.add_mem_iff_right _ h3).mp h5
    intro x
    rw [← h2 1 h4, one_mul, ← add_assoc, ← one_add_mul d, add_comm 1]
    exact h2 _ h5 x
  -- Solve the case `d ∉ quasiPeriodIdeal`
  intro d h2
  rw [period_iff h, quasi_period_iff h]
  constructor
  · intro x
    rw [period_iff h, quasi_period_iff h] at h0
    rw [mul_assoc, mul_left_comm]
    exact h0.1 (d * x)
  · obtain ⟨x, h2⟩ := not_forall.mp h2
    have h3 := h d (c + x)
    rw [add_left_comm, h0, h0, ← h, sub_left_inj, mul_add, add_assoc] at h3
    replace h0 : d * c ∈ quasiPeriodIdeal h :=
      Ideal.mul_mem_left _ d (period_imp_quasi_period h h0)
    rwa [(quasi_period_iff h).mpr h0, mul_left_eq_self₀,
      or_iff_left h2, neg_eq_iff_eq_neg, ← h1] at h3

/-- (2.2) The ideal of periods -/
def periodIdeal : Ideal R where
  carrier := {c | ∀ x, f (c + x) = f x}
  add_mem' h0 h1 x := by rw [add_assoc, h0, h1]
  zero_mem' x := congr_arg f <| zero_add x
  smul_mem' d c h0 := period_mul h h0 d

theorem mem_periodIdeal_iff :
    c ∈ periodIdeal h ↔ c ∈ quasiPeriodIdeal h ∧ f c = f 0 :=
  (period_iff h).trans <| and_congr_left' (quasi_period_iff h)

theorem period_equiv_imp_f_eq
    (h0 : Ideal.Quotient.ringCon (periodIdeal h) a b) : f a = f b :=
  sub_add_cancel a b ▸ Ideal.Quotient.eq.mp ((RingCon.eq _).mpr h0) b

/-- Lifting of `f` along the ideal of periods. -/
def periodLift : R ⧸ periodIdeal h → S :=
  Quot.lift f λ _ _ ↦ period_equiv_imp_f_eq h

theorem periodLift_is_good : good (periodLift h) :=
  good_of_comp_hom_good_surjective Ideal.Quotient.mk_surjective h

theorem zero_of_periodic_periodLift (c : R ⧸ periodIdeal h) :
    (∀ x, periodLift h (c + x) = periodLift h x) → c = 0 :=
  c.induction_on λ _ h0 ↦ Ideal.Quotient.eq_zero_iff_mem.mpr λ y ↦ h0 ⟦y⟧

theorem IsAnswer_of_periodLift (h0 : IsAnswer (periodLift h)) : IsAnswer f :=
  IsAnswer_comp_hom Ideal.Quotient.mk_surjective h0



/-! ### Extra structure given a non-period, quasi-period element

The results in this mini-subsection is useful for Subcase 2.2 and 2.4. -/

section QuasiPeriod

variable (h0 : f 0 = -1) (h1 : c ∈ quasiPeriodIdeal h) (h2 : c ∉ periodIdeal h)

theorem map_nonperiod_quasi_period : f c = 1 :=
  have h3 := (quasi_period_iff h).mpr h1
  (map_quasi_period h h0 h3).resolve_right λ h4 ↦
    h2 <| (period_iff h).mpr ⟨h3, h4.trans h0.symm⟩

theorem map_quasi_period_add (x : R) : f (c + x) = -f x := by
  rw [← neg_one_mul, (quasi_period_iff h).mpr h1 x,
    map_nonperiod_quasi_period h h0 h1 h2]

theorem is_period_or_eq_quasi_nonperiod (h3 : d ∈ quasiPeriodIdeal h) :
    d ∈ periodIdeal h ∨ d - c ∈ periodIdeal h :=
  Classical.or_iff_not_imp_left.mpr λ h4 x ↦ by
    rw [← add_sub_right_comm, add_sub_assoc, map_quasi_period_add h h0 h3 h4,
      ← map_quasi_period_add h h0 h1 h2, add_sub_cancel]

theorem mul_nonquasi_period_is_nonperiod (h3 : d ∉ quasiPeriodIdeal h) :
    d * c ∉ periodIdeal h := by
  obtain ⟨x, h3⟩ := not_forall.mp h3
  refine not_forall.mpr ⟨d * x + 1, λ h4 ↦ ?_⟩
  have h5 := map_quasi_period_add h h0 h1 h2
  rw [← add_assoc, ← mul_add, eq_add_of_sub_eq (h _ _), h5,
    add_left_comm, h5, mul_neg, ← neg_add, ← neg_one_mul,
    ← eq_add_of_sub_eq (h _ _), mul_left_eq_self₀] at h4
  refine h4.elim (λ h4 ↦ h2 <| (period_iff h).mpr <|
    ⟨(quasi_period_iff h).mpr h1, ?_⟩) h3
  rw [h0, h4]; exact map_nonperiod_quasi_period h h0 h1 h2

theorem equiv_mod_quasiPeriodIdeal (x : R) :
    x ∈ quasiPeriodIdeal h ∨ x - 1 ∈ quasiPeriodIdeal h :=
  have h3 : ∀ y, y * c ∈ periodIdeal h → y ∈ quasiPeriodIdeal h :=
    λ _ ↦ not_imp_not.mp <| mul_nonquasi_period_is_nonperiod h h0 h1 h2
  Or.imp (h3 x) (h3 (x - 1)) <| (sub_one_mul x c).symm ▸
    is_period_or_eq_quasi_nonperiod h h0 h1 h2 (Ideal.mul_mem_left _ x h1)

theorem equiv_mod_periodIdeal (x : R) :
    (x ∈ periodIdeal h ∨ x - c ∈ periodIdeal h) ∨
      x - 1 ∈ periodIdeal h ∨ x - (c + 1) ∈ periodIdeal h :=
  have h3 : ∀ x ∈ quasiPeriodIdeal h, x ∈ periodIdeal h ∨ x - c ∈ periodIdeal h :=
    λ _ ↦ is_period_or_eq_quasi_nonperiod h h0 h1 h2
  (equiv_mod_quasiPeriodIdeal h h0 h1 h2 x).imp (h3 x)
    (λ h4 ↦ by rw [add_comm, ← sub_sub]; exact h3 (x - 1) h4)

end QuasiPeriod


theorem cases_of_nonperiod_quasi_period (h0 : ∀ c ∈ periodIdeal h, c = 0)
    (h1 : f 0 = -1) (h2 : c ∈ quasiPeriodIdeal h) (h3 : c ≠ 0) (x : R) :
    (x = 0 ∨ x = c) ∨ x = 1 ∨ x = c + 1 := by
  refine (equiv_mod_periodIdeal h h1 h2 (mt (h0 c) h3) x).imp
    (Or.imp (h0 x) ?_) (Or.imp ?_ ?_)
  all_goals exact λ h5 ↦ eq_of_sub_eq_zero <| h0 _ h5
