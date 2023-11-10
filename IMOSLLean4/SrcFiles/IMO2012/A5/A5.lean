import Mathlib.RingTheory.Ideal.Quotient
import Mathlib.Logic.Lemmas
import IMOSLLean4.SrcFiles.IMO2012.A5.ExplicitRings.F2
import IMOSLLean4.SrcFiles.IMO2012.A5.ExplicitRings.F2e
import IMOSLLean4.SrcFiles.IMO2012.A5.ExplicitRings.F3
import IMOSLLean4.SrcFiles.IMO2012.A5.ExplicitRings.F4
import IMOSLLean4.SrcFiles.IMO2012.A5.ExplicitRings.Z4

/-! # IMO 2012 A5 -/

namespace IMOSL
namespace IMO2012A5

open Function

/-- The problem definition. -/
def good {R S : Type _} [Ring R] [Ring S] (f : R → S) :=
  ∀ x y : R, f (x * y + 1) - f (x + y) = f x * f y





/-! ## Answer description -/

section ExtraMaps

variable (R : Type _) [Ring R]

def 𝔽₂Map : 𝔽₂ → R
  | 𝔽₂.O => -1
  | 𝔽₂.I => 0

def 𝔽₂εMap : 𝔽₂ε → R
  | 𝔽₂ε.O => -1
  | 𝔽₂ε.I => 0
  | 𝔽₂ε.X => 1
  | 𝔽₂ε.Y => 0

def 𝔽₃Map1 : 𝔽₃ → R
  | 𝔽₃.𝔽₃0 => -1
  | 𝔽₃.𝔽₃1 => 0
  | 𝔽₃.𝔽₃2 => 1

def 𝔽₃Map2 : 𝔽₃ → R
  | 𝔽₃.𝔽₃0 => -1
  | 𝔽₃.𝔽₃1 => 0
  | 𝔽₃.𝔽₃2 => 0

def 𝔽₄Map (c : R) : 𝔽₄ → R
  | 𝔽₄.O => -1
  | 𝔽₄.I => 0
  | 𝔽₄.X => c
  | 𝔽₄.Y => 1 - c

def ℤ₄Map : ℤ₄ → R
  | 0 => -1
  | 1 => 0
  | 2 => 1
  | 3 => 0

end ExtraMaps

/-- The set of answers, defined using a proposition. -/
inductive IsAnswer {R S : Type _} [Ring R] [Ring S] : (R → S) → Prop
  | of_zero :
      IsAnswer (0 : R → S)
  | hom_sub_one (φ : R →+* S) :
      IsAnswer (φ.toFun · - 1)
  | hom_sq_sub_one (φ : R →+* S) :
      IsAnswer (φ.toFun · ^ 2 - 1)
  | 𝔽₂_map_comp (φ : R →+* 𝔽₂) (_ : Surjective φ.toFun) :
      IsAnswer (𝔽₂Map S ∘ φ.toFun)
  | 𝔽₃_map1_comp (φ : R →+* 𝔽₃) (_ : Surjective φ.toFun) :
      IsAnswer (𝔽₃Map1 S ∘ φ.toFun)
  | 𝔽₃_map2_comp (φ : R →+* 𝔽₃) (_ : Surjective φ.toFun) :
      IsAnswer (𝔽₃Map2 S ∘ φ.toFun)
  | ℤ₄_map_comp (φ : R →+* ℤ₄) (_ : Surjective φ.toFun) :
      IsAnswer (ℤ₄Map S ∘ φ.toFun)
  | 𝔽₂ε_map_comp (φ : R →+* 𝔽₂ε) (_ : Surjective φ.toFun) :
      IsAnswer (𝔽₂εMap S ∘ φ.toFun)
  | 𝔽₄_map_comp (φ : R →+* 𝔽₄) (_ : Surjective φ.toFun)
        (c : S) (_ : c * (1 - c) = -1) :
      IsAnswer (𝔽₄Map S c ∘ φ.toFun)





/-! ## Step 0: Answer checking -/

section AnswerChecking

variable {R : Type _} [Ring R]

/-- The zero map is good. -/
theorem zero_is_good {S : Type _} [Ring S] : good (0 : R → S) :=
  λ _ _ ↦ (sub_self 0).trans (mul_zero 0).symm

/-- The map `x ↦ x - 1` is good. -/
theorem sub_one_is_good : good (· - (1 : R)) := λ x y ↦ by
  rw [sub_sub_sub_cancel_right, ← sub_sub_sub_eq, ← mul_sub_one, sub_one_mul]

/-- The map `x ↦ x^2 - 1` is good if `R` is commutative. -/
theorem sq_sub_one_is_good {R : Type _} [CommRing R] : good (· ^ 2 - (1 : R)) :=
  λ x y ↦ by rw [sub_sub_sub_cancel_right, sq_sub_sq, add_add_add_comm,
    ← mul_add_one (α := R), add_comm 1 y, ← add_one_mul (α := R),
    ← sub_sub_sub_eq, ← mul_sub_one, ← sub_one_mul,
    mul_mul_mul_comm, ← sq_sub_sq, ← sq_sub_sq, one_pow]

/-- The map `𝔽₂_map` is good. -/
theorem 𝔽₂Map_is_good : good (𝔽₂Map R)
  | 0, _ => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm

/-- The map `𝔽₃_map1` is good. -/
theorem 𝔽₃Map1_is_good : good (𝔽₃Map1 R)
  | 0, _ => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm
  | 2, 0 => (zero_sub _).trans (mul_neg_one _).symm
  | 2, 1 => (sub_self _).trans (mul_zero _).symm
  | 2, 2 => (sub_zero _).trans (mul_one _).symm

/-- The map `𝔽₃_map2` is good. -/
theorem 𝔽₃Map2_is_good : good (𝔽₃Map2 R)
  | 0, _ => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm
  | 2, 0 => (sub_self _).trans (zero_mul _).symm
  | 2, 1 => (sub_self _).trans (mul_zero _).symm
  | 2, 2 => (sub_zero _).trans (mul_zero _).symm

/-- The map `ℤ₄_map` is good. -/
theorem ℤ₄Map_is_good : good (ℤ₄Map R)
  | 0, _ => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm
  | x, 0 => by rw [mul_zero, add_zero]
               exact (zero_sub _).trans (mul_neg_one _).symm
  | x, 1 => (mul_one x).symm ▸ (sub_self _).trans (mul_zero _).symm
  | 2, 2 => (zero_sub _).trans <| (neg_neg _).trans (mul_one _).symm
  | 2, 3 => (sub_self _).trans (mul_zero _).symm
  | 3, 2 => (sub_self _).trans (zero_mul _).symm
  | 3, 3 => (sub_self _).trans (zero_mul _).symm

/-- The map `𝔽₂ε_map` is good. -/
theorem 𝔽₂εMap_is_good : good (𝔽₂εMap R)
  | 0, x => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm
  | x, 0 => by rw [mul_zero, add_zero]
               exact (zero_sub _).trans (mul_neg_one _).symm
  | x, 1 => (mul_one x).symm ▸ (sub_self _).trans (mul_zero _).symm
  | 𝔽₂ε.X, 𝔽₂ε.X => (zero_sub _).trans <| (neg_neg _).trans (one_mul _).symm
  | 𝔽₂ε.X, 𝔽₂ε.Y => (sub_self _).trans (one_mul _).symm
  | 𝔽₂ε.Y, 𝔽₂ε.X => (sub_self _).trans (zero_mul _).symm
  | 𝔽₂ε.Y, 𝔽₂ε.Y => (sub_self _).trans (zero_mul _).symm

/-- The map `𝔽₄_map` is good. -/
theorem 𝔽₄Map_is_good {c : R} (h : c * (1 - c) = -1) : good (𝔽₄Map R c)
  | 0, x => (zero_sub _).trans (neg_one_mul _).symm
  | 1, x => by rw [one_mul, add_comm, sub_self]; exact (zero_mul _).symm
  | x, 0 => by rw [mul_zero, add_zero]
               exact (zero_sub _).trans (mul_neg_one _).symm
  | x, 1 => (mul_one x).symm ▸ (sub_self _).trans (mul_zero _).symm
  | 𝔽₄.X, 𝔽₄.X => calc c - -1 = c * c := by rw [← h, ← mul_one_sub, sub_sub_cancel]
  | 𝔽₄.X, 𝔽₄.Y => (sub_zero _).trans h.symm
  | 𝔽₄.Y, 𝔽₄.X => calc (-1) - 0 = (1 - c) * c := by rw
      [sub_zero (-1), ← h, mul_one_sub, ← one_sub_mul]
  | 𝔽₄.Y, 𝔽₄.Y => calc (1 - c) - -1 = (1 - c) * (1 - c) := by rw [one_sub_mul, h]

end AnswerChecking



theorem good_map_comp_hom {R R₀ S : Type _} [Ring R] [Ring R₀] [Ring S]
    {f : R → S} (h : good f) (φ : R₀ →+* R) : good (f ∘ φ) := λ x y ↦
  h (φ x) (φ y) ▸ congr_arg₂ (λ u v ↦ f u - f v)
    (by rw [φ.map_add, φ.map_mul, φ.map_one]) (φ.map_add x y)

theorem good_of_isAnswer {R S : Type _} [Ring R] [CommRing S]
    {f : R → S} (h : IsAnswer f) : good f :=
  h.recOn zero_is_good
    (good_map_comp_hom sub_one_is_good)
    (good_map_comp_hom sq_sub_one_is_good)
    (λ φ _ ↦ good_map_comp_hom 𝔽₂Map_is_good φ)
    (λ φ _ ↦ good_map_comp_hom 𝔽₃Map1_is_good φ)
    (λ φ _ ↦ good_map_comp_hom 𝔽₃Map2_is_good φ)
    (λ φ _ ↦ good_map_comp_hom ℤ₄Map_is_good φ)
    (λ φ _ ↦ good_map_comp_hom 𝔽₂εMap_is_good φ)
    (λ φ _ _ h ↦ good_map_comp_hom (𝔽₄Map_is_good h) φ)





/-! ## Step 1: Small observations -/

section Hom

variable {R R₀ S : Type _} [Ring R] [Ring R₀] [Ring S]

/-- Given `f : R → S` and `φ : R₀ →+* R` surjective,
  `f` is good if `f ∘ φ` is good. -/
theorem good_of_comp_hom_good_surjective {φ : R₀ →+* R} (h : Surjective φ)
    {f : R → S} (h0 : good (f ∘ φ.toFun)) : good f := λ x y ↦ by
  rcases h x with ⟨a, rfl⟩
  rcases h y with ⟨b, rfl⟩
  rw [← φ.map_add, ← φ.map_mul, ← φ.map_one, ← φ.map_add]
  exact h0 a b

/-- Given `f : R → S` and `φ : R₀ →+* R` surjective,
  `f ∘ φ` is an answer if `f` is an answer. -/
theorem isAnswerCompHom {φ : R₀ →+* R} (h : Surjective φ.toFun)
    {f : R → S} (h0 : IsAnswer f) : IsAnswer (f ∘ φ.toFun) :=
  h0.recOn IsAnswer.of_zero
    (λ ρ ↦ IsAnswer.hom_sub_one (ρ.comp φ))
    (λ ρ ↦ IsAnswer.hom_sq_sub_one (ρ.comp φ))
    (λ ρ h1 ↦ IsAnswer.𝔽₂_map_comp (ρ.comp φ) (h1.comp h))
    (λ ρ h1 ↦ IsAnswer.𝔽₃_map1_comp (ρ.comp φ) (h1.comp h))
    (λ ρ h1 ↦ IsAnswer.𝔽₃_map2_comp (ρ.comp φ) (h1.comp h))
    (λ ρ h1 ↦ IsAnswer.ℤ₄_map_comp (ρ.comp φ) (h1.comp h))
    (λ ρ h1 ↦ IsAnswer.𝔽₂ε_map_comp (ρ.comp φ) (h1.comp h))
    (λ ρ h1 ↦ IsAnswer.𝔽₄_map_comp (ρ.comp φ) (h1.comp h))

end Hom



section Noncomm

variable {R S : Type _} [Ring R] [Ring S] [IsDomain S] {f : R → S} (h : good f)

theorem good_map_one : f 1 = 0 := by
  rw [← mul_self_eq_zero, ← h, mul_one, sub_self]

theorem neg_map_zero_mul (x : R) : -f 0 * f x = f x := by
  rw [neg_mul, neg_eq_iff_eq_neg, ← h, zero_mul,
    zero_add, good_map_one h, zero_sub, zero_add]

/-- (1.1) -/
theorem eq_zero_of_map_zero_ne_neg_one (h0 : f 0 ≠ -1) : f = 0 :=
  funext λ x ↦ (mul_left_eq_self₀.mp <| neg_map_zero_mul h x).resolve_left λ h1 ↦
    h0 <| neg_eq_iff_eq_neg.mp h1

theorem one_ne_zero_of_map_zero (h0 : f 0 = -1) : (1 : R) ≠ 0 :=
  mt (congr_arg f) <| by rw [good_map_one h, h0, zero_eq_neg]; exact one_ne_zero

/-- (1.2) -/
theorem map_neg_sub_map1 (x : R) : f (1 - x) - f (x - 1) = f x * f (-1) := by
  rw [← h, mul_neg_one, neg_add_eq_sub, ← sub_eq_add_neg]

/-- (1.3) -/
theorem map_neg_sub_map2 (x : R) : f (-x) - f x = f (x + 1) * f (-1) := by
  rw [← map_neg_sub_map1 h, sub_add_cancel'', add_sub_cancel]

/-- Auxiliary lemma for two sub-cases -/
theorem eq_hom_sub_one_of (h0 : ∀ x y, f (x + y) = f x + f y + 1) :
    ∃ φ : R →+* S, f = (φ.toFun · - 1) :=
  let g := (f · + 1)
  have h1 : f 1 = 0 := good_map_one h
  have h2 : g 1 = 1 := add_left_eq_self.mpr h1
  have h3 : ∀ x y, g (x + y) = g x + g y := λ x y ↦ by
    rw [add_add_add_comm, ← add_assoc, ← h0]
  have h4 : ∀ x y, g (x * y) = g x * g y := λ x y ↦ by
    rw [add_one_mul (f x), mul_add_one (f x), add_assoc, ← add_assoc (f x),
      ← h0, ← h, sub_add_cancel, h0, add_assoc, h1, zero_add]
  ⟨RingHom.mk' ⟨⟨g, h2⟩, h4⟩ h3, funext λ x ↦ (add_sub_cancel (f x) 1).symm⟩

/-- Corollary of the previous result -/
theorem isAnswerOfAddOneAdditive (h0 : ∀ x y, f (x + y) = f x + f y + 1) :
    IsAnswer f :=
  Exists.elim (eq_hom_sub_one_of h h0) (λ φ h1 ↦ h1.symm ▸ IsAnswer.hom_sub_one φ)

end Noncomm





/-! ## Step 2: Ring quotient -/

section Quot

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f)

theorem quasi_period_iff {c : R} :
    (∀ x, f (c + x) = -f c * f x) ↔ ∀ x, f (c * x + 1) = 0 :=
  forall_congr' λ x ↦ by rw [neg_mul, ← h, neg_sub, eq_comm, sub_eq_self]

theorem quasi_period_add {c d : R}
    (h0 : ∀ x, f (c * x + 1) = 0) (h1 : ∀ x, f (d * x + 1) = 0) :
    ∀ x, f ((c + d) * x + 1) = 0 := by
  rw [← quasi_period_iff h] at h0 h1 ⊢
  intro x
  rw [add_assoc, h0, h1, ← mul_assoc, mul_neg, ← h0]

theorem map_quasi_period (h0 : f 0 = -1)
    {c : R} (h1 : ∀ x, f (c + x) = -f c * f x) : f c = 1 ∨ f c = -1 := by
  have h2 := map_neg_sub_map2 h c
  rw [h1, good_map_one h, mul_zero, zero_mul, sub_eq_zero] at h2
  replace h1 := h1 (-c)
  rwa [add_neg_self, h0, h2, neg_mul, neg_inj, eq_comm, mul_self_eq_one_iff] at h1

/-- (2.1) The ideal of quasi-periods -/
def quasiPeriodIdeal : Ideal R where
  carrier := {c | ∀ x, f (c * x + 1) = 0}
  add_mem' := quasi_period_add h
  zero_mem' x := by rw [zero_mul, zero_add, good_map_one h]
  smul_mem' a b h1 x := by rw [smul_eq_mul, mul_assoc, mul_left_comm, h1]

theorem period_iff {c : R} :
    (∀ x, f (c + x) = f x) ↔ (∀ x, f (c + x) = -f c * f x) ∧ f c = f 0 :=
  have h1 := neg_map_zero_mul h
  ⟨λ h0 ↦ have h2 : f c = f 0 := add_zero c ▸ h0 0
    ⟨λ x ↦ by rw [h0, h2, h1], h2⟩,
  λ h0 x ↦ by rw [h0.1, h0.2, h1]⟩

theorem period_imp_quasi_period {c : R} (h0 : ∀ x, f (c + x) = f x) :
    ∀ x, f (c * x + 1) = 0 :=
  (quasi_period_iff h).mp ((period_iff h).mp h0).1

theorem period_mul {c : R} (h0 : ∀ x, f (c + x) = f x) (d : R) :
    ∀ x : R, f (d * c + x) = f x := by
  -- Eliminate the case `f = 0` first
  rcases ne_or_eq (f 0) (-1) with h1 | h1
  · intros x; rw [eq_zero_of_map_zero_ne_neg_one h h1]; rfl
  -- Now assume `f(0) = 1`. Reduce the goal to the case `d ∉ quasiPeriodIdeal`
  suffices h2 : ∀ d ∉ quasiPeriodIdeal h, ∀ x, f (d * c + x) = f x
  · by_cases h3 : d ∈ quasiPeriodIdeal h
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

theorem period_equiv_imp_f_eq {a b : R}
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

theorem isAnswerOfPeriodLift (h0 : IsAnswer (periodLift h)) : IsAnswer f :=
  isAnswerCompHom Ideal.Quotient.mk_surjective h0



/-! ### Extra structure given a non-period, quasi-period element

The results in this mini-subsection is useful for Subcase 2.2 and 2.4. -/

section QuasiPeriod

variable {c : R} (h0 : f 0 = -1)
  (h1 : c ∈ quasiPeriodIdeal h) (h2 : c ∉ periodIdeal h)

theorem map_nonperiod_quasi_period : f c = 1 :=
  have h3 := (quasi_period_iff h).mpr h1
  (map_quasi_period h h0 h3).resolve_right λ h4 ↦
    h2 <| (period_iff h).mpr ⟨h3, h4.trans h0.symm⟩

theorem map_quasi_period_add (x : R) : f (c + x) = -f x := by
  rw [← neg_one_mul, (quasi_period_iff h).mpr h1 x,
    map_nonperiod_quasi_period h h0 h1 h2]

theorem is_period_or_eq_quasi_nonperiod {d : R} (h3 : d ∈ quasiPeriodIdeal h) :
    d ∈ periodIdeal h ∨ d - c ∈ periodIdeal h :=
  Classical.or_iff_not_imp_left.mpr λ h4 x ↦ by
    rw [← add_sub_right_comm, add_sub_assoc, map_quasi_period_add h h0 h3 h4,
      ← map_quasi_period_add h h0 h1 h2, add_sub_cancel'_right]

theorem mul_nonquasi_period_is_nonperiod
    {d : R} (h3 : d ∉ quasiPeriodIdeal h) : d * c ∉ periodIdeal h := by
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

theorem cases_of_nonperiod_quasi_period (h0 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)
    {c : R} (h1 : f 0 = -1) (h2 : c ∈ quasiPeriodIdeal h) (h3 : c ≠ 0) (x : R) :
    (x = 0 ∨ x = c) ∨ x = 1 ∨ x = c + 1 :=
  (equiv_mod_periodIdeal h h1 h2 (mt (h0 c) h3) x).imp
    (Or.imp (h0 x) (λ h5 ↦ eq_of_sub_eq_zero <| h0 _ h5))
    (Or.imp (λ h5 ↦ eq_of_sub_eq_zero <| h0 _ h5)
      (λ h5 ↦ eq_of_sub_eq_zero <| h0 _ h5))

end Quot





/-! ## Step 3: Case 1: `f_ ≠ 0` -/

set_option profiler true
set_option profiler.threshold 50
section Step3

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f)

/-- (3.5) The lemma depends only on `good f`, but is useless in the case `f = 0`. -/
theorem case1_map_add_main_eq1 (x y : R) :
    f (x + y) - f (-(x + y)) = f (-x) * f (-y) - f x * f y :=
  by rw [← h, ← h, neg_mul_neg, sub_sub_sub_cancel_left, ← neg_add]

/-- (3.6) The lemma depends only on `good f`, but is useless in the case `f = 0`. -/
theorem case1_map_add_main_eq2 (x y : R) :
    -(f (x + y + 1) * f (-1)) = f (-x) * f (-y) - f x * f y :=
  by rw [← case1_map_add_main_eq1 h, ← map_neg_sub_map2 h, neg_sub]

variable (h0 : f (-1) ≠ 0)

/-- (3.1) -/
theorem case1_map_neg_add_one (x : R) : f (-x + 1) = -f (x + 1) :=
  mul_right_cancel₀ h0 <| let h1 := map_neg_sub_map2 h
    by rw [← h1, neg_mul, ← h1, neg_neg, neg_sub]

theorem case1_map_zero : f 0 = -1 :=
  by_contra λ h1 ↦ h0 <| congr_fun (eq_zero_of_map_zero_ne_neg_one h h1) _

/-- (3.2) -/
theorem case1_map_two : f 2 = 1 := by
  rw [← neg_inj, ← one_add_one_eq_two, ← case1_map_zero h h0,
    ← case1_map_neg_add_one h h0, neg_add_self]

/-- (3.3) -/
theorem case1_map_add_one_add_map_sub_one (x : R) :
    f (x + 1) + f (x - 1) = -(f x * f (-1)) := by
  rw [← neg_eq_iff_eq_neg, neg_add', ← map_neg_sub_map1 h,
    ← case1_map_neg_add_one h h0, neg_add_eq_sub x 1]

/-- (3.4) -/
theorem case1_map_two_mul_add_one (x : R) :
    f (2 * x + 1) = -(f (x + 1) * f (-1)) := by
  rw [← case1_map_add_one_add_map_sub_one h h0, add_sub_cancel, add_rotate,
    one_add_one_eq_two, ← sub_eq_iff_eq_add', h, case1_map_two h h0, one_mul]

/-- Main claim -/
theorem case1_map_neg_one_cases : f (-1) = -2 ∨ f (-1) = 1 := by
  sorry
/-
  have h1 : f (-1) = -f 3 :=
    case1_map_neg_add_one h h0 (1 + 1 : R) ▸
      sub_eq_neg_add (1 : R) (1 + 1) ▸ sub_add_cancel'' (1 : R) 1 ▸ rfl
  have h2 : f 2 = 1 := case1_map_two h h0
  have h3 := case1_map_add_one_add_map_sub_one h h0
  have h4 := (neg_eq_iff_eq_neg.mpr h1).symm
  have h5 : f (2 + 2) = -f _ + 1 :=
    mul_right_cancel₀ h0 <|
      (neg_eq_iff_eq_neg.mpr <| h3 (2 + 2)).symm.trans <|
        (neg_add _ _).trans <|
          (add_sub_assoc (2 : R) 2 1).symm ▸
            (add_sub_cancel (1 : R) 1).symm ▸
              two_mul (2 : R) ▸
                h4 ▸
                  (add_one_mul (f 3) (f _)).symm ▸
                    congr_arg₂ _ (neg_eq_iff_eq_neg.mpr <| case1_map_two_mul_add_one h h0 2)
                      h1.symm
  suffices f (2 + (1 + 1)) = (-f _ + 1) * (-f _ - 1) from
    (mul_right_eq_self₀.mp <| this.symm.trans h5).imp
      (λ h6 => neg_eq_iff_eq_neg.mp <| eq_add_of_sub_eq h6) neg_add_eq_zero.mp
  mul_self_sub_mul_self (-f _) 1 ▸
    (mul_neg (-f _) (f _)).symm ▸
      h4 ▸
        h3 3 ▸
          eq_sub_of_add_eq
            (congr_arg₂ _ (add_assoc (2 : R) 1 1 ▸ rfl)
              ((mul_one _).trans <| (add_sub_cancel (2 : R) 1).symm ▸ h2.symm))
-/

/-- (3.7) -/
theorem case1_map_add_one_ne_zero_imp {x : R} (h1 : f (x + 1) ≠ 0) :
    f (-x) + f x = f (-1) := by
  have h2 := map_neg_sub_map2 h x
  apply mul_right_cancel₀ (h2.trans_ne <| mul_ne_zero h1 h0)
  rw [← mul_self_sub_mul_self, ← case1_map_add_main_eq2 h, ← two_mul,
    ← neg_mul, h2, case1_map_two_mul_add_one h h0, neg_neg, mul_comm]

/-- (3.8) -/
theorem case1_map_add_one_eq_zero_imp {x : R} (h1 : f (x + 1) = 0) :
    f x = -1 ∧ f (-x) = -1 := by
  have h2 : f (-x) = f x := by rw [← sub_eq_zero, map_neg_sub_map2 h, h1, zero_mul]
  rw [h2, and_self]
  have h3 := case1_map_two_mul_add_one h h0
  have h4 := case1_map_add_main_eq1 h x (x + 1)
  rw [h1, mul_zero, sub_zero, ← add_assoc, ← two_mul, h3, h1, zero_mul,
    neg_zero, zero_sub, ← sub_add_cancel'' (1 : R), add_assoc,
    one_add_one_eq_two, ← mul_add_one _ x, ← neg_add_eq_sub, ← mul_neg,
    h3, neg_neg, neg_add_eq_sub, sub_add_cancel'', h2] at h4
  have h5 := case1_map_add_main_eq2 h x (-(x + 1))
  rwa [neg_neg, h1, mul_zero, zero_sub, neg_inj, add_right_comm, add_neg_self,
    ← h4, mul_eq_mul_right_iff, case1_map_zero h h0, or_iff_left h0, eq_comm] at h5

end Step3

#exit





/-! ## Step 4: Subcase 1.1: `f_ = -2 ≠ 0` -/

section Step4

/-- Auxiliary lemma: `2 ≠ 0` -/
theorem case1_1_S_two_ne_zero {S : Type _} [AddGroup S] {a b : S} (h : a ≠ 0) (h0 : a = -b) :
    (b : S) ≠ 0 :=
  neg_ne_zero.mp λ h1 => h <| h0.trans h1

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S] {f : R → S} (h : good f)
  (h0 : f (-1) ≠ 0) (h1 : f (-1) = -2)

/-- (4.1) -/
theorem case1_1_lem1 (x : R) : f (-x) + f x = -2 :=
  (ne_or_eq (f (x + 1)) 0).elim (λ h2 => h1 ▸ case1_map_add_one_ne_zero_imp h h0 h2) λ h2 =>
    let h3 := case1_map_add_one_eq_zero_imp h h0 h2
    (congr_arg₂ _ h3.2 h3.1).trans (neg_add _ _).symm

/-- (4.2) -/
theorem case1_1_lem2 (x : R) : f (x + 1) = f x + 1 :=
  eq_add_of_sub_eq <|
    mul_right_cancel₀ h0 <|
      (sub_one_mul _ _).trans <|
        map_neg_sub_map2 h x ▸
          h1.symm ▸
            (mul_neg (f x) 2).symm ▸
              (mul_two (f x)).symm ▸
                case1_1_lem1 h h0 h1 x ▸
                  sub_sub (f (-x) - f x) (f (-x)) (f x) ▸
                    (sub_sub_cancel_left (f (-x)) (f x)).symm ▸ (neg_add' (f x) (f x)).symm

/-- Solution for the current subcase (`hom_sub_one: x ↦ φ(x) - 1`) -/
theorem case11IsAnswer : IsAnswer f :=
  isAnswerOfAddOneAdditive h (case1_map_zero h h0) λ x y =>
    by
    have h2 := λ t => eq_sub_of_add_eq (case1_1_lem1 h h0 h1 t)
    have h3 := case1_map_add_main_eq2 h x y
    rw [h1, h2, h2, case1_1_lem2 h h0 h1, mul_neg, neg_neg, add_one_mul] at h3
    refine' mul_right_cancel₀ (case1_1_S_two_ne_zero h0 h1) ((eq_sub_of_add_eq h3).trans _)
    ring

end Step4





/-! ## Step 5: Subcase 1.2: `f_ = 1 ≠ -2` -/

section Step5

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S] {f : R → S} (h : good f)
  (h0 : f (-1) ≠ 0) (h1 : f (-1) ≠ -2)

/-- (5.1) -/
theorem case1_2_lem1 (h1 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) {c : R} (h2 : f (c + 1) = 0) :
    c = 0 :=
  h1 c λ x => by
    let h4 := case1_map_add_main_eq2 h c (x - 1)
    let h5 := case1_map_add_one_eq_zero_imp h h0 h2
    rw [h5.1, h5.2, ← mul_sub, neg_one_mul, neg_inj, map_neg_sub_map2 h, add_assoc, sub_add_cancel,
        mul_eq_mul_right_iff] at h4  <;>
      exact h4.resolve_right h0

variable (h2 : f (-1) = 1) (h3 : ∀ c, (∀ x, f (c + x) = f x) → c = 0)

/-- (5.2) -/
theorem case1_2_lem2 (x : R) : f (x + 1) + f (x - 1) + f x = 0 :=
  add_eq_zero_iff_eq_neg.mpr <| mul_one (f x) ▸ h2 ▸ case1_map_add_one_add_map_sub_one h h0 x

/-- `3 = 0` in `R` -/
theorem case1_2_lem3 : (3 : R) = 0 :=
  h3 (3 : R) <|
    let h4 x := eq_neg_of_add_eq_zero_left (case1_2_lem2 h h0 h1 h2 h3 x)
    λ x =>
    add_comm x 3 ▸
      add_assoc x 2 1 ▸
        (eq_add_neg_of_add_eq <| h4 _).trans
          (add_assoc x 1 1 ▸
            (add_sub_cancel (x + 1) 1).symm ▸
              h4 (x + 1) ▸ (add_sub_cancel x 1).symm ▸ neg_add_cancel_left _ _)

/-- (5.3) -/
theorem case1_2_lem4 (x : R) (h4 : x ≠ 0) : f (-x) + f x = 1 :=
  h2 ▸ case1_map_add_one_ne_zero_imp h h0 (mt (case1_2_lem1 h h0 h3) h4)

/-- The main lemma for the subcase -/
theorem case1_2_lem5 (x : R) : x = 0 ∨ x = 1 ∨ x = -1 :=
  by
  by_contra' h4
  rw [← add_eq_zero_iff_eq_neg] at h4
  have h5 := case1_2_lem4 h h0 h1 h2 h3
  have h6 := congr_arg₂ Add.add (h5 (x + 1) h4.2.2) (h5 (x - 1) <| sub_ne_zero_of_ne h4.2.1)
  have h7 := λ x => eq_neg_of_add_eq_zero_left (case1_2_lem2 h h0 h1 h2 h3 x)
  rw [add_add_add_comm, h7, add_comm (f (-(x + 1))), neg_sub', sub_neg_eq_add, neg_add', h7, ←
    neg_add, ← bit0, h5 x h4.1] at h6
  exact h1 (h2.trans <| neg_eq_iff_eq_neg.mp h6)

/-- Solution for the current subcase (`𝔽₃_map1`) -/
theorem case12QuotIsAnswer : IsAnswer f :=
  let X := case1_map_zero h h0
  let X0 : Bijective (𝔽₃.castHom <| case1_2_lem3 h h0 h1 h2 h3) :=
    ⟨𝔽₃.castHom_injective _ (one_ne_zero_of_map_zero h X), λ x =>
      (case1_2_lem5 h h0 h1 h2 h3 x).elim (λ h4 => ⟨𝔽₃.𝔽₃0, h4.symm⟩) λ h4 =>
        h4.elim (λ h4 => ⟨𝔽₃.𝔽₃1, h4.symm⟩) λ h4 => ⟨𝔽₃.𝔽₃2, h4.symm⟩⟩
  let π := (RingEquiv.ofBijective _ X0).symm
  suffices f = 𝔽₃Map1 S ∘ π from this.symm ▸ IsAnswer.𝔽₃_map1_comp π.toRingHom π.Surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <|
    funext λ x =>
      match x with
      | 𝔽₃.𝔽₃0 => X
      | 𝔽₃.𝔽₃1 => good_map_one h
      | 𝔽₃.𝔽₃2 => h2

end Step5





/-! ## Step 6: Case 2: `f_ = 0` -/

section Step6

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S] {f : R → S} (h : good f)
  (h0 : f (-1) = 0)

/-- (6.1) `f` is even -/
theorem case2_map_even (x : R) : f (-x) = f x :=
  eq_of_sub_eq_zero <| (map_neg_sub_map2 h x).trans <| mul_eq_zero_of_right _ h0

/-- (6.2) -/
theorem case2_good_alt (x y : R) : f (x * y - 1) - f (x - y) = f x * f y :=
  suffices -(x * -y + 1) = x * y - 1 from
    case2_map_even h h0 y ▸
      h x (-y) ▸
        congr_arg₂ _ ((congr_arg f this.symm).trans <| case2_map_even h h0 _)
          (congr_arg f <| sub_eq_add_neg x y)
  (neg_add' _ _).trans <| congr_arg₂ _ ((neg_mul _ _).symm.trans <| neg_mul_neg x y) rfl

/-- (6.3) -/
theorem case2_map_sq_sub_one (h3 : f 0 = -1) (x : R) : f (x ^ 2 - 1) = f x ^ 2 - 1 :=
  (sq x).symm ▸ (eq_add_of_sub_eq <| case2_good_alt h h0 x x).trans <|
    (congr_arg₂ _ (sq (f x)).symm ((congr_arg f <| sub_self x).trans h3)).trans
      (sub_eq_add_neg _ _).symm

/-- (6.4) -/
theorem case2_map_self_mul_add_one_sub_one (x : R) : f (x * (x + 1) - 1) = f x * f (x + 1) :=
  (eq_add_of_sub_eq <| case2_good_alt h h0 x (x + 1)).trans <|
    add_right_eq_self.mpr <| h0 ▸ congr_arg f <| sub_add_cancel' x 1

/-- (6.5) -/
theorem case2_map_add_two_eq (x : R) : f (x + 2) = f 2 * (f (x + 1) - f x) + f (x - 1) :=
  by
  have h1 : f (-(2 * x + 1)) = f (2 * -(x + 1) + 1) := congr_arg f (by ring)
  have h2 := case2_map_even h h0
  have h3 := λ t => eq_add_of_sub_eq (h 2 t)
  rw [h2, h3, h3, h2, ← eq_sub_iff_add_eq', add_sub_right_comm, ← mul_sub] at h1
  refine' (congr_arg f <| add_comm _ _).trans (h1.trans <| congr_arg₂ _ rfl _)
  rw [bit0, ← sub_eq_add_neg, add_sub_add_right_eq_sub, ← neg_sub, h2]

/-- Main claim -/
theorem case2_map_two_cases (h1 : f 0 = -1) : f 2 = -1 ∨ f 2 = 1 ∨ f 2 = 3 ∨ f 2 = 0 :=
  by
  suffices (f 2 + 1) * ((f 2 - 1) * ((f 2 - 3) * f 2)) = 0 from
    (mul_eq_zero.mp this).imp eq_neg_of_add_eq_zero_left λ this =>
      (mul_eq_zero.mp this).imp eq_of_sub_eq_zero λ this =>
        (mul_eq_zero.mp this).imp_left eq_of_sub_eq_zero
  have h2 := case2_map_sq_sub_one h h0 h1 2
  rw [sq, two_mul, add_sub_assoc, bit0, add_sub_cancel, ← bit0] at h2
  have h3 := case2_map_add_two_eq h h0
  have h4 := h3 (1 + 1)
  rw [add_sub_cancel, ← bit0, good_map_one h, add_zero, h2] at h4
  have h5 := case2_map_self_mul_add_one_sub_one h h0 2
  rw [two_mul, add_sub_assoc, add_sub_cancel, h3, add_sub_cancel, add_assoc, ← bit0, h4, h2, ←
    sub_eq_zero] at h5
  rw [← h5]; ring

/-- (6.6) -/
theorem case2_special_identity (x : R) :
    f x * f (x + 1) - f (x - 1) * f (x + 2) = f x * f 2 + f (x + 2) := by
  calc
    f x * f (x + 1) - f (x - 1) * f (x + 2) =
        f (x * (x + 1) - 1) - (f ((x - 1) * (x + 2) + 1) - f (x - 1 + (x + 2))) :=
      congr_arg₂ _ (case2_map_self_mul_add_one_sub_one h h0 x).symm (h _ _).symm
    _ = f (x * (x + 1) - 1) - f ((x - 1) * (x + 2) + 1) + f (x - 1 + (x + 2)) :=
      (sub_add _ _ _).symm
    _ = 0 + f (x * 2 + 1) :=
      (congr_arg₂ _ (sub_eq_zero_of_eq <| congr_arg f <| by ring) (congr_arg f <| by ring))
    _ = f x * f 2 + f (x + 2) := (zero_add _).trans <| eq_add_of_sub_eq (h x 2)

end Step6

/-! ## Step 7: Subcase 2.1: `f_ = 0` and `f(2) = 0 ≠ 3` -/


section Step7

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S] {f : R → S} (h : good f)
  (h0 : f (-1) = 0)

/-- If `f(2) = 0`, then `3 ∈ I` -/
theorem case2_1_lem1 (h1 : f 2 = 0) (x : R) : f (3 + x) = f x :=
  (congr_arg f <| add_rotate 2 1 x).trans <|
    (case2_map_add_two_eq h h0 _).trans <|
      (add_sub_cancel' 1 x).symm ▸ add_left_eq_self.mpr <| mul_eq_zero_of_left h1 _

section ThreeEqZero

variable (h1 : (3 : R) = 0)

/-- (7.1) -/
theorem case2_1_lem2 (x : R) : f x * f (x + 1) - f (x - 1) ^ 2 = f (x - 1) :=
  sub_eq_of_eq_add <|
    (eq_add_of_sub_eq <| case2_special_identity h h0 x).symm ▸
      (eq_neg_of_add_eq_zero_left h1).symm ▸
        sub_eq_add_neg x 1 ▸
          h0.symm ▸
            (mul_zero (f x)).symm ▸ sq (f (x - 1)) ▸ (zero_add (f (x - 1))).symm ▸ rfl

/-- (7.1) with `x` replaced by `x + 1` -/
theorem case2_1_lem3 (x : R) : f (x + 1) * f (x - 1) - f x ^ 2 = f x :=
  sub_eq_of_eq_add <|
    (sub_eq_add_neg x 1).symm ▸
      eq_neg_of_add_eq_zero_left h1 ▸
        add_assoc x 1 1 ▸
          (eq_add_of_sub_eq <| case2_1_lem2 h h0 h1 (x + 1)).trans ((add_sub_cancel x 1).symm ▸ rfl)

/-- (7.2) -/
theorem case2_1_lem4 (x : R) : f (x - 1) + f x + f (x + 1) = -1 ∨ f x = f (x - 1) :=
  by
  suffices (f (x - 1) + f x + f (x + 1) + 1) * (f x - f (x - 1)) = 0 from
    (mul_eq_zero.mp this).imp eq_neg_of_add_eq_zero_left eq_of_sub_eq_zero
  calc
    _ = f x * f (x + 1) - f (x - 1) ^ 2 - (f (x + 1) * f (x - 1) - f x ^ 2) - (f (x - 1) - f x) :=
      by ring
    _ = 0 :=
      sub_eq_zero_of_eq <| congr_arg₂ Sub.sub (case2_1_lem2 h h0 h1 x) (case2_1_lem3 h h0 h1 x)

/-- (7.3) -/
theorem case2_1_lem5 {c : R} (h2 : f (c + 1) = 0) (h3 : f (c - 1) = 0) : ∀ x, f (c + x) = f x :=
  let h4 : (2 : R) = -1 := eq_neg_of_add_eq_zero_left h1
  suffices ∀ x, f (x + 1 - (c - 1)) = f (x + 1 + (c + 1)) from λ x =>
    by
    let h5 := this (x - (c + 1) - 1)
    rwa [sub_add_cancel, sub_add_cancel, sub_sub, add_add_sub_cancel, ← two_mul, h4, neg_one_mul,
      sub_neg_eq_add, add_comm] at h5
  λ x =>
  (eq_of_sub_eq_zero <|
          (case2_good_alt h h0 (x + 1) (c - 1)).trans (mul_eq_zero_of_right _ h3)).symm.trans <|
    by
    let h5 : ∀ x y : R, f y = 0 → f (x * y + 1) = f (x + y) := λ x y h5 =>
      eq_of_sub_eq_zero <| (h x y).trans (mul_eq_zero_of_right _ h5)
    rw [← h5 _ _ h2, add_one_mul, add_sub_assoc, sub_sub, add_one_mul, add_assoc, add_assoc, ← bit0,
      h4, sub_neg_eq_add, ← sub_eq_add_neg, ← h5 _ _ h3, ← h5 _ _ h2, mul_right_comm]

end ThreeEqZero

section Quotient

variable (h1 : f 2 = 0) (h2 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) (h3 : f 0 = -1)

/-- (7.4) -/
theorem case2_1_lem6 (x : R) : f (x - 1) + f x + f (x + 1) = -1 :=
  by
  have h4 := h2 3 (case2_1_lem1 h h0 h1)
  have h5 := case2_1_lem4 h h0 h4
  refine' (h5 x).elim id λ h6 => _
  have h7 := h5 (x - 1)
  rw [sub_add_cancel, sub_sub, ← bit0, eq_neg_of_add_eq_zero_left h4, sub_neg_eq_add] at h7
  cases h7; exact (add_rotate _ _ _).symm.trans h7
  have h8 := case2_1_lem2 h h0 h4 x
  rw [← h7, h6, ← sq, sub_self, eq_comm] at h8
  have h9 := case2_1_lem5 h h0 h4 (h7.symm.trans h8) h8 0
  rw [add_zero, h6, h8, h3, zero_eq_neg] at h9
  exact absurd h9 one_ne_zero

variable (h4 : f 2 ≠ 3)

/-- (7.5) -/
theorem case2_1_lem7 (x : R) : f x = -1 ∨ f x = 0 :=
  by
  suffices 3 * ((f x + 1) * f x) = 0 from
    (mul_eq_zero.mp this).elim (λ h5 => False.elim <| h4 <| h1.trans h5.symm) λ this =>
      (mul_eq_zero.mp this).imp_left eq_neg_of_add_eq_zero_left
  have h5 := case2_1_lem6 h h0 h1 h2 h3 (x ^ 2)
  rw [case2_map_sq_sub_one h h0 h3 x, add_rotate, ← add_sub_assoc, sub_eq_neg_self] at h5
  nth_rw 1 [← sub_add_cancel (x ^ 2) (1 ^ 2)] at h5
  rw [sq_sub_sq, one_pow, eq_add_of_sub_eq (h _ _), sq, add_add_sub_cancel,
    eq_add_of_sub_eq (h _ _), ← two_mul] at h5
  have h6 := h2 3 (case2_1_lem1 h h0 h1)
  rw [eq_add_of_sub_eq (case2_1_lem3 h h0 h6 x), eq_neg_of_add_eq_zero_left h6, neg_one_mul,
    case2_map_even h h0] at h5
  rw [← h5]; ring

/-- (7.6) -/
theorem case2_1_lem8 (x : R) (h5 : f x = -1) : x = 0 :=
  by
  replace h4 := case2_1_lem7 h h0 h1 h2 h3 h4
  replace h3 := case2_1_lem6 h h0 h1 h2 h3 x
  rw [h5, add_right_comm, add_left_eq_self] at h3
  have h6 := eq_add_of_sub_eq' (case2_1_lem3 h h0 (h2 3 <| case2_1_lem1 h h0 h1) x)
  rw [sq, ← add_one_mul, mul_eq_zero_of_left (add_eq_zero_iff_eq_neg.mpr h5),
    eq_neg_of_add_eq_zero_left h3, mul_neg, neg_eq_zero, mul_self_eq_zero] at h6
  rw [h6, add_zero] at h3
  exact h2 x (case2_1_lem5 h h0 (h2 3 <| case2_1_lem1 h h0 h1) h6 h3)

/-- The main lemma for the subcase -/
theorem case2_1_lem9 (x : R) : x = 0 ∨ x = 1 ∨ x = -1 :=
  let h5 := case2_1_lem7 h h0 h1 h2 h3 h4
  let h6 := case2_1_lem8 h h0 h1 h2 h3 h4
  let h7 := h2 3 <| case2_1_lem1 h h0 h1
  (h5 x).imp (h6 x) λ h8 =>
    (h5 (x + 1)).symm.imp
      (λ h9 =>
        eq_of_sub_eq_zero <|
          h2 _ <|
            case2_1_lem5 h h0 h7 ((congr_arg f <| sub_add_cancel x 1).trans h8)
              ((sub_sub x 1 1).symm ▸
                (sub_eq_add_neg x 2).symm ▸ (neg_eq_of_add_eq_zero_right h7).symm ▸ h9))
      λ h9 => eq_neg_of_add_eq_zero_left <| h6 (x + 1) h9

/-- Solution for the current subcase (`𝔽₃_map2`) -/
theorem case21QuotIsAnswer : IsAnswer f :=
  have X : Bijective (𝔽₃.castHom <| h2 3 <| case2_1_lem1 h h0 h1) :=
    ⟨𝔽₃.castHom_injective _ (one_ne_zero_of_map_zero h h3), λ x =>
      (case2_1_lem9 h h0 h1 h2 h3 h4 x).elim (λ h5 => ⟨𝔽₃.𝔽₃0, h5.symm⟩) λ h5 =>
        h5.elim (λ h5 => ⟨𝔽₃.𝔽₃1, h5.symm⟩) λ h5 => ⟨𝔽₃.𝔽₃2, h5.symm⟩⟩
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₃Map2 S ∘ π from this.symm ▸ IsAnswer.𝔽₃_map2_comp π.toRingHom π.Surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <|
    funext λ x =>
      match x with
      | 𝔽₃.𝔽₃0 => h3
      | 𝔽₃.𝔽₃1 => good_map_one h
      | 𝔽₃.𝔽₃2 => h0

end Quotient

end Step7

/-! ## Step 8: Subcase 2.2: `f_ = 0` and `f(2) = 1 ≠ -1` -/


section Step8

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S] {f : R → S} (h : good f)
  (h0 : f (-1) = 0) (h1 : f 2 = 1)

/-- (8.1) -/
theorem case2_2_lem1 (x : R) : f (x + 2) + f x = f (x + 1) + f (x - 1) :=
  (case2_map_add_two_eq h h0 x).symm ▸
    h1.symm ▸ (one_mul (f (x + 1) - f x)).symm ▸ (add_assoc _ _ _).trans (sub_add_add_cancel _ _ _)

/-- `4 ∈ I` -/
theorem case2_2_lem2 (x : R) : f (4 + x) = f x :=
  by
  have h2 := case2_2_lem1 h h0 h1
  have h3 := (h2 (x + 1 + 1)).symm
  rw [add_sub_cancel, add_assoc, ← bit0, h2, add_sub_cancel, add_comm] at h3
  refine' ((add_left_injective _ h3).trans <| congr_arg f (-1)).symm
  rw [add_assoc x, ← bit0, add_assoc, ← bit0, add_comm]

variable (h2 : f 2 ≠ -1)

theorem case2_2_lem3 (x : R) : f (2 * x + 1) = 0 :=
  by
  have h3 := eq_add_of_sub_eq' (h x 2)
  rw [h1, mul_one, case2_2_lem1 h h0 h1] at h3
  have h4 := eq_add_of_sub_eq' (h (x - 1) 2)
  rw [h1, mul_one, bit0, sub_add_add_cancel, ← h3, ← bit0] at h4
  have h5 := eq_add_of_sub_eq (case2_good_alt h h0 (x * 2 + 1) 2)
  rw [h1, mul_one, add_sub_right_comm, ← sub_one_mul, h4, add_one_mul, add_sub_assoc, bit0,
    add_sub_cancel, ← bit0, mul_rotate, two_mul, ← bit0, mul_comm x 2,
    period_imp_quasi_period h (case2_2_lem2 h h0 h1), ← two_mul, zero_eq_mul] at h5
  exact h5.resolve_left λ h5 => h2 <| h1.trans <| eq_neg_of_add_eq_zero_left h5

theorem case2_2_lem4 : f 0 = -1 :=
  Not.imp_symm (eq_zero_of_map_zero_ne_neg_one h) λ h3 =>
    one_ne_zero' S <| h1.symm.trans <| congr_fun h3 2

/-- The main lemma for the subcase -/
theorem case2_2_lem5 (h3 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) (x : R) :
    (x = 0 ∨ x = 2) ∨ x = 1 ∨ x = -1 :=
  suffices (x = 0 ∨ x = 2) ∨ x = 1 ∨ x = 2 + 1 from
    this.imp_right <|
      Or.imp_right λ this =>
        this.trans <|
          eq_neg_of_add_eq_zero_left <| (add_assoc _ _ _).trans <| h3 _ <| case2_2_lem2 h h0 h1
  let h4 : f 0 = -1 := case2_2_lem4 h h0 h1 h2
  cases_of_nonperiod_quasi_period h h3 h4 (case2_2_lem3 h h0 h1 h2)
    (λ h5 => h2 <| (congr_arg f h5).trans h4) x

/-- Solution for the current subcase (`ℤ₄_map`) -/
theorem case22QuotIsAnswer (h3 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) : IsAnswer f :=
  have X : Bijective (ℤ₄.castHom <| h3 4 <| case2_2_lem2 h h0 h1) :=
    ⟨ℤ₄.castHom_injective _ λ h4 => h2 <| (congr_arg f h4).trans <| case2_2_lem4 h h0 h1 h2,
      λ x =>
      (case2_2_lem5 h h0 h1 h2 h3 x).elim
        (λ h5 => h5.elim (λ h5 => ⟨0, h5.symm⟩) λ h5 => ⟨2, h5.symm⟩) λ h5 =>
        h5.elim (λ h5 => ⟨1, h5.symm⟩) λ h5 => ⟨3, h5.symm⟩⟩
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = ℤ₄Map S ∘ π from this.symm ▸ IsAnswer.ℤ₄_map_comp π.toRingHom π.Surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <|
    funext λ x =>
      match x with
      | ℤ₄.ℤ₄0 => case2_2_lem4 h h0 h1 h2
      | ℤ₄.ℤ₄1 => good_map_one h
      | ℤ₄.ℤ₄2 => h1
      | ℤ₄.ℤ₄3 => h0

end Step8

/-! ## Step 9: Subcase 2.3: `f_ = 0` and `f(2) = 3 ≠ 1` -/


section Step9Domain

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S] {f : R → S} (h : good f)
  (h0 : f (-1) = 0)

/-- A copy of `case2_1_lem6` (7.4) from Subcase 2.1,
  without quotienting by the "period ideal". -/
theorem case2_1_lem6_nonquotient (h1 : f 2 = 0) (h2 : f 0 = -1) (x : R) :
    f (x - 1) + f x + f (x + 1) = -1 :=
  let X :=
    case2_1_lem6 (periodLift_is_good h) h0 h1 (zero_of_periodic_periodLift h) h2
      (Ideal.Quotient.mk _ x)
  X

variable (h1 : f 2 = 3)

/-- (9.1) -/
theorem case2_3_lem1 (x : R) : f (x + 2) = 3 * (f (x + 1) - f x) + f (x - 1) :=
  h1 ▸ case2_map_add_two_eq h h0 x

/-- (9.2) -/
theorem case2_3_lem2 (x : R) :
    f x * (3 * f (x - 1) + f (x + 1)) - (f (x - 1) + 3 * f (x + 1)) * (1 + f (x - 1)) = 0 :=
  sub_eq_zero_of_eq (case2_special_identity h h0 x) ▸
    h1.symm ▸ (case2_3_lem1 h h0 h1 x).symm ▸ by ring

/-- (9.3) -/
theorem case2_3_lem3 (x : R) : f (x + 1) + f (x - 1) = 2 * f x + 2 ∨ f (x + 1) = f (x - 1) :=
  by
  suffices (f (x + 1) + f (x - 1) - (2 * f x + 2)) * (f (x + 1) - f (x - 1)) = 0 from
    (mul_eq_zero.mp this).imp eq_of_sub_eq_zero eq_of_sub_eq_zero
  have X := case2_map_even h h0
  have X0 := case2_3_lem2 h h0 h1
  have h2 := X0 (-x)
  rw [X, ← neg_add', X, neg_add_eq_sub, ← neg_sub x, X] at h2
  refine' Eq.trans _ ((congr_arg₂ Sub.sub (X0 x) h2).trans <| sub_zero _)
  ring

/-- (9.4) -/
theorem case2_3_lem4 (h2 : f 2 ≠ 1) (x : R) :
    f (x + 1) + f (x - 1) = 2 * f x + 2 ∨ f (x + 1) = 0 ∧ f (x - 1) = 0 :=
  let X := case2_3_lem3 h h0 h1
  (X x).imp_right λ h3 =>
    by
    suffices f (x - 1) = 0 from ⟨h3.trans this, this⟩
    have h4 := case2_3_lem2 h h0 h1 x
    rw [h3, sub_eq_zero, add_comm, ← one_add_mul, mul_comm, mul_eq_mul_left_iff, mul_eq_zero, bit1,
      add_left_comm] at h4
    have h5 : (2 : S) + 2 ≠ 0 := by
      rw [← two_mul, mul_self_ne_zero] <;> exact add_left_ne_self.mp (h1.symm.trans_ne h2)
    revert h4 <;> refine' λ h4 => (h4.resolve_left _).resolve_left h5
    intro h4
    have h6 := case2_3_lem1 h h0 h1 x
    rw [h3, ← sub_eq_of_eq_add' h4, sub_sub_cancel_left, mul_neg_one, neg_add_eq_sub, sub_sub, bit1,
      add_left_comm, ← bit0] at h6
    have h7 := X (x + 1)
    rw [add_sub_cancel, add_assoc, ← bit0, h6] at h7
    refine' h5 (h7.elim (λ h7 => _) sub_eq_self.mp)
    rwa [← add_sub_right_comm, h3, ← two_mul, ← mul_add_one, ← h4.trans (add_comm _ _),
      sub_eq_self] at h7

/-- (9.5) -/
theorem case2_3_lem5 (h2 : f 2 ≠ 1) (x : R) :
    f (x + 1) + f (x - 1) = 2 * f x + 2 ∨ f x = 0 ∧ f (x + 1) = 0 ∧ f (x - 1) = 0 :=
  let X := case2_3_lem4 h h0 h1 h2
  (X x).elim Or.inl λ h3 =>
    (X (x + 1)).imp
      (λ h4 =>
        eq_add_of_sub_eq' <|
          (eq_of_sub_eq_zero <| by
                  rw [add_sub_cancel, add_assoc, ← bit0, case2_3_lem1 h h0 h1] <;>
                    ring).symm.trans <|
            sub_eq_of_eq_add' h4)
      λ h4 => ⟨add_sub_cancel x 1 ▸ h4.2, h3⟩

/-- (9.6) Very slow, but... well it works -/
theorem case2_3_lem6 (h2 : f 2 ≠ 1) (h3 : f 0 = -1) (x : R) : f (x + 1) + f (x - 1) = 2 * f x + 2 :=
  let X := case2_3_lem5 h h0 h1 h2
  (X x).resolve_right λ h4 =>
    (em <| f 2 = 0).elim
      (---- Case 1: `char(S) = 3` (borrows case2_1_lem6 i.e. (7.4) from Subcase 2.1)
      λ h5 =>
        absurd (case2_1_lem6_nonquotient h h0 h5 h3 x) <|
          h4.1.symm ▸
            h4.2.1.symm ▸
              h4.2.2.symm ▸
                (add_zero (0 : S)).symm ▸
                  (add_zero (0 : S)).symm ▸ λ h6 =>
                    one_ne_zero' S <| zero_eq_neg.mp h6)---- Case 2: `char(S) ≠ 3`
    λ h5 => by
      let X0 := add_left_ne_self.mp (h1.symm.trans_ne h2)
      suffices f (2 * x) = -3 from
        (---- First reduce to `f(2x) = -3`
                X
                (2 * x)).symm.elim
          (λ h6 => absurd (this.symm.trans h6.1) <| neg_ne_zero.mpr <| h1.symm.trans_ne h5)
          λ h6 => by
          have h7 := eq_add_of_sub_eq (h 2 (x - 1))
          rw [h4.2.2, mul_zero, zero_add, mul_sub_one, bit0, add_add_sub_cancel, ←
            sub_sub, sub_add_cancel, ← bit0, add_comm, h4.2.1] at h7
          have h8 := eq_add_of_sub_eq (case2_good_alt h h0 (x + 1) 2)
          rw [h4.2.1, zero_mul, zero_add, bit0, add_sub_add_right_eq_sub, add_one_mul,
            ← add_assoc, add_sub_cancel, ← bit0, mul_comm, h4.2.2] at h8
          rw [h7, h8, add_zero, this, ← mul_add_one, bit1, neg_add, neg_add_cancel_right, mul_neg,
            zero_eq_neg, mul_self_eq_zero] at h6
          exact X0 h6
      ---- Now prove that `f(2x) = -3`
      suffices 2 * (f (2 * x) + 3) = 0 from
        eq_neg_of_add_eq_zero_left <| (mul_eq_zero.mp this).resolve_left X0
      have h6 := eq_add_of_sub_eq (case2_good_alt h h0 (x + 1) (x - 1))
      rw [← sq_sub_sq, one_pow, add_sub_sub_cancel, h4.2.1, zero_mul, zero_add, ← bit0,
        h1] at h6
      have h7 := eq_add_of_sub_eq (case2_good_alt h h0 x x)
      rw [← sq, h4.1, zero_mul, zero_add, sub_self, h3] at h7
      have h8 := eq_add_of_sub_eq (h (x + 1) (x - 1))
      rw [← sq_sub_sq, one_pow, h4.2.1, zero_mul, zero_add, add_add_sub_cancel] at h8
      have h9 := case2_3_lem1 h h0 h1 (x ^ 2 - 1)
      rw [h8, h7, h6, sq, bit0, sub_add_add_cancel, eq_add_of_sub_eq (h x x), h4.1,
        zero_mul, zero_add, ← two_mul, eq_comm, ← sub_eq_zero] at h9
      rw [← h9]; ring

end Step9Domain

section Step9Field

variable {R S : Type _} [CommRing R] [Field S]

def homGuess (f : R → S) (x : R) :=
  (f x - f (x - 1) + 1) / 2

variable {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 2 = 3) (h2 : f 2 ≠ 1) (h3 : f 0 = -1)

/-- (9.g1) -/
theorem case2_3_lem_g1 : homGuess f 0 = 0 :=
  div_eq_zero_iff.mpr <|
    Or.inl <|
      h3.symm ▸ (zero_sub (1 : R)).symm ▸ h0.symm ▸ (sub_zero (-1 : S)).symm ▸ neg_add_self 1

/-- (9.g2) -/
theorem case2_3_lem_g2 (x : R) : homGuess f (x + 1) = homGuess f x + 1 :=
  by
  let X : (2 : S) ≠ 0 := add_left_ne_self.mp (h1.symm.trans_ne h2)
  rw [hom_guess, hom_guess, div_eq_iff X, add_one_mul, div_mul_cancel _ X, add_right_comm,
      add_left_inj, add_sub_cancel, sub_eq_iff_eq_add', ← add_sub_right_comm, ← add_sub_assoc,
      eq_sub_iff_add_eq, ← add_assoc, ← two_mul] <;>
    exact case2_3_lem6 h h0 h1 h2 h3 x

/-- Variant of (9.g2) -/
theorem case2_3_lem_g2' (x : R) : homGuess f (x - 1) = homGuess f x - 1 :=
  eq_sub_of_add_eq <|
    (case2_3_lem_g2 h h0 h1 h2 h3 _).symm.trans <| congr_arg _ <| sub_add_cancel x 1

/-- (9.g3) -/
theorem case2_3_lem_g3 (x : R) : homGuess f (-x) = -homGuess f x :=
  by
  suffices f (-x) - f (-x - 1) + 1 = -(f x - f (x - 1) + 1) from
    (congr_arg (· / (2 : S)) this).trans <| neg_div _ _
  let X := case2_map_even h h0
  rw [X, ← neg_add', X, eq_neg_iff_add_eq_zero, add_add_add_comm, sub_add_sub_comm, ← two_mul, ←
      bit0, ← add_sub_right_comm, sub_eq_zero] <;>
    exact (case2_3_lem6 h h0 h1 h2 h3 x).symm

/-- (9.g4) -/
theorem case2_3_lem_g4 (x : R) : f x = homGuess f x ^ 2 - 1 :=
  by
  have X : (2 : S) ≠ 0 := add_left_ne_self.mp (h1.symm.trans_ne h2)
  have X0 : (2 : S) ^ 2 ≠ 0 := pow_ne_zero 2 X
  rw [hom_guess, div_pow, div_sub_one X0, eq_div_iff X0]
  refine' mul_left_cancel₀ X (eq_of_sub_eq_zero _).symm
  rw [← case2_3_lem2 h h0 h1 x, eq_sub_of_add_eq (case2_3_lem6 h h0 h1 h2 h3 x)]
  ring

/-- (9.g5) -/
theorem case2_3_lem_g5 (x y : R) :
    (homGuess f (x * y) + 1) ^ 2 - homGuess f (x + y) ^ 2 =
      (homGuess f x ^ 2 - 1) * (homGuess f y ^ 2 - 1) :=
  by
  let h4 := case2_3_lem_g4 h h0 h1 h2 h3
  let h5 := h x y
  rwa [h4, h4, h4, h4, sub_sub_sub_cancel_right, case2_3_lem_g2 h h0 h1 h2 h3] at h5

/-- (9.g6) -/
theorem case2_3_lem_g6 (x y : R) :
    (homGuess f (x * y) - 1) ^ 2 - homGuess f (x - y) ^ 2 =
      (homGuess f x ^ 2 - 1) * (homGuess f y ^ 2 - 1) :=
  by
  let h4 := case2_3_lem_g4 h h0 h1 h2 h3
  let h5 := case2_good_alt h h0 x y
  rwa [h4, h4, h4, h4, sub_sub_sub_cancel_right, case2_3_lem_g2' h h0 h1 h2 h3] at h5

/-- (9.g7) -/
theorem case2_3_lem_g7 (x y : R) :
    2 ^ 2 * homGuess f (x * y) = homGuess f (x + y) ^ 2 - homGuess f (x - y) ^ 2 := by
  calc
    _ = (hom_guess f (x * y) + 1) ^ 2 - (hom_guess f (x * y) - 1) ^ 2 := by ring
    _ = hom_guess f (x + y) ^ 2 - hom_guess f (x - y) ^ 2 :=
      sub_eq_sub_iff_sub_eq_sub.mp <|
        (case2_3_lem_g5 h h0 h1 h2 h3 x y).trans (case2_3_lem_g6 h h0 h1 h2 h3 x y).symm

/-- (9.g8) -/
theorem case2_3_lem_g8 (x y : R) :
    (homGuess f (x + y) ^ 2 - homGuess f (x - y) ^ 2) ^ 2 + 2 ^ 4 =
      2 ^ 3 * (homGuess f (x + y) ^ 2 + homGuess f (x - y) ^ 2) +
        (2 ^ 2) ^ 2 * ((homGuess f x ^ 2 - 1) * (homGuess f y ^ 2 - 1)) :=
  by
  rw [← case2_3_lem_g5 h h0 h1 h2 h3, mul_sub, ← mul_pow, mul_add_one,
      case2_3_lem_g7 h h0 h1 h2 h3] <;>
    ring

theorem case2_3_lem_g9 (x y : R) :
    homGuess f (x + y) + homGuess f (x - y) = 2 * homGuess f x ∨
      homGuess f (x + y) + homGuess f (x - y) = -(2 * homGuess f x) :=
  let X : (2 : S) ≠ 0 := add_left_ne_self.mp (h1.symm.trans_ne h2)
  sq_eq_sq_iff_eq_or_eq_neg.mp <|
    mul_left_cancel₀ (pow_ne_zero 3 X) <|
      by
      have h4 := case2_3_lem_g2 h h0 h1 h2 h3
      have h5 := case2_3_lem_g2' h h0 h1 h2 h3
      have h6 := case2_3_lem_g8 h h0 h1 h2 h3 x
      have h7 :=
        congr_arg₂ Sub.sub (congr_arg₂ Add.add (h6 (y + 1)) (h6 (y - 1)))
          (congr_arg (Mul.mul (2 : S)) (h6 y))
      rw [← add_assoc x, h4, ← sub_sub x, h5, ← add_sub_assoc x, h5, ← sub_add x, h4, h4, h5] at h7
      rw [← sub_eq_zero, ← sub_eq_zero_of_eq h7]
      ring

/-- (9.g9) -/
theorem case2_3_lem_g10 (x y : R) : homGuess f (x + y) + homGuess f (x - y) = 2 * homGuess f x :=
  let X := case2_3_lem_g9 h h0 h1 h2 h3
  (X x y).elim id λ h4 => by
    have X0 := case2_3_lem_g2 h h0 h1 h2 h3
    have h5 := X (x + 1) y
    rw [add_right_comm, X0, add_sub_right_comm, X0, add_add_add_comm, X0, mul_add_one, ← bit0] at h5
    cases h5; exact add_left_injective _ h5
    rw [h4, neg_add, add_right_inj, eq_neg_iff_add_eq_zero, ← two_mul, mul_self_eq_zero] at h5
    exact absurd h5 (add_left_ne_self.mp <| h1.symm.trans_ne h2)

theorem case2_3_lem_g_mul (x y : R) : homGuess f (x * y) = homGuess f x * homGuess f y :=
  mul_left_cancel₀ (pow_ne_zero 2 <| add_left_ne_self.mp <| h1.symm.trans_ne h2) <|
    let h4 := case2_3_lem_g10 h h0 h1 h2 h3
    (case2_3_lem_g7 h h0 h1 h2 h3 x y).trans <|
      (sq_sub_sq _ _).trans <|
        suffices homGuess f (x + y) - homGuess f (x - y) = 2 * homGuess f y from
          (congr_arg₂ _ (h4 x y) this).trans <| (sq (2 : S)).symm ▸ mul_mul_mul_comm _ _ _ _
        neg_sub y x ▸
          (case2_3_lem_g3 h h0 h1 h2 h3 (y - x)).symm ▸
            add_comm y x ▸ (sub_neg_eq_add _ _).trans (h4 y x)

theorem case2_3_lem_g_one : homGuess f 1 = 1 :=
  zero_add (1 : R) ▸ (case2_3_lem_g2 h h0 h1 h2 h3 _).trans <|
    (congr_arg (· + (1 : S)) <| case2_3_lem_g1 h h0 h1 h2 h3).trans (zero_add 1)

theorem case2_3_lem_g_add (x y : R) : homGuess f (x + y) = homGuess f x + homGuess f y :=
  by
  have h4 := case2_3_lem_g_mul h h0 h1 h2 h3 2
  rw [bit0, case2_3_lem_g2 h h0 h1 h2 h3, case2_3_lem_g_one h h0 h1 h2 h3, ← bit0, ← bit0] at h4
  have h5 := case2_3_lem_g10 h h0 h1 h2 h3 (x + y) (x - y)
  rw [add_add_sub_cancel, ← two_mul, h4, add_sub_sub_cancel, ← two_mul, h4, ← mul_add] at h5
  exact mul_left_cancel₀ (add_left_ne_self.mp <| h1.symm.trans_ne h2) h5.symm

theorem case2_3_sol : ∃ φ : R →+* S, f = λ x => φ x ^ 2 - 1 :=
  ⟨⟨homGuess f, case2_3_lem_g_one h h0 h1 h2 h3, case2_3_lem_g_mul h h0 h1 h2 h3,
      case2_3_lem_g1 h h0 h1 h2 h3, case2_3_lem_g_add h h0 h1 h2 h3⟩,
    funext <| case2_3_lem_g4 h h0 h1 h2 h3⟩

/-- Solution for the current subcase (`hom_sq_sub_one: x ↦ φ(x)^2 - 1`) -/
theorem case23IsAnswer : IsAnswer f :=
  Exists.elim (case2_3_sol h h0 h1 h2 h3) λ φ h4 => h4.symm ▸ IsAnswer.hom_sq_sub_one φ

end Step9Field

/-! ## Step 10: Subcase 2.3: `f_ = 0` and `f(2) = -1` -/


section Step10

namespace Char2

variable {R : Type _} [CommRing R] (h : (2 : R) = 0)

theorem add_self (x : R) : x + x = 0 :=
  (two_mul x).symm.trans (mul_eq_zero_of_left h x)

theorem add_add_cancel (x y : R) : x + y + y = x :=
  (add_assoc x y y).trans <| (congr_arg (Add.add x) (add_self h y)).trans (add_zero x)

theorem sub_eq_add (x y : R) : x - y = x + y :=
  sub_eq_of_eq_add (add_add_cancel h x y).symm

theorem add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  (add_sq' x y).trans <|
    (congr_arg (Add.add _) <| mul_eq_zero_of_left (mul_eq_zero_of_left h x) y).trans (add_zero _)

theorem add_one_sq (x : R) : (x + 1) ^ 2 = x ^ 2 + 1 :=
  (add_sq h x 1).trans <| congr_arg (Add.add <| x ^ 2) (one_pow 2)

theorem add_eq_iff_eq_add {x y z : R} : x + y = z ↔ x = z + y :=
  sub_eq_add h x y ▸ sub_eq_iff_eq_add

theorem add_eq_iff_eq_add' {x y z : R} : x + y = z ↔ x = y + z :=
  sub_eq_add h x y ▸ sub_eq_iff_eq_add'

theorem add_eq_zero_iff_eq {x y : R} : x + y = 0 ↔ x = y :=
  (add_eq_iff_eq_add h).trans <| by rw [zero_add]

theorem add_pow_four (x y : R) : (x + y) ^ 4 = x ^ 4 + y ^ 4 := by
  rw [bit0, ← two_mul, pow_mul, pow_mul, pow_mul, add_sq h, add_sq h]

theorem add_one_pow_four (x : R) : (x + 1) ^ 4 = x ^ 4 + 1 :=
  (add_pow_four h x 1).trans <| congr_arg (Add.add <| x ^ 4) (one_pow 4)

end Char2

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S] {f : R → S} (h : good f)

/-- `2 ∈ I` -/
theorem case2_4_lem1 (h0 : f (-1) = 0) (h1 : f 2 = -1) : ∀ x, f (2 + x) = f x :=
  suffices ∀ x, f (x + 1) = f (x - 1) from λ x =>
    add_rotate x 1 1 ▸ (this (x + 1)).trans <| congr_arg f (add_sub_cancel x 1)
  ---- First assume an intermediate statement
  suffices ∀ x, f (x + 1) = f (x - 1) ∨ f x + f (x - 1) = -1 from λ x =>
    (this x).elim id λ h2 => by
      have h3 := this (-x)
      have h4 := case2_map_even h h0
      rw [h4, neg_add_eq_sub, ← neg_sub, h4, ← neg_add', h4] at h3
      exact h3.elim Eq.symm λ h3 => add_right_injective (f x) <| h3.trans h2.symm
  ---- Now prove the intermediate statement
λ x =>
  by
  suffices (f (x + 1) - f (x - 1)) * (f x + f (x - 1) + 1) = 0 from
    (mul_eq_zero.mp this).imp eq_of_sub_eq_zero eq_neg_of_add_eq_zero_left
  rw [← sub_eq_zero_of_eq (case2_special_identity h h0 x), case2_map_add_two_eq h h0 x, h1] <;> ring

section Rchar2

variable (h0 : (2 : R) = 0)

theorem case2_4_lem2 : f (-1) = 0 :=
  eq_neg_of_add_eq_zero_left h0 ▸ good_map_one h

/-- (10.1) -/
theorem case2_4_lem3 (x : R) : f (x * (x + 1) + 1) = f x * f (x + 1) :=
  Char2.sub_eq_add h0 (x * (x + 1)) 1 ▸ case2_map_self_mul_add_one_sub_one h (case2_4_lem2 h h0) x

variable (h1 : f 0 = -1)

/-- (10.2) -/
theorem case2_4_lem4 (x : R) : f (x ^ 2 + 1) = f x ^ 2 - 1 :=
  Char2.sub_eq_add h0 (x ^ 2) 1 ▸ case2_map_sq_sub_one h (case2_4_lem2 h h0) h1 x

/-- (10.3) -/
theorem case2_4_lem5 (x : R) : f (x ^ 2) = f (x + 1) ^ 2 - 1 :=
  (congr_arg₂ _ (Char2.add_one_sq h0 x) rfl).trans (Char2.add_add_cancel h0 (x ^ 2) 1) ▸
    case2_4_lem4 h h0 h1 (x + 1)

theorem case2_4_lem6 : ∀ x, f x ^ 2 + f (x + 1) ^ 2 = 1 ∨ f x + f (x + 1) = 1 :=
  let h3 := case2_4_lem3 h h0
  let h4 := case2_4_lem5 h h0 h1
  ---- (10.L1.1)
  have h5 : ∀ x, (f (x + 1) ^ 2 - 1) * (f (x + 1) - 1) + f x * f (x + 1) = f x * f (x * (x + 1)) :=
    λ x => by
    rw [← h3, ← h4, ← h, eq_sub_iff_add_eq, add_right_comm, ← eq_sub_iff_add_eq, ← mul_assoc,
      mul_add_one, ← sq, add_left_comm, char2.add_self h0, add_zero, ← mul_add_one, sub_add_cancel,
      add_assoc, h]
  ---- Assuming the lemma + possibility of `f(x + 1) = f(x)`
λ x =>
  by
  suffices (f x ^ 2 + f (x + 1) ^ 2 = 1 ∨ f x + f (x + 1) = 1) ∨ f x = f (x + 1) from
    this.elim id λ h6 =>
      Or.inr <| by
        rw [← h6, ← two_mul, eq_comm]
        have h7 := case2_4_lem4 h h0 h1
        have h8 := h7 (x * (x + 1))
        rw [mul_pow, char2.add_one_sq h0, h3, h4, h7] at h8
        replace h8 := sub_eq_zero_of_eq (congr_arg₂ Mul.mul (rfl : f x ^ 2 = f x ^ 2) h8)
        rw [mul_sub_one (f x ^ 2), ← mul_pow, ← h5, ← h6] at h8
        replace h8 : (1 - 2 * f x) * (f x ^ 2 - 1) = 0 := h8 ▸ by ring
        rw [mul_eq_zero] at h8 ; refine' h8.elim eq_of_sub_eq_zero λ h8 => _
        refine' absurd (h5 (x ^ 2)) _
        rw [h7, h4, ← h6, h8, sq, zero_mul, zero_mul, add_zero, zero_sub,
          ← sq, neg_one_sq]
        exact one_ne_zero' S
  ---- Proving the lemma + possibility of `f(x + 1) = f(x)`
  suffices (f x ^ 2 + f (x + 1) ^ 2 - 1) * (f x + f (x + 1) - 1) * (f x - f (x + 1)) = 0 from
    (mul_eq_zero.mp this).imp
      (λ this => (mul_eq_zero.mp this).imp eq_of_sub_eq_zero eq_of_sub_eq_zero) eq_of_sub_eq_zero
  have h6 := congr_arg (Mul.mul <| f x) (h5 (x + 1))
  rw [char2.add_add_cancel h0, mul_left_comm, mul_comm (x + 1), ← h5] at h6
  rw [← sub_eq_zero_of_eq h6]; ring

/-- Solution for the current sub-subcase (`hom_sub_one: x ↦ φ(x) - 1`) -/
theorem case24Schar2QuotIsAnswer (h3 : (2 : S) = 0) : IsAnswer f :=
  isAnswerOfAddOneAdditive h h1 λ x y => ---- (10.L2.1)
  by
    have h4 : ∀ x, f (x + 1) = f x + 1 := λ x =>
      (Char2.add_eq_iff_eq_add' h3).mp <|
        (add_comm _ _).trans <|
          (case2_4_lem6 h h0 h1 x).symm.elim id λ h4 =>
            (sq_eq_one_iff.mp <| (Char2.add_sq h3 _ _).trans h4).elim id λ h5 =>
              h5.trans <| neg_eq_of_add_eq_zero_left h3
    ---- (10.L2.2)
    have h5 : ∀ x y, f (x * y) = f x * f y + f (x + y) + 1 := λ x y =>
      (Char2.add_eq_iff_eq_add h3).mp ((h4 _).symm.trans <| eq_add_of_sub_eq <| h x y)
    ---- Back to the main equality
    let a := f x
    let b := f y
    let c := f (x + y)
    have h6 := h5 (x * y) ((y + 1) * (x + 1))
    rw [mul_mul_mul_comm, h5, add_left_inj] at h6
    have h7 : x * y + (y + 1) * (x + 1) = x * (y + 1) + y * (x + 1) + 1 := by ring
    rw [h7, h4, ← add_assoc, ← sub_eq_iff_eq_add', add_sub_add_right_eq_sub] at h6
    replace h7 : f (x * y) = a * b + c + 1 := h5 x y
    have h8 : f (x * (y + 1)) = a * (b + 1) + (c + 1) + 1 := by rw [h5, ← add_assoc, h4, h4]
    have h9 : f (y * (x + 1)) = b * (a + 1) + (c + 1) + 1 := by
      rw [h5, add_left_comm, ← add_assoc, h4, h4]
    have h10 : f ((y + 1) * (x + 1)) = (b + 1) * (a + 1) + c + 1 := by
      rw [h5, add_add_add_comm, ← bit0, h0, add_zero, add_comm y x, h4, h4]
    replace h6 := (congr_arg₂ _ (congr_arg₂ _ h8 h9) (congr_arg₂ _ h7 h10)).symm.trans h6
    rw [← sub_eq_iff_eq_add', ← h6, eq_comm, ← sub_eq_zero]
    refine' Eq.trans _ (mul_eq_zero_of_left h3 <| (a + 1) * (b + 1))
    ring

variable (h2 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) (h3 : (2 : S) ≠ 0)

theorem case2_4_lem7 (x : R) : f x * f (x + 1) = 0 ∨ f x + f (x + 1) = 1 ∧ f x * f (x + 1) = -1 :=
  by
  suffices---- Reduce the condition to `2 f(x)^2 f(x + 1)^2 (f(x)^2 + f(x + 1)^2 - 3) = 0`
          2 *
          (f x * f (x + 1)) ^ 2 *
        (f x ^ 2 + f (x + 1) ^ 2 - 3) =
      0
    from
    (mul_eq_zero.mp this).imp (λ h4 => sq_eq_zero_iff.mp <| (mul_eq_zero.mp h4).resolve_left h3)
      λ h4 =>
      let h5 := eq_of_sub_eq_zero h4
      let h6 :=
        (case2_4_lem6 h h0 h1 x).resolve_left <|
          (eq_of_sub_eq_zero h4).trans_ne <| add_left_ne_self.mpr h3
      ⟨h6, by
        let h7 := add_sq' (f x) (f (x + 1))
        rwa [h5, h6, one_pow, bit1, add_right_comm, self_eq_add_left, mul_assoc, ← mul_one_add,
          mul_eq_zero, or_iff_right h3, add_eq_zero_iff_neg_eq, eq_comm] at h7 ⟩
  ---- Prove the above equality
  have h4 : ∀ x, f (x ^ 4) = (f x ^ 2 - 1) ^ 2 - 1 := λ x => by
    rw [bit0, ← two_mul, pow_mul, case2_4_lem5 h h0 h1, case2_4_lem4 h h0 h1]
  have h5 := case2_4_lem3 h h0
  have h6 := char2.add_one_pow_four h0
  have h7 := h4 (x * (x + 1) + 1)
  rw [h5, h6, mul_pow, h6, h5, h4, ← h6, h4, eq_comm, ← sub_eq_zero] at h7
  rw [← h7]; ring

/-- This lemma's proof implementation is too slow... at least 0.7s.
  It should be optimized or broken down into more lemmas.
  Or, you could give a simpler proof. -/
theorem case2_4_lem8 (c : R) (h4 : f c = -1) : c = 0 :=
  by
  have
    h5 :---- (10.L3.1)
    ∀ x, f x = -1 → f (x + 1) = 0 :=
    λ x h5 =>
    let X : (1 : S) ≠ 0 := one_ne_zero' S
    (case2_4_lem7 h h0 h1 h2 h3 x).elim
      (λ h6 => (mul_eq_zero.mp h6).resolve_left <| h5.trans_ne <| neg_ne_zero.mpr X) λ h6 => by
      rw [h5, neg_one_mul, neg_inj, neg_add_eq_iff_eq_add] at h6  <;>
        exact absurd (h6.1.symm.trans h6.2) (add_right_ne_self.mpr X)
  ---- (10.L3.2)
  have h6 : ∀ c, f c = -1 → ∀ x, f (c ^ 2 + c * x + 1) = -f (c * x + 1) := λ c h6 x => by
    rw [eq_add_of_sub_eq (h c _), sq, ← mul_add, eq_add_of_sub_eq (h c _), h6, ← add_assoc,
        char2.add_self h0, zero_add] <;>
      ring
  ---- The main problem
  have X := char2.add_sq h0
  have X0 := case2_4_lem5 h h0 h1
  -- Reduce to `c^4 = 0`
  have h7 := X0 c
  rw [h5 c h4, zero_pow (Nat.succ_pos 1), zero_sub] at h7
  suffices h8 : (c ^ 2) ^ 2 = 0
  · suffices h9 : ∀ c, f c = -1 → c ^ 2 = 0 → c = 0
    exact h9 c h4 (h9 _ h7 h8)
    intro d h9 h10
    refine' h2 d ((period_iff h).mpr ⟨(quasi_period_iff h).mpr λ x => _, h9.trans h1.symm⟩)
    have h11 := h6 d h9 x
    rw [h10, zero_add, eq_neg_iff_add_eq_zero, ← two_mul, mul_eq_zero] at h11
    exact h11.resolve_left h3
  -- Get `c^6 + c^4 = 0`
  have h8 : ∀ x, f ((c ^ 2) ^ 2 + c ^ 2 + c ^ 2 * x + 1) = f (c ^ 2 * x + 1) := λ x => by
    rw [add_assoc ((c ^ 2) ^ 2), ← mul_one_add, h6 _ h7, mul_one_add, sq, mul_assoc, ← sq, h6 _ h4,
      neg_neg]
  have h9 : f (c + 1) = 0 := h5 c h4
  have h10 : f (c ^ 2 + c + 1) = 0 := by
    rw [sq, ← mul_add_one, case2_4_lem3 h h0, h9, mul_zero]
  replace h8 : ∀ x, f (((c ^ 2) ^ 2 + c ^ 2) * c ^ 2 * x + 1) = 0 :=
    by
    suffices f ((c ^ 2) ^ 2 + c ^ 2) = -1 from λ x => by
      rw [mul_assoc, mul_left_comm, ← h8, mul_left_comm, ← mul_one_add, add_comm (1 : R),
        eq_add_of_sub_eq (h _ _), this, neg_one_mul, ← add_assoc, h8, neg_add_self]
    rw [← X, X0, h10, sq, zero_mul, zero_sub]
  replace h8 : ((c ^ 2) ^ 2 + c ^ 2) * c ^ 2 = 0 :=
    h2 _
      ((period_iff h).mpr
        ⟨(quasi_period_iff h).mpr h8, by
          rwa [← X, ← mul_pow, X0, h1, sub_eq_neg_self, sq_eq_zero_iff, sq, ← add_one_mul,
            mul_rotate, ← sq, eq_add_of_sub_eq (h _ _), h9, mul_zero, zero_add, ←
            add_assoc]⟩)
  -- Now show that `c^4 = 0`
  refine'
    h2 _
      ((period_iff h).mpr
        ⟨(quasi_period_iff h).mpr λ x => _, by
          rw [X0, h1, sub_eq_neg_self, sq_eq_zero_iff] <;> exact h5 _ h7⟩)
  rw [sq, ← add_one_mul, mul_assoc, ← sq] at h8
  have h11 := eq_add_of_sub_eq (h (c ^ 2 + 1) ((c ^ 2) ^ 2 * x + 1))
  rw [h5 _ h7, zero_mul, zero_add, mul_add_one, ← mul_assoc, h8, zero_mul,
    zero_add, add_left_comm, char2.add_add_cancel h0, h7, eq_comm] at h11
  rw [sq, sq, mul_assoc, mul_assoc, ← neg_eq_zero, ← h6 _ h4, ← mul_assoc, ← sq, ← mul_assoc, ← sq,
    add_comm (c ^ 2)]
  exact h5 _ h11

theorem case2_4_lem9 (x : R) :
    (x ^ 2 = 0 ∨ x ^ 2 = 1) ∨ f x + f (x + 1) = 1 ∧ x * (x + 1) + 1 = 0 :=
  by
  suffices
    (---- Reduce to showing that either `f(x) = 0`, `f(x + 1) = 0`, or `f(x)^2 + f(x + 1)^2 = 3`
            f
            (x + 1) =
          0 ∨
        f x = 0) ∨
      f x ^ 2 + f (x + 1) ^ 2 = 3
    from
    let h4 := case2_4_lem8 h h0 h1 h2 h3
    this.imp
      (Or.imp
        (λ h5 =>
          h4 _ <| (case2_4_lem5 h h0 h1 _).trans <| sub_eq_neg_self.mpr <| sq_eq_zero_iff.mpr h5)
        λ h5 =>
        eq_of_sub_eq_zero <|
          (Char2.sub_eq_add h0 _ _).trans <|
            h4 _ <| (case2_4_lem4 h h0 h1 x).trans <| sub_eq_neg_self.mpr <| sq_eq_zero_iff.mpr h5)
      λ this =>
      let h5 := (case2_4_lem6 h h0 h1 x).resolve_left (this.trans_ne <| add_left_ne_self.mpr h3)
      ⟨h5,
        h4 _ <|
          (case2_4_lem3 h h0 _).trans <|
            by
            have h6 := add_sq' (f x) (f (x + 1))
            rw [h5, this, one_pow, bit1, add_right_comm, self_eq_add_left, mul_assoc, ← mul_one_add,
              mul_eq_zero] at h6
            exact h6.elim (λ h6 => absurd h6 h3) eq_neg_of_add_eq_zero_right⟩
  ---- Now prove that either `f(x) = 0`, `f(x + 1) = 0`, or `f(x)^2 + f(x + 1)^2 = 3`
  suffices 2 * (f (x + 1) * f x) ^ 2 * (f x ^ 2 + f (x + 1) ^ 2 - 3) = 0 from
    (mul_eq_zero.mp this).imp
      (λ h4 => mul_eq_zero.mp <| sq_eq_zero_iff.mp <| (mul_eq_zero.mp h4).resolve_left h3)
      eq_of_sub_eq_zero
  have h4 : ∀ x, f (x ^ 4) = (f x ^ 2 - 1) ^ 2 - 1 := λ x => by
    rw [bit0, ← two_mul, pow_mul, case2_4_lem5 h h0 h1, case2_4_lem4 h h0 h1]
  have h5 := case2_4_lem3 h h0
  have h6 := char2.add_one_pow_four h0
  have h7 := h4 (x * (x + 1) + 1)
  rw [h5, h6, mul_pow, h6, h5, h4, ← h6, h4, eq_comm, ← sub_eq_zero] at h7
  rw [← h7]; ring

theorem case2_4_lem10 (h4 : ∀ x : R, x ^ 2 = 0 → x = 0) (x : R) :
    (x = 0 ∨ x = 1) ∨ f x + f (x + 1) = 1 ∧ x * (x + 1) + 1 = 0 :=
  (case2_4_lem9 h h0 h1 h2 h3 x).imp_left <|
    Or.imp (h4 x) λ h5 =>
      eq_of_sub_eq_zero <|
        h4 (x - 1) <| (Char2.sub_eq_add h0 x 1).symm ▸ (Char2.add_one_sq h0 x).symm ▸ h5.symm ▸ h0

/-- The main lemma for the `𝔽₂[X]/⟨X^2⟩` subcase -/
theorem case2_4_𝔽₂ε_main_lemma {c : R} (h4 : c ≠ 0) (h5 : c * c = 0) :
    ∀ x, (x = 0 ∨ x = c) ∨ x = 1 ∨ x = c + 1 :=
  suffices ∀ x, f (c * x + 1) = 0 from cases_of_nonperiod_quasi_period h h2 h1 this h4
  λ x => by
  let h6 := (case2_4_lem5 h h0 h1 <| c * x).symm
  rwa [mul_pow, sq c, h5, zero_mul, h1, sub_eq_neg_self, sq_eq_zero_iff] at h6

/-- Solution for the current sub-subcase (`𝔽₂ε_map`) -/
theorem case24𝔽₂εQuotIsAnswer {c : R} (h4 : c ≠ 0) (h5 : c * c = 0) : IsAnswer f :=
  have X : Bijective (𝔽₂ε.cast'Hom h0 h5) :=
    ⟨𝔽₂ε.cast'Hom_injective _ _ h4, λ x =>
      (case2_4_𝔽₂ε_main_lemma h h0 h1 h2 h3 h4 h5 x).elim
        (λ h5 => h5.elim (λ h5 => ⟨𝔽₂ε.O, h5.symm⟩) λ h5 => ⟨𝔽₂ε.X, h5.symm⟩) λ h5 =>
        h5.elim (λ h5 => ⟨𝔽₂ε.I, h5.symm⟩) λ h5 => ⟨𝔽₂ε.Y, h5.symm⟩⟩
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₂εMap S ∘ π from this.symm ▸ IsAnswer.𝔽₂ε_map_comp π.toRingHom π.Surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <|
    funext λ x =>
      let h6 := good_map_one h
      match x with
      | 𝔽₂ε.O => h1
      | 𝔽₂ε.I => h6
      | 𝔽₂ε.X =>
        suffices f c = 1 ∨ f c = -1 from this.resolve_right <| mt (case2_4_lem8 h h0 h1 h2 h3 c) h4
        sq_eq_one_iff.mp <|
          sub_eq_zero.mp <|
            (case2_4_lem4 h h0 h1 c).symm.trans <|
              ((sq c).trans h5).symm ▸ (zero_add (1 : R)).symm ▸ h6
      | 𝔽₂ε.Y => by
        let h7 := case2_4_lem5 h h0 h1 c
        rwa [sq, h5, h1, eq_comm, sub_eq_neg_self, sq_eq_zero_iff] at h7

/-- The main lemma for the `𝔽₄` subcase -/
theorem case2_4_𝔽₄_main_lemma (h4 : ∀ x : R, x ^ 2 = 0 → x = 0) {c : R} (h5 : f c + f (c + 1) = 1)
    (h6 : c * c + c = 1) : ∀ x, (x = 0 ∨ x = c) ∨ x = 1 ∨ x = c + 1 := λ x =>
  (or_or_or_comm _ _ _ _).mp <|
    let h7 := case2_4_lem10 h h0 h1 h2 h3 h4
    (h7 x).imp_right λ h8 =>
      (h7 (x + c)).elim (Or.imp (Char2.add_eq_zero_iff_eq h0).mp (Char2.add_eq_iff_eq_add' h0).mp)
        (by
          let h9 := one_ne_zero_of_map_zero h h1
          suffices (x + c) * (x + c + 1) = 0 from λ h10 =>
            absurd h10.2 <| this.symm ▸ (zero_add (1 : R)).trans_ne h9
          rw [mul_add_one, ← sq, char2.add_sq h0, add_add_add_comm, sq, sq, h6, ← mul_add_one,
            h8.2])

/-- Solution for the current sub-subcase (`𝔽₄_map`) -/
theorem case24𝔽₄QuotIsAnswer (h4 : ∀ x : R, x ^ 2 = 0 → x = 0) {c : R} (h5 : f c + f (c + 1) = 1)
    (h6 : c * c + c = 1) : IsAnswer f :=
  have X : Bijective (𝔽₄.cast'Hom h0 h6) :=
    ⟨𝔽₄.cast'Hom_injective _ _ (one_ne_zero_of_map_zero h h1), λ x =>
      (case2_4_𝔽₄_main_lemma h h0 h1 h2 h3 h4 h5 h6 x).elim
        (λ h5 => h5.elim (λ h5 => ⟨𝔽₄.O, h5.symm⟩) λ h5 => ⟨𝔽₄.X, h5.symm⟩) λ h5 =>
        h5.elim (λ h5 => ⟨𝔽₄.I, h5.symm⟩) λ h5 => ⟨𝔽₄.Y, h5.symm⟩⟩
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₄Map S (f c) ∘ π from
    this.symm ▸
      IsAnswer.𝔽₄_map_comp π.toRingHom π.Surjective (f c)
        (eq_sub_of_add_eq' h5 ▸
          case2_4_lem3 h h0 c ▸ (mul_add_one c c).symm ▸ h6.symm ▸ h1 ▸ congr_arg f h0)
  (MulEquiv.eq_comp_symm _ _ _).mpr <|
    funext λ x =>
      match x with
      | 𝔽₄.O => h1
      | 𝔽₄.I => good_map_one h
      | 𝔽₄.X => rfl
      | 𝔽₄.Y => eq_sub_of_add_eq' h5

/-- The main lemma for the `𝔽₂` subcase -/
theorem case2_4_𝔽₂_main_lemma (h4 : ∀ x : R, x ^ 2 = 0 → x = 0)
    (h5 : ¬∃ c, f c + f (c + 1) = 1 ∧ c * c + c = 1) (x : R) : x = 0 ∨ x = 1 :=
  (case2_4_lem10 h h0 h1 h2 h3 h4 x).resolve_right λ h6 =>
    h5 ⟨x, h6.1, (mul_add_one x x).symm.trans <| (Char2.add_eq_zero_iff_eq h0).mp h6.2⟩

/-- Solution for the current sub-subcase (`𝔽₂_map`) -/
theorem case24𝔽₂QuotIsAnswer (h4 : ∀ x : R, x ^ 2 = 0 → x = 0)
    (h5 : ¬∃ c, f c + f (c + 1) = 1 ∧ c * c + c = 1) : IsAnswer f :=
  have X : Bijective (𝔽₂.castHom h0) :=
    ⟨𝔽₂.castHom_injective _ (one_ne_zero_of_map_zero h h1), λ x =>
      (case2_4_𝔽₂_main_lemma h h0 h1 h2 h3 h4 h5 x).elim (λ h5 => ⟨𝔽₂.O, h5.symm⟩) λ h5 =>
        ⟨𝔽₂.I, h5.symm⟩⟩
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₂Map S ∘ π from this.symm ▸ IsAnswer.𝔽₂_map_comp π.toRingHom π.Surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <|
    funext λ x =>
      match x with
      | 𝔽₂.O => h1
      | 𝔽₂.I => good_map_one h

end Rchar2

/-- Solution for the current subcase (`hom_sub_one`, `𝔽₂ε_map`, `𝔽₄_map`, `𝔽₂_map`) -/
theorem case24QuotIsAnswer (h0 : f (-1) = 0) (h1 : f 2 = -1)
    (h2 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) : IsAnswer f :=
  let h3 : (2 : R) = 0 := h2 _ (case2_4_lem1 h h0 h1)
  let h4 : f 0 = -1 := h3 ▸ h1
  (---- Map 1
        em <|
        (2 : S) = 0).elim
    (λ h5 => case24Schar2QuotIsAnswer h h3 h4 h5) λ h5 =>
    (---- Map 2
          em' <|
          ∀ x : R, x ^ 2 = 0 → x = 0).elim
      (λ h6 =>
        Exists.elim (Classical.not_forall.mp h6) λ c h6 =>
          let h6 := not_imp.mp h6
          case24𝔽₂εQuotIsAnswer h h3 h4 h2 h5 h6.2 ((sq c).symm.trans h6.1))
      λ h6 =>
      (em <| ∃ c, f c + f (c + 1) = 1 ∧ c * c + c = 1).elim
        (---- Map 3
        λ h7 =>
          Exists.elim h7 λ c h7 => case24𝔽₄QuotIsAnswer h h3 h4 h2 h5 h6 h7.1 h7.2)---- Map 4
      λ h7 => case24𝔽₂QuotIsAnswer h h3 h4 h2 h5 h6 h7

end Step10

/-! ## Summary: Final solution -/


section FinalSolution

variable {R S : Type _} [CommRing R] [Field S] {f : R → S}

theorem quotIsAnswerOfGood (h : good f) (h0 : ∀ c, (∀ x, f (c + x) = f x) → c = 0) : IsAnswer f :=
  (ne_or_eq (f 0) _).elim
    (---- `f(0) ≠ -1`
    λ h1 => (eq_zero_of_map_zero_ne_neg_one h h1).symm ▸ IsAnswer.zero)
    λ h1 =>
    (ne_or_eq (f _) 0).elim
      (---- Case 1: `f(0) = -1`, `f_ ≠ 0`
      λ h2 =>
        (eq_or_ne (f _) (-2)).elim (case11IsAnswer h h2) λ h3 =>
          case12QuotIsAnswer h h2 h3 ((case1_map_neg_one_cases h h2).resolve_left h3)
            h0)---- Case 2: `f(0) = -1`, `f_ = 0`
    λ h2 =>
      (eq_or_ne (f 2) _).elim (λ h3 => case24QuotIsAnswer h h2 h3 h0) λ h3 =>
        (eq_or_ne (f 2) 1).elim (λ h4 => case22QuotIsAnswer h h2 h4 h3 h0) λ h4 =>
          (eq_or_ne (f 2) 3).elim (λ h5 => case23IsAnswer h h2 h5 h4 h1) λ h5 =>
            suffices f 2 = 0 from case21QuotIsAnswer h h2 this h0 h1 h5
            (((case2_map_two_cases h h2 h1).resolve_left h3).resolve_left h4).resolve_left h5

theorem isAnswerOfGood (h : good f) : IsAnswer f :=
  isAnswerOfPeriodLift h <|
    quotIsAnswerOfGood (periodLift_is_good h) (zero_of_periodic_periodLift h)

/-- Final solution -/
theorem final_solution : good f ↔ IsAnswer f :=
  ⟨isAnswerOfGood, good_of_isAnswer⟩

end FinalSolution

end IMO2012A5
end IMOSL
