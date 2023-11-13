import Mathlib.RingTheory.Ideal.Quotient
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

theorem good_of_IsAnswer {R S : Type _} [Ring R] [CommRing S]
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
theorem IsAnswerCompHom {φ : R₀ →+* R} (h : Surjective φ.toFun)
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
  funext λ x ↦ (mul_left_eq_self₀.mp <| neg_map_zero_mul h x).resolve_left
    λ h1 ↦ h0 <| neg_eq_iff_eq_neg.mp h1

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
theorem IsAnswer_of_add_one_additive
    (h0 : ∀ x y, f (x + y) = f x + f y + 1) : IsAnswer f :=
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
  intro x; rw [add_assoc, h0, h1, ← mul_assoc, mul_neg, ← h0]

theorem map_quasi_period (h0 : f 0 = -1)
    {c : R} (h1 : ∀ x, f (c + x) = -f c * f x) : f c = 1 ∨ f c = -1 := by
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

theorem mem_periodIdeal_iff :
    c ∈ periodIdeal h ↔ c ∈ quasiPeriodIdeal h ∧ f c = f 0 :=
  (period_iff h).trans <| and_congr_left' (quasi_period_iff h)

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

theorem IsAnswer_of_periodLift (h0 : IsAnswer (periodLift h)) : IsAnswer f :=
  IsAnswerCompHom Ideal.Quotient.mk_surjective h0



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
    {c : R} (h1 : f 0 = -1) (h2 : c ∈ quasiPeriodIdeal h) (h3 : c ≠ 0) (x : R) :
    (x = 0 ∨ x = c) ∨ x = 1 ∨ x = c + 1 := by
  refine (equiv_mod_periodIdeal h h1 h2 (mt (h0 c) h3) x).imp
    (Or.imp (h0 x) ?_) (Or.imp ?_ ?_)
  all_goals exact λ h5 ↦ eq_of_sub_eq_zero <| h0 _ h5

end Quot







/-! ## Step 3: Case 1: `f(-1) ≠ 0` -/

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
  have h1 : -f (-1) = f (2 + 1) := by
    rw [neg_eq_iff_eq_neg, ← one_add_one_eq_two,
      ← case1_map_neg_add_one h h0, neg_add, neg_add_cancel_comm]
  have h2 : f 2 = 1 := case1_map_two h h0
  -- `f(4) = C^2 - 1`, where `C = f(-1)`
  have h3 := case1_map_add_one_add_map_sub_one h h0
  have h4 := h3 (2 + 1)
  rw [add_sub_cancel, h2, ← h1, neg_mul, neg_neg, ← eq_sub_iff_add_eq] at h4
  -- Double-evaluating `f(5)` gives `(C - 1) C = -(C^2 - 1) C`, where `C = f(-1)`
  have h5 := h3 (2 + 1 + 1)
  rw [add_sub_cancel, h4, ← h1, ← neg_mul, add_assoc (2 : R), ← one_add_one_eq_two,
    ← two_mul, eq_add_of_sub_eq (h _ _), ← add_assoc, h4, one_add_one_eq_two, h2,
    one_mul, add_sub_cancel'_right, ← sub_eq_add_neg, ← sub_one_mul] at h5
  -- Finishing
  apply mul_right_cancel₀ h0 at h5
  replace h3 := sq_sub_sq (f (-1)) 1
  rwa [one_pow, sq, ← neg_eq_iff_eq_neg.mpr h5,
    ← neg_one_mul, mul_eq_mul_right_iff, sub_eq_zero, eq_comm,
    ← eq_sub_iff_add_eq, ← neg_add', one_add_one_eq_two] at h3

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
  -- Reduce to `f(x) = -1` via `f(-x) = f(x)`
  have h2 : f (-x) = f x := by rw [← sub_eq_zero, map_neg_sub_map2 h, h1, zero_mul]
  rw [h2, and_self]
  -- Prove `f(x) f(-1) = f(x) f(-x - 1)`
  have h3 := case1_map_two_mul_add_one h h0
  have h4 := case1_map_add_main_eq1 h x (x + 1)
  rw [h1, mul_zero, sub_zero, ← add_assoc, ← two_mul, h3, h1, zero_mul,
    neg_zero, zero_sub, ← sub_add_cancel'' (1 : R), add_assoc,
    one_add_one_eq_two, ← mul_add_one _ x, ← neg_add_eq_sub, ← mul_neg,
    h3, neg_neg, neg_add_eq_sub, sub_add_cancel'', h2] at h4
  -- Finish with (3.6)
  have h5 := case1_map_add_main_eq2 h x (-(x + 1))
  rwa [neg_neg, h1, mul_zero, zero_sub, neg_inj, add_right_comm, add_neg_self,
    ← h4, mul_eq_mul_right_iff, case1_map_zero h h0, or_iff_left h0, eq_comm] at h5

end Step3







/-! ## Step 4: Subcase 1.1: `f(-1) = -2 ≠ 0` -/

section Step4

/-- Auxiliary lemma: `2 ≠ 0` -/
theorem case1_1_S_two_ne_zero {S : Type _} [AddGroup S]
    {a b : S} (h : a ≠ 0) (h0 : a = -b) : (b : S) ≠ 0 :=
  neg_ne_zero.mp λ h1 ↦ h <| h0.trans h1

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) ≠ 0) (h1 : f (-1) = -2)

/-- (4.1) -/
theorem case1_1_lem1 (x : R) : f (-x) + f x = -2 :=
  (ne_or_eq (f (x + 1)) 0).elim
    (λ h2 ↦ h1 ▸ case1_map_add_one_ne_zero_imp h h0 h2)
    (λ h2 ↦ by have h3 := case1_map_add_one_eq_zero_imp h h0 h2
               rw [h3.1, h3.2, ← neg_add, one_add_one_eq_two])

/-- (4.2) -/
theorem case1_1_lem2 (x : R) : f (x + 1) = f x + 1 := by
  rw [← sub_eq_iff_eq_add]
  apply mul_right_cancel₀ h0
  rw [sub_one_mul, ← map_neg_sub_map2 h, h1, mul_neg, mul_two,
    ← case1_1_lem1 h h0 h1 x, ← sub_sub, sub_sub_cancel_left, neg_add']

/-- Solution for the current subcase (`x ↦ φ(x) - 1`) -/
theorem case1_1_IsAnswer : IsAnswer f :=
  IsAnswer_of_add_one_additive h λ x y ↦ by
    apply mul_right_cancel₀ (case1_1_S_two_ne_zero h0 h1)
    have h2 := λ t ↦ eq_sub_of_add_eq (case1_1_lem1 h h0 h1 t)
    have h3 := case1_map_add_main_eq2 h x y
    rw [h1, case1_1_lem2 h h0 h1, mul_neg, neg_neg, add_one_mul (α := S)] at h3
    rw [eq_sub_of_add_eq h3, h2, h2]
    ring

end Step4







/-! ## Step 5: Subcase 1.2: `f(-1)= 1 ≠ -2` -/

section Step5

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) ≠ 0) (h1 : f (-1) ≠ -2)
    (h2 : f (-1) = 1) (h3 : ∀ c ∈ periodIdeal h, c = 0)

/-- (5.1) -/
theorem case1_2_lem1 (h1 : ∀ c ∈ periodIdeal h, c = 0)
    {c : R} (h2 : f (c + 1) = 0) : c = 0 :=
  h1 c λ x ↦ by
    have h4 := case1_map_add_main_eq2 h c (x - 1)
    have h5 := case1_map_add_one_eq_zero_imp h h0 h2
    rw [h5.1, h5.2, ← mul_sub, neg_one_mul, neg_inj, map_neg_sub_map2 h,
      add_assoc, sub_add_cancel, mul_eq_mul_right_iff] at h4
    exact h4.resolve_right h0

/-- (5.2) -/
theorem case1_2_lem2 (x : R) : f (x + 1) + f (x - 1) + f x = 0 := by
  rw [add_eq_zero_iff_eq_neg, case1_map_add_one_add_map_sub_one h h0, h2, mul_one]

/-- `3 = 0` in `R` -/
theorem case1_2_lem3 : (3 : R) = 0 :=
  h3 (3 : R) λ x ↦ by
    have h4 y : f (y + 1) = -f y - f (y - 1) :=
      eq_sub_of_add_eq <| eq_neg_of_add_eq_zero_left (case1_2_lem2 h h0 h2 y)
    rw [add_comm, ← two_add_one_eq_three, ← add_assoc, h4, ← one_add_one_eq_two,
      ← add_assoc, add_sub_cancel, ← neg_add', h4, add_sub_cancel,
      ← add_sub_right_comm, neg_add_self, zero_sub, neg_neg]

/-- (5.3) -/
theorem case1_2_lem4 (x : R) (h4 : x ≠ 0) : f (-x) + f x = 1 :=
  h2 ▸ case1_map_add_one_ne_zero_imp h h0 (mt (case1_2_lem1 h h0 h3) h4)

/-- The main lemma for the subcase -/
theorem case1_2_lem5 (x : R) : x = 0 ∨ x = 1 ∨ x = -1 := by
  by_contra h4
  rw [not_or, not_or, ← add_eq_zero_iff_eq_neg] at h4
  have h5 := case1_2_lem4 h h0 h2 h3
  have h6 := case1_2_lem2 h h0 h2
  replace h6 : _ + _ = 0 + 0 := congr_arg₂ (· + ·) (h6 (-x)) (h6 x)
  rw [add_zero, add_add_add_comm, h5 x h4.1, add_comm (f (x + 1)),
    add_add_add_comm, ← neg_add', h5 _ h4.2.2, neg_add_eq_sub, ← neg_sub,
    h5 _ (sub_ne_zero_of_ne h4.2.1), one_add_one_eq_two] at h6
  apply h1; rwa [h2, eq_neg_iff_add_eq_zero, add_comm]

/-- Solution for the current subcase (`𝔽₃Map1`) -/
theorem case1_2_quot_IsAnswer : IsAnswer f :=
  -- `𝔽₃ → R/I` is bijective
  have X : Bijective (𝔽₃.castHom <| case1_2_lem3 h h0 h2 h3) :=
    ⟨𝔽₃.castHom_injective _ (one_ne_zero_of_map_zero h (case1_map_zero h h0)),
    λ x ↦ by rcases case1_2_lem5 h h0 h1 h2 h3 x with h4 | h4 | h4
             exacts [⟨𝔽₃.𝔽₃0, h4.symm⟩, ⟨𝔽₃.𝔽₃1, h4.symm⟩, ⟨𝔽₃.𝔽₃2, h4.symm⟩]⟩
  -- Factor `f` out as `𝔽₃Map1 ∘ π`
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₃Map1 S ∘ π.toFun
    from this.symm ▸ IsAnswer.𝔽₃_map1_comp π.toRingHom π.surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <| funext λ x ↦
    match x with
      | 𝔽₃.𝔽₃0 => case1_map_zero h h0
      | 𝔽₃.𝔽₃1 => good_map_one h
      | 𝔽₃.𝔽₃2 => h2

end Step5







/-! ## Step 6: Case 2: `f(-1) = 0` -/

section Step6

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0)

/-- (6.1) `f` is even -/
theorem case2_map_even (x : R) : f (-x) = f x :=
  by rw [← sub_eq_zero, map_neg_sub_map2 h, h0, mul_zero]

/-- (6.2) -/
theorem case2_good_alt (x y : R) : f (x * y - 1) - f (x - y) = f x * f y := by
  have h1 := case2_map_even h h0
  rw [← h1 y, ← h, ← sub_eq_add_neg, mul_neg, neg_add_eq_sub, ← neg_sub 1, h1]

/-- (6.3) -/
theorem case2_map_sq_sub_one (h3 : f 0 = -1) (x : R) :
    f (x ^ 2 - 1) = f x ^ 2 - 1 := by
  rw [sq, sq, ← case2_good_alt h h0, sub_self, h3, sub_neg_eq_add, add_sub_cancel]

/-- (6.4) -/
theorem case2_map_self_mul_add_one_sub_one (x : R) :
    f (x * (x + 1) - 1) = f x * f (x + 1) := by
  rw [← case2_good_alt h h0, sub_add_cancel', h0, sub_zero]

/-- (6.5) -/
theorem case2_map_add_two_eq (x : R) :
    f (x + 2) = f 2 * (f (x + 1) - f x) + f (x - 1) := by
  have h2 := case2_map_even h h0
  have h3 := λ t ↦ eq_add_of_sub_eq (h 2 t)
  rw [add_comm, mul_sub, ← add_sub_right_comm, eq_sub_iff_add_eq', ← h3,
    ← h2, ← add_sub_cancel (2 * x + 1) 1, neg_sub', sub_neg_eq_add, add_assoc,
    one_add_one_eq_two, ← mul_add_one 2 x, ← mul_neg, h3, h2, add_right_inj, ← h2,
    ← sub_eq_add_neg, neg_sub, ← one_add_one_eq_two, add_sub_add_right_eq_sub]

/-- Main claim -/
theorem case2_map_two_cases (h1 : f 0 = -1) :
    f 2 = 1 ∨ f 2 = -1 ∨ f 2 = 3 ∨ f 2 = 0 := by
  -- `f(3) = f(2)^2 - 1`
  have h2 := case2_map_sq_sub_one h h0 h1 2
  rw [sq, two_mul, ← one_add_one_eq_two, ← add_assoc,
    add_sub_cancel, one_add_one_eq_two] at h2
  rw [← or_assoc, ← sq_eq_sq_iff_eq_or_eq_neg, one_pow, ← sub_eq_zero, ← h2]
  -- `f(4) = (f(2) - 1) f(3) - 1`
  have h3 := case2_map_add_two_eq h h0
  have h4 := h3 (1 + 1)
  rw [add_sub_cancel, good_map_one h, add_zero, one_add_one_eq_two, mul_sub, ← sq,
    ← sub_sub_sub_cancel_right _ _ 1, ← h2, sub_right_comm, ← sub_one_mul] at h4
  -- `f(5) = f(2) f(3) = f(2) (f(2) - 2) f(3)`
  replace h2 := case2_map_self_mul_add_one_sub_one h h0 (1 + 1)
  rw [mul_add_one (1 + 1 : R), ← add_assoc,
    add_sub_cancel, one_add_one_eq_two] at h2
  specialize h3 (2 + 1)
  rwa [add_sub_cancel, add_right_comm, ← two_mul, h2, add_assoc, one_add_one_eq_two,
    ← mul_add_one (f 2), ← add_sub_right_comm, h4, sub_add_cancel, ← sub_one_mul,
    mul_eq_mul_left_iff, eq_comm, mul_left_eq_self₀, sub_sub, one_add_one_eq_two,
    sub_eq_iff_eq_add', two_add_one_eq_three, or_assoc, or_left_comm] at h3

/-- (6.6) -/
theorem case2_special_identity (x : R) :
    f x * f (x + 1) - f (x - 1) * f (x + 2) = f x * f 2 + f (x + 2) := by
  rw [← case2_map_self_mul_add_one_sub_one h h0, ← h, ← h, sub_add_cancel,
    mul_two, ← sub_add, ← one_add_one_eq_two, ← add_assoc,
    sub_add_add_cancel, ← add_assoc, add_left_eq_self, sub_eq_zero]
  apply congr_arg f
  rw [sub_eq_iff_eq_add, mul_add_one (x - 1), add_assoc _ (x - 1),
    sub_add_cancel, add_assoc, sub_one_mul, sub_add_cancel]

end Step6







/-! ## Step 7: Subcase 2.1: `f(-1)= 0` and `f(2) = 0 ≠ 3` -/

section Step7

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0)

/-- If `f(2) = 0`, then `3 ∈ I` -/
theorem case2_1_lem1 (h1 : f 2 = 0) : 3 ∈ periodIdeal h := λ x ↦ by
  rw [← two_add_one_eq_three, add_rotate, case2_map_add_two_eq h h0,
    h1, zero_mul, zero_add, add_sub_cancel']


section ThreeEqZero

variable (h1 : (3 : R) = 0)

/-- (7.1) -/
theorem case2_1_lem2 (x : R) : f x * f (x + 1) - f (x - 1) ^ 2 = f (x - 1) := by
  rw [← two_add_one_eq_three, add_eq_zero_iff_eq_neg] at h1
  have h2 := case2_special_identity h h0 x
  rwa [h1, h0, mul_zero, zero_add, ← sub_eq_add_neg, ← sq] at h2

/-- (7.1) with `x` replaced by `x + 1` -/
theorem case2_1_lem3 (x : R) : f (x + 1) * f (x - 1) - f x ^ 2 = f x := by
  have h2 := case2_1_lem2 h h0 h1 (x + 1)
  rw [← two_add_one_eq_three, add_eq_zero_iff_eq_neg] at h1
  rwa [add_sub_cancel, add_assoc, one_add_one_eq_two, h1, ← sub_eq_add_neg] at h2

/-- (7.2) -/
theorem case2_1_lem4 (x : R) :
    f (x - 1) + f x + f (x + 1) = -1 ∨ f x = f (x - 1) := by
  have h2 : _ - _ = _ - _ :=
    congr_arg₂ _ (case2_1_lem2 h h0 h1 x) (case2_1_lem3 h h0 h1 x)
  rwa [sub_sub_sub_comm, mul_comm, ← mul_sub, sub_eq_iff_eq_add,
    sq_sub_sq, ← one_add_mul (α := S), ← neg_sub (f x), mul_neg,
    ← neg_mul, mul_eq_mul_right_iff, sub_eq_zero, eq_neg_iff_add_eq_zero,
    add_comm, add_assoc, add_eq_zero_iff_neg_eq, eq_comm] at h2

/-- (7.3) -/
theorem case2_1_lem5 {c : R} (h2 : f (c + 1) = 0) (h3 : f (c - 1) = 0) :
    c ∈ periodIdeal h := λ x ↦ by
  rw [← two_add_one_eq_three, add_eq_zero_iff_eq_neg, ← one_add_one_eq_two] at h1
  let y := x - c - 1 - 1
  -- `f (y (c - 1) + (c + 1)) = f (y + 2 - c)`
  have h4 := case2_good_alt h h0 (y + 1) (c - 1)
  rw [h3, mul_zero, sub_eq_zero, add_one_mul y,
    add_sub_assoc, sub_sub, h1, sub_neg_eq_add] at h4
  -- `f (y (c + 1) + (c - 1)) = f (y + 2 + c)`
  have h5 := h (y * (c - 1)) (c + 1)
  rw [h2, mul_zero, sub_eq_zero, h4, mul_right_comm,
    eq_add_of_sub_eq (h _ _), h3, mul_zero, zero_add] at h5
  -- Finish by expressing `f(y (c^2 - 1) + 1)` in two ways
  replace h4 := h (y + 1) (c + 1)
  rwa [h2, mul_zero, sub_eq_zero, add_one_mul y, add_assoc, add_assoc,
    h1, ← sub_eq_add_neg, h5, sub_add_cancel, sub_sub_sub_cancel_right,
    sub_add_add_cancel, sub_add_cancel, sub_sub, ← two_mul,
    ← one_add_one_eq_two, h1, neg_one_mul, sub_neg_eq_add, add_comm] at h4

end ThreeEqZero


section Quotient

variable (h1 : f 2 = 0) (h2 : ∀ c ∈ periodIdeal h, c = 0)
  (h3 : f 0 = -1) (h4 : f 2 ≠ 3)

/-- (7.4) -/
theorem case2_1_lem6 (x : R) : f (x - 1) + f x + f (x + 1) = -1 := by
  -- Restrict to case `f(x) = f(x - 1)`
  replace h4 := h2 3 (case2_1_lem1 h h0 h1)
  have h5 := case2_1_lem4 h h0 h4
  refine (h5 x).elim id λ h6 ↦ ?_
  -- Restrict to case `f(x) = f(x - 1) = f(x + 1)`
  replace h2 : (1 + 1 : R) = -1 := by
    rwa [one_add_one_eq_two, eq_neg_iff_add_eq_zero, two_add_one_eq_three]
  have h7 := h5 (x - 1)
  rw [sub_add_cancel, sub_sub, h2, sub_neg_eq_add, add_rotate] at h7
  refine h7.resolve_right λ h7 ↦ ?_
  -- Get `f(x) = f(x - 1) = f(x + 1) = 0` and a contradiction
  have h8 := case2_1_lem2 h h0 h4 x
  rw [← h7, h6, ← sq, sub_self, eq_comm] at h8
  have h9 := case2_1_lem5 h h0 h4 (h7.symm.trans h8) h8 0
  rw [add_zero, h6, h8, h3, zero_eq_neg] at h9
  exact one_ne_zero h9

/-- (7.5) -/
theorem case2_1_lem7 (x : R) : f x = -1 ∨ f x = 0 := by
  have h7 := h2 3 (case2_1_lem1 h h0 h1)
  have h5 : (2 : R) = -1 := by rwa [eq_neg_iff_add_eq_zero, two_add_one_eq_three]
  -- `f(x^2) = f(x)^2 + f(x) + f(-x)`
  have h6 := h (x + 1) (x - 1)
  rw [← sq_sub_sq, one_pow, sub_add_cancel, add_add_sub_cancel,
    ← two_mul, h5, eq_add_of_sub_eq (case2_1_lem3 h h0 h7 _),
    neg_one_mul, add_comm, sub_eq_iff_eq_add, add_assoc] at h6
  -- `f(x^2 + 1) = f(x)^2 + f(-x)`
  replace h7 := h x x
  rw [← sq, ← two_mul, ← sq, h5, neg_one_mul, sub_eq_iff_eq_add] at h7
  -- Plug into (7.4): `f(x^2 - 1) + f(x^2) + f(x^2 + 1) = -1`
  replace h5 := case2_1_lem6 h h0 h1 h2 h3 (x ^ 2)
  rw [case2_map_sq_sub_one h h0 h3 x, h6, h7, case2_map_even h h0,
    ← two_mul, add_rotate, add_add_add_comm, ← two_mul, ← add_sub_assoc,
    sub_eq_neg_self, add_right_comm, ← add_one_mul (2 : S), sq,
    ← add_one_mul (2 : S), ← mul_add, two_add_one_eq_three, mul_eq_zero,
    ← add_one_mul (f x), mul_eq_zero, add_eq_zero_iff_eq_neg] at h5
  exact h5.resolve_left (h4.symm.trans_eq h1)

/-- (7.6) -/
theorem case2_1_lem8 (x : R) (h5 : f x = -1) : x = 0 := by
  replace h3 := case2_1_lem6 h h0 h1 h2 h3 x
  rw [h5, add_right_comm, add_left_eq_self] at h3
  have h6 := eq_add_of_sub_eq' (case2_1_lem3 h h0 (h2 3 <| case2_1_lem1 h h0 h1) x)
  rw [sq, ← add_one_mul (f x), mul_eq_zero_of_left (add_eq_zero_iff_eq_neg.mpr h5),
    eq_neg_of_add_eq_zero_left h3, mul_neg, neg_eq_zero, mul_self_eq_zero] at h6
  rw [h6, add_zero] at h3
  exact h2 x (case2_1_lem5 h h0 (h2 3 <| case2_1_lem1 h h0 h1) h6 h3)

/-- The main lemma for the subcase -/
theorem case2_1_lem9 (x : R) : x = 0 ∨ x = 1 ∨ x = -1 := by
  have h5 := case2_1_lem8 h h0 h1 h2 h3
  have h6 := case2_1_lem7 h h0 h1 h2 h3 h4
  refine (h6 x).imp (h5 x) (λ h7 ↦ ?_)
  refine (h6 (x - 1)).imp (λ h8 ↦ eq_of_sub_eq_zero (h5 _ h8)) (λ h8 ↦ ?_)
  replace h6 := case2_1_lem6 h h0 h1 h2 h3 x
  rw [h8, zero_add, h7, zero_add] at h6
  exact eq_neg_of_add_eq_zero_left (h5 _ h6)

/-- Solution for the current subcase (`𝔽₃Map2`) -/
theorem case2_1_quot_IsAnswer : IsAnswer f :=
  -- `𝔽₃ → R/I` is bijective
  have X : Bijective (𝔽₃.castHom <| h2 3 <| case2_1_lem1 h h0 h1) :=
    ⟨𝔽₃.castHom_injective _ (one_ne_zero_of_map_zero h h3),
    λ x ↦ by rcases case2_1_lem9 h h0 h1 h2 h3 h4 x with h5 | h5 | h5
             exacts [⟨𝔽₃.𝔽₃0, h5.symm⟩, ⟨𝔽₃.𝔽₃1, h5.symm⟩, ⟨𝔽₃.𝔽₃2, h5.symm⟩]⟩
  -- Factor `f` out as `𝔽₃Map2 ∘ π`
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₃Map2 S ∘ π.toFun
    from this.symm ▸ IsAnswer.𝔽₃_map2_comp π.toRingHom π.surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <| funext λ x ↦
    match x with
      | 𝔽₃.𝔽₃0 => h3
      | 𝔽₃.𝔽₃1 => good_map_one h
      | 𝔽₃.𝔽₃2 => h0

end Quotient

end Step7







/-! ## Step 8: Subcase 2.2: `f(-1) = 0` and `f(2) = 1 ≠ -1` -/

section Step8

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
  have X : Bijective (ℤ₄.castHom h4) :=
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

end Step8







/-! ## Step 9: Subcase 2.3: `f(-1) = 0` and `f(2) = 3 ≠ 1` -/

section Step9Domain

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f) (h0 : f (-1) = 0) (h1 : f 2 = 3)

/-- (9.1) -/
theorem case2_3_lem1 (x : R) : f (x + 2) = 3 * (f (x + 1) - f x) + f (x - 1) :=
  h1 ▸ case2_map_add_two_eq h h0 x

/-- (9.2) -/
theorem case2_3_lem2 (x : R) :
    f x * (3 * f (x - 1) + f (x + 1))
      = (f (x - 1) + 3 * f (x + 1)) * (1 + f (x - 1)) := by
  have h2 := case2_special_identity h h0 x
  rw [← h1, mul_add, eq_add_of_sub_eq h2, case2_map_add_two_eq h h0]
  ring

/-- (9.3) -/
theorem case2_3_lem3 (x : R) :
    f (x + 1) + f (x - 1) = 2 * f x + 2 ∨ f (x - 1) = f (x + 1) := by
  have X := case2_map_even h h0
  have X0 := case2_3_lem2 h h0 h1
  have h2 := X0 (-x)
  rw [X, ← neg_add', X, neg_add_eq_sub, ← neg_sub x, X] at h2
  rw [← sub_eq_zero, or_comm, ← mul_eq_mul_right_iff, ← sub_eq_zero,
    ← sub_eq_zero.mpr (congr_arg₂ (· - ·) h2 (X0 x))]
  ring

/-- (9.4) -/
theorem case2_3_lem4 (h2 : f 2 ≠ 1) (x : R) :
    f (x + 1) + f (x - 1) = 2 * f x + 2 ∨ f (x + 1) = 0 ∧ f (x - 1) = 0 := by
  -- Reduce to `f(x - 1) = 0` assuming `f(x - 1) = f(x + 1)`
  have X := case2_3_lem3 h h0 h1
  refine (X x).imp_right λ h3 ↦ ?_
  rw [← h3, and_self]
  -- Get either `f (x - 1) = 0`, `(4 : S) = 0`, or `f(x) = f(x - 1) + 1`
  have h4 := case2_3_lem2 h h0 h1 x
  rw [← h3, add_comm, ← one_add_mul (3 : S), mul_comm,
    mul_eq_mul_left_iff, mul_eq_zero, or_comm] at h4
  -- Eliminate the other two cases
  have h5 : (2 : S) ≠ 0 := λ h5 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, h5, zero_add]
  refine (h4.resolve_right ?_).resolve_left ?_
  -- Obtain contradiction via `f(x + 2) + f(x) = 2 f(x + 1) + 2`
  · intros h4; apply h5
    specialize X (x + 1)
    rwa [add_sub_cancel, add_assoc, one_add_one_eq_two, case2_3_lem1 h h0 h1,
      ← h3, h4, sub_add_cancel'', mul_neg_one, add_left_inj, add_add_add_comm,
      ← two_mul, add_comm, add_right_inj, ← two_add_one_eq_three, neg_add',
      sub_add_cancel, eq_comm, eq_sub_iff_add_eq, one_add_one_eq_two, or_self,
      eq_neg_iff_add_eq_zero, ← two_mul, ← sq, sq_eq_zero_iff] at X
  · rw [← two_add_one_eq_three, add_left_comm, one_add_one_eq_two, ← two_mul]
    exact mul_ne_zero h5 h5

/-- (9.5) -/
theorem case2_3_lem5 (h2 : f 2 ≠ 1) (x : R) :
    f (x + 1) + f (x - 1) = 2 * f x + 2 ∨
      f x = 0 ∧ f (x + 1) = 0 ∧ f (x - 1) = 0 := by
  have X := case2_3_lem4 h h0 h1 h2
  refine (X x).elim Or.inl λ h3 ↦ (X (x + 1)).imp
    (λ h4 ↦ ?_) (λ h4 => ⟨add_sub_cancel x 1 ▸ h4.2, h3⟩)
  rw [h3.1, mul_zero, zero_add, add_assoc, one_add_one_eq_two,
    add_sub_cancel, case2_3_lem1 h h0 h1, h3.1, zero_sub, h3.2,
    add_zero, mul_neg, neg_add_eq_iff_eq_add, ← two_add_one_eq_three,
    add_one_mul (2 : S), add_right_comm, self_eq_add_left] at h4
  rw [h3.1, h3.2, h4, zero_add]

/-- (9.6) -/
theorem case2_3_lem6 (h2 : f 2 ≠ 1) (h3 : f 0 = -1) (x : R) :
    f (x + 1) + f (x - 1) = 2 * f x + 2 := by
  refine (case2_3_lem5 h h0 h1 h2 x).resolve_right λ h4 ↦ ?_
  by_cases h5 : f 2 = 0
  -- Case 1: `char(S) = 3`
  · have h6 : f (x - 1) + f x + f (x + 1) = -1 :=
      case2_1_lem6 (periodLift_is_good h) h0 h5
        (zero_of_periodic_periodLift h) h3 x
    rw [h4.1, h4.2.1, h4.2.2, add_zero, add_zero, zero_eq_neg] at h6
    exact one_ne_zero h6
  -- Case 2: `char(S) ≠ 3`
  · suffices (f (2 * x) = -1 ∨ f (2 * x) = 0) ∧ f (2 * x) = -3 by
      rcases this with ⟨h6 | h6, h7⟩
      · rw [h7, neg_inj, ← h1] at h6; exact h2 h6
      · rw [h7, neg_eq_zero, ← h1] at h6; exact h5 h6
    constructor
    -- `f(2x) ∈ {-1, 0}`
    · refine (case2_3_lem5 h h0 h1 h2 (2 * x)).imp (λ h6 ↦ ?_) And.left
      have h7 := h (1 + 1) (x - 1)
      rw [h4.2.2, mul_zero, add_add_sub_cancel, add_comm 1 x, h4.2.1, sub_zero,
        mul_sub_one, ← sub_sub, sub_add_cancel, one_add_one_eq_two] at h7
      have h8 := case2_good_alt h h0 (x + 1) (1 + 1)
      rw [h4.2.1, zero_mul, add_sub_add_right_eq_sub,
        h4.2.2, sub_zero, add_one_mul x, ← add_assoc,
        add_sub_cancel, one_add_one_eq_two, mul_comm] at h8
      rw [h7, h8, zero_add, ← mul_add_one (2 : S), zero_eq_mul] at h6
      rcases h6 with h6 | h6
      · refine absurd ?_ h2
        rw [h1, ← two_add_one_eq_three, h6, zero_add]
      · rw [eq_neg_iff_add_eq_zero, h6]
    -- `f(2x) = -3`
    · have h6 := case2_3_lem1 h h0 h1 ((x + 1) * (x - 1))
      rw [eq_add_of_sub_eq (h _ _), eq_add_of_sub_eq (case2_good_alt h h0 _ _),
        h4.2.1, zero_mul, zero_add, zero_add, ← one_add_one_eq_two, ← sq_sub_sq,
        one_pow, add_add_sub_cancel, add_sub_sub_cancel, sub_add_add_cancel,
        case2_map_sq_sub_one h h0 h3, sq, eq_add_of_sub_eq (h _ _), h4.1, sq 0,
        zero_mul, zero_add, zero_sub, ← two_mul, one_add_one_eq_two, h1,
        sub_neg_eq_add, mul_add_one (3 : S), add_assoc, ← two_mul] at h6
      nth_rw 1 [← two_add_one_eq_three] at h6
      rw [add_one_mul (α := S), add_right_comm, self_eq_add_left,
        ← mul_add, mul_eq_zero, add_eq_zero_iff_eq_neg] at h6
      apply h6.resolve_left
      rwa [h1, ← two_add_one_eq_three, add_left_ne_self] at h2

end Step9Domain


section Step9Field

variable {R S : Type _} [CommRing R] [Field S]

def homGuess (f : R → S) (x : R) := (f x - f (x - 1) + 1) / 2

variable {f : R → S} (h : good f) (h0 : f (-1) = 0)
  (h1 : f 2 = 3) (h2 : f 2 ≠ 1) (h3 : f 0 = -1)

/-- (9.g1) -/
theorem case2_3_lem_g1 : homGuess f 0 = 0 :=
  div_eq_zero_iff.mpr <| Or.inl <|
    by rw [h3, zero_sub, h0, sub_zero, neg_add_self]

/-- (9.g2) -/
theorem case2_3_lem_g2 (x : R) : homGuess f (x + 1) = homGuess f x + 1 := by
  have h4 : (2 : S) ≠ 0 := λ h4 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, h4, zero_add]
  rw [homGuess, homGuess, div_add_one h4, add_sub_cancel]
  refine congr_arg₂ _ ?_ rfl
  rw [add_right_comm, add_left_inj, ← add_sub_right_comm,
    eq_sub_iff_add_eq, ← add_sub_right_comm, sub_eq_iff_eq_add,
    case2_3_lem6 h h0 h1 h2 h3, two_mul, add_right_comm]

/-- Variant of (9.g2) -/
theorem case2_3_lem_g2' (x : R) : homGuess f (x - 1) = homGuess f x - 1 := by
  rw [eq_sub_iff_add_eq, ← case2_3_lem_g2 h h0 h1 h2 h3, sub_add_cancel]

/-- (9.g3) -/
theorem case2_3_lem_g3 (x : R) : homGuess f (-x) = -homGuess f x := by
  have X := case2_map_even h h0
  rw [← add_left_inj 1, ← case2_3_lem_g2 h h0 h1 h2 h3, homGuess, add_sub_cancel,
    X, neg_add_eq_sub, ← X, neg_sub, homGuess, ← neg_div, neg_add', neg_sub]
  replace X : (2 : S) ≠ 0 := λ h4 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, h4, zero_add]
  rw [div_add_one X, ← one_add_one_eq_two, sub_add_add_cancel]

/-- (9.g4) -/
theorem case2_3_lem_g4 (x : R) : f x = homGuess f x ^ 2 - 1 := by
  have h4 : (2 : S) ≠ 0 := λ h4 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, h4, zero_add]
  have h5 : (2 : S) ^ 2 ≠ 0 := pow_ne_zero 2 h4
  rw [homGuess, div_pow, div_sub_one h5, eq_div_iff h5]
  refine mul_left_cancel₀ h4 (eq_of_sub_eq_zero ?_).symm
  rw [← sub_eq_zero_of_eq (case2_3_lem2 h h0 h1 x),
    eq_sub_of_add_eq (case2_3_lem6 h h0 h1 h2 h3 x)]
  ring

/-- (9.g5) -/
theorem case2_3_lem_g5 (x y : R) :
    (homGuess f (x * y) + 1) ^ 2 - homGuess f (x + y) ^ 2 =
      (homGuess f x ^ 2 - 1) * (homGuess f y ^ 2 - 1) := by
  have h4 := case2_3_lem_g4 h h0 h1 h2 h3
  have h5 := h x y
  iterate 4 rw [h4] at h5
  rwa [sub_sub_sub_cancel_right, case2_3_lem_g2 h h0 h1 h2 h3] at h5

/-- (9.g6) -/
theorem case2_3_lem_g6 (x y : R) :
    (homGuess f (x * y) - 1) ^ 2 - homGuess f (x - y) ^ 2 =
      (homGuess f x ^ 2 - 1) * (homGuess f y ^ 2 - 1) := by
  have h4 := case2_3_lem_g4 h h0 h1 h2 h3
  have h5 := case2_good_alt h h0 x y
  iterate 4 rw [h4] at h5
  rwa [sub_sub_sub_cancel_right, case2_3_lem_g2' h h0 h1 h2 h3] at h5

/-- (9.g7) -/
theorem case2_3_lem_g7 (x y : R) :
    2 ^ 2 * homGuess f (x * y)
      = homGuess f (x + y) ^ 2 - homGuess f (x - y) ^ 2 := by
  rw [← sub_sub_sub_cancel_left, case2_3_lem_g5 h h0 h1 h2 h3, add_sq',
    ← case2_3_lem_g6 h h0 h1 h2 h3, sub_sub_sub_cancel_right, sub_sq',
    add_sub_sub_cancel, mul_one, ← two_mul, ← mul_assoc, ← sq]

/-- (9.g8) -/
theorem case2_3_lem_g8 (x y : R) :
    (homGuess f (x + y) ^ 2 - homGuess f (x - y) ^ 2) ^ 2 + 2 ^ 4 =
      2 ^ 3 * (homGuess f (x + y) ^ 2 + homGuess f (x - y) ^ 2) +
        (2 ^ 2) ^ 2 * ((homGuess f x ^ 2 - 1) * (homGuess f y ^ 2 - 1)) := by
  rw [← case2_3_lem_g5 h h0 h1 h2 h3, mul_sub, ← mul_pow,
    mul_add_one (α := S), case2_3_lem_g7 h h0 h1 h2 h3]
  ring

/-- TODO: Optimize the proof -/
theorem case2_3_lem_g9 (x y : R) :
    homGuess f (x + y) + homGuess f (x - y) = 2 * homGuess f x ∨
      homGuess f (x + y) + homGuess f (x - y) = -(2 * homGuess f x) := by
  have h4 : (2 : S) ≠ 0 := λ h4 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, h4, zero_add]
  rw [← sq_eq_sq_iff_eq_or_eq_neg]
  apply mul_left_cancel₀ (pow_ne_zero 3 h4)

  replace h4 := case2_3_lem_g2 h h0 h1 h2 h3
  have h5 := case2_3_lem_g2' h h0 h1 h2 h3
  have h6 := case2_3_lem_g8 h h0 h1 h2 h3 x
  replace h6 : (_ + _) - (2 * _) = _ - _ :=
    congr_arg₂ (· - ·)
      (congr_arg₂ (· + ·) (h6 (y + 1)) (h6 (y - 1)))
      (congr_arg (2 * ·) (h6 y))
  rw [← add_assoc x, h4, ← sub_sub x, h5, ← add_sub_assoc x,
    h5, ← sub_add x, h4, h4, h5] at h6
  rw [← sub_eq_zero, ← sub_eq_zero_of_eq h6]
  ring

/-- (9.g9) -/
theorem case2_3_lem_g10 (x y : R) :
    homGuess f (x + y) + homGuess f (x - y) = 2 * homGuess f x := by
  have h4 x := case2_3_lem_g9 h h0 h1 h2 h3 x y
  refine (h4 x).elim id λ h5 ↦ ?_
  have h6 := case2_3_lem_g2 h h0 h1 h2 h3
  specialize h4 (x + 1)
  rw [add_right_comm, h6, add_sub_right_comm, h6, add_add_add_comm,
    h6, mul_add_one (2 : S), one_add_one_eq_two, add_left_inj] at h4
  refine h4.resolve_right λ h4 ↦ ?_
  rw [h5, neg_add, add_right_inj, eq_neg_iff_add_eq_zero, ← two_mul,
    mul_self_eq_zero, ← add_left_eq_self, two_add_one_eq_three] at h4
  exact h2 (h1.trans h4)

theorem case2_3_sol : ∃ φ : R →+* S, f = λ x => φ x ^ 2 - 1 := by
  have X := case2_3_lem_g2 h h0 h1 h2 h3
  have X0 := case2_3_lem_g10 h h0 h1 h2 h3
  have X1 : (2 : S) ≠ 0 := λ X1 ↦ h2 <| by
    rw [h1, ← two_add_one_eq_three, X1, zero_add]
  -- Zero map
  have hZero := case2_3_lem_g1 h0 h3
  -- One map
  have hOne : homGuess f 1 = 1 := by
    rw [← zero_add (1 : R), X, hZero, zero_add]
  -- Multiplicativity
  have hMul x y : homGuess f (x * y) = homGuess f x * homGuess f y
  · have h4 := case2_3_lem_g7 h h0 h1 h2 h3 x y
    rw [sq_sub_sq, X0, sub_eq_add_neg, ← case2_3_lem_g3 h h0 h1 h2 h3,
      neg_sub, add_comm x, X0, mul_mul_mul_comm, ← sq] at h4
    exact mul_left_cancel₀ (pow_ne_zero 2 X1) h4
  -- Additivity
  have hAdd x y : homGuess f (x + y) = homGuess f x + homGuess f y
  · specialize X0 (x + y) (x - y)
    rw [add_add_sub_cancel, add_sub_sub_cancel, ← two_mul, hMul, ← two_mul,
      hMul, ← mul_add, ← one_add_one_eq_two, X, hOne, one_add_one_eq_two] at X0
    exact (mul_left_cancel₀ X1 X0).symm
  -- Finish
  exact ⟨⟨⟨⟨homGuess f, hOne⟩, hMul⟩, hZero, hAdd⟩,
    funext <| case2_3_lem_g4 h h0 h1 h2 h3⟩

/-- Solution for the current subcase (`x ↦ φ(x)^2 - 1`) -/
theorem case2_3_IsAnswer : IsAnswer f :=
  Exists.elim (case2_3_sol h h0 h1 h2 h3)
    (λ φ h4 ↦ h4.symm ▸ IsAnswer.hom_sq_sub_one φ)

end Step9Field







/-! #### Some lemmas in characteristic two (to avoid `CharP` imports) -/

namespace Char2

variable {R : Type _} [CommRing R] (h : (2 : R) = 0)

theorem add_self (x : R) : x + x = 0 :=
  (two_mul x).symm.trans (mul_eq_zero_of_left h x)

theorem add_add_cancel (x y : R) : x + y + y = x :=
  by rw [add_assoc, add_self h, add_zero]

theorem sub_eq_add (x y : R) : x - y = x + y :=
  sub_eq_of_eq_add (add_add_cancel h x y).symm

theorem add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  by rw [add_sq', h, zero_mul, zero_mul, add_zero]

theorem add_one_sq (x : R) : (x + 1) ^ 2 = x ^ 2 + 1 :=
  by rw [add_sq h, one_pow]

theorem add_eq_iff_eq_add {x y z : R} : x + y = z ↔ x = z + y :=
  sub_eq_add h x y ▸ sub_eq_iff_eq_add

theorem add_eq_iff_eq_add' {x y z : R} : x + y = z ↔ x = y + z :=
  sub_eq_add h x y ▸ sub_eq_iff_eq_add'

theorem add_eq_zero_iff_eq {x y : R} : x + y = 0 ↔ x = y :=
  by rw [add_eq_iff_eq_add h, zero_add]

end Char2


/-! ## Step 10: Subcase 2.3: `f(-1) = 0` and `f(2) = -1` -/

section Step10

variable {R S : Type _} [CommRing R] [CommRing S] [IsDomain S]
  {f : R → S} (h : good f)

/-- `2 ∈ I` -/
theorem case2_4_lem1 (h0 : f (-1) = 0) (h1 : f 2 = -1) :
    2 ∈ periodIdeal h := by
  have h2 x : f (x + 1) = f (x - 1) ∨ f x + f (x - 1) = -1 := by
    have h2 := case2_special_identity h h0 x
    rwa [case2_map_add_two_eq h h0, h1, neg_one_mul, neg_sub, sub_add,
      mul_neg_one, ← add_sub_assoc, neg_add_self, eq_sub_iff_add_eq, mul_sub,
      ← sub_add, mul_comm _ (f x), ← mul_sub, ← add_mul, ← add_one_mul (α := S),
      mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_comm] at h2
  intro x
  rw [← one_add_one_eq_two, ← add_rotate]
  rcases h2 (x + 1) with h3 | h3
  rwa [add_sub_cancel] at h3
  specialize h2 (-(x + 1))
  have h4 := case2_map_even h h0
  rw [← neg_add', h4, h4, neg_add_eq_sub, sub_add_cancel'', h4] at h2
  refine h2.elim Eq.symm λ h2 ↦ ?_
  rwa [add_sub_cancel, ← h2, add_right_inj, eq_comm] at h3

section Rchar2

variable (h0 : (2 : R) = 0) (h1 : f 0 = -1)

theorem case2_4_lem2 : f (-1) = 0 := by
  rw [← one_add_one_eq_two, add_eq_zero_iff_eq_neg] at h0
  rw [← h0, good_map_one h]

/-- (10.1) -/
theorem case2_4_lem3 (x : R) : f (x * (x + 1) + 1) = f x * f (x + 1) :=
  Char2.sub_eq_add h0 (x * (x + 1)) 1 ▸
    case2_map_self_mul_add_one_sub_one h (case2_4_lem2 h h0) x

/-- (10.2) -/
theorem case2_4_lem4 (x : R) : f (x ^ 2 + 1) = f x ^ 2 - 1 :=
  Char2.sub_eq_add h0 (x ^ 2) 1 ▸ case2_map_sq_sub_one h (case2_4_lem2 h h0) h1 x

/-- (10.3) -/
theorem case2_4_lem5 (x : R) : f (x ^ 2) = f (x + 1) ^ 2 - 1 := by
  rw [← case2_4_lem4 h h0 h1, Char2.add_one_sq h0, Char2.add_add_cancel h0]

/-- Lemma 4 (TODO: Optimize the proof, if possible) -/
theorem case2_4_lem6 (x : R) :
    f x ^ 2 + f (x + 1) ^ 2 = 1 ∨ f x + f (x + 1) = 1 := by
  have h3 := case2_4_lem3 h h0
  have h4 := case2_4_lem5 h h0 h1
  ---- (10.L1.1)
  have h5 x :
      (f (x + 1) ^ 2 - 1) * (f (x + 1) - 1) + f x * f (x + 1)
        = f x * f (x * (x + 1)) := by
    rw [← h3, ← h4, ← h, eq_sub_iff_add_eq, add_right_comm, ← eq_sub_iff_add_eq,
      ← mul_assoc, mul_add_one x, ← sq, add_left_comm, Char2.add_self h0,
      add_zero, ← mul_add_one (f (x ^ 2)), sub_add_cancel, add_assoc, h]
  ---- Now use (10.L1.1) for more reduction
  have h6 : (f x) * _ = _ := congr_arg₂ _ rfl (h5 (x + 1))
  rw [Char2.add_add_cancel h0, mul_left_comm, mul_comm (x + 1), ← h5] at h6
  replace h6 :
      (f x ^ 2 + f (x + 1) ^ 2 - 1) * (f x + f (x + 1) - 1)
        * (f x - f (x + 1)) = 0 :=
    sub_eq_zero_of_eq h6 ▸ by ring
  rw [mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero] at h6
  rcases h6 with h6 | h6; exact h6; right
  ---- Assuming `f(x) = f(x + 1)`, prove that `f(x) + f(x + 1) = 1`
  specialize h3 (x ^ 2)
  have h2 := case2_4_lem4 h h0 h1
  rw [h4, h2, ← Char2.add_one_sq h0, ← mul_pow, h2] at h3
  replace h3 : _ * _ = _ * _ := congr_arg ((f x) ^ 2 * ·) h3
  rw [mul_sub_one, ← mul_pow, ← h5, ← h6, ← sq, mul_sub_one,
    ← add_sub_right_comm, add_sub_assoc, sub_sub_cancel, ← sq, add_sq,
    mul_comm, one_pow, add_assoc, mul_pow, sub_eq_iff_eq_add, add_right_inj,
    mul_one, ← eq_sub_iff_add_eq,← mul_assoc, mul_left_eq_self₀] at h3
  rcases h3 with h3 | h3
  · rwa [← h6, ← two_mul]
  · specialize h5 (x ^ 2)
    rw [h2, h4, ← h6, h3, sq, zero_mul, zero_mul,
      zero_sub, neg_mul_neg, mul_one, add_zero] at h5
    exact absurd h5 one_ne_zero

/-- Solution for the current sub-subcase (`hom_sub_one: x ↦ φ(x) - 1`).
  (TODO: Optimize the proof, if possible) -/
theorem case2_4_Schar2_quot_IsAnswer (h3 : (2 : S) = 0) : IsAnswer f :=
  IsAnswer_of_add_one_additive h <| by
    ---- (10.L2.1)
    have h4 x : f (x + 1) = f x + 1 := by
      rw [← Char2.add_eq_iff_eq_add' h3, add_comm]
      refine (case2_4_lem6 h h0 h1 x).elim (λ h4 ↦ ?_) id
      rwa [← Char2.add_sq h3, ← Char2.add_eq_zero_iff_eq h3,
        ← Char2.add_one_sq h3, sq_eq_zero_iff, Char2.add_eq_zero_iff_eq h3] at h4
    ---- (10.L2.2)
    replace h x y : f (x * y) = f x * f y + f (x + y) + 1 :=
      by rw [← h, sub_add_cancel, h4, Char2.add_add_cancel h3]
    ---- Back to the main equality
    intros x y
    let a := f x
    let b := f y
    let c := f (x + y)
    have h6 := h (x * y) ((y + 1) * (x + 1))
    rw [mul_mul_mul_comm, h, add_left_inj] at h6
    have h7 : x * y + (y + 1) * (x + 1) = x * (y + 1) + y * (x + 1) + 1 := by ring
    rw [h7, h4, ← add_assoc, ← sub_eq_iff_eq_add', add_sub_add_right_eq_sub] at h6
    replace h7 : f (x * y) = a * b + c + 1 := h x y
    have h8 : f (x * (y + 1)) = a * (b + 1) + (c + 1) + 1 := by rw [h, ← add_assoc, h4, h4]
    have h9 : f (y * (x + 1)) = b * (a + 1) + (c + 1) + 1 := by
      rw [h, add_left_comm, ← add_assoc, h4, h4]
    have h10 : f ((y + 1) * (x + 1)) = (b + 1) * (a + 1) + c + 1 := by
      rw [h, add_add_add_comm, one_add_one_eq_two, h0, add_zero, add_comm y x, h4, h4]
    replace h6 := (congr_arg₂ _ (congr_arg₂ _ h8 h9) (congr_arg₂ _ h7 h10)).symm.trans h6
    rw [← sub_eq_iff_eq_add', ← h6, eq_comm, ← sub_eq_zero]
    refine' Eq.trans _ (mul_eq_zero_of_left h3 <| (a + 1) * (b + 1))
    ring

variable (h2 : ∀ c ∈ periodIdeal h, c = 0) (h3 : (2 : S) ≠ 0)

/-- Lemma 5 -/
theorem case2_4_lem7 (x : R) :
    f x * f (x + 1) = 0 ∨ f x + f (x + 1) = 1 ∧ f x * f (x + 1) = -1 := by
  have h4 x : f ((x ^ 2) ^ 2) = f x ^ 2 * (f x ^ 2 - 2) := by
    rw [case2_4_lem5 h h0 h1, case2_4_lem4 h h0 h1, ← one_pow 2,
      sq_sub_sq, one_pow, sub_add_cancel, sub_sub, one_add_one_eq_two]
  have h5 := case2_4_lem3 h h0
  have h6 := Char2.add_one_sq h0
  have h7 := h4 (x * (x + 1) + 1)
  rw [h5, h6, h6, mul_pow, h6, mul_pow, h6, h5, h4, ← h6, ← h6, h4,
    mul_mul_mul_comm, ← mul_pow, mul_eq_mul_left_iff, or_comm] at h7
  refine h7.imp sq_eq_zero_iff.mp λ h8 ↦ ?_
  rw [sub_mul, mul_sub, ← mul_pow, sub_sub, sub_right_inj, mul_comm, ← mul_add,
    mul_right_eq_self₀, or_iff_left h3, ← add_sub_assoc, sub_eq_iff_eq_add] at h8
  replace h7 := case2_4_lem6 h h0 h1 x
  rw [h8, add_right_eq_self, or_iff_right h3] at h7
  refine ⟨h7, ?_⟩
  apply congr_arg (· ^ 2) at h7
  rw [add_sq', h8, one_pow, add_assoc, add_right_eq_self, mul_assoc,
    ← mul_one_add (2 : S), mul_eq_zero, or_iff_right h3] at h7
  exact eq_neg_of_add_eq_zero_right h7

/-- Lemma 6 (TODO: Refactor the proof, if possible) -/
theorem case2_4_lem8 : ∀ c, f c = -1 → c = 0 := by
  ---- (10.L3.1)
  have A1 x (h6 : f x = -1) : f (x + 1) = 0 := by
    rcases case2_4_lem7 h h0 h1 h3 x with h7 | ⟨h7, h8⟩
    · rwa [h6, neg_one_mul, neg_eq_zero] at h7
    · rw [h6, neg_one_mul, neg_inj] at h8
      rw [h6, h8, neg_add_self] at h7
      rw [h8, h7]
  ---- (10.L3.2)
  have A2 c (h6 : f c = -1) x : f (c ^ 2 + c * x + 1) = -f (c * x + 1) := by
    rw [sq, ← mul_add, eq_add_of_sub_eq (h _ _), ← add_assoc,
      Char2.add_self h0, zero_add, eq_add_of_sub_eq (h _ _), h6,
      neg_one_mul, neg_one_mul, neg_add, neg_neg, add_comm]
  ---- Reduce to `c^4 = 0`
  intro c h4
  have X := case2_4_lem5 h h0 h1
  have h5 := X c
  rw [A1 c h4, sq (0 : S), zero_mul, zero_sub] at h5
  have h6 (d : R) (h7 : f d = -1) (h8 : d ^ 2 = 0) : d = 0 := h2 d <| by
    rw [mem_periodIdeal_iff, h1]
    refine ⟨λ x ↦ ?_, h7⟩
    have h9 := A2 d h7 x
    rwa [h8, zero_add, eq_neg_iff_add_eq_zero,
      ← two_mul, mul_eq_zero, or_iff_right h3] at h9
  refine h6 c h4 (h6 _ h5 ?_)
  ---- Prove that `c^6 + c^4 = 0`
  replace h6 : ((c ^ 2) ^ 2 + c ^ 2) * c ^ 2 = 0 := h2 _ <| by
    rw [mem_periodIdeal_iff, h1]
    have h7 := Char2.add_sq h0
    specialize A1 c h4
    have h8 : f (c ^ 2 + c + 1) = 0 := by
      rw [sq c, ← mul_add_one c, case2_4_lem3 h h0, A1, mul_zero]
    constructor
    · replace h6 x : f ((c ^ 2) ^ 2 + c ^ 2 + c ^ 2 * x + 1) = f (c ^ 2 * x + 1) :=
        by rw [add_assoc ((c ^ 2) ^ 2), ← mul_one_add (c ^ 2) x, A2 _ h5,
          mul_one_add (c ^ 2) x, sq, mul_assoc, ← sq, A2 _ h4, neg_neg]
      intro x
      rw [mul_assoc, mul_left_comm, ← h6, mul_left_comm,
        ← mul_one_add (α := R), eq_add_of_sub_eq (h _ _),
        add_comm (1 : R), ← add_assoc, h6, ← add_one_mul (α := S)]
      apply mul_eq_zero_of_left
      rw [← h7, X, sub_add_cancel, h8, sq, zero_mul]
    · rwa [← h7, ← mul_pow, X, sub_eq_neg_self, sq_eq_zero_iff,
        sq, ← add_one_mul c, mul_assoc, eq_add_of_sub_eq (h _ _),
        A1, zero_mul, zero_add, ← sq, ← add_rotate]
  ---- Final step
  apply h2
  rw [mem_periodIdeal_iff, h1, and_comm]
  have h7 := A1 (c ^ 2) h5
  constructor
  · rw [X, h7, sq, zero_mul, zero_sub]
  · intro x
    rw [sq, ← add_one_mul (α := R), mul_assoc, ← sq] at h6
    have h8 := h (c ^ 2 + 1) ((c ^ 2) ^ 2 * x + 1)
    rw [h7, zero_mul, sub_eq_zero, add_add_add_comm, Char2.add_self h0,
      add_zero, mul_add_one (α := R), ← mul_assoc, h6, zero_mul,
      zero_add, Char2.add_add_cancel h0, h5] at h8
    replace h6 : (c ^ 2) ^ 2 = c * (c * c ^ 2) := by rw [← mul_assoc, ← sq, ← sq]
    rw [h6, mul_assoc, ← neg_eq_zero, ← A2 c h4, ← mul_assoc, ← h6]
    exact A1 _ h8.symm

/-- Lemma 7 -/
theorem case2_4_lem9 (x : R) :
    (x ^ 2 = 0 ∨ x ^ 2 = 1) ∨ f x + f (x + 1) = 1 ∧ x * (x + 1) + 1 = 0 := by
  have h4 := case2_4_lem8 h h0 h1 h2 h3
  refine (case2_4_lem7 h h0 h1 h3 x).imp ?_ (λ h5 ↦ ?_)
  · rw [mul_eq_zero, or_comm]
    refine Or.imp (λ h5 ↦ h4 _ <| ?_) (λ h5 ↦ ?_)
    · rw [case2_4_lem5 h h0 h1, h5, sq, zero_mul, zero_sub]
    · rw [← Char2.add_eq_zero_iff_eq h0]
      apply h4; rw [case2_4_lem4 h h0 h1, h5, sq, zero_mul, zero_sub]
  · exact ⟨h5.1, h4 _ <| (case2_4_lem3 h h0 x).trans h5.2⟩

theorem case2_4_lem10 (h4 : ∀ x : R, x ^ 2 = 0 → x = 0) (x : R) :
    (x = 0 ∨ x = 1) ∨ f x + f (x + 1) = 1 ∧ x * (x + 1) + 1 = 0 :=
  (case2_4_lem9 h h0 h1 h2 h3 x).imp_left <| Or.imp (h4 x) λ h5 ↦ by
    rw [← Char2.add_eq_zero_iff_eq h0] at h5 ⊢
    exact h4 _ ((Char2.add_one_sq h0 x).trans h5)



/-- The main lemma for the `𝔽₂[X]/⟨X^2⟩` subcase -/
theorem case2_4_𝔽₂ε_main_lemma {c : R} (h4 : c ≠ 0) (h5 : c * c = 0) :
    ∀ x, (x = 0 ∨ x = c) ∨ x = 1 ∨ x = c + 1 := by
  refine cases_of_nonperiod_quasi_period h h2 h1 (λ x ↦ ?_) h4
  have h6 := case2_4_lem5 h h0 h1 (c * x)
  rwa [mul_pow, sq, h5, zero_mul, h1, eq_comm,
    sub_eq_neg_self, sq_eq_zero_iff] at h6

/-- Solution for the current sub-subcase (`𝔽₂εMap`) -/
theorem case2_4_𝔽₂ε_quot_IsAnswer {c : R} (h4 : c ≠ 0) (h5 : c * c = 0) :
    IsAnswer f :=
  -- `𝔽₂[X]/⟨X^2⟩ → R/I` induced by `X ↦ c` is bijective
  have X : Bijective (𝔽₂ε.castHom h0 h5) :=
    ⟨𝔽₂ε.castHom_injective _ _ h4,
    λ x ↦ by rcases case2_4_𝔽₂ε_main_lemma h h0 h1 h2 h4 h5 x
               with (h5 | h5) | (h5 | h5)
             exacts [⟨𝔽₂ε.O, h5.symm⟩, ⟨𝔽₂ε.X, h5.symm⟩,
                     ⟨𝔽₂ε.I, h5.symm⟩, ⟨𝔽₂ε.Y, h5.symm⟩]⟩
  -- Factor `f` out as `𝔽₂εMap ∘ π`
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₂εMap S ∘ π
    from this.symm ▸ IsAnswer.𝔽₂ε_map_comp π.toRingHom π.surjective
  have h6 := good_map_one h
  (MulEquiv.eq_comp_symm _ _ _).mpr <| funext λ x ↦
    match x with
      | 𝔽₂ε.O => h1
      | 𝔽₂ε.I => h6
      | 𝔽₂ε.X => by
          have h7 := case2_4_lem4 h h0 h1 c
          rw [sq, h5, zero_add, h6, eq_comm, sub_eq_zero, sq_eq_one_iff] at h7
          exact h7.resolve_right <| mt (case2_4_lem8 h h0 h1 h2 h3 c) h4
      | 𝔽₂ε.Y => by
          have h7 := case2_4_lem5 h h0 h1 c
          rwa [sq, h5, h1, eq_comm, sub_eq_neg_self, sq_eq_zero_iff] at h7



/-- The main lemma for the `𝔽₄` subcase -/
theorem case2_4_𝔽₄_main_lemma
    (h4 : ∀ x : R, x ^ 2 = 0 → x = 0) (h5 : c * (c + 1) = 1) (x : R) :
    (x = 0 ∨ x = 1) ∨ x = c ∨ x = c + 1 := by
  have h7 := case2_4_lem10 h h0 h1 h2 h3 h4
  refine (h7 x).imp_right λ h8 ↦ (h7 (x + c)).elim ?_ ?_
  · exact Or.imp (Char2.add_eq_zero_iff_eq h0).mp (Char2.add_eq_iff_eq_add' h0).mp
  · rintro ⟨-, h9⟩
    rw [mul_add_one (x + c), ← sq, Char2.add_sq h0, add_add_add_comm, sq,
      sq, ← mul_add_one c, h5, ← mul_add_one x, h8.2, zero_add] at h9
    exact absurd h9 (one_ne_zero_of_map_zero h h1)

/-- Solution for the current sub-subcase (`𝔽₄Map`) -/
theorem case2_4_𝔽₄_quot_IsAnswer (h4 : ∀ x : R, x ^ 2 = 0 → x = 0)
    (h5 : f c + f (c + 1) = 1) (h6 : c * (c + 1) = 1) : IsAnswer f :=
  -- `𝔽₄ → R/I` is bijective
  have X : Bijective (𝔽₄.castHom h0 h6) :=
    ⟨𝔽₄.castHom_injective _ _ (one_ne_zero_of_map_zero h h1),
    λ x ↦ by rcases case2_4_𝔽₄_main_lemma h h0 h1 h2 h3 h4 h6 x
               with (h7 | h7) | (h7 | h7)
             exacts [⟨𝔽₄.O, h7.symm⟩, ⟨𝔽₄.I, h7.symm⟩,
                     ⟨𝔽₄.X, h7.symm⟩, ⟨𝔽₄.Y, h7.symm⟩]⟩
  -- Factor `f` out as `𝔽₄Map ∘ π`
  let π := (RingEquiv.ofBijective _ X).symm
  have h7 := eq_sub_of_add_eq' h5
  suffices f = 𝔽₄Map S (f c) ∘ π
    from this.symm ▸ IsAnswer.𝔽₄_map_comp π.toRingHom π.surjective (f c) <|
      by rwa [← h7, ← case2_4_lem3 h h0, h6, Char2.add_self h0]
  (MulEquiv.eq_comp_symm _ _ _).mpr <| funext λ x ↦
    match x with
      | 𝔽₄.O => h1
      | 𝔽₄.I => good_map_one h
      | 𝔽₄.X => rfl
      | 𝔽₄.Y => h7



/-- The main lemma for the `𝔽₂` subcase -/
theorem case2_4_𝔽₂_main_lemma (h4 : ∀ x : R, x ^ 2 = 0 → x = 0)
    (h5 : ¬∃ c, f c + f (c + 1) = 1 ∧ c * (c + 1) = 1) (x : R) : x = 0 ∨ x = 1 :=
  (case2_4_lem10 h h0 h1 h2 h3 h4 x).resolve_right λ h6 ↦
    h5 ⟨x, h6.1, (Char2.add_eq_zero_iff_eq h0).mp h6.2⟩

/-- Solution for the current sub-subcase (`𝔽₂Map`) -/
theorem case2_4_𝔽₂_quot_IsAnswer (h4 : ∀ x : R, x ^ 2 = 0 → x = 0)
    (h5 : ¬∃ c, f c + f (c + 1) = 1 ∧ c * (c + 1) = 1) : IsAnswer f :=
  -- `𝔽₂ → R/I` is bijective
  have X : Bijective (𝔽₂.castHom h0) :=
    ⟨𝔽₂.castHom_injective _ (one_ne_zero_of_map_zero h h1),
    λ x ↦ by rcases case2_4_𝔽₂_main_lemma h h0 h1 h2 h3 h4 h5 x with h5 | h5
             exacts [⟨𝔽₂.O, h5.symm⟩, ⟨𝔽₂.I, h5.symm⟩]⟩
  -- Factor `f` out as `𝔽₂Map ∘ π`
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₂Map S ∘ π
    from this.symm ▸ IsAnswer.𝔽₂_map_comp π.toRingHom π.surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <| funext λ x ↦
    match x with
      | 𝔽₂.O => h1
      | 𝔽₂.I => good_map_one h

end Rchar2



/-- Solution for the current subcase (4 classes) -/
theorem case2_4_quot_IsAnswer (h0 : f (-1) = 0) (h1 : f 2 = -1)
    (h2 : ∀ c ∈ periodIdeal h, c = 0) : IsAnswer f := by
  have h3 := h2 _ (case2_4_lem1 h h0 h1)
  have h4 : f 0 = -1 := h3 ▸ h1
  by_cases h5 : (2 : S) = 0
  · exact case2_4_Schar2_quot_IsAnswer h h3 h4 h5
  by_cases h6 : ∃ x : R, ¬(x ^ 2 = 0 → x = 0)
  · rcases h6 with ⟨c, h6⟩; rw [not_imp] at h6
    exact case2_4_𝔽₂ε_quot_IsAnswer h h3 h4 h2 h5 h6.2 ((sq c).symm.trans h6.1)
  rw [← not_forall, not_not] at h6
  rcases em (∃ c, f c + f (c + 1) = 1 ∧ c * (c + 1) = 1) with ⟨c, h7, h8⟩ | h7
  · exact case2_4_𝔽₄_quot_IsAnswer h h3 h4 h2 h5 h6 h7 h8
  · exact case2_4_𝔽₂_quot_IsAnswer h h3 h4 h2 h5 h6 h7

end Step10







/-! ## Summary: Final solution -/

section FinalSolution

variable {R S : Type _} [CommRing R] [Field S] {f : R → S}

theorem quot_IsAnswer_of_good (h : good f) (h0 : ∀ c ∈ periodIdeal h, c = 0) :
    IsAnswer f := by
  rcases ne_or_eq (f 0) (-1) with h1 | h1
  ---- Case 1: `f(0) ≠ -1`
  · rw [eq_zero_of_map_zero_ne_neg_one h h1]
    exact IsAnswer.of_zero
  rcases ne_or_eq (f (-1)) 0 with h2 | h2
  ---- Case 2: `f(0) = -1`, `f(-1) ≠ 0`
  · rcases eq_or_ne (f (-1)) (-2) with h3 | h3
    · exact case1_1_IsAnswer h h2 h3
    · exact case1_2_quot_IsAnswer h h2 h3
        ((case1_map_neg_one_cases h h2).resolve_left h3) h0
  ---- Case 3: `f(0) = -1`, `f(-1) = 0`
  · rcases eq_or_ne (f 2) (-1) with h3 | h3
    · exact case2_4_quot_IsAnswer h h2 h3 h0
    rcases eq_or_ne (f 2) 1 with h4 | h4
    · exact case2_2_quot_IsAnswer h h2 h4 h3 h0
    rcases eq_or_ne (f 2) 3 with h5 | h5
    · exact case2_3_IsAnswer h h2 h5 h4 h1
    · have h6 := case2_map_two_cases h h2 h1
      rw [or_iff_right h4, or_iff_right h3, or_iff_right h5] at h6
      exact case2_1_quot_IsAnswer h h2 h6 h0 h1 h5

theorem IsAnswer_of_good (h : good f) : IsAnswer f :=
  IsAnswer_of_periodLift h <|
    quot_IsAnswer_of_good (periodLift_is_good h) (zero_of_periodic_periodLift h)

/-- Final solution -/
theorem final_solution : good f ↔ IsAnswer f :=
  ⟨ IsAnswer_of_good, good_of_IsAnswer⟩

end FinalSolution

end IMO2012A5
end IMOSL
