/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.RingTheory.Congruence.Defs
import Mathlib.Algebra.Regular.SMul

/-!
# IMO 2017 A6 (P2, Generalization)

Let $R$ be a ring.
Determine all functions $f : R → R$ such that for any $x, y ∈ R$,
$$ f(f(x) f(y)) + f(x + y) = f(xy). $$

### Progress

Let $I$ be a double-sided ideal of $R$ and $[·] : R → R/I$ be the projection map.
Let $φ : R/I → R$ be a group homomorphism such that $[φ(x)] = x$ for all $x ∈ R/I$.
Let $a$ be an element of the centre $Z(R/I)$ of $R/I$ such that $a^2 = 1$.
Then the function $f(x) = \phi(a(1 - [x]))$ is a solution to the functional equation.
If $2$ and $3$ are non-zero-divisors of $R$, then these are all the functions.
-/

namespace IMOSL
namespace IMO2017A6
namespace Generalization

/-- A function `f : R → G` is called *`ι`-good* if
  `f(ι(f(x)) ι(f(y))) + f(x + y) = f(xy)` for all `x, y : R`. -/
def good [NonUnitalNonAssocSemiring R] [AddZero G] (ι : G →+ R) (f : R → G) :=
  ∀ x y : R, f (ι (f x) * ι (f y)) + f (x + y) = f (x * y)





/-! ### Construction of `ι`-good functions -/

section

variable [NonAssocRing R] (x y : R)

/-- The formula `(1 - x)(1 - y) = 1 - (x + y - xy)`. -/
lemma one_sub_mul_one_sub : (1 - x) * (1 - y) = 1 - (x + y - x * y) := by
  rw [mul_one_sub, one_sub_mul, sub_sub, add_sub_assoc]

/-- The formula `1 - (1 - x)(1 - y) + (1 - (x + y)) = 1 - xy`. -/
lemma one_sub_one_sub_mul_one_sub_add_one_sub_add :
    1 - (1 - x) * (1 - y) + (1 - (x + y)) = 1 - x * y := by
  rw [one_sub_mul_one_sub, sub_sub_cancel, sub_add_sub_cancel']

end


/-- The most general form of good functions. -/
theorem good_of_RingCon [Ring R] [AddZero G] (ι : G →+ R)
    {I : RingCon R} {φ : I.Quotient →+ G} (h : ∀ x : I.Quotient, ↑(ι (φ x)) = x)
    {a : I.Quotient} (ha : a * a = 1) (ha0 : ∀ x, a * x = x * a) :
    good ι (λ x ↦ φ (a * (1 - x))) := by
  intro x y
  calc φ (a * (1 - ι (φ (a * (1 - x))) * ι (φ (a * (1 - y))))) + φ (a * (1 - (x + y)))
    _ = φ (a * (1 - (1 - x) * (1 - y))) + φ (a * (1 - (x + y))) := by
      rw [h, h, ha0 (1 - x), mul_assoc, ← mul_assoc a a, ha, one_mul]
    _ = φ (a * (1 - (1 - x) * (1 - y) + (1 - (x + y)))) := by rw [mul_add, φ.map_add]
    _ = φ (a * (1 - x * y)) := by rw [one_sub_one_sub_mul_one_sub_add_one_sub_add]





/-! ### Congruence of periods induced by `ι`-good functions -/

/-- A function `f : G → α` is called *non-periodic* if for any `c, d : G`
  such that `f(x + c) = f(x + d)` for all `x : G`, we have `c = d`. -/
def nonperiodic [Add G] (f : G → α) :=
  ∀ c d : G, (∀ x, f (x + c) = f (x + d)) → c = d

/-- General additive congruence induced by `f`-period relation. -/
def PeriodEquiv [AddCommSemigroup R] (f : R → α) : AddCon R where
  r c d := ∀ x, f (x + c) = f (x + d)
  iseqv := ⟨λ _ _ ↦ rfl, λ h x ↦ (h x).symm, λ h h0 x ↦ (h x).trans (h0 x)⟩
  add' h h0 x := by rw [← add_assoc, h0, add_right_comm, h, add_right_comm, add_assoc]

/-- If `c` and `d` are `f`-period equivalent, then `f(c) = f(d)`. -/
lemma PeriodEquiv_map_eq [AddCommMonoid R] {f : R → α} (h : PeriodEquiv f c d) :
    f c = f d := by
  rw [← zero_add c, h, zero_add]


namespace good

section

variable [NonUnitalNonAssocSemiring R] [AddZero G]

/-- If `f(a) = f(b)`, `f(c) = f(d)`, and `f(a + c) = f(b + d)`, then `f(ac) = f(bd)`. -/
lemma map_mul_eq_of_map_eq_of_map_add_eq {ι : G →+ R} {f : R → G}
    (hf : good ι f) (hab : f a = f b) (hcd : f c = f d) (h : f (a + c) = f (b + d)) :
    f (a * c) = f (b * d) := by
  rw [← hf, hab, hcd, h, hf]

/-- If `f(a) = f(b)` and `f(c) = f(d)`, then `f(a + c) = f(b + d)` iff `f(ac) = f(bd)`. -/
lemma map_add_eq_iff_map_mul_eq [IsCancelAdd G] {ι : G →+ R} {f : R → G}
    (hf : good ι f) (hab : f a = f b) (hcd : f c = f d) :
    f (a + c) = f (b + d) ↔ f (a * c) = f (b * d) := by
  rw [← hf, hab, hcd, ← hf b, add_left_cancel_iff]

end


section

variable [NonUnitalSemiring R] [AddZero G] [IsCancelAdd G]
  {ι : G →+ R} {f : R → G} (hf : good ι f)
include hf

/-- If `f(x + a) = f(x + b)` and `f(x + c) = f(x + d)` for all `x : R`,
  then `f(x + ac) = f(x + bd)` for all `x : R`. -/
lemma PeriodEquiv_mul (hab : PeriodEquiv f a b) (hcd : PeriodEquiv f c d) :
    PeriodEquiv f (a * c) (b * d) := by
  intro x
  have hab0 : f a = f b := PeriodEquiv_map_eq hab
  have hcd0 : f c = f d := PeriodEquiv_map_eq hcd
  have h (y) : f (y * a) = f (y * b) :=
    hf.map_mul_eq_of_map_eq_of_map_add_eq rfl hab0 (hab y)
  have h0 : f (x * a) = f (x * b) := h x
  replace h : f (x * a * c) = f (x * b * d) := by
    refine hf.map_mul_eq_of_map_eq_of_map_add_eq h0 hcd0 ?_
    rw [hcd, add_comm, add_comm _ d, hf.map_add_eq_iff_map_mul_eq rfl h0,
      ← mul_assoc, h, mul_assoc]
  replace h0 : f (a * c) = f (b * d) :=
    hf.map_mul_eq_of_map_eq_of_map_add_eq hab0 hcd0
      (PeriodEquiv_map_eq ((PeriodEquiv f).add' hab hcd))
  rw [hf.map_add_eq_iff_map_mul_eq rfl h0, ← mul_assoc, h, mul_assoc]

/-- The ring congruence induced by an `ι`-good map. -/
def inducedRingCon : RingCon R :=
  { PeriodEquiv f with mul' := hf.PeriodEquiv_mul }

/-- If `c ∼ d`, then `f(c) = f(d)`. -/
theorem inducedRingConEquiv_map_eq (h : hf.inducedRingCon c d) : f c = f d :=
  PeriodEquiv_map_eq h

/-- The quotient map `R/I → G` induced by `f` via `inducedRingCon`. -/
def Quotient : hf.inducedRingCon.Quotient → G :=
  Quotient.lift f λ _ _ ↦ hf.inducedRingConEquiv_map_eq

/-- The induced quotient map is non-periodic. -/
theorem Quotient_is_nonperiodic : nonperiodic hf.Quotient :=
  Quotient.ind₂ λ _ _ h ↦ Quot.sound λ x ↦ h x

end


/-- The quotient map induced by `f` is `q ∘ ι`-good, where `q : R → R/I` is the quotient. -/
theorem Quotient_is_good [Semiring R] [AddZero G] [IsCancelAdd G]
    {ι : G →+ R} {f : R → G} (hf : good ι f) :
    good (hf.inducedRingCon.mk'.toAddMonoidHom.comp ι) hf.Quotient :=
  Quotient.ind₂ hf





/-! ### Properties of `ι`-good functions -/

section

variable [NonAssocSemiring R] [AddZero G] [IsCancelAdd G]
  {ι : G →+ R} {f : R → G} (hf : good ι f) (h : f a = f b)
include hf h

/-- If `f(a) = f(b)`, then `f(a + 1) = f(b + 1)`. -/
lemma map_add_one_eq_of_map_eq : f (a + 1) = f (b + 1) := by
  rw [hf.map_add_eq_iff_map_mul_eq h rfl, mul_one, h, mul_one]

/-- If `f(a) = f(b)`, then `f(a + 2) = f(b + 2)`. -/
lemma map_add_two_eq_of_map_eq : f (a + 2) = f (b + 2) := by
  replace h : f (a + 1 + 1) = f (b + 1 + 1) :=
    hf.map_add_one_eq_of_map_eq (hf.map_add_one_eq_of_map_eq h)
  rwa [add_assoc, add_assoc, one_add_one_eq_two] at h

/-- If `f(a) = f(b)`, then `f(2a) = f(2b)`. -/
lemma map_two_mul_eq_of_map_eq : f (2 * a) = f (2 * b) := by
  rw [← hf.map_add_eq_iff_map_mul_eq rfl h, add_comm,
    hf.map_add_two_eq_of_map_eq h, add_comm]

end


section

variable [NonAssocRing R] [AddZero G] [IsCancelAdd G]
  {ι : G →+ R} {f : R → G} (hf : good ι f)
include hf

/-- If `f(a) = f(b)`, then `f(-(a + 1)) = f(-(b + 1))`. -/
lemma map_neg_add_one_eq_of_map_eq (h : f a = f b) : f (-(a + 1)) = f (-(b + 1)) := by
  have h0 : f (a + 1) = f (b + 1) := hf.map_add_one_eq_of_map_eq h
  replace h : f (a + 1 + -1) = f (b + 1 + -1) := by
    rw [add_neg_cancel_right, add_neg_cancel_right, h]
  replace h : f ((a + 1) * -1) = f ((b + 1) * -1) :=
    hf.map_mul_eq_of_map_eq_of_map_add_eq h0 rfl h
  rwa [mul_neg_one, mul_neg_one] at h

/-- If `f(a) = f(b)`, then `f(-a) = f(-b)`. -/
lemma map_neg_eq_of_map_eq (h : f a = f b) : f (-a) = f (-b) := by
  have h0 : f (-(a + 1) + 1) = f (-(b + 1) + 1) :=
    hf.map_add_one_eq_of_map_eq (hf.map_neg_add_one_eq_of_map_eq h)
  rwa [neg_add_rev, neg_add_cancel_comm, neg_add_rev, neg_add_cancel_comm] at h0

/-- We have `f(-a) = f(-b)` if and only if `f(a) = f(b)`. -/
lemma map_neg_eq_iff_map_eq : f (-a) = f (-b) ↔ f a = f b :=
  ⟨λ h ↦ by simpa only [neg_neg] using hf.map_neg_eq_of_map_eq h, hf.map_neg_eq_of_map_eq⟩

end


section

variable [NonAssocSemiring R] [AddZero G] {ι : G →+ R} {f : R → G} (hf : good ι f)
include hf

/-- For any `x : R`, we have `f(ι(f(0)) ι(f(x))) + f(x) = f(0)`. -/
lemma map_ι_map_zero_mul_ι_map_add_map (x) : f (ι (f 0) * ι (f x)) + f x = f 0 := by
  simpa only [zero_add, zero_mul] using hf 0 x

/-- If `f(d) = 0` then `f(xd) = f(0) + f(x + d)` for any `x : R`. -/
lemma map_mul_kernel (hd : f d = 0) (x) : f (x * d) = f 0 + f (x + d) := by
  rw [← hf, hd, ι.map_zero, mul_zero]

/-- If `f(d) = 0` then `f(0) + f(d + 1) = 0`. -/
lemma map_kernel_add_one (hd : f d = 0) : f 0 + f (d + 1) = 0 := by
  rw [add_comm, ← hf.map_mul_kernel hd, one_mul, hd]

end


/-- We have `f(ι(f(0))^2) = 0`. -/
lemma map_ι_map_zero_mul_self [NonAssocSemiring R] [AddZeroClass G] [IsCancelAdd G]
  {ι : G →+ R} {f : R → G} (hf : good ι f) : f (ι (f 0) * ι (f 0)) = 0 := by
  rw [← add_right_cancel_iff (a := f 0), hf.map_ι_map_zero_mul_ι_map_add_map, zero_add]


section

variable [Semiring R] [AddCancelMonoid G] {ι : G →+ R} {f : R → G} (hf : good ι f)
include hf

/-- We have `f(0) + f(2 ι(f(0))^2) = 0`. -/
lemma map_two_mul_ι_map_zero_mul_self : f 0 + f (2 * (ι (f 0) * ι (f 0))) = 0 := by
  let C := ι (f 0)
  -- First, we prove that there exists `b` such that `f(b) = 2f(0)`.
  obtain ⟨b, hb⟩ : ∃ b, f b = f 0 + f 0 := by
    refine ⟨ι (f 0) * ι (f (C * C + 1)), ?_⟩
    rw [← add_right_cancel_iff (a := f (C * C + 1)), add_assoc,
      hf.map_kernel_add_one hf.map_ι_map_zero_mul_self,
      add_zero, hf.map_ι_map_zero_mul_ι_map_add_map]
  ---- Then substituting `(x, y) = (0, b)` almost gives the desired equality.
  replace h : f (2 * (C * C)) + f 0 = 0 := by
    refine add_right_cancel (b := f 0) ?_
    calc f (2 * (C * C)) + f 0 + f 0
      _ = f (ι (f 0) * ι (f b)) + f b := by
        rw [hb, ι.map_add, mul_add, ← two_mul, add_assoc]
      _ = 0 + f 0 := by
        rw [hf.map_ι_map_zero_mul_ι_map_add_map, zero_add]
  ---- Add both sides by `f(0)` on the right and then subtract on the left.
  rw [← add_right_cancel_iff (a := f 0), add_assoc, h, add_zero, zero_add]

/-- If `f(c) = 0`, then `f(x + c) = f(x + 1)` for all `x : R`. -/
theorem period_of_map_eq_zero' (hc : f c = 0) :
    ∀ x, f (x + c * c + c) = f (x + c * c + 1) := by
  let C := ι (f 0)
  have hc0 (x) : f (x * c) = f 0 + f (x + c) := hf.map_mul_kernel hc x
  have hc1 : f 0 + f (c + 1) = 0 := hf.map_kernel_add_one hc
  ---- First we show that `f(0) + f(2c) = 0`.
  have hc3 : f 0 + f (2 * c) = 0 := by
    rw [hf.map_two_mul_eq_of_map_eq (hc.trans hf.map_ι_map_zero_mul_self.symm),
      hf.map_two_mul_ι_map_zero_mul_self]
  ---- We now get `f(c^2) = 0`, and so `f(xc^2) = f(0) + f(x + c^2)` for all `x`.
  have hc2 : f (c * c) = 0 := by rw [hc0, ← two_mul, hc3]
  replace hc2 (x) : f (x * (c * c)) = f 0 + f (x + c * c) := hf.map_mul_kernel hc2 x
  ---- Next we show `f(c^3) = 0`.
  replace hc3 : f (c * c * c) = 0 := by
    have h : f (2 * c + 1) = f (c + 1 + 1) :=
      hf.map_add_one_eq_of_map_eq (add_left_cancel (hc3.trans hc1.symm))
    rw [hc0, ← add_one_mul, hc0, add_right_comm, ← two_mul, h,
      add_assoc c, one_add_one_eq_two, add_comm, ← hc0, hc3]
  ---- Now we proceed by writing `f(xc^4)` in two ways.
  intro x; refine add_left_cancel (a := f 0) (add_left_cancel (a := f 0) ?_)
  calc f 0 + (f 0 + f (x + c * c + c))
    _ = f (x * c * (c * c * c)) := by rw [hf.map_mul_kernel hc3, ← hc0, add_mul]
    _ = f (x * (c * c) * (c * c)) := by simp only [mul_assoc]
    _ = f 0 + (f 0 + f (x + c * c + 1)) := by rw [hc2, ← add_one_mul, hc2, add_right_comm]

/-- For any `x : R`, we have `f(x + ι(f(0))^2) = f(x + 1)`. -/
theorem map_add_ι_map_zero_mul_self (x) : f (x + ι (f 0) * ι (f 0)) = f (x + 1) := by
  let D := ι (f 0) * ι (f 0)
  have h : f D = 0 := hf.map_ι_map_zero_mul_self
  ---- First show that there exists `d` such that `d + ι(f(0))^4 = 0`.
  obtain ⟨d, hd⟩ : ∃ d, d + D * D = 0 := by
    refine ⟨D * (ι (f 0) * ι (f (D + 1))), ?_⟩
    rw [← mul_add, add_comm, ← mul_add, ← ι.map_add,
      hf.map_kernel_add_one h, ι.map_zero, mul_zero, mul_zero]
  ---- Now the previous lemma immediately implies what we want.
  have h0 : f (x + d + D * D + D) = f (x + d + D * D + 1) :=
    hf.period_of_map_eq_zero' h (x + d)
  rwa [add_assoc x, hd, add_zero] at h0

/-- We have `f(1) = 0`. -/
theorem map_one_eq_zero : f 1 = 0 := by
  rw [← zero_add 1, ← hf.map_add_ι_map_zero_mul_self, zero_add, hf.map_ι_map_zero_mul_self]

/-- For any `x : R`, we have `f(0) + f(x + 1) = f(x)`. -/
theorem map_zero_add_map_add_one (x) : f 0 + f (x + 1) = f x := by
  simpa only [mul_one] using (hf.map_mul_kernel hf.map_one_eq_zero x).symm

end


/-- For any `x : R`, we have `f(x - 1) = f(0) + f(x)`. -/
theorem map_sub_one [Ring R] [AddCancelMonoid G]
    {ι : G →+ R} {f : R → G} (hf : good ι f) (x) : f (x - 1) = f 0 + f x := by
  simpa only [sub_add_cancel] using (hf.map_zero_add_map_add_one (x - 1)).symm


section

variable [Ring R] [AddCancelCommMonoid G] {ι : G →+ R} {f : R → G} (hf : good ι f)
include hf

/-- For any `x : R`, we have `f(1 - ι(f(0)) ι(f(x))) = f(x)`. -/
theorem map_one_sub_map_ι_map_zero_mul_ι_map (x) : f (1 - ι (f 0) * ι (f x)) = f x := by
  let C := ι (f 0)
  have h : ι (f (C * ι (f x))) = -ι (f x) + C := by
    rw [eq_neg_add_iff_add_eq, add_comm, ← ι.map_add, hf.map_ι_map_zero_mul_ι_map_add_map]
  refine (add_right_inj (f 0)).mp ?_
  calc f 0 + f (1 - C * ι (f x))
    _ = f (C * ι (f (C * ι (f x)))) + f 0 := by
      rw [h, mul_add, hf.map_add_ι_map_zero_mul_self, mul_neg, neg_add_eq_sub, add_comm]
    _ = f (C * ι (f (C * ι (f x)))) + f (C * ι (f x)) + f x := by
      rw [add_assoc, hf.map_ι_map_zero_mul_ι_map_add_map]
    _ = f 0 + f x := by rw [hf.map_ι_map_zero_mul_ι_map_add_map]

/-- For any `x : R`, we have `f(x) + f(-x) = 2f(0)`. -/
theorem map_add_map_neg (x) : f x + f (-x) = 2 • f 0 := by
  have h : f 0 + f (ι (f 0) * ι (f x)) = f (-x) := by
    rw [← hf.map_sub_one, ← neg_sub, hf.map_neg_eq_iff_map_eq]
    exact hf.map_one_sub_map_ι_map_zero_mul_ι_map x
  rw [← h, add_rotate', hf.map_ι_map_zero_mul_ι_map_add_map, two_nsmul]

end





/-! ### Properties of non-periodic `ι`-good functions -/

section

variable [Semiring R] [IsCancelAdd R] [AddCancelMonoid G] {ι : G →+ R}
  {f : R → G} (hf : good ι f) (hf0 : nonperiodic f)
include hf hf0

/-- If `f` is non-periodic and `f(c) = 0`, then `c = 1`. -/
theorem map_eq_zero_imp_eq_one (h : f c = 0) : c = 1 := by
  refine add_left_cancel (a := c * c) (hf0 _ _ λ x ↦ ?_)
  rw [← add_assoc, ← add_assoc, hf.period_of_map_eq_zero' h]

/-- If `f` is non-periodic, then `f(x) = 0` if and only if `x = 1`. -/
theorem map_eq_zero_iff_eq_one : f x = 0 ↔ x = 1 :=
  ⟨hf.map_eq_zero_imp_eq_one hf0, λ h ↦ h ▸ hf.map_one_eq_zero⟩

/-- If `f` is non-periodic, then `ι(f(0))^2 = 1`. -/
theorem ι_map_zero_mul_self : ι (f 0) * ι (f 0) = 1 :=
  hf.map_eq_zero_imp_eq_one hf0 hf.map_ι_map_zero_mul_self

end


/-- If `G` is `2`- and `3`-torsion free, then any function `g : R → G` satisfying
  `g(x + y - xy) + g(1 - (x + y)) = g(1 - xy)` for all `x, y : R` is a homomorphism. -/
theorem sideFE [NonAssocRing R] [AddCancelCommMonoid G]
    (hG2 : IsSMulRegular G 2) (hG3 : IsSMulRegular G 3)
    {g : R → G} (hg : ∀ x y, g (x + y - x * y) + g (1 - (x + y)) = g (1 - x * y)) :
    ∃ φ : R →+ G, g = φ := by
  ---- First get `g(-x) = -g(x)` and `g(x + 1) = g(x) + g(1)` for all `x`.
  have hg0 (x) : g x + g (1 - x) = g 1 := by
    simpa only [zero_add, zero_mul, sub_zero] using hg 0 x
  have hg1 (x) : g 1 + g (-x) = g (1 - x) := by
    simpa only [mul_one, add_sub_cancel_left, sub_add_cancel_right] using hg x 1
  replace hg1 (x) : g x + g (-x) = 0 := by
    rw [← add_eq_right (b := g 1), add_right_comm, add_assoc, hg1, hg0]
  have hg2 (x) : g (x + 1) = g x + g 1 := by
    have h := hg 1 (-x)
    rwa [one_mul, add_sub_cancel_right, sub_add_cancel_left,
      neg_neg, sub_neg_eq_add, add_comm, eq_comm, add_comm] at h
  ---- Since `G` is `2`-torsion-free, we get `g(0) = 0`, so it remains to prove additivity.
  have hg3 : g 0 = 0 := by
    refine hG2 (?_ : 2 • g 0 = 2 • 0)
    rw [two_nsmul, nsmul_zero, ← hg1 0, neg_zero]
  refine ⟨⟨⟨g, hg3⟩, ?_⟩, rfl⟩; simp only
  ---- By induction, we get `g(x + n) = g(x) + ng(1)` for any `x : R` and `n : ℕ`.
  have hg4 (x : R) (n : ℕ) : g (x + n) = g x + n • g 1 := by
    induction n with
    | zero => rw [Nat.cast_zero, add_zero, zero_nsmul, add_zero]
    | succ n n_ih => rw [succ_nsmul, Nat.cast_succ, ← add_assoc, hg2, n_ih, add_assoc]
  ---- Now we prove `g((x + 1)(y + 1)) = g(xy) + g(x + y) + g(1)` for all `x, y : R`.
  replace hg (x y) : g (x + y + 1) = g (1 - x * y) + g (x * y + (x + y)) := by
    rw [← neg_mul_neg, ← hg, neg_mul_neg, ← neg_add, sub_neg_eq_add,
      ← add_rotate (g _), ← neg_add', add_comm, add_comm (x * y), hg1, zero_add]
  replace hg (x y) : g ((x + 1) * (y + 1)) = g (x * y) + g (x + y) + g 1 := by
    rw [add_assoc, ← hg2, hg, ← add_assoc, hg0, add_one_mul, mul_add_one,
      add_assoc, ← add_assoc x, ← add_assoc, hg2, add_comm]
  ---- By induction on `n`, we have `g((x + n)(y + n)) = g(xy) + n g(x + y) + n^2 g(1)`.
  replace hg (x y) (n : ℕ) :
      g ((x + n) * (y + n)) = g (x * y) + n • g (x + y) + (n * n) • g 1 := by
    induction n with
    | zero => simp_rw [Nat.cast_zero, Nat.mul_zero, zero_nsmul, add_zero]
    | succ n n_ih =>
        calc g ((x + ↑(n + 1)) * (y + ↑(n + 1)))
        _ = g ((x + n + 1) * (y + n + 1)) := by rw [Nat.cast_succ, add_assoc, add_assoc]
        _ = g (x * y) + n • g (x + y) + (n * n) • g 1 + g (x + y + ↑(n + n)) + g 1 := by
          rw [hg, n_ih, add_add_add_comm, Nat.cast_add]
        _ = g (x * y) + ((n • g (x + y) + g (x + y)) + (n * n + (n + n)) • g 1) + g 1 := by
          rw [hg4, add_assoc (g _), add_assoc (g _), add_add_add_comm, add_nsmul _ (n * n)]
        _ = g (x * y) + (n + 1) • g (x + y) + (n * n + (n + n) + 1) • g 1 := by
          rw [← add_assoc, ← succ_nsmul, add_assoc, succ_nsmul (g 1)]
        _ = g (x * y) + (n + 1) • g (x + y) + ((n + 1) * (n + 1)) • g 1 := by
          rw [add_right_inj, Nat.succ_mul, Nat.mul_succ]
          iterate 3 rw [Nat.add_assoc]
  ---- Plugging `x = 0` and `y = t - n` gives `g(nt) = ng(t)` for all `n : ℕ` and `t : R`.
  replace hg0 (t) (n : ℕ) : g (n * t) = n • g t := by
    have h := hg 0 (t - n) n
    rwa [zero_add, zero_mul, hg3, zero_add,  mul_nsmul,
      ← nsmul_add, ← hg4, zero_add, sub_add_cancel] at h
  ---- We only need `g(2t) = 2g(t)` and `g(3t) = 3g(t)`.
  replace hg2 (t) : g (2 * t) = 2 • g t := hg0 t 2
  replace hg3 (t) : g (3 * t) = 3 • g t := hg0 t 3
  ---- We also only need `g((x + n)(y + n)) = g(xy) + n g(x + y) + n^2 g(1)` for `n = 2, 3`.
  replace hg0 (x y) : g ((x + 2) * (y + 2)) = g (x * y) + 2 • g (x + y) + 4 • g 1 := hg x y 2
  replace hg1 (x y) : g ((x + 3) * (y + 3)) = g (x * y) + 3 • g (x + y) + 9 • g 1 := hg x y 3
  ---- Next, we get `g((x + 1)(y + 2)) = g(xy) + g(2x + y) + 2 g(1)`.
  replace hg (x y) : g ((x + 1) * (y + 2)) = g (x * y) + g (2 * x + y) + 2 • g 1 := by
    have h := hg0 (2 * x) y
    have X (t u : R) : 2 * t * u = 2 * (t * u) := by rw [two_mul, two_mul, add_mul]
    rw [← mul_add_one, X, hg2, X, hg2, mul_nsmul _ 2 2, ← nsmul_add, ← nsmul_add] at h
    exact hG2 h
  ---- We also get `g((x + 2)(y + 1)) = g(xy) + g(x + 2y) + 2 g(1)`.
  replace hg2 (x y) : g ((x + 2) * (y + 1)) = g (x * y) + g (x + 2 * y) + 2 • g 1 := by
    have h := hg0 x (2 * y)
    have X (t u : R) : t * (2 * u) = 2 * (t * u) := by rw [two_mul, two_mul, mul_add]
    rw [← mul_add_one, X, hg2, X, hg2, mul_nsmul _ 2 2, ← nsmul_add, ← nsmul_add] at h
    exact hG2 h
  ---- Writing `g((x + 3)(y + 3))` in two ways give `g(2x + y) + g(x + 2y) = 3 g(x + y)`.
  replace hg (x y) : g (2 * x + y) + g (x + 2 * y) = 3 • g (x + y) := by
    -- First add `g(xy) + 9 g(1)` to both sides of the equality to be proved.
    suffices g ((x + 3) * (y + 3)) = g (x * y) + (g (2 * x + y) + g (x + 2 * y)) + 9 • g 1 by
      rwa [hg1, add_left_inj, add_right_inj, eq_comm] at this
    -- Now do the calculations.
    calc g ((x + 3) * (y + 3))
      _ = g ((x + 1 + 2) * (y + 2 + 1)) := by
        rw [add_assoc, add_assoc, add_comm 1, two_add_one_eq_three]
      _ = g ((x + 1) * (y + 2)) + g (x + 2 * y + (2 * 2 + 1)) + 2 • g 1 := by
        rw [hg2, mul_add 2, add_add_add_comm, add_comm 1]
      _ = g ((x + 1) * (y + 2)) + g (x + 2 * y + (5 : ℕ)) + 2 • g 1 := by
        rw [Nat.cast_succ, two_mul 2, two_add_two_eq_four, Nat.cast_ofNat]
      _ = g ((x + 1) * (y + 2)) + g (x + 2 * y) + 7 • g 1 := by
        rw [hg4, ← add_assoc, add_assoc, ← add_nsmul]
      _ = g (x * y) + (g (2 * x + y) + g (x + 2 * y)) + 9 • g 1 := by
        rw [hg, add_assoc, add_add_add_comm, add_assoc (g _), ← add_nsmul]
  ---- We finish by substituting `(x, y) ↦ (2x - y, 2y - x)`.
  replace hg4 (x y : R) : 2 * (2 * x - y) + (2 * y - x) = 3 * x := by
    rw [mul_sub, sub_add_sub_cancel, ← two_add_one_eq_three, add_one_mul,
      two_mul, two_mul, ← add_assoc, add_sub_cancel_right]
  intro x y; specialize hg (2 * x - y) (2 * y - x)
  rw [hg4, add_comm (2 * x - y), hg4, hg3, hg3, ← nsmul_add, sub_add_sub_comm,
    ← mul_add, add_comm y, two_mul, add_sub_cancel_right] at hg
  exact (hG3 hg).symm


section

variable [Ring R] [AddCancelCommMonoid G]

/-- If `G` is `2`-torsion free, then a non-periodic good function `R → G` is injective. -/
theorem injective_of_IsSMulRegular_two (hG2 : IsSMulRegular G 2)
    {ι : G →+ R} {f : R → G} (hf : good ι f) (hf0 : nonperiodic f) : f.Injective := by
  intro a b h
  have h0 : f (a * b) = f (b * a) :=
    hf.map_mul_eq_of_map_eq_of_map_add_eq h h.symm (congrArg f (add_comm a b))
  replace h0 : f (a * -b) = f (b * -a) := by
    rw [mul_neg, mul_neg, hf.map_neg_eq_iff_map_eq, h0]
  replace h0 : f (a + -b) = f (b + -a) :=
    (hf.map_add_eq_iff_map_mul_eq h (hf.map_neg_eq_of_map_eq h).symm).mpr h0
  replace h : f (-(a - b)) = f (a - b) := by
    rw [neg_sub, sub_eq_add_neg, ← h0, ← sub_eq_add_neg]
  replace h : 2 • f (a - b) = 2 • f 0 := by
    rw [← hf.map_add_map_neg (a - b), h, two_nsmul]
  replace h : f (a - b) = f 0 := hG2 h
  rwa [← hf.map_zero_add_map_add_one, add_eq_left,
    hf.map_eq_zero_iff_eq_one hf0, add_eq_right, sub_eq_zero] at h

/-- If `f` is injective, then there exists `a ∈ Z(R)` such that
  `a^2 = 1` and `ι(f(x)) = a(1 - x)` for all `x : R`. -/
theorem exists_central_mul_self_eq_one
    {ι : G →+ R} {f : R → G} (hf : good ι f) (hf0 : f.Injective) :
    ∃ a : R, a * a = 1 ∧ (∀ x, a * x = x * a) ∧ (∀ x, ι (f x) = a * (1 - x)) := by
  ---- The choice of `a` that works is `ι(f(0))`.
  let a := ι (f 0)
  ---- First show that `a^2 = 1` and `ι(f(x)) = a(1 - x)` for all `x : R`.
  have ha : a * a = 1 := hf0 (hf.map_ι_map_zero_mul_self.trans hf.map_one_eq_zero.symm)
  have ha0 (x) : ι (f x) = a * (1 - x) := calc
    _ = a * (1 - (1 - a * ι (f x))) := by rw [sub_sub_cancel, ← mul_assoc, ha, one_mul]
    _ = a * (1 - x) := by rw [hf0 (hf.map_one_sub_map_ι_map_zero_mul_ι_map x)]
  ---- Now it remains to show that `ax = xa` for all `x : R`.
  refine ⟨a, ha, λ x ↦ ?_, ha0⟩
  ---- Choose some `t` such that `ι(f(t)) = x`.
  obtain ⟨t, rfl⟩ : ∃ t, ι (f t) = x :=
    ⟨1 - a * x, by rw [ha0, sub_sub_cancel, ← mul_assoc, ha, one_mul]⟩
  ---- Compare the original FE with `(x, y) = (0, t)` and `(x, y) = (t, 0)`.
  refine hf0 (add_right_cancel (b := f t) ?_)
  rw [hf.map_ι_map_zero_mul_ι_map_add_map, ← mul_zero t, ← hf, add_zero]

/-- If `G` is `2`- and `3`-torsion free, then any non-periodic `ι`-good function
  can be written as `φ(a(1 - x))` for some `φ : R →+ G` with `ι ∘ φ = id_R` and
  `a ∈ Z(R)` with `a^2 = 1`. -/
theorem IsSMulRegular_two_three_nonperiodic_imp
    (hG2 : IsSMulRegular G 2) (hG3 : IsSMulRegular G 3)
    {ι : G →+ R} {f : R → G} (hf : good ι f) (hf0 : nonperiodic f) :
    ∃ (φ : R →+ G) (_ : ∀ x, ι (φ x) = x) (a : R) (_ : a * a = 1) (_ : ∀ x, a * x = x * a),
      f = λ x : R ↦ φ (a * (1 - x)) := by
  ---- Recall that there exists `a ∈ Z(R)` with `a^2 = 1` and `ι(f(x)) = a(1 - x)`.
  obtain ⟨a, ha, ha0, ha1⟩ :
      ∃ a, a * a = 1 ∧ (∀ x, a * x = x * a) ∧ (∀ x, ι (f x) = a * (1 - x)) :=
    hf.exists_central_mul_self_eq_one (hf.injective_of_IsSMulRegular_two hG2 hf0)
  ---- Substituting into the original FE gives `f((1 - x)(1 - y)) + f(x + y) = f(xy)`.
  have hf1 (x y) : f ((1 - x) * (1 - y)) + f (x + y) = f (x * y) := by
    rw [← hf x y, ha1, ha1, ha0, mul_assoc, ← mul_assoc a, ha, one_mul]
  ---- Then the function `x ↦ f(1 - x)` is a group homomorphism.
  replace hf1 (x y) :
      f (1 - (x + y - x * y)) + f (1 - (1 - (x + y))) = f (1 - (1 - x * y)) := by
    rw [sub_sub_cancel, sub_sub_cancel, add_sub_assoc,
      ← one_sub_mul, ← sub_sub, ← mul_one_sub, hf1]
  obtain ⟨φ, hφ⟩ : ∃ φ : R →+ G, (λ x ↦ f (1 - x)) = φ := sideFE hG2 hG3 hf1
  ---- We pick `x ↦ φ(ax)` instead of `φ` and work everything out now.
  replace hφ (x) : (φ.comp (AddMonoidHom.mulLeft a)) x = f (1 - a * x) := by
    rw [φ.comp_apply, AddMonoidHom.coe_mulLeft, ← hφ]
  refine ⟨φ.comp (AddMonoidHom.mulLeft a), ?_, a, ha, ha0, ?_⟩
  · intro x; rw [hφ, ha1, sub_sub_cancel, ← mul_assoc, ha, one_mul]
  · funext x; rw [hφ, ← mul_assoc, ha, one_mul, sub_sub_cancel]

end

end good





/-! ### Summary -/

/-- The criterion for a function `f : R → G` to be `ι`-good. -/
theorem good_iff [Ring R] [AddCancelCommMonoid G]
    (hG2 : IsSMulRegular G 2) (hG3 : IsSMulRegular G 3) {ι : G →+ R} {f : R → G} :
    good ι f ↔ ∃ (I : RingCon R) (φ : I.Quotient →+ G) (_ : ∀ x, ↑(ι (φ x)) = x)
      (a : I.Quotient) (_ : a * a = 1) (_ : ∀ x, a * x = x * a),
      f = λ x : R ↦ φ (a * (1 - x)) := by
  refine ⟨λ hf ↦ ?_, λ hf ↦ ?_⟩
  ---- The `←` direction.
  · obtain ⟨φ, hφ, a, ha, ha0, h⟩ :=
      hf.Quotient_is_good.IsSMulRegular_two_three_nonperiodic_imp
        hG2 hG3 hf.Quotient_is_nonperiodic
    exact ⟨hf.inducedRingCon, φ, hφ, a, ha, ha0, funext λ x ↦ congrFun h x⟩
  ---- The `→` direction.
  · rcases hf with ⟨I, φ, hφ, a, ha, ha0, rfl⟩
    exact good_of_RingCon ι hφ ha ha0

/-- If `n : ℕ` is left regular as an element of a ring `R`, then `R` is `n`-torsion free. -/
theorem IsSMulRegular_of_IsLeftRegular_Nat
    [NonAssocSemiring R] {n : ℕ} (hRn : IsLeftRegular (n : R)) : IsSMulRegular R n :=
  λ a b h ↦ hRn (by simpa only [nsmul_eq_mul] using h)

/-- Final solution -/
theorem final_solution
    [Ring R] (hR2 : IsLeftRegular (2 : R)) (hR3 : IsLeftRegular (3 : R)) {f : R → R} :
    (∀ x y, f (f x * f y) + f (x + y) = f (x * y)) ↔
      ∃ (I : RingCon R) (φ : I.Quotient →+ R) (_ : ∀ x, ↑(φ x) = x)
        (a : I.Quotient) (_ : a * a = 1) (_ : ∀ x, a * x = x * a),
        f = λ x : R ↦ φ (a * (1 - x)) :=
  good_iff (IsSMulRegular_of_IsLeftRegular_Nat hR2)
    (IsSMulRegular_of_IsLeftRegular_Nat hR3) (ι := AddMonoidHom.id R)
