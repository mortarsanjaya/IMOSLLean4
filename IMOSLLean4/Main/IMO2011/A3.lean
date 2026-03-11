/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs

/-!
# IMO 2011 A3

Let $R$ be an integral domain of characteristic not equal to $2$.
Find all pairs $(f, g)$ of functions $f, g : R → R$ such that for any $x, y ∈ R$,
$$ g(f(x + y)) = f(x) + (2x + y) g(y). $$

### Answer

$(f, g) = (0, 0)$ and $(f(x), g(x)) = (x^2 + C, x)$ for some $C ∈ R$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2011SL.pdf),
  but linearity of $g$ uses the proof in the comment section to avoid Ravi substitution.
We still need the equations $g(f(x)) = f(-x)$ and $f(-a) = f(-b) + (a - b) g(a + b)$.
Many steps of the problem generalize; we do not even require associativity on $R$.
-/

namespace IMOSL
namespace IMO2011A3

/-- A pair of functions `f, g : R → R` is called *good* if
  `g(f(x + y)) = f(x) + (2x + y) g(y)` for any `x, y : R`. -/
def good [NonUnitalNonAssocSemiring R] (f g : R → R) :=
  ∀ x y, g (f (x + y)) = f x + (2 • x + y) * g y

/-- The pair `(x ↦ x^2 + C, x ↦ x)` is good for any `C : R`. -/
theorem mul_self_add_const_is_good [NonUnitalNonAssocCommSemiring R] (C : R) :
    good (λ x ↦ x * x + C) id := by
  intro x y; calc (x + y) * (x + y) + C
    _ = x * x + x * y + (x + y) * y + C := by rw [mul_add, add_mul, mul_comm y]
    _ = x * x + (x + (x + y)) * y + C := by rw [add_assoc (x * x), ← add_mul]
    _ = x * x + C + (2 • x + y) * y := by rw [two_nsmul, add_right_comm, add_assoc x]

/-- The pair `(0, 0)` is good. -/
theorem zero_is_good [NonUnitalNonAssocSemiring R] : good (λ _ : R ↦ 0) (λ _ ↦ 0) :=
  λ _ _ ↦ ((zero_add _).trans (mul_zero _)).symm


namespace good

section

variable [NonUnitalNonAssocRing R] {f g : R → R} (h : good f g)
include h

/-- We have `g(f(x)) = -x` for any `x : R`. -/
theorem gf_eq_f_neg (x : R) : g (f x) = f (-x) := by
  specialize h (-x) (2 • x)
  rwa [← nsmul_add, neg_add_cancel, nsmul_zero, zero_mul,
    add_zero, two_nsmul, neg_add_cancel_left] at h

/-- We have `f(-a) = f(-b) + (a - b) g(a + b)` for any `a, b : R`. -/
theorem f_neg_eq_f_neg_add (a b : R) : f (-a) = f (-b) + (a - b) * g (a + b) := calc
  _ = g (f a) := (h.gf_eq_f_neg a).symm
  _ = g (f (-b + (a + b))) := congrArg (g ∘ f) (neg_add_cancel_comm_assoc b a).symm
  _ = f (-b) + (2 • -b + (a + b)) * g (a + b) := h _ _
  _ = f (-b) + (a - b) * g (a + b) := by
    rw [two_nsmul, add_assoc, neg_add_cancel_comm_assoc, neg_add_eq_sub]

/-- We have `f(-x) = x g(x) + f(0)` for any `x : R`. -/
theorem f_eq_x_mul_g_add_f_zero (x : R) : f (-x) = x * g x + f 0 := by
  rw [h.f_neg_eq_f_neg_add x 0, neg_zero, sub_zero, add_zero, add_comm]

/-- We have `(f(x) - xg(x)) - (f(y) - yg(y)) = 2(yg(x) - xg(y))` for any `x, y : R`. -/
theorem f_sub_self_mul_g_diff (x y : R) :
    (f x - x * g x) - (f y - y * g y) = 2 • (y * g x - x * g y) := by
  have h0 (a b : R) : g (f (a + b)) = f a + 2 • (a * g b) + b * g b := by
    rw [add_assoc, h, add_right_inj, add_mul, two_nsmul, two_nsmul, add_mul]
  rw [nsmul_sub, sub_eq_sub_iff_add_eq_add, ← add_sub_right_comm, ← add_sub_assoc,
    sub_eq_sub_iff_add_eq_add, ← h0, add_comm _ (f y), ← h0, add_comm]

/-- We have `2y(g(x) - g(0)) = 2x(g(y) - g(0))` for any `x, y : R`. -/
theorem two_nsmul_mul_g_sub_g_zero (x y : R) :
    2 • (y * (g x - g 0)) = 2 • (x * (g y - g 0)) := by
  suffices 2 • (y * g x - x * g y) = 2 • (y * g 0) - 2 • (x * g 0) by
    rwa [mul_sub, nsmul_sub, mul_sub, nsmul_sub, sub_eq_sub_iff_sub_eq_sub, ← nsmul_sub]
  calc 2 • (y * g x - x * g y)
    _ = (f x - x * g x) - (f y - y * g y) := (h.f_sub_self_mul_g_diff x y).symm
    _ = (f x - x * g x - (f 0 - 0 * g 0)) - (f y - y * g y - ((f 0 - 0 * g 0))) :=
      (sub_sub_sub_cancel_right _ _ _).symm
    _ = 2 • (0 * g x - x * g 0) - 2 • (0 * g y - y * g 0) :=
      congrArg₂ _ (h.f_sub_self_mul_g_diff _ _) (h.f_sub_self_mul_g_diff _ _)
    _ = -(2 • (x * g 0)) - -(2 • (y * g 0)) := by
      iterate 2 rw [zero_mul, zero_sub, neg_nsmul]
    _ = 2 • (y * g 0) - 2 • (x * g 0) := neg_sub_neg _ _

end


section

variable [NonAssocRing R]

/-- If `2` is not a zero divisor in `R`, then `g` is (right) linear. -/
theorem g_right_linear (hR2 : IsLeftRegular (2 : R)) {f g : R → R} (h : good f g) :
    ∃ A B : R, ∀ x : R, g x = x * A + B := by
  refine ⟨g 1 - g 0, g 0, λ x ↦ eq_add_of_sub_eq (hR2 ?_)⟩
  calc 2 * (g x - g 0)
    _ = 2 • (g x - g 0) := (nsmul_eq_mul _ _).symm
    _ = 2 • (1 * (g x - g 0)) := congrArg (2 • ·) (one_mul _).symm
    _ = 2 • (x * (g 1 - g 0)) := h.two_nsmul_mul_g_sub_g_zero x 1
    _ = 2 * (x * (g 1 - g 0)) := nsmul_eq_mul _ _

/-- If `R` is a domain and `2 ≠ 0` in `R`, then `(f, g)` is either
  `(x ↦ x^2 + C, x ↦ x)` for some `C : R` or `(0, 0)`. -/
theorem solve_of_NoZeroDivisors_two_ne_zero
    [IsLeftCancelMulZero R] (hR2 : (2 : R) ≠ 0) {f g : R → R} (h : good f g) :
    ((∃ C, f = λ x ↦ x * x + C) ∧ g = id) ∨ (f = (λ _ ↦ 0) ∧ g = (λ _ ↦ 0)) := by
  ---- Take `A` and `B` as before so that `g(x) = xA + B` for all `x : R`.
  replace hR2 : IsLeftRegular (2 : R) := IsLeftCancelMulZero.mul_left_cancel_of_ne_zero hR2
  obtain ⟨A, B, hg⟩ : ∃ A B : R, ∀ x : R, g x = x * A + B := h.g_right_linear hR2
  ---- Then `f(x) = x(xA - B) + f(0)` for all `x : R`.
  have hf (x : R) : f x = x * (x * A - B) + f 0 := calc
    _ = f (- -x) := congrArg f (neg_neg x).symm
    _ = -x * g (-x) + f 0 := h.f_eq_x_mul_g_add_f_zero (-x)
    _ = x * (x * A - B) + f 0 := by
      rw [add_left_inj, hg, neg_mul_comm, neg_mul, neg_add', neg_neg]
  ---- By plugging `x = 0` into `g(f(x)) = f(-x)`, we get `f(0) A + B = f(0)`.
  have h0 : f 0 * A + B = f 0 := by simpa only [neg_zero, hg] using h.gf_eq_f_neg 0
  ---- The equation `g(f(x)) = f(-x)` now gives `(x(xA - B))A = x(xA + B)` for all `x`.
  have h1 (x : R) : -x * (-x * A - B) = x * (x * A + B) := by
    rw [neg_mul_comm, neg_mul, ← neg_add', neg_neg]
  have h2 (x : R) : x * (x * A - B) * A = x * (x * A + B) := by
    have h2 : g (f x) = f (-x) := h.gf_eq_f_neg x
    rwa [hf, hg, add_mul, add_assoc, h0, hf (-x), h1, add_left_inj] at h2
  ---- In particular, we get `(A - B)A = A + B` and `(A + B)A = A - B`.
  replace h1 : (A - B) * A = A + B := by simpa only [one_mul] using h2 1
  replace h2 : (A + B) * A = A - B := calc
    _ = (-1) * (-1 * A - B) * A := by rw [neg_one_mul, neg_one_mul, ← neg_add', neg_neg]
    _ = (-1) * (-1 * A + B) := h2 (-1)
    _ = A - B := by rw [neg_one_mul, neg_one_mul, neg_add_eq_sub, neg_sub]
  ---- Since `2` is left regular, we then get `AA = A` and `BA = -B`.
  replace h1 : A * A = A := by
    refine hR2 (?_ : 2 * (A * A) = 2 * A)
    calc 2 * (A * A)
      _ = (A - B) * A + (A + B) * A := by rw [two_mul, sub_mul, add_mul, sub_add_add_cancel]
      _ = A + B + (A - B) := congrArg₂ _ h1 h2
      _ = 2 * A := by rw [two_mul, add_add_sub_cancel]
  replace h2 : B * A = -B := by rwa [add_mul, h1, sub_eq_add_neg, add_right_inj] at h2
  ---- Note that `AA = A` implies `A = 1` or `A = 0`.
  replace h1 : A = 1 ∨ A = 0 := by
    rw [← sub_eq_zero, ← mul_eq_zero, sub_one_mul, h1, sub_self]
  rcases h1 with rfl | rfl
  ---- If `A = 1`, then we get `B = 0` and we are done.
  · replace h2 : 2 * B = 2 * 0 := by
      rw [two_mul, mul_zero, ← eq_neg_iff_add_eq_zero, ← h2, mul_one]
    obtain rfl : B = 0 := hR2 h2
    replace hf (x : R) : f x = x * x + f 0 := by rw [hf, mul_one, sub_zero]
    replace hg (x : R) : g x = x := by rw [hg, mul_one, add_zero]
    left; exact ⟨⟨f 0, funext hf⟩, funext hg⟩
  ---- If `A = 0`, then we also get `B = 0`, but in addition we get `f(0) = 0`.
  · obtain rfl : B = 0 := by rwa [mul_zero, zero_eq_neg] at h2
    replace h0 : f 0 = 0 := by rwa [mul_zero, add_zero, eq_comm] at h0
    replace hf (x : R) : f x = 0 := by rw [hf, mul_zero, sub_zero, mul_zero, h0, add_zero]
    replace hg (x : R) : g x = 0 := by rw [hg, add_zero, mul_zero]
    right; exact ⟨funext hf, funext hg⟩

end

end good


/-- Final solution -/
theorem final_solution
    [NonAssocCommRing R] [IsLeftCancelMulZero R] (hR2 : (2 : R) ≠ 0) {f g : R → R} :
    good f g ↔ ((∃ C, f = λ x ↦ x * x + C) ∧ g = id) ∨ (f = (λ _ ↦ 0) ∧ g = (λ _ ↦ 0)) := by
  refine ⟨good.solve_of_NoZeroDivisors_two_ne_zero hR2, ?_⟩
  rintro (⟨⟨C, rfl⟩, rfl⟩ | ⟨rfl, rfl⟩)
  exacts [mul_self_add_const_is_good C, zero_is_good]
