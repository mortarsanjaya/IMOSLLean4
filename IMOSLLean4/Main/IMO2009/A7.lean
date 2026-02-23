/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.CharP.Two

/-!
# IMO 2009 A7

Fix a domain $R$.
Find all functions $f : R → R$ such that for any $x, y ∈ R$,
$$ f(x f(x + y)) = f(f(x) y) + x^2. $$

### Answer

$f(x) = x$ and $f(x) = -x$.

### Solution

We follow and modify Solution 2 of the
  [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
We change the proof of $f(0) = 0$ as follows: plugging $(x, y) = (0, f(f(0)))$ gives
  $f(f(0) f(f(0))) = f(0)$, and then plugging $(x, y) = (f(0), 0)$ gives $f(0) = 0$.
Their proof that $f$ is odd follows Solution 1, but this also follows
  from injectivity of $f$, $f(x) = 0 ↔ x = 0$, and $f(-x f(-x)) = f(x f(x)) = x^2$.
Afterwards, it is easy to see that $-f$ satisfies the same functional equation.
Thus we may then WLOG assume that $f(1) = 1$.
The rest of the solution works over any ring of characteristic not equal to $2$.
We now solve the functional equation over characteristic $2$.

Fix an arbitrary $y ∈ R$.
Recall that $f(1) = 1$.
Plugging $x = 1$ into the functional equation gives $f(f(y + 1)) = f(y) + 1$.
Similarly, with $y$ replaced with $y + 1$, we get $f(f(y)) = f(y + 1) + 1$.
Since $f$ is injective, it now suffices to show that $f(y + 1) = f(y) + 1$.

For convenience, denote $c = f(y)$ and $d = f(y + 1)$.
Recall that $f(c) = d + 1$ and $f(d) = c + 1$.
First we show that $c$ and $d$ commute.
Indeed, plugging $x = y = c$ into the original equation gives $f(f(c) c) = c^2 = f(c f(c))$.
Injectivity implies that $c$ and $f(c)$ commute, and so does $c$ and $d = f(c) + 1$.

Now plugging $x = c$ and $y = c + 1$ into the original equation gives
$$ d + 1 = f(c) = f((d + 1)(c + 1)) + c^2 ↔ f((d + 1)(c + 1)) = c^2 + d + 1. $$
By symmetry, we also have $f((c + 1)(d + 1)) = d^2 + c + 1$.
But $c$ and $d$ commute, so we get $c^2 + d = f((c + 1)(d + 1)) = d^2 + c$.
Using the fact that $c$ and $d$ commute again, $c^2 + d = d^2 + c$ reduces to
$$ (c + d)^2 = c + d ↔ (c + d)(c + d + 1) = 0. $$
Since $c = f(y) ≠ f(y + 1) = d$, we have $c + d ≠ 0$, forcing $c + d + 1 = 0$.
That is, we have $f(y + 1) = d = c + 1 = f(y) + 1$, as desired.

### Notes

We use $xx$ instead of $x^2$ to be able to define the
  functional equation over non-associative rings.
-/

namespace IMOSL
namespace IMO2009A7

section

variable [NonAssocRing R]

/-- A function `f : R → R` is called *good* if
  `f(x f(x + y)) = f(f(x) y) + x^2` for any `x, y : R`. -/
def good (f : R → R) := ∀ x y : R, f (x * f (x + y)) = f (f x * y) + x * x

/-- The identity function is good. -/
theorem id_is_good : good (id : R → R) :=
  λ x y ↦ (mul_add x x y).trans (add_comm _ _)

/-- The function `x ↦ -x` is good. -/
theorem neg_is_good : good (λ x : R ↦ -x) := by
  intro x y; simp only
  rw [mul_neg, neg_neg, neg_mul, neg_neg, mul_add, add_comm]

end


namespace good

section

variable [NonAssocRing R] [NoZeroDivisors R] {f : R → R} (hf : good f)
include hf

omit [NoZeroDivisors R] in
/-- If `f` is a good function, then `f(0) f(0) = 0`. -/
theorem map_zero_mul_self_eq_zero : f 0 * f 0 = 0 := by
  ---- Plugging `(x, y) = (0, f(f(0)))` gives `f(f(0) f(f(0))) = f(0)`.
  have h : f (f 0 * f (f 0)) = f 0 := calc
    _ = f (f 0 * f (f 0)) + 0 * 0 := by rw [zero_mul, add_zero]
    _ = f 0 := by rw [← hf, zero_mul]
  ---- Then plugging `(x, y) = (f(0), 0)` yields `f(0) f(0) = 0`.
  have h0 := hf (f 0) 0
  rwa [add_zero, h, mul_zero, left_eq_add] at h0

/-- If `f` is a good function, then `f(0) = 0`. -/
theorem map_zero : f 0 = 0 :=
  mul_self_eq_zero.mp hf.map_zero_mul_self_eq_zero

/-- For any `x : R`, we have `f(x f(x)) = xx`. -/
theorem map_self_mul_map (x : R) : f (x * f x) = x * x := by
  have h := hf x 0
  rwa [add_zero, mul_zero, hf.map_zero, zero_add] at h

/-- For any `x : R`, we have `f(x) = 0 ↔ x = 0`. -/
theorem map_eq_zero_iff {x : R} : f x = 0 ↔ x = 0 := by
  refine ⟨λ h ↦ ?_, λ h ↦ (congrArg f h).trans hf.map_zero⟩
  have h0 := hf.map_self_mul_map x
  rwa [h, mul_zero, hf.map_zero, zero_eq_mul_self] at h0

/-- A good function is injective. -/
theorem injective : f.Injective := by
  intro r s h
  ---- From `rr = f(f(r) (s - r)) + rr`, we get either `f(r) = 0` or `s - r = 0`.
  obtain h0 | h0 : f r = 0 ∨ s - r = 0 := by
    rw [← mul_eq_zero, ← hf.map_eq_zero_iff, ← add_eq_right (b := r * r),
      ← hf, add_sub_cancel, ← h, hf.map_self_mul_map]
  ---- If `f(r) = 0` then `f(r) = f(s) = 0` implies `r = s = 0`.
  · replace h : s = 0 := by rwa [h0, eq_comm, hf.map_eq_zero_iff] at h
    replace h0 : r = 0 := hf.map_eq_zero_iff.mp h0
    exact h0.trans h.symm
  ---- If `s - r = 0` then clearly `r = s`.
  · exact (eq_of_sub_eq_zero h0).symm

/-- Injectivity in the iff form. -/
theorem inj {x y : R} : f x = f y ↔ x = y :=
  ⟨λ h ↦ hf.injective h, congrArg f⟩

/-- A good function is odd. -/
theorem map_neg (x : R) : f (-x) = -f x := by
  ---- Comparing `f(-x f(-x)) = f(x f(x))` gives either `x = 0` or `f(-x) + f(x) = 0`.
  obtain rfl | h : x = 0 ∨ f (-x) + f x = 0 := by
    have h : -x * f (-x) = x * f x := by
      rw [← hf.inj, hf.map_self_mul_map, hf.map_self_mul_map, neg_mul_neg]
    rwa [neg_mul, neg_eq_iff_add_eq_zero, ← mul_add, mul_eq_zero] at h
  ---- If `x = 0`, then `f(-x) = 0 = -f(x)`.
  · rw [neg_zero, hf.map_zero, neg_zero]
  ---- If `f(-x) + f(x) = 0`, then clearly `f(-x) = -f(x)`.
  · exact eq_neg_of_add_eq_zero_left h

/-- If `f` is good, then so is `-f`. -/
theorem neg_apply : good (-f) := by
  intro x y; calc -f (x * -f (x + y))
    _ = f (x * f (x + y)) := by rw [mul_neg, hf.map_neg, neg_neg]
    _ = f (f x * y) + x * x := hf x y
    _ = -f (-f x * y) + x * x := by rw [neg_mul, hf.map_neg, neg_neg]

/-- If `f` is a good function, then `f(1) = ±1`. -/
theorem map_one_eq : f 1 = 1 ∨ f 1 = -1 := by
  have h : f (f 1) = 1 := by rw [← one_mul (f 1), hf.map_self_mul_map, one_mul]
  have h0 : f 1 * f 1 = 1 := by rw [← hf.map_self_mul_map, h, mul_one, h]
  exact mul_self_eq_one_iff.mp h0

omit [NoZeroDivisors R] in
/-- If `f(1) = 1`, then `f(f(y + 1)) = f(y) + 1` for all `y : R`. -/
theorem map_map_add_one (h : f 1 = 1) (y) : f (f (y + 1)) = f y + 1 := by
  rw [← one_mul (f (y + 1)), add_comm y, hf, h, one_mul, one_mul]

end


section

variable [NonAssocRing R] [NoZeroDivisors R] (hR : (2 : R) ≠ 0) {f : R → R} (hf : good f)
include hR hf

/-- If `char(R) ∤ 2`, the only good function `f` with `f(1) = 1` is the identity. -/
theorem case_two_ne_zero_map_one_eq_one (hf1 : f 1 = 1) : f = id := by
  ---- First show that `f(y + 2) = f(y) + 2` for all `y`.
  have h0 (y) : f (f (y + 1)) = f y + 1 := hf.map_map_add_one hf1 y
  replace h0 (y) : f (y + 2) = f y + 2 := calc
    _ = -(f (f (-1) * (y + 2)) + (-1) * (-1)) + 1 := by
      rw [neg_mul_neg, one_mul, neg_add', sub_add_cancel,
        hf.map_neg, hf1, neg_one_mul, hf.map_neg, neg_neg]
    _ = -f (-f (y + 1)) + 1 := by
      rw [← hf, neg_one_mul, ← one_add_one_eq_two,
        ← add_assoc, ← add_assoc, neg_add_cancel_comm]
    _ = f (f (y + 1)) + 1 := by rw [hf.map_neg, neg_neg]
    _ = f y + 2 := by rw [h0, add_assoc, one_add_one_eq_two]
  ---- Now finish by plugging `x = 2` into the original equation.
  have h1 : f 2 = 2 := by rw [← zero_add 2, h0, hf.map_zero]
  funext y; have h2 : f (2 * f (2 + y)) = f (f 2 * y) + 2 * 2 := hf 2 y
  replace h2 : 2 * f y = 2 * y := by
    rwa [h1, add_comm, h0, mul_add, two_mul 2, ← add_assoc,
      h0, h0, add_assoc, add_left_inj, hf.inj] at h2
  rwa [← sub_eq_zero, ← mul_sub, mul_eq_zero, or_iff_right hR, sub_eq_zero] at h2

/-- If `char(R) ∤ 2`, then the only good functions are `f(x) = x` and `f(x) = -x`. -/
theorem case_two_ne_zero : f = id ∨ f = (λ x ↦ -x) := by
  refine hf.map_one_eq.imp (hf.case_two_ne_zero_map_one_eq_one hR) (λ h ↦ ?_)
  have h0 : ∀ x, -f x = x :=
    congrFun (hf.neg_apply.case_two_ne_zero_map_one_eq_one hR (neg_eq_iff_eq_neg.mpr h))
  funext x; rw [← neg_eq_iff_eq_neg, h0]

end


/-- If `char(R) = 2`, then the only good function is `f(x) = x`. -/
theorem char_eq2_solution [Ring R] [NoZeroDivisors R] [CharP R 2]
    {f : R → R} (hf : good f) : f = id := by
  ---- In this case, we must have `f(1) = 1`.
  have hf1 : f 1 = 1 ∨ f 1 = -1 := hf.map_one_eq
  replace hf1 : f 1 = 1 := by rwa [CharTwo.neg_eq, or_self] at hf1
  ---- In particular, we get `f(f(y + 1)) = f(y) + 1` for all `y : R`.
  have h (y) : f (f (y + 1)) = f y + 1 := hf.map_map_add_one hf1 y
  ---- Fix `y`, let `c = f(y)`, `d = f(y + 1)`, and get `f(c) = d + 1`, `f(d) = c + 1`.
  funext y
  let c : R := f y
  let d : R := f (y + 1)
  have h0 : f c = d + 1 := by rw [← h, CharTwo.add_cancel_right]
  replace h : f d = c + 1 := h y
  ---- Then it suffices to show that `c = d + 1`.
  suffices c = d + 1 by rwa [← h0, hf.inj, eq_comm] at this
  ---- Now we show that `c` and `d` commute.
  have h1 : f c * c = c * f c := by
    rw [← hf.inj, hf.map_self_mul_map, ← CharTwo.add_eq_zero, ← hf,
      CharTwo.add_self_eq_zero, hf.map_zero, mul_zero, hf.map_zero]
  replace h1 : c * d = d * c := by
    rw [← CharTwo.add_eq_iff_eq_add.mpr h0, mul_add_one, add_one_mul, h1]
  ---- Now we show that `f((c + 1)(d + 1)) = d^2 + c + 1`.
  have h2 {c d : R} (h : f d = c + 1) : f ((c + 1) * (d + 1)) = d * d + c + 1 := by
    rw [add_assoc, add_comm (d * d), ← CharTwo.add_eq_iff_eq_add,
      ← h, ← hf, CharTwo.add_cancel_left, hf1, mul_one]
  ---- By symmetry, `f((d + 1)(c + 1)) = c^2 + d + 1`, so `c^2 + d = d^2 + c`.
  replace h2 : d * d + c = c * c + d := by
    rw [← add_left_inj 1, ← h2 h, ← h2 h0, add_one_mul,
      mul_add_one, h1, mul_add_one, add_one_mul]
  ---- Rearranging gives either `(c + d)(c + d + 1) = 0`.
  replace h2 : (c + d) * (c + d + 1) = 0 := calc
    _ = (c + d) * (c + d) + (c + d) := mul_add_one _ _
    _ = c * c + d * d + (c + d) := by
      rw [add_mul, mul_add, h1, mul_add, add_assoc (c * c), CharTwo.add_cancel_left]
    _ = 0 := by rw [add_comm c, add_add_add_comm, h2, CharTwo.add_self_eq_zero]
  ---- Thus we have eithe `c = d` or `c = d + 1`.
  replace h2 : c = d ∨ c = d + 1 := by
    rwa [mul_eq_zero, CharTwo.add_eq_zero, CharTwo.add_eq_zero,
      CharTwo.add_eq_iff_eq_add, add_comm] at h2
  ---- In the former case we get `1 = 0`, so the ring is trivial.
  refine h2.elim (λ h3 ↦ ?_) id
  replace h2 : (1 : R) = 0 := by rwa [hf.inj, left_eq_add] at h3
  rw [h2, add_zero, h3]

end good





/-! ### Summary -/

/-- Final solution -/
theorem final_solution [Ring R] [NoZeroDivisors R] {f : R → R} :
    good f ↔ f = (·) ∨ f = (- ·) := by
  ---- The `←` direction has been done before.
  refine Iff.symm ⟨λ hf ↦ ?_, λ hf ↦ ?_⟩
  · rcases hf with rfl | rfl
    exacts [id_is_good, neg_is_good]
  ---- We solved the case `char(R) ∤ 2`.
  obtain h | h : (2 : R) ≠ 0 ∨ (2 : R) = 0 := ne_or_eq 2 0
  · exact hf.case_two_ne_zero h
  ---- If `R` is trivial then there is nothing to do.
  left; obtain h0 | h0 : (1 : R) = 0 ∨ (1 : R) ≠ 0 := eq_or_ne 1 0
  · replace h0 (x : R) : x = 0 := eq_zero_of_zero_eq_one h0.symm x
    funext y; rw [h0 (f y), h0 y]
  ---- Otherwise we get the case `char(R) = 2`.
  · haveI : CharP R 2 := CharTwo.of_one_ne_zero_of_two_eq_zero h0 h
    exact hf.char_eq2_solution
