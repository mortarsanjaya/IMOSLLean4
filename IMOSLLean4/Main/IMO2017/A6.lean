/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.FieldSimp

/-!
# IMO 2017 A6 (P2)

Let $F$ be a field.
Find all functions $f : F → F$ such that for any $x, y ∈ F$,
$$ f(f(x) f(y)) + f(x + y) = f(xy). $$

### Answer

$f(x) = x$ and $f(x) = 2 - x$.

### Solution

We follow the [solution](https://artofproblemsolving.com/community/c6h1480146p8693244)
  in the AoPS thread post #75 by **anantmudgal09**, which works in characteristic $≠ 2$.
This solution can be modified very slightly to work over
  division rings of characteristic $≠ 2$, not just fields.
Comparing the substitution $(x, y) = (a, -b)$ and $(x, y) = (-a, b)$ doesn't work this time.
Replacing $(-a, b)$ with $(b, -a)$ almost works; we're only missing $f(-ab) = f(-ba)$.
But comparing $(x, y) = (a, b)$ with $(x, y) = (b, a)$ gives $f(ab) = f(ba)$,
  which implies $f(-ab) = f(-ba)$, completing the proof of injectivity.

In the same thread, the author of this project solved the characteristic $2$ case.
(See [here](https://artofproblemsolving.com/community/c6h1480146p29214012),
  post #176 by **BlazingMuddy**.)
Both follows the [official solution](https://www.imo-official.org/problems/IMO2017SL.pdf)
  up to reduction to injectivity, but then proves injectivity in a different way.

### Generalization

We can also solve the functional equation under a milder assumption:
  $2$ and $3$ are not zero divisors of $R$.
See `IMOSLLean4/Generalization/IMO2017A6/IMO2017A6.lean` for the implementation.
-/

namespace IMOSL
namespace IMO2017A6

open Function

/-- We say that a function `f : R → R` is *good* if
  `f(f(x) f(y)) + f(x + y) = f(xy)` for all `x, y ∈ R`. -/
def good [Ring R] (f : R → R) :=
  ∀ x y : R, f (f x * f y) + f (x + y) = f (x * y)

/-- The zero function is good. -/
theorem zero_is_good [Ring R] : good (0 : R → R) :=
  λ _ _ ↦ add_zero 0

/-- The function `x ↦ 1 - x` is good. -/
theorem one_sub_is_good [Ring R] : good ((1 : R) - ·) := by
  intro x y; calc 1 - (1 - x) * (1 - y) + (1 - (x + y))
    _ = 1 - (1 - x - (y - x * y)) + (1 - (x + y)) := by rw [mul_one_sub, one_sub_mul]
    _ = x + y - x * y + (1 - (x + y)) := by rw [sub_sub, sub_sub_cancel, add_sub_assoc]
    _ = 1 - x * y := by rw [sub_add_sub_cancel']


namespace good

section Ring

variable [Ring R] {f : R → R} (hf : good f)
include hf

/-- If `f` is good then `-f` is good as well. -/
theorem neg : good (-f) := by
  intro x y; calc -f (-f x * -f y) + -f (x + y)
    _ = -(f (f x * f y) + f (x + y)) := by rw [neg_mul_neg, neg_add]
    _ = -f (x * y) := congrArg _ (hf x y)

/-- If `xy = 1`, then `f(f(x + 1) f(y + 1)) = 0`. -/
theorem map_map_add_one_mul_add_one_of_mul_eq_one {x y : R} (h0 : x * y = 1) :
    f (f (x + 1) * f (y + 1)) = 0 :=
  calc f (f (x + 1) * f (y + 1))
  _ = f ((x + 1) * (y + 1)) - f ((x + 1) + (y + 1)) := eq_sub_of_add_eq (hf _ _)
  _ = f ((1 + x) + (y + 1)) - f ((x + 1) + (y + 1)) := by rw [add_one_mul, mul_add_one, h0]
  _ = 0 := by rw [add_comm 1 x, sub_self]

/-- For any `x ∈ R`, we have `f(f(x) f(0)) + f(x) = f(0)`. -/
theorem map_map_mul_map_zero_add_map (x) : f (f x * f 0) + f x = f 0 :=
  calc f (f x * f 0) + f x
  _ = f (f x * f 0) + f (x + 0) := by rw [add_zero]
  _ = f 0 := by rw [hf, mul_zero]

/-- We have `f(f(0)^2) = 0`. -/
theorem map_map_zero_sq : f (f 0 ^ 2) = 0 :=
  have h : (-1 : R) * -1 = 1 := by rw [neg_mul_neg, one_mul]
  calc f (f 0 ^ 2)
    _ = f (f (-1 + 1) * f (-1 + 1)) := by rw [neg_add_cancel, sq]
    _ = 0 := hf.map_map_add_one_mul_add_one_of_mul_eq_one h

/-- If `f(0) = 1` and `f` is injective, then `f` is the function `x ↦ 1 - x`. -/
theorem eq_of_map_zero_of_inj (h0 : f 0 = 1) (h1 : Injective f) : f = (1 - ·) := by
  have h2 (x) : f (f x) + f x = 1 := calc
    _ = f (f x * f 0) + f x := by rw [h0, mul_one]
    _ = 1 := by rw [hf.map_map_mul_map_zero_add_map, h0]
  have h3 (x) : f (f x) = x := h1 (by rw [← add_left_inj (f (f x)), h2, add_comm, h2])
  funext x; rw [eq_sub_of_add_eq' (h2 x), h3]

end Ring


section DivisionRing

variable [DivisionRing D] {f : D → D} (hf : good f)
include hf

/-- For any `x ≠ 0`, we have `f(f(x + 1) f(x⁻¹ + 1)) = 0`. -/
theorem map_map_add_one_mul_map_inv_add_one {x} (hx : x ≠ 0) :
    f (f (x + 1) * f (x⁻¹ + 1)) = 0 :=
  hf.map_map_add_one_mul_add_one_of_mul_eq_one (mul_inv_cancel₀ hx)

/-- If `f ≠ 0` and `f(c) = 0`, then `c = 1`. -/
theorem map_eq_zero_imp_eq_one (hf0 : f ≠ 0) {c : D} (hc : f c = 0) : c = 1 := by
  ---- If `c ≠ 1`, we claim that `f ≡ 0`.
  contrapose! hf0
  have hc0 : c - 1 ≠ 0 := sub_ne_zero_of_ne hf0
  ---- First prove that `f(0) = 0`.
  replace hf0 : f 0 = 0 := calc
    _ = f (f (c - 1 + 1) * f ((c - 1)⁻¹ + 1)) := by rw [sub_add_cancel, hc, zero_mul]
    _ = 0 := hf.map_map_add_one_mul_map_inv_add_one hc0
  ---- Now use `f(0) = 0` to prove that `f ≡ 0`.
  funext x; calc f x
    _ = f 0 - f (f x * f 0) := eq_sub_of_add_eq' (hf.map_map_mul_map_zero_add_map x)
    _ = 0 := by rw [hf0, mul_zero, hf0, sub_zero]

/-- If `f ≠ 0`, then `f(0)^2 = 1`. -/
theorem map_zero_sq_eq_one (hf0 : f ≠ 0) : f 0 ^ 2 = 1 :=
  hf.map_eq_zero_imp_eq_one hf0 hf.map_map_zero_sq

/-- If `f ≠ 0`, then `f(0) = ±1`. -/
theorem map_zero_eq_one_or_neg_one (hf0 : f ≠ 0) : f 0 = 1 ∨ f 0 = -1 :=
  sq_eq_one_iff.mp (hf.map_zero_sq_eq_one hf0)

/-- We always have `f(1) = 0`. -/
theorem map_one_eq_zero : f 1 = 0 := by
  obtain hf0 | hf0 : f = 0 ∨ f ≠ 0 := eq_or_ne f 0
  · exact congrFun hf0 1
  · rw [← hf.map_zero_sq_eq_one hf0, hf.map_map_zero_sq]

/-- If `f(0) = 1`, then `f(c) = 0` if and only if `c = 1`. -/
theorem map_eq_zero_iff_eq_one (hf0 : f 0 = 1) {c : D} : f c = 0 ↔ c = 1 := by
  refine ⟨λ h ↦ hf.map_eq_zero_imp_eq_one ?_ h, λ h ↦ h ▸ hf.map_one_eq_zero⟩
  rintro rfl; exact zero_ne_one hf0

/-- If `f(0) = 1`, then `f(x + 1) + 1 = f(x)` for any `x ∈ D`. -/
theorem map_add_one (hf0 : f 0 = 1) (x : D) : f (x + 1) + 1 = f x := by
  have h := hf x 1
  rwa [hf.map_one_eq_zero, mul_zero, hf0, add_comm, mul_one] at h

/-- If `f(0) = 1`, then `f(x - 1) = f(x) + 1` for any `x ∈ D`. -/
theorem map_sub_one (hf0 : f 0 = 1) (x : D) : f (x - 1) = f x + 1 := by
  rw [← hf.map_add_one hf0, sub_add_cancel]

end DivisionRing

end good



/-- The general framework reducing to injectivity. -/
theorem solution_of_map_zero_eq_one_imp_injective
    [DivisionRing D] (h : ∀ f : D → D, good f → f 0 = 1 → Injective f) {f : D → D} :
    good f ↔ f = 0 ∨ f = (1 - ·) ∨ f = -(1 - ·) := by
  ---- The `←` direction is easy.
  refine Iff.symm ⟨?_, λ hf ↦ ?_⟩
  · rintro (rfl | rfl | rfl)
    exacts [zero_is_good, one_sub_is_good, one_sub_is_good.neg]
  ---- For the `→` direction, if `f = 0` then we are done.
  obtain hf0 | hf0 : f = 0 ∨ f ≠ 0 := eq_or_ne _ _
  · left; exact hf0
  ---- If `f(0) = 1`, we are done too.
  right; obtain hf1 | hf1 : f 0 = 1 ∨ f 0 = -1 := hf.map_zero_eq_one_or_neg_one hf0
  · left; exact hf.eq_of_map_zero_of_inj hf1 (h f hf hf1)
  ---- It remains to consider the `f(0) = -1` case.
  replace hf : good (-f) := hf.neg
  replace hf1 : (-f) 0 = 1 := (neg_eq_iff_eq_neg.mp hf1.symm).symm
  right; exact (neg_eq_iff_eq_neg.mp (hf.eq_of_map_zero_of_inj hf1 (h (-f) hf hf1)))

/-- Let `D` be a division ring with `char(D) ≠ 2`.
  Then a good function `f : D → D` with `f(0) = 1` is injective. -/
theorem case1_injective [DivisionRing D] (hD : (2 : D) ≠ 0)
    {f : D → D} (hf : good f) (hf0 : f 0 = 1) : Injective f := by
  have h : ∀ x, f (x - 1) = f x + 1 := hf.map_sub_one hf0
  have h0 {x} : f x = 0 ↔ x = 1 := hf.map_eq_zero_iff_eq_one hf0
  ---- First prove `f(2 f(y)) + f(y) + 1 = f(-y)` for all `y ∈ D`.
  have h1 {y} : f (2 * f y) + 1 + f y = f (-y) := calc
    _ = f (f (0 - 1) * f y) + f (y - 1) := by
      rw [h, hf0, one_add_one_eq_two, h, add_right_comm, add_assoc]
    _ = f (f (-1) * f y) + f (-1 + y) := by rw [zero_sub, neg_add_eq_sub]
    _ = f (-y) := by rw [hf, neg_one_mul]
  ---- Thus `f(-y) = f(y)` implies `y = 0`.
  replace h {y} (hy : f (-y) = f y) : y = 0 := by
    rwa [← h1, add_eq_right, ← h, h0, sub_eq_iff_eq_add, ← hf.map_add_one hf0 y,
      mul_add_one, one_add_one_eq_two, add_eq_right, mul_eq_zero,
      or_iff_right hD, h0, add_eq_right] at hy
  ---- If `f(x) = f(y)`, then `f(-x) = f(-y)`.
  replace h1 {x y} (hxy : f x = f y) : f (-x) = f (-y) := by rw [← h1, hxy, h1]
  ---- Now we go back on track and prove injectivity.
  intro a b hab
  suffices f (a + -b) = f (b + -a) by
    rw [← sub_eq_add_neg, ← sub_eq_add_neg, ← neg_sub] at this
    exact (eq_of_sub_eq_zero (h this)).symm
  have hab0 : f (a * b) = f (b * a) := by rw [← hf, ← hf b, hab, add_comm a]
  replace hab0 : f (a * -b) = f (b * -a) := by rw [mul_neg, h1 hab0, mul_neg]
  rwa [← hf, ← hf b, hab, h1 hab, add_right_inj] at hab0

/-- Let `F` be a field with `char(F) = 2`.
  Then a good function `f : F → F` with `f(0) = 1` is injective. -/
theorem case2_injective [Field F] [CharP F 2]
    {f : F → F} (hf : good f) (hf0 : f 0 = 1) : Injective f := by
  have hf1 (x) : f (x + 1) = f x + 1 := by rw [← CharTwo.sub_eq_add, hf.map_sub_one hf0]
  have hf2 {x} : f x = 0 ↔ x = 1 := hf.map_eq_zero_iff_eq_one hf0
  ---- Let `a, b ∈ F` with `f(a) = f(b)`.
  intro a b hab
  ---- First if `a = 0` or `b = 0` then we are done since `f(x) = 1 ↔ x = 0`.
  have hf3 {x} : f x = 1 ↔ x = 0 := by rw [← CharTwo.add_eq_zero, ← hf1, hf2, add_eq_right]
  obtain rfl | ha : a = 0 ∨ a ≠ 0 := eq_or_ne a 0
  · rwa [hf0, eq_comm, hf3, eq_comm] at hab
  obtain rfl | hb : b = 0 ∨ b ≠ 0 := eq_or_ne b 0
  · rwa [hf0, hf3] at hab
  /- Now suppose `a, b ≠ 0`. First we prove `f(ab⁻¹ + a + b⁻¹) = f(a + b⁻¹ + 1)`
    and similarly, `f(ba⁻¹ + b + a⁻¹) = f(b + a⁻¹ + 1)`. -/
  have h (c d : F) (hd : d ≠ 0) (h : f c = f d) :
      f (c * d⁻¹ + c + d⁻¹) = f (c + d⁻¹ + 1) := calc
    _ = f ((c + 1) * (d⁻¹ + 1)) + 1 := by
      rw [add_one_mul, mul_add_one, ← add_assoc, hf1, CharTwo.add_cancel_right]
    _ = f (f (c + 1) * f (d⁻¹ + 1)) + f (c + d⁻¹) + 1 := by
      rw [← hf, add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]
    _ = f (f (d + 1) * f (d⁻¹ + 1)) + f (c + d⁻¹) + 1 := by rw [hf1, hf1 d, h]
    _ = f (c + d⁻¹ + 1) := by rw [hf.map_map_add_one_mul_map_inv_add_one hd, zero_add, hf1]
  have h0 : f (a * b⁻¹ + a + b⁻¹) = f (a + b⁻¹ + 1) := h a b hb hab
  replace h : f (b * a⁻¹ + b + a⁻¹) = f (b + a⁻¹ + 1) := h b a ha hab.symm
  ---- Consider the identity `(ab⁻¹ + a + b⁻¹)(ba⁻¹ + b + a⁻¹) = (a + b⁻¹ + 1)(b + a⁻¹ + 1)`.
  replace hab :
      (a * b⁻¹ + a + b⁻¹) * (b * a⁻¹ + b + a⁻¹) = (a + b⁻¹ + 1) * (b + a⁻¹ + 1) := by
    field_simp [ha, hb]; ring
  /- Combining with the previous two equalities and the original FE, we get
    `f(ab⁻¹ + a + b⁻¹ + ba⁻¹ + b + a⁻¹) = f(a + b⁻¹ + 1 + b + a⁻¹ + 1)`. -/
  replace h : f ((a * b⁻¹ + a + b⁻¹) + (b * a⁻¹ + b + a⁻¹))
      = f ((a + b⁻¹ + 1) + (b + a⁻¹ + 1)) := by
    rw [eq_sub_of_add_eq' (hf _ _), hab, h, h0, sub_eq_iff_eq_add', hf]
  ---- But `ab⁻¹ + a + b⁻¹ + ba⁻¹ + b + a⁻¹ = (a + b + 1)(b⁻¹ + a⁻¹ + 1) + 1`.
  replace h0 : (a * b⁻¹ + a + b⁻¹) + (b * a⁻¹ + b + a⁻¹)
      = (a + b + 1) * (b⁻¹ + a⁻¹ + 1) + 1 := calc
    _ = (a + b + 1) * (b⁻¹ + a⁻¹ + 1) + 1 - (2 + 2) := by field_simp [ha, hb]; ring
    _ = (a + b + 1) * (b⁻¹ + a⁻¹ + 1) + 1 := by rw [CharTwo.add_self_eq_zero, sub_zero]
  ---- Thus `f((a + b + 1)(b⁻¹ + a⁻¹ + 1)) + 1 = f((b + a + 1) + (b⁻¹ + a⁻¹ + 1))`.
  replace hab : f ((a + b + 1) * (b⁻¹ + a⁻¹ + 1)) + 1
      = f ((a + b + 1) + (b⁻¹ + a⁻¹ + 1)) := by
    rw [← hf1, ← h0, h, add_add_add_comm, add_add_add_comm a, add_add_add_comm]
  clear h h0
  ---- Simplifying gives us `a = b` or `b⁻¹ = a⁻¹ ↔ a = b`.
  replace hf3 {x} : f (x + 1) = 0 ↔ x = 0 := by rw [hf2, add_eq_right]
  rwa [← hf, add_right_comm, add_eq_right, ← hf1, hf3, mul_eq_zero, hf3, hf3,
    CharTwo.add_eq_zero, CharTwo.add_eq_zero, inv_inj, eq_comm (a := b), or_self] at hab

/-- Let `F` be a field. Then a good function `f : F → F` with `f(0) = 1` is injective. -/
theorem map_zero_eq_one_imp_injective [Field F] (f : F → F) :
    good f → f 0 = 1 → Injective f := by
  obtain hF | hF : (2 : F) ≠ 0 ∨ (2 : F) = 0 := ne_or_eq _ _
  · exact case1_injective hF
  · haveI : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hF
    exact case2_injective

/-- Final solution -/
theorem final_solution [Field F] {f : F → F} :
    good f ↔ f = 0 ∨ f = Sub.sub 1 ∨ f = λ x ↦ -(1 - x) :=
  solution_of_map_zero_eq_one_imp_injective map_zero_eq_one_imp_injective
