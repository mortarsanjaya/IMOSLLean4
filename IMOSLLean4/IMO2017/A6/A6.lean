/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Tactic.Ring

/-!
# IMO 2017 A6 (P2)

Let $F$ be a field.
Determine all functions $f : F → F$ such that, for any $x, y ∈ F$,
$$ f(f(x) f(y)) + f(x + y) = f(xy). $$

### Further directions

We have solved the problem when $F$ is a division ring with $char(F) ≠ 2$.
We are still interested in lifting the commutativity assumption on $F$ when $char(F) = 2$.
If this works, then we have a complete solution even when $F$ is just a division ring!
-/

namespace IMOSL
namespace IMO2017A6

section

variable [NonAssocRing R]

/-- The problem. -/
def good (f : R → R) := ∀ x y : R, f (f x * f y) + f (x + y) = f (x * y)

theorem zero_is_good : good (0 : R → R) :=
  λ _ _ ↦ add_zero 0

theorem one_sub_is_good : good ((1 : R) - ·) := λ x y ↦ by
  rw [sub_add_sub_comm, mul_one_sub, one_sub_mul, sub_sub, sub_add, add_sub_sub_cancel,
    add_sub_add_left_eq_sub, sub_sub_cancel_left, ← sub_eq_add_neg]

variable {f : R → R} (h : good f)

theorem good_neg : good (-f) := λ x y ↦ by
  simp only [Pi.neg_apply]; rw [neg_mul_neg, ← neg_add, h]

theorem sub_one_is_good : good (id - 1 : R → R) :=
  neg_sub (1 : R → R) id ▸ good_neg one_sub_is_good

/-- (1) -/
theorem good_special_equality {x y : R} (h0 : x * y = 1) :
    f (f (x + 1) * f (y + 1)) = 0 := by
  rw [← add_left_eq_self, h, add_one_mul x, mul_add_one x, h0, add_comm 1 x]

end



section Ring

variable [Ring R] {f : R → R} (h : good f)

theorem good_map_map_zero_sq : f (f 0 ^ 2) = 0 := by
  specialize h 0 0; rwa [add_zero, mul_zero, add_left_eq_self, ← sq] at h

theorem good_eq_of_inj (h0 : f 0 = 1) (h1 : f.Injective) : f = (1 - ·) :=
  have h2 : ∀ x : R, f (f x) + f x = 1 := λ x ↦ by
    rw [← h0, ← mul_zero x, ← h, add_zero, h0, mul_one]
  funext λ x ↦ by
    rw [eq_sub_iff_add_eq', ← h2 x, add_left_inj]
    apply h1
    rw [eq_sub_of_add_eq (h2 (f x)), ← h2 x, add_sub_cancel_left]

end Ring



section DivisionRing

variable [DivisionRing D] {f : D → D} (h : good f)

theorem good_map_eq_zero (h0 : f ≠ 0) {c : D} (h1 : f c = 0) : c = 1 :=
  h0.imp_symm λ h2 ↦ by
    ---- Get `f(0) = 0`
    have h3 := good_special_equality h (mul_inv_cancel <| sub_ne_zero_of_ne h2)
    rw [sub_add_cancel, h1, zero_mul] at h3
    ---- Finish
    ext x
    rw [Pi.zero_apply, ← h3, ← mul_zero x, ← h,
      h3, mul_zero, h3, zero_add, add_zero]

theorem good_map_zero_sq (h0 : f ≠ 0) : f 0 ^ 2 = 1 :=
  good_map_eq_zero h h0 (good_map_map_zero_sq h)

theorem good_map_zero (h0 : f ≠ 0) : f 0 = 1 ∨ f 0 = -1 :=
  sq_eq_one_iff.mp (good_map_zero_sq h h0)

theorem good_map_one : f 1 = 0 :=
  (eq_or_ne f 0).elim (λ h0 ↦ congr_fun h0 1)
    (λ h0 ↦ good_map_zero_sq h h0 ▸ good_map_map_zero_sq h)

/-- (2) -/
theorem good_map_eq_zero_iff (h0 : f 0 = 1) (c : D) : f c = 0 ↔ c = 1 :=
  ⟨good_map_eq_zero h λ h1 ↦ zero_ne_one (α := D) (by rwa [h1] at h0),
  λ h1 ↦ good_map_one h ▸ congr_arg f h1⟩

/-- (3) -/
theorem good_shift (h0 : f 0 = 1) (x : D) : f (x + 1) + 1 = f x := by
  have h1 := h x 1
  rwa [good_map_one h, mul_zero, h0, add_comm, mul_one] at h1

theorem good_shift2 (h0 : f 0 = 1) (x : D) : f (x - 1) = f x + 1 := by
  rw [← good_shift h h0, sub_add_cancel]

theorem good_map_add_one_eq_zero_iff (h0 : f 0 = 1) (x : D) :
    f (x + 1) = 0 ↔ x = 0 := by
  rw [good_map_eq_zero_iff h h0, add_left_eq_self]



/-- The general framework; reducing to injectivity. -/
theorem solution_of_map_zero_eq_one_imp_injective
    (h : ∀ f : D → D, good f → f 0 = 1 → f.Injective) {f : D → D} :
    good f ↔ f = 0 ∨ f = (1 - ·) ∨ f = (· - 1) :=
  ⟨λ h0 ↦ by
    rw [or_iff_not_imp_left]
    intros h1
    apply (good_map_zero h0 h1).imp <;> intro h1
    · exact good_eq_of_inj h0 h1 (h f h0 h1)
    · rw [← neg_eq_iff_eq_neg] at h1
      have h2 := good_neg h0
      have h3 := good_eq_of_inj h2 h1 (h (-f) h2 h1)
      rw [← neg_inj, h3]
      exact funext λ x ↦ (neg_sub x 1).symm,
  λ h0 ↦ by
    rcases h0 with rfl | rfl | rfl
    exacts [zero_is_good, one_sub_is_good, sub_one_is_good]⟩

/-- Injectivity for `char(D) ≠ 2`, `D` a division ring -/
theorem case1_injective (h : (2 : D) ≠ 0)
    {f : D → D} (h0 : good f) (h1 : f 0 = 1) : f.Injective := by
  have h2 := good_shift2 h0 h1
  -- `f(2 f(y)) + f(y) + 1 = f(-y)`
  have h3 : ∀ y, f (2 * f y) + 1 + f y = f (-y) := λ y ↦ by
    rw [add_assoc, ← neg_one_mul, ← h0 (-1)]
    refine congr_arg₂ _ ?_ ?_
    · rw [← zero_sub, h2, h1, one_add_one_eq_two]
    · rw [add_comm, ← h2, neg_add_eq_sub]
  -- `f(y) = f(-y)` implies `y = 0`
  replace h2 : ∀ y, f y = f (-y) → y = 0 := λ y h4 ↦ by
    rwa [← h3, self_eq_add_left, ← h2, good_map_eq_zero_iff h0 h1,
      sub_eq_iff_eq_add, one_add_one_eq_two, mul_right_eq_self₀,
      or_iff_left h, ← add_sub_cancel_right y 1, h2, add_left_eq_self,
      good_map_add_one_eq_zero_iff h0 h1] at h4
  -- Finishing
  intros a b h4
  refine eq_of_sub_eq_zero (h2 _ ?_)
  have h5 : ∀ y z, f y = f z → f (-y) = f (-z) :=
    λ y z h5 ↦ by rw [← h3, h5, h3]
  have h6 : f (a * b) = f (b * a) := by rw [← h0, ← h0 b, h4, add_comm a]
  have h8 := h0 a (-b)
  rwa [mul_neg, h5 _ _ h6, ← mul_neg, ← h0 b, h4, h5 a b h4,
    add_right_inj, ← sub_eq_add_neg, ← sub_eq_add_neg, ← neg_sub a] at h8

end DivisionRing





/-- Injectivity for `char(F) = 2` -/
theorem case2_injective [Field F] (h : (2 : F) = 0)
    {f : F → F} (h0 : good f) (h1 : f 0 = 1) : f.Injective := by
  have h2 := good_shift h0 h1
  have h3 : ∀ c d : F, d ≠ 0 → f (c + 1) = f (d + 1) →
      f ((c + 1) * (d⁻¹ + 1) - 1) = f (c + d⁻¹ + 1) := λ c d h3 h4 ↦ by
    rw [good_shift2 h0 h1, ← h0, h4, add_assoc, ← add_assoc (c + 1), h2,
      good_special_equality h0 (mul_inv_cancel h3), zero_add, add_right_comm]

  intros a b h4
  rw [← h2 a, ← h2 b, add_left_inj] at h4
  have h5 := good_map_add_one_eq_zero_iff h0 h1
  rcases eq_or_ne a 0 with rfl | ha
  · rwa [zero_add, good_map_one h0, eq_comm, h5, eq_comm] at h4
  rcases eq_or_ne b 0 with rfl | hb
  · rwa [zero_add, good_map_one h0, h5] at h4

  have h6 : ((a + 1) * (b⁻¹ + 1) - 1) * ((b + 1) * (a⁻¹ + 1) - 1) =
    (a + b⁻¹) * (b + a⁻¹) + ((a + a⁻¹) * (b * b⁻¹) + (b + b⁻¹) * (a * a⁻¹))
      + a * a⁻¹ * (b * b⁻¹) := by ring
  have h7 : ∀ c d : F, (c + 1) * (d + 1) = c * d + c + d + 1 := λ c d ↦ by
    rw [add_one_mul (α := F), mul_add_one (α := F), ← add_assoc]
  rw [mul_inv_cancel ha, mul_inv_cancel hb, mul_one, mul_one, mul_one,
    add_comm b b⁻¹, add_add_add_comm, add_comm a⁻¹ b, ← add_assoc, ← h7] at h6
  replace h6 := congr_arg f h6
  rw [← h0, h3 a b hb h4, h3 b a ha h4.symm, h7, add_sub_cancel_right,
    h7, add_sub_cancel_right, ← h0 (a + b⁻¹ + 1), add_right_inj] at h6
  replace h7 : (a + b + 1) * (b⁻¹ + a⁻¹ + 1) =
    a * b⁻¹ + a + b⁻¹ + (b * a⁻¹ + b + a⁻¹) + (a * a⁻¹ + b * b⁻¹ + 1) := by ring
  rw [mul_inv_cancel ha, mul_inv_cancel hb, one_add_one_eq_two, h, zero_add] at h7
  rw [← h2, ← h7, add_add_add_comm, add_add_add_comm a, ← add_add_add_comm,
    ← h0, add_right_comm, add_left_eq_self, ← h2, add_assoc,
    one_add_one_eq_two, h, add_zero, h5, mul_eq_zero, h5, h5] at h6
  replace h3 : ∀ c : F, -c = c := λ c ↦ by
    rw [neg_eq_iff_add_eq_zero, ← two_mul, h, zero_mul]
  rcases h6 with h6 | h6
  · rwa [add_eq_zero_iff_eq_neg, h3] at h6
  · rwa [add_eq_zero_iff_eq_neg, h3, inv_inj, eq_comm] at h6

/-- Injectivity -/
theorem map_zero_eq_one_imp_injective [Field F] :
    ∀ f : F → F, good f → f 0 = 1 → f.Injective :=
  (ne_or_eq (2 : F) 0).elim case1_injective case2_injective



/-- Final solution -/
theorem final_solution [Field F] {f : F → F} :
    good f ↔ f = 0 ∨ f = (1 - ·) ∨ f = (· - 1) :=
  solution_of_map_zero_eq_one_imp_injective map_zero_eq_one_imp_injective
