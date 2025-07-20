/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.CharTwo.Ring
import Mathlib.Algebra.Ring.Commute

/-!
# IMO 2009 A7

Fix a domain $R$.
Find all functions $f : R → R$ such that, for all $x, y ∈ R$,
$$ f(x f(x + y)) = f(f(x) y) + x^2. $$
-/

namespace IMOSL
namespace IMO2009A7

variable [Ring R]

def good (f : R → R) := ∀ x y : R, f (x * f (x + y)) = f (f x * y) + x ^ 2

theorem id_is_good : good (λ x : R ↦ x) :=
  λ x y ↦ by rw [sq, add_comm, mul_add]

theorem neg_is_good : good (λ x : R ↦ -x) := λ x y ↦ by
  simp only; rw [mul_neg, neg_mul, neg_neg, neg_neg]
  exact id_is_good x y



namespace good

theorem sq_eq_zero {f : R → R} (hf : good f) : f 0 ^ 2 = 0 := by
  have h := hf 0 (f (f 0))
  rw [zero_mul, sq, zero_mul, add_zero] at h
  have h0 := hf (f 0) 0
  rwa [add_zero, ← h, mul_zero, left_eq_add] at h0

variable [NoZeroDivisors R]


section

variable {f : R → R} (hf : good f)
include hf

theorem map_zero : f 0 = 0 :=
  sq_eq_zero_iff.mp hf.sq_eq_zero

theorem self_mul_map (x : R) : f (x * f x) = x ^ 2 := by
  have h := hf x 0; rwa [add_zero, mul_zero, hf.map_zero, zero_add] at h

theorem map_eq_zero_iff {x : R} : f x = 0 ↔ x = 0 := by
  refine ⟨λ h ↦ ?_, λ h ↦ h ▸ hf.map_zero⟩
  have h0 := hf.self_mul_map x
  rwa [h, mul_zero, hf.map_zero, eq_comm, sq_eq_zero_iff] at h0

theorem injective : f.Injective := by
  intro x y h; obtain h0 : f y = 0 ∨ x - y = 0 := by
    have h0 := hf.self_mul_map y
    rwa [← h, ← add_sub_cancel y x, hf, add_eq_right, hf.map_eq_zero_iff, mul_eq_zero] at h0
  rcases h0 with h0 | h0
  · rw [hf.map_eq_zero_iff.mp h0, hf.map_eq_zero_iff.mp (h.trans h0)]
  · exact eq_of_sub_eq_zero h0

theorem inj {x y : R} : f x = f y ↔ x = y :=
  ⟨λ h ↦ hf.injective h, congrArg f⟩

theorem map_neg (x : R) : f (-x) = -f x := by
  have h0 : -x * f (-x) = x * f x := by
    rw [← hf.inj, hf.self_mul_map, hf.self_mul_map, neg_sq]
  rw [neg_mul, neg_eq_iff_add_eq_zero, ← mul_add, mul_eq_zero] at h0
  rcases h0 with rfl | h0
  · rw [neg_zero, hf.map_zero, neg_zero]
  · exact eq_neg_of_add_eq_zero_left h0

theorem map_one_sq_eq : f 1 ^ 2 = 1 := by
  have h : f (f 1) = 1 := by rw [← one_mul (f 1), hf.self_mul_map, one_pow]
  have h0 := hf.self_mul_map (f 1)
  rwa [h, mul_one, h, eq_comm] at h0

theorem map_one_eq : f 1 = 1 ∨ f 1 = -1 :=
  sq_eq_one_iff.mp hf.map_one_sq_eq

theorem neg_apply : good (λ x ↦ -f x) := λ x y ↦ by
  simp only [mul_neg, neg_mul, hf.map_neg, neg_neg]; exact hf x y

omit [NoZeroDivisors R] in
theorem map_map_add_one (h : f 1 = 1) (y) : f (f (y + 1)) = f y + 1 := by
  rw [← one_mul (f (y + 1)), add_comm y, hf, h, one_mul, one_pow]

end



/-! ### Case `char(R) ≠ 2` -/

section

variable (hR : (2 : R) ≠ 0) {f : R → R} (hf : good f)
include hR hf

theorem char_ne2_of_map_one (h : f 1 = 1) : f = (·) := by
  ---- First show that `f(y + 2) = f(y) + 2` for all `y`
  have h0 (y) : f (y + 2) = f y + 2 := by
    have h0 := hf.map_map_add_one h
    have h1 := h0 (-(y + 1) - 1)
    rw [sub_add_cancel, hf.map_neg, hf.map_neg, ← neg_add', hf.map_neg, h0, neg_add_eq_sub,
      ← neg_sub, neg_inj, eq_sub_iff_add_eq, add_assoc, add_assoc, one_add_one_eq_two] at h1
    exact h1.symm
  ---- Now finish by plugging `x = 2` into the original equation
  have h1 : f 2 = 2 := by rw [← zero_add 2, h0, hf.map_zero]
  funext y; have h2 := hf 2 y
  rw [add_comm, h0, mul_add, two_mul 2, ← add_assoc, h0, h0, h1, sq, add_assoc,
    ← two_mul, add_left_inj, hf.inj, ← sub_eq_zero, ← mul_sub, mul_eq_zero] at h2
  exact h2.elim (λ h2 ↦ absurd h2 hR) eq_of_sub_eq_zero

theorem char_ne2_solution : f = (·) ∨ f = (- ·) := by
  refine hf.map_one_eq.imp (hf.char_ne2_of_map_one hR) (λ h ↦ ?_)
  have h0 : ∀ x, -f x = x :=
    congrFun (hf.neg_apply.char_ne2_of_map_one hR (neg_eq_iff_eq_neg.mpr h))
  funext x; rw [← neg_eq_iff_eq_neg, h0]

end



/-! ### Case `char(R) = 2` -/

section

open Extra.CharTwo

theorem char_eq2_solution [Extra.CharTwo R] {f : R → R} (hf : good f) : f = (·) := by
  ---- First note that `f(1) = 1`
  have hf1 : f 1 = 1 := sq_eq_one_iff.mp hf.map_one_sq_eq
  ---- Now show that if `f(c) = d + 1` and `f(d) = c + 1`, then either `d ∈ {c, c + 1}`.
  have h {c d : R} (h : f c = d + 1) : f ((d + 1) * (c + 1)) = c ^ 2 + d + 1 := by
    have h1 := hf c (c + 1)
    rw [add_add_cancel_left, hf1, mul_one, h, ← add_eq_iff_eq_add, ← add_rotate] at h1
    exact h1.symm
  replace h {c d : R} (h0 : f c = d + 1) (h1 : f d = c + 1) : c = d ∨ c = d + 1 := by
    have h2 : c * d = d * c := by
      rw [← add_eq_iff_eq_add.mpr h0, mul_add_one, add_one_mul, _root_.add_left_inj,
        ← hf.inj, hf.self_mul_map, ← add_eq_iff_eq_add'.mpr (hf c c),
        add_self_eq_zero, hf.map_zero, mul_zero, hf.map_zero, zero_add]
    have h3 : c ^ 2 + d = d ^ 2 + c := by
      rw [← add_left_inj (a := 1), ← h h0, ← h h1, mul_add_one,
        add_one_mul, ← h2, ← mul_add_one, ← add_one_mul]
    rw [← add_eq_zero_iff_eq, add_add_add_comm, _root_.add_comm d,
      ← add_sq_of_Commute h2, sq, ← mul_add_one, mul_eq_zero, add_assoc] at h3
    exact h3.imp add_eq_zero_iff_eq.mp add_eq_zero_iff_eq.mp
  ---- Now use the fact that the above is satisfied for `(c, d) = (f(y), f(y + 1))`
  have h0 := hf.map_map_add_one hf1
  funext y; have h1 := h0 (y + 1)
  rw [add_add_cancel_right] at h1
  obtain h2 | h2 := h (h0 y) h1
  · rw [hf.inj, add_eq_left] at h2
    rw [← sub_eq_zero, ← mul_one (f y - y), h2, mul_zero]
  · rwa [h2, add_add_cancel_right, hf.inj] at h1

end

end good





/-! ### Final solution -/

/-- Final solution -/
theorem final_solution [NoZeroDivisors R] {f : R → R} : good f ↔ f = (·) ∨ f = (- ·) := by
  refine ⟨λ hf ↦ ?_, λ h ↦ ?_⟩
  ---- `→` direction
  · obtain h | h : (2 : R) ≠ 0 ∨ (2 : R) = 0 := ne_or_eq 2 0
    · exact hf.char_ne2_solution h
    · have : Extra.CharTwo R := Extra.CharTwo.Semiring_of_two_eq_zero h
      left; exact hf.char_eq2_solution
  ---- `←` direction
  · rcases h with rfl | rfl
    exacts [id_is_good, neg_is_good]
