/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2015.A4

/-!
# IMO 2015 A4 (P5, Generalization)

Let $R$ be a ring.
Find all functions $f : R → R$ such that for any $x, y ∈ R$,
$$ f(x + f(x + y)) + f(xy) = x + f(x + y) + f(x) y. $$

### Progress

If $R$ is a domain, then the answer is $x ↦ x$ and $x ↦ 2 - x$.
-/

namespace IMOSL
namespace IMO2015A4

namespace good

variable [Ring R] {f : R → R} (hf : good f)
include hf

@[inherit_doc map_add_map_add_one_fixed]
alias eq1_map_add_map_add_one_fixed := map_add_map_add_one_fixed

@[inherit_doc map_map_add_map_zero]
alias eq2_map_map_add_map_zero := map_map_add_map_zero

@[inherit_doc map_self_add_map_self]
alias eq3_map_self_add_map_self := map_self_add_map_self

/-- (4) We have `f(f(0)) = 0`. -/
theorem eq4_map_map_zero_eq_zero : f (f 0) = 0 := by
  have h := hf.map_map_add_map_zero 0
  rwa [mul_zero, add_zero, add_eq_right] at h

/-- (5) We have `f(f(0) - 1) = f(0) - 1`. -/
theorem eq5_map_zero_sub_one_fixed : f (f 0 - 1) = f 0 - 1 := by
  have h := hf.map_add_map_add_one_fixed (f 0 - 1)
  rwa [sub_add_cancel, hf.eq4_map_map_zero_eq_zero, add_zero] at h

/-- We have `f(1) = 1`, unconditionally. -/
theorem map_one_eq_one : f 1 = 1 := by
  ---- Let `b = f(1) - 1`; it suffices to show that `b = 0`.
  let b : R := f 1 - 1
  suffices b = 0 from eq_of_sub_eq_zero this
  have hb : b + 1 = f 1 := sub_add_cancel (f 1) 1
  ---- Plugging `x = 0` into (1) yields `f(b + 1) = b + 1`.
  have h : f (b + 1) = b + 1 := by
    have h := hf.map_add_map_add_one_fixed 0
    rwa [zero_add, zero_add, ← hb] at h
  ---- Plugging `x = b + 1` into (2) yields `f(0) b = 0`.
  have h0 : f 0 * b = 0 := by
    have h0 := hf.eq2_map_map_add_map_zero (b + 1)
    rwa [h, h, add_right_inj, mul_add_one, right_eq_add] at h0
  ---- Plugging `(x, y) = (1, f(0) - 1)` into the original FE gives `b(f(0) - 1) = b`.
  have h1 : b * (f 0 - 1) = b := by
    have h1 := hf 1 (f 0 - 1)
    rw [add_sub_cancel, hf.eq4_map_map_zero_eq_zero,
      add_zero, one_mul, hf.eq5_map_zero_sub_one_fixed] at h1
    rw [sub_one_mul, sub_eq_sub_iff_add_eq_add, add_comm, h1]
  ---- Then `-b^2 = b (f(0) - 1) b = b^2`, so `2b^2 = 0`.
  replace h1 : b * b + b * b = 0 := calc
    _ = b * (1 + (f 0 - 1)) * b := by rw [mul_one_add, h1, add_mul]
    _ = 0 := by rw [add_sub_cancel, mul_assoc, h0, mul_zero]
  ---- Plugging `(x, y) = (-b, 2b + 1)` into the original FE gives `f(-b)(2b) = b`.
  have h2 : f (-b) * (b + b) = b := by
    have h2 := hf (-b) (b + (b + 1))
    rw [neg_add_cancel_left, h, neg_add_cancel_left, ← add_assoc, mul_add_one, neg_mul,
      mul_add, h1, neg_zero, zero_add, mul_add_one, ← add_assoc, add_left_inj,
      ← sub_eq_iff_eq_add'] at h2
    exact h2.symm
  ---- Then `b^2 = 0`.
  replace h1 : b * b = 0 := calc
    _ = f (-b) * (b + b) * b := by rw [h2]
    _ = 0 := by rw [mul_assoc, add_mul, h1, mul_zero]
  ---- Plugging `(x, y) = (b + 1, -b)` into the original FE gives `f(-b) = f(0) - b`.
  replace h : f (-b) = f 0 - b := by
    -- We also need to plug `x = b + 1` into (3) to get `f(2(b + 1)) = 2(b + 1) - f(0)`.
    have h3 : f (b + 1 + (b + 1)) = b + 1 + (b + 1) - f 0 := by
      have h3 := hf.eq3_map_self_add_map_self (b + 1)
      rwa [h, ← eq_sub_iff_add_eq] at h3
    -- Now go back on track.
    have h4 := hf (b + 1) (-b)
    rwa [add_neg_cancel_comm, h, add_one_mul, mul_neg, h1, neg_zero, zero_add, ← hb, h3,
      ← add_sub_right_comm, add_sub_assoc, add_right_inj, sub_eq_iff_eq_add',
      ← sub_eq_add_neg] at h4
  ---- Now bring all the pieces together and get `b = 0`.
  rw [h, sub_mul, mul_add, h0, mul_add, h1, sub_self] at h2
  exact h2.symm

/-- If `f(y) = y` and `f(y + 1) = y + 1`, then `f(y + 2) = y + 2`. -/
theorem fixed_pt_add_two_of_fixed_pt (hy : f y = y) (hy0 : f (y + 1) = y + 1) :
    f (y + 2) = y + 2 :=
  fixed_pt_add_two_of_map_one hf hf.map_one_eq_one hy hy0

/-- If `(y) = y` and `f(y + 1) = y + 1`, then `f(y + n) = y + n` for every `n ∈ ℕ`. -/
theorem fixed_pt_add_nat_of_fixed_pt (hy : f y = y) (hy0 : f (y + 1) = y + 1) (n : ℕ) :
    f (y + n) = y + n := by
  ---- We use two-step induction on `n`; the two base cases are given as hypothesis.
  induction n using Nat.twoStepInduction with
  | zero => rw [Nat.cast_zero, add_zero, hy]
  | one => rw [Nat.cast_one, hy0]
  | more k hk hk0 => ?_
  ---- Now apply the previous argument and we are done.
  rw [Nat.cast_succ, ← add_assoc] at hk0
  rw [Nat.cast_add, Nat.cast_two, ← add_assoc]
  exact hf.fixed_pt_add_two_of_fixed_pt hk hk0


variable (hf0 : f 0 = 0)
include hf0

/-- (7) If `f(0) = 0`, then `f(-x) = -f(x)` for every `x ∈ R`. -/
theorem eq7_map_neg (x) : f (-x) = -f x :=
  map_neg_of_map_zero_map_one hf hf0 hf.map_one_eq_one x

/-- (8) If `f(0) = 0`, then `f(nx) = nf(x)` for every `n ∈ ℕ` and `x ∈ R`. -/
theorem eq8_map_nsmul (n : ℕ) (x : R) : f (x * n) = f x * n := by
  ---- First show that for any `x ∈ R`, `x + n + f(x)` is a fixed point of `f`.
  have h (x) : f (x + f x + n) = x + f x + n := by
    suffices f (x + f x - 1 + n.succ) = x + f x - 1 + n.succ by
      rwa [Nat.cast_succ, sub_add_add_cancel] at this
    -- We just have to show that `x + f(x) - 1` and `x + f(x)` are fixed points of `f`.
    refine hf.fixed_pt_add_nat_of_fixed_pt ?_ ?_ n.succ
    -- Case `x + f(x) - 1`.
    · have h := hf.eq1_map_add_map_add_one_fixed (x - 1)
      rwa [sub_add_cancel, ← add_sub_right_comm] at h
    -- Case `x + f(x)`.
    · rw [sub_add_cancel, ← add_zero (f _), ← hf0, hf.eq3_map_self_add_map_self]
  ---- Now specialize to saying that `x + f(x - n)` is a fixed point of `f`.
  replace h : f (x + f (x + -n)) = x + f (x + -n) := by
    specialize h (x + -n)
    rwa [add_right_comm, neg_add_cancel_right] at h
  ---- Now substitute `y = -n` into the original FE and simplify.
  have h0 := hf x (-n)
  rwa [h, add_right_inj, mul_neg, mul_neg, hf.eq7_map_neg hf0, neg_inj] at h0

/-- (8), specialized to the case `n = 2`: `f(2x) = 2f(x)` for all `x ∈ R`. -/
theorem eq8_map_two_mul (x : R) : f (2 * x) = 2 * f x := by
  simpa only [Nat.cast_two, mul_two, two_mul] using hf.eq8_map_nsmul hf0 2 x

/-- (9) If `f(0) = 0`, then `2f(t) = 2t` for all `t ∈ R`. -/
theorem eq9_two_mul_map (t : R) : 2 * f t = 2 * t :=
  two_mul_map_of_map_zero_eq_zero hf hf0 hf.map_one_eq_one t

/-- If `f(0) = 0`, then `f` is the identity map. -/
theorem eq_id_of_map_zero_eq_zero : f = id := by
  ---- Define `g : R → R` by `g(x) = f(x) - x`. It suffices to show that `g = 0`.
  let g (x : R) : R := f x - x
  suffices ∀ x, g x = 0 from funext λ x ↦ eq_of_sub_eq_zero (this x)
  ---- From (9), we have `2 g(x) = 0` for all `x ∈ R`.
  have hg9 (x) : 2 * g x = 0 := by rw [mul_sub, hf.eq9_two_mul_map hf0, sub_self]
  have hg9' (x) : -g x = g x := by rw [neg_eq_iff_add_eq_zero, ← two_mul, hg9]
  ---- From (7), we have `g(-x) = g(x)` for all `x ∈ R`.
  have hg7 (x) : g (-x) = g x :=
    calc f (-x) - (-x)
    _ = -(f x - x) := by rw [hf.eq7_map_neg hf0, neg_sub']
    _ = f x - x := hg9' x
  ---- From (8), we have `g(2x) = 0` for all `x ∈ R`.
  have hg8 (x) : g (2 * x) = 0 :=
    calc f (2 * x) - 2 * x
    _ = 2 * (f x - x) := by rw [hf.eq8_map_two_mul hf0, mul_sub]
    _ = 0 := hg9 x
  ---- From (2), we have `g(y + g(y)) = 0` for all `y ∈ R`.
  have hg2 (y) : g (y + g y) = 0 := by
    have h : f (f y) + f 0 = f y + f 0 * y := hf.eq2_map_map_add_map_zero y
    rw [hf0, add_zero, zero_mul, add_zero, ← add_sub_cancel y (f y)] at h
    exact sub_eq_zero_of_eq h
  ---- Since `f(0) = 0` and `f(1) = `, we have `g(0) = g(1) = 0`.
  replace hf0 : g 0 = 0 := (sub_zero _).trans hf0
  have hf1 : g 1 = 0 := sub_eq_zero_of_eq hf.map_one_eq_one
  ---- (10). The new functional equation is `g(2x + y + g(x + y)) + g(xy) = g(x) y`.
  replace hf (x y) : g (x + x + y + g (x + y)) + g (x * y) = g x * y := by
    dsimp only [g]
    rw [add_assoc x, add_assoc x, add_sub_cancel,
      sub_add_sub_comm, hf, add_sub_add_left_eq_sub, sub_mul]
  ---- From the new FE (10), we get `g(g(t)) = 0` for all `t ∈ R`.
  have h (t) : g (g t) = 0 := by
    have h := hf (-t) (t + t)
    rwa [← neg_add, neg_add_cancel, zero_add, neg_add_cancel_left, mul_add,
      ← two_mul, hg8, add_zero, mul_add, ← two_mul, ← mul_assoc, hg9, zero_mul] at h
  ---- (11). Plug `x = g(t)` into (10) and get `g(y + g(g(t) + y)) = g(g(t) y)`.
  have hg11 (t y) : g (y + g (g t + y)) = g (g t * y) := by
    have h0 := hf (g t) y
    rwa [← two_mul, hg9, zero_add, h, zero_mul, add_eq_zero_iff_eq_neg, hg9'] at h0
  ---- (12). Plug `y = t` into (11) and get `g(g(t) t) = g(t)`.
  have hg12 (t) : g (g t * t) = g t := by
    rw [← hg11, add_comm (g t) t, hg2, add_zero]
  ---- Plugging `(x, y) = (2, t - 2)` into (10) gives `g(g(t) + t + 2) = 0`.
  have h0 (t) : g (g t + t + 2) = 0 := by
    have h0 := hf 2 (t - 2)
    rw [add_assoc 2, add_sub_cancel, hg8, add_zero] at h0
    rw [add_right_comm, add_rotate, h0, ← mul_one 2, hg8, zero_mul]
  ---- Plugging `y = t + 2` into (11) now gives `g(t + 2) = g(t)`.
  replace h0 (t) : g (t + 2) = g t := by
    have h1 := hg11 t (t + 2)
    rwa [← add_assoc, h0, add_zero, mul_add, mul_two, ← two_mul, hg9, add_zero, hg12] at h1
  ---- Plugging `y = 1 - x` into (10) gives `g(x(1 - x)) = g(x)(1 - x) + g(1 - x)`.
  have h1 (x) : g (x * (1 - x)) = g x * (1 - x) + g (1 - x) :=
    calc g (x * (1 - x))
    _ = g x * (1 - x) - g (x + x + (1 - x) + g (x + (1 - x))) := eq_sub_of_add_eq' (hf _ _)
    _ = g x * (1 - x) - g (x + 1) := by rw [add_assoc x, add_sub_cancel, hf1, add_zero]
    _ = g x * (1 - x) + g (x + 1) := by rw [sub_eq_add_neg, hg9']
    _ = g x * (1 - x) + g (x - 1 + (1 + 1)) := by rw [sub_add_add_cancel]
    _ = g x * (1 - x) + g (x - 1) := by rw [one_add_one_eq_two, h0]
    _ = g x * (1 - x) + g (1 - x) := by rw [← neg_sub 1 x, hg7]
  ---- Now fix `x`. Applying symmetry, we get `g(1 - x) (1 - x) = g(x) x`.
  intro x
  replace h1 : g x * (1 - x) + g (1 - x) = g (1 - x) * x + g x := by
    calc g x * (1 - x) + g (1 - x)
    _ = g (x * (1 - x)) := (h1 x).symm
    _ = g ((1 - x) * x) := by rw [mul_one_sub, one_sub_mul]
    _ = g (1 - x) * x + g x := by simpa only [sub_sub_cancel] using h1 (1 - x)
  replace h1 : g (1 - x) * (1 - x) = g x * x := by
    rwa [← sub_eq_sub_iff_add_eq_add, ← mul_sub_one, sub_sub_cancel_left, mul_neg,
      ← mul_sub_one, neg_eq_iff_eq_neg, ← mul_neg, neg_sub, eq_comm] at h1
  ---- Now finish up via `g(1 - x) = g(g(1 - x) (1 - x)) = g(g(x) x) = g(x)`.
  replace h0 : g (1 - x) = g x := by rw [← hg12, h1, hg12]
  rwa [h0, mul_one_sub, sub_eq_add_neg, ← neg_mul, hg9', add_eq_right] at h1

end good


/-- Final solution to the generalized version -/
theorem Generalization.final_solution [Ring R] [DecidableEq R] [NoZeroDivisors R]
    {f : R → R} : good f ↔ f = (λ x ↦ 2 - x) ∨ f = id := by
  refine ⟨λ hf ↦ ?_, λ hf ↦ ?_⟩
  ---- The `→` direction.
  · apply (Decidable.em (f 0 = 0)).symm.imp
    exacts [hf.eq_two_sub_of_map_zero_ne_zero, hf.eq_id_of_map_zero_eq_zero]
  ---- The `←` direction.
  · rcases hf with rfl | rfl
    exacts [two_sub_is_good, id_is_good]
