/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.FieldTheory.Finite.Basic

/-!
# IMO 2024 N6

Determine all positive integers $n$ such that for any polynomial $P ∈ ℤ[X]$,
  there exists a polynomial $Q ∈ ℤ[X]$ of degree $2$ such that for any integer $k$,
$$ n ∤ Q(k)(P(k) + Q(k)). $$

### Answer

$n > 2$.

### Solution

We follow and generalize Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2024SL.pdf).
Given a commutative ring $R$, we say that a function $f : R → R$ is *good* if
  there exists $a, b, c ∈ R$ such that for any $r ∈ R$,
$$ (ar^2 + br + c)(f(r) - (ar^2 + br + c)) ≠ 0. $$

The original problem is equivalent to finding all values of $n > 0$
  for which every polynomial over $ℤ/nℤ$ is good.
The official solution implies that this holds for $n > 2$, and "more generally",
  every function over $𝔽ₚ$ is good if $p$ is an odd prime.
(This isn't really more general, as every function from $𝔽ₚ$ to itself is a polynomial.)
We show even more:
* every function from $ℤ/4ℤ$ to itself is good (see below);
* every function from a finite field of characteristic $≠ 2$ to itself is good
  (follows from the official solution).

### The case $n = 4$

Consider an arbitrary function $f : ℤ/4ℤ → ℤ/4ℤ$.
We show that there exists $a, c ∈ ℤ/4ℤ$ such that $Q(r)(f(r) - Q(r)) ≠ 0$
  for all $r ∈ ℤ/4ℤ$, where $Q(r) = a(1 - r^2) + cr^2$.
If $\{f(0), f(2)\} ≠ \{1, 3\}$, pick any $a \in \{1, 3\} \setminus \{f(0), f(2)\}$.
If $\{f(0), f(2)\} = \{1, 3\}$, pick $a = 2$.
We do similar procedure to pick $c$ but with $\{f(1), f(3)\}$ replacing $\{f(0), f(2)\}$.
-/

namespace IMOSL
namespace IMO2024N6

open Polynomial

/-! ### Definitions and general properties -/

/-- A function `f : R → R` is called `good` if there exists `a, b, c ∈ R`
  such that `(ar^2 + br + c)(f(r) - (ar^2 + br + c)) ≠ 0` for any `r ∈ R`. -/
def good [Ring R] (f : R → R) :=
  ∃ a b c : R, ∀ r : R, (a * r ^ 2 + b * r + c) * (f r - (a * r ^ 2 + b * r + c)) ≠ 0

/-- A surjective ring homomorphism pulls good polynomials back to good polynomials. -/
theorem good_of_good_polynomial_map [Ring R] [Ring S]
    (φ : R →+* S) (hφ : (⇑φ).Surjective) (P : R[X]) (hP : good (P.map φ).eval) :
    good P.eval := by
  rcases hP with ⟨a', b', c', h'⟩
  obtain ⟨a, rfl⟩ : ∃ a, φ a = a' := hφ a'
  obtain ⟨b, rfl⟩ : ∃ b, φ b = b' := hφ b'
  obtain ⟨c, rfl⟩ : ∃ c, φ c = c' := hφ c'
  refine ⟨a, b, c, λ r hr ↦ h' (φ r) ?_⟩
  dsimp only; rw [P.eval_map φ, P.eval₂_at_apply, ← φ.map_pow, ← φ.map_mul,
    ← φ.map_mul, ← φ.map_add, ← φ.map_add, ← φ.map_sub, ← φ.map_mul, hr, φ.map_zero]

/-- If `R` is a domain, then `f : R → R` is good if and only if there exists `a, b, c ∈ R`
  such that `ar^2 + br + c ≠ 0` and `ar^2 + br + c ≠ f(r)` for any `r ∈ R`. -/
theorem good_iff_of_domain [Ring R] [NoZeroDivisors R] {f : R → R} :
    good f ↔ ∃ a b c : R, ∀ r : R,
      a * r ^ 2 + b * r + c ≠ 0 ∧ a * r ^ 2 + b * r + c ≠ f r := by
  conv => left; unfold good; right; ext; right; ext; right; ext; ext
          rw [mul_ne_zero_iff, sub_ne_zero, ne_comm (a := f _)]

/-- If `f : R → R` does not attain some unit, then `f` is good. -/
theorem good_of_map_ne_unit [Ring R]
    (f : R → R) (u : Rˣ) (hf : ∀ r, f r ≠ u) : good f := by
  refine ⟨0, 0, u, λ r ↦ ?_⟩
  rw [zero_mul, zero_mul, zero_add, zero_add, ne_eq, Units.mul_right_eq_zero, sub_eq_zero]
  exact hf r


section

variable [CommRing R] {f : R → R}

/-- If `f : R → R` is good, then for any `v ∈ R`, the function `x ↦ f(x + v)` is good. -/
theorem good.shift (hf : good f) (v : R) : good (λ x ↦ f (x + v)) := by
  rcases hf with ⟨a, b, c, h⟩
  refine ⟨a, a * (2 * v) + b, a * v ^ 2 + b * v + c, λ r ↦ ?_⟩
  rw [add_mul _ _ r, ← add_assoc (a * r ^ 2), mul_assoc, ← mul_add, ← add_assoc,
    add_add_add_comm, ← mul_add, ← mul_add, mul_right_comm, ← add_sq]
  exact h (r + v)

/-- For any `f : R → R` and `v ∈ R`, the function `x ↦ f(x + v)` is good iff `f` is good. -/
theorem good_shift_iff {v : R} : good (λ x ↦ f (x + v)) ↔ good f :=
  ⟨λ hf ↦ by simpa only [neg_add_cancel_right] using hf.shift (-v), λ hf ↦ hf.shift v⟩

/-- If `f : R → R` is good, then for any `u ∈ R`, the function `x ↦ f(ux)` is good. -/
theorem good.scale (hf : good f) (u : R) : good (λ x ↦ f (u * x)) := by
  rcases hf with ⟨a, b, c, h⟩
  refine ⟨a * u ^ 2, b * u, c, λ r ↦ ?_⟩
  rw [mul_assoc, ← mul_pow, mul_assoc]
  exact h (u * r)

/-- For any `f : R → R` and `u ∈ Rˣ`, the function `x ↦ f(ux)` is good iff `f` is good. -/
theorem good_scale_iff {u : Rˣ} : good (λ x ↦ f (u * x)) ↔ good f :=
  ⟨λ hf ↦ by simpa only [Units.mul_inv_cancel_left] using hf.scale ↑u⁻¹, λ hf ↦ hf.scale u⟩

/-- For any `f : R → R`, `u ∈ Rˣ`, and `v ∈ R`,
  the function `x ↦ f(ux + v)` is good iff `f` is good. -/
theorem good_shift_scale_iff {u : Rˣ} {v : R} : good (λ x ↦ f (u * x + v)) ↔ good f :=
  (good_scale_iff (f := λ x ↦ f (x + v)) (u := u)).trans good_shift_iff

end





/-! ### The finite field case -/

/-- Let `F` be a division ring. For any `a, b, c, d ∈ F` such that `a ≠ b` and `c ≠ d`,
  there exists `u ∈ Fˣ` and `v ∈ F` such that `uc + v = a` and `ud + v = b`. -/
theorem linear_transform_solver [DivisionRing F] {a b c d : F} (h : a ≠ b) (h0 : c ≠ d) :
    ∃ u : Fˣ, ∃ v : F, u * c + v = a ∧ u * d + v = b := by
  ---- Solving directly yields `u = (b - a)/(d - c)`; and `v = a - uc`.
  replace h : b - a ≠ 0 := sub_ne_zero_of_ne h.symm
  replace h0 : d - c ≠ 0 := sub_ne_zero_of_ne h0.symm
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, ↑u = (b - a) / (d - c) :=
    ⟨Units.mk0 ((b - a) / (d - c)) (div_ne_zero h h0), rfl⟩
  refine ⟨u, a - u * c, add_sub_cancel _ _, ?_⟩
  rw [add_sub_left_comm, ← mul_sub, hu, div_mul_cancel₀ _ h0, add_sub_cancel]

open Finset in
/-- Let `f : S → S` be a function on a finite set `S`. Suppose that there exists
  `a, b, c ∈ S` pairwise distinct and `d ≠ c` such that `f(a) = f(b)` and `f(c) = f(d)`.
  Then for any `x ∈ S`, there exists `y ∈ S` with `y ≠ x` such that `y ∉ f(S)`. -/
theorem exists_ne_map_ne_of_four [Fintype S] [DecidableEq S] {f : S → S}
    {a b c d : S} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hcd : c ≠ d)
    (hab0 : f a = f b) (hcd0 : f c = f d) (x) :
    ∃ y ≠ x, ∀ z, f z ≠ y := by
  ---- WLOG assume that `a ≠ d`.
  wlog had : a ≠ d generalizing a b
  · exact this hab.symm hbc hac hab0.symm λ h ↦ had (hab.trans_eq h)
  ---- First note that `{c, a}ᶜ` is smaller than `{x}ᶜ`.
  have h : ({c, a}ᶜ : Finset S).card < ({x}ᶜ : Finset S).card := by
    rw [card_compl {x}, card_singleton, ← card_singleton a, ← card_compl, compl_insert]
    refine card_erase_lt_of_mem ?_
    rwa [mem_compl, mem_singleton, eq_comm]
  ---- Then there exists `y ≠ x` such that `f(z) ≠ y` for `z ≠ a, c`.
  obtain ⟨y, hy, hy0⟩ : ∃ y ≠ x, ∀ z ≠ c, z ≠ a → f z ≠ y := by
    -- Thus `f` does not map `{c, a}ᶜ` into a superset of `{x}ᶜ`, and so we're done.
    replace h : ¬Set.SurjOn f ({c, a}ᶜ : Finset S) ({x}ᶜ : Finset S) :=
      λ h0 ↦ h.not_ge (card_le_card_of_surjOn f h0)
    rw [Set.SurjOn, Set.subset_def, not_forall] at h
    rcases h with ⟨y, hy⟩
    rw [_root_.not_imp, mem_coe, mem_compl, mem_singleton, Set.mem_image, not_exists] at hy
    refine ⟨y, hy.1, λ z ↦ ?_⟩
    replace hy : ¬(z ∈ (({c, a}ᶜ : Finset S) : Set S) ∧ f z = y) := hy.2 z
    rw [not_and, mem_coe, mem_compl, mem_insert, not_or, mem_singleton] at hy
    exact λ h h0 ↦ hy ⟨h, h0⟩
  ---- Now we claim that this `y` indeed works, i.e., `f(a), f(c) ≠ y`.
  refine ⟨y, hy, λ z ↦ ?_⟩
  clear h hy
  ---- First consider the case `z = a`.
  obtain rfl | hza : z = a ∨ z ≠ a := dec_em _
  · exact hab0.trans_ne (hy0 b hbc hab.symm)
  ---- Second, consider the case `z = c`.
  obtain rfl | hzc : z = c ∨ z ≠ c := dec_em _
  · exact hcd0.trans_ne (hy0 d hcd.symm had.symm)
  ---- Finally, resolve the case `z ≠ a, c`.
  · exact hy0 z hzc hza

/-- Let `F` be a finite field of characteristic `≠ 2`.
  Then every function from `F` to itself is good. -/
theorem good_of_char_ne_two [Field F] [Fintype F] [DecidableEq F] (hF : ringChar F ≠ 2) :
    ∀ f : F → F, good f := by
  have X : (1 : F) ≠ 0 := one_ne_zero
  ---- Reduce to the case where `0 ∉ f(F)`.
  intro f; wlog h : ∀ x, f x ≠ 0 generalizing f
  · -- Consider `g : F → F` defined by `g(x) = 1` if `x = 0` and `g(x) = f(x)` otherwise.
    obtain ⟨a, b, c, h⟩ : ∃ a b c : F, ∀ r : F, a * r ^ 2 + b * r + c ≠ 0 ∧
        a * r ^ 2 + b * r + c ≠ if f r = 0 then 1 else f r := by
      refine good_iff_of_domain.mp (this (λ x ↦ if f x = 0 then 1 else f x) ?_)
      intro x; dsimp only
      split_ifs with h
      exacts [X, h]
    -- Now that we've shown that `g` is good, use it to show that `f` is good.
    refine good_iff_of_domain.mpr ⟨a, b, c, λ r ↦ ?_⟩
    let s : F := a * r ^ 2 + b * r + c
    obtain ⟨h0, h1⟩ : s ≠ 0 ∧ s ≠ if f r = 0 then 1 else f r := h r
    refine ⟨h0, λ (h2 : s = f r) ↦ h1 ?_⟩
    rw [h2, if_neg (h2.symm.trans_ne h0)]
  ---- Now reduce to the case where `f(-1) = f(1)`.
  wlog h0 : f 1 = f (-1) generalizing f
  · -- Note that `f` is not injective. Find `c ≠ d ∈ F` such that `f(c) = f(d)`.
    obtain ⟨c, d, h1, h2⟩ : ∃ c d, f c = f d ∧ c ≠ d := by
      have h1 : ¬f.Surjective := λ h1 ↦ (h1 0).elim h
      simpa [Function.Injective] using Finite.surjective_of_injective.mt h1
    -- Now find `u ∈ Rˣ` and `v ∈ R` such that `uc + v = 1` and `ud + v = -1`.
    obtain ⟨u, v, h3, h4⟩ : ∃ u : Fˣ, ∃ v : F, u * c + v = 1 ∧ u * d + v = -1 :=
      linear_transform_solver (λ h3 ↦ h0 (congrArg f h3)) h2
    -- Then `x ↦ f(u⁻¹(x - v))` being good implies that `f` is good.
    refine (good_shift_scale_iff (u := u⁻¹) (v := u⁻¹ * -v)).mp (this _ (λ x ↦ h _) ?_)
    rw [← mul_add, ← mul_add, ← h4, add_neg_cancel_right, Units.inv_mul_cancel_left,
      ← h3, add_neg_cancel_right, Units.inv_mul_cancel_left, h1]
  ---- If `f` does not attain a non-zero value, then we are done.
  by_cases h1 : ∃ u : Fˣ, ∀ x, f x ≠ u
  · rcases h1 with ⟨u, hu⟩
    exact good_of_map_ne_unit f u hu
  ---- Now suppose that `f` attains every non-zero value.
  replace h1 : ∀ u ≠ 0, ∃ x, f x = u := by
    simp only [ne_eq, not_exists, not_forall, not_not] at h1
    exact λ u hu ↦ h1 (Units.mk0 u hu)
  ---- Let `r` be a non-square in `F`.
  obtain ⟨r', hr⟩ : ∃ r' : F, ¬IsSquare r' := FiniteField.exists_nonsquare hF
  ---- Choose `y` such that `f(y) = (1 - r') f(0)`, and note that `y ≠ 0`.
  obtain ⟨y, hy⟩ : ∃ y, f y = (1 - r') * f 0 :=
    h1 _ (mul_ne_zero (sub_ne_zero.mpr λ hr0 ↦ hr (hr0 ▸ IsSquare.one)) (h 0))
  have hr' : r' ≠ 0 := λ hr' ↦ hr (hr' ▸ IsSquare.zero)
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [eq_comm, mul_eq_right₀ (h 0), sub_eq_self] at hy
    exact hr' hy
  ---- Let `r = y^2/r'`, and note that `r` is not a square either.
  let r : F := y ^ 2 / r'
  replace hr : ¬IsSquare r := by
    refine λ hr0 ↦ hr ?_
    simpa only [r, div_div_cancel₀ (pow_ne_zero 2 hy0)] using (IsSquare.sq y).div hr0
  replace hr (x) : x ^ 2 - r ≠ 0 :=
    λ hr0 ↦ hr ⟨x, by rw [← sq, eq_comm, ← sub_eq_zero, hr0]⟩
  ---- The function `φ(x) = f(x)/(x^2 - r)` does not attain a non-zero value.
  obtain ⟨a, ha, ha0⟩ : ∃ a ≠ 0, ∀ x, f x / (x ^ 2 - r) ≠ a := by
    refine exists_ne_map_ne_of_four (a := -1) (b := 1) (c := 0) (d := y)
      (Ring.neg_one_ne_one_of_char_ne_two hF) (neg_ne_zero.mpr X) X hy0.symm ?_ ?_ _
    -- Verify that `φ(-1) = φ(1)`.
    · rw [h0, neg_sq]
    -- Verify that `φ(0) = φ(y)`.
    · rw [hy, div_eq_div_iff (hr _) (hr _), zero_pow Nat.two_pos.ne.symm, zero_sub,
        mul_right_comm, mul_neg, one_sub_mul, neg_sub, mul_div_cancel₀ _ hr', mul_comm]
  ---- Then take `(a, b, c) = (a, 0, -ar)` and see that it works.
  refine good_iff_of_domain.mpr ⟨a, 0, a * (-r), λ x ↦ ?_⟩
  rw [zero_mul, add_zero, ← mul_add, ← sub_eq_add_neg]
  exact ⟨mul_ne_zero ha (hr x), λ h2 ↦ ha0 x (eq_div_of_mul_eq (hr x) h2).symm⟩





/-! ### The `ZMod` case -/

/-- Any function over `ZMod 1` is not good. -/
theorem ZMod1_not_good (f : ZMod 1 → ZMod 1) : ¬good f := by
  rintro ⟨_, _, c, h⟩
  replace h : (0 + c) * (f 0 - (0 + c)) ≠ 0 := h 0
  rw [Subsingleton.eq_zero c, Subsingleton.eq_zero (f 0)] at h
  exact h rfl

/-- The constant one function is not good over `ZMod 2`. -/
theorem const_one_ZMod2_not_good : ¬good (λ _ : ZMod 2 ↦ 1) := by
  rintro ⟨_, _, c, h⟩
  refine h 0 (?_ : (0 + c) * (1 - (0 + c)) = 0)
  match c with | 0 => rfl | 1 => rfl

/-- For any `a, b ∈ ZMod 4`, there exists `c ∈ ZMod 4` such that `c(a - c), c(b - c) ≠ 0`. -/
theorem ZMod4_exists_mul_sub_ne_zero₂ :
    ∀ a b : ZMod 4, ∃ c, c * (a - c) ≠ 0 ∧ c * (b - c) ≠ 0 := by
  decide

/-- Every function `f : ZMod 4 → ZMod 4` is good. -/
theorem ZMod4_good (f : ZMod 4 → ZMod 4) : good f := by
  ---- Pick some `u ∈ ZMod 4` such that `c(f(0) - c) ≠ 0` and `c(f(2) - c) ≠ 0`.
  obtain ⟨u, hc0, hc2⟩ : ∃ u, u * (f 0 - u) ≠ 0 ∧ u * (f 2 - u) ≠ 0 :=
    ZMod4_exists_mul_sub_ne_zero₂ (f 0) (f 2)
  ---- Similarly, pick some `v ∈ ZMod 4` such that `d(f(1) - d) ≠ 0` and `d(f(3) - d) ≠ 0`.
  obtain ⟨v, hd1, hd3⟩ : ∃ v, v * (f 1 - v) ≠ 0 ∧ v * (f 3 - v) ≠ 0 :=
    ZMod4_exists_mul_sub_ne_zero₂ (f 1) (f 3)
  ---- Then `ax^2 + bx + c = u(1 - x^2) + vx^2 = (v - u)x^2 + u` works.
  refine ⟨v - u, 0, u, λ r ↦ ?_⟩
  have h (y) : ((v - u) * 0 + u) * (y - ((v - u) * 0 + u)) = u * (y - u) := by
    rw [mul_zero, zero_add]
  have h0 (y) : ((v - u) * 1 + u) * (y - ((v - u) * 1 + u)) = v * (y - v) := by
    rw [mul_one, sub_add_cancel]
  rw [zero_mul, add_zero]
  match r with
  | 0 => exact (h (f 0)).trans_ne hc0
  | 1 => exact (h0 (f 1)).trans_ne hd1
  | 2 => exact (h (f 2)).trans_ne hc2
  | 3 => exact (h0 (f 3)).trans_ne hd3

/-- If `p` is an odd prime, then every function `f : ZMod p → ZMod p` is good. -/
theorem ZMod_good_of_prime_ne_two (p) [Fact (Nat.Prime p)] (hp : p ≠ 2) :
    ∀ f : ZMod p → ZMod p, good f :=
  good_of_char_ne_two ((ZMod.ringChar_zmod_n p).trans_ne hp)

/-- If `n > 2`, then every polynomial over `ZMod n` is good. -/
theorem ZMod_good_of_two_lt (hn : 2 < n) (P : (ZMod n)[X]) : good P.eval := by
  ---- There are two cases: (1). `n` is a power of `2`; (2). `n` has an odd prime factor.
  obtain ⟨k, rfl⟩ | ⟨p, hp, hpn, hp0⟩ :
      (∃ k, n = 2 ^ k) ∨ (∃ p, Nat.Prime p ∧ p ∣ n ∧ Odd p) :=
    Nat.eq_two_pow_or_exists_odd_prime_and_dvd n
  ---- Case 1: `n` is a power of two.
  · replace hn : 2 ≤ k := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hn
    replace hn : 4 ∣ 2 ^ k := Nat.pow_dvd_pow 2 hn
    exact good_of_good_polynomial_map (ZMod.castHom hn (ZMod 4))
      (ZMod.castHom_surjective _) P (ZMod4_good _)
  ---- Case 2: `n` is divisible by an odd prime.
  · haveI : Fact (Nat.Prime p) := ⟨hp⟩
    replace hp0 : p ≠ 2 := λ h ↦ Nat.not_even_iff_odd.mpr hp0 (h ▸ even_two)
    exact good_of_good_polynomial_map (ZMod.castHom hpn (ZMod p))
      (ZMod.castHom_surjective _) P (ZMod_good_of_prime_ne_two p hp0 _)

/-- If `n > 0`, then every polynomial over `ZMod n` is good iff `n > 2`. -/
theorem ZMod_forall_polynomial_good_iff_two_lt (hn : n > 0) :
    (∀ P : (ZMod n)[X], good P.eval) ↔ 2 < n := by
  refine ⟨λ hn0 ↦ Nat.lt_of_not_le λ hn1 ↦ ?_, ZMod_good_of_two_lt⟩
  rw [Nat.le_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one] at hn1
  rcases (hn1 : (n = 0 ∨ n = 1) ∨ n = 2) with (rfl | rfl) | rfl
  exacts [hn.ne rfl, ZMod1_not_good X.eval (hn0 _),
    const_one_ZMod2_not_good (by simpa only [eval_one] using hn0 1)]





/-! ### The `ℤ` version -/

/-- A function `f : ℤ → ℤ` is called `n`-good if there exists `a, b, c ∈ ℤ` with `a ≠ 0`
  such that `n ∤ (ak^2 + bk + c)(P(k) + (ak^2 + bk + c))` for all integer `k`. -/
def natGood (n : ℕ) (f : ℤ → ℤ) :=
  ∃ a ≠ 0, ∃ b c, ∀ k, ¬(n : ℤ) ∣ (a * k ^ 2 + b * k + c) * (f k + (a * k ^ 2 + b * k + c))

/-- The version of `natGood` over `ZMod n`, also with `f(k) - (ak^2 + bk + c)`
  instead of `f(k) + (ak^2 + bk + c)`. -/
theorem natGood_iff :
    natGood n f ↔ ∃ a ≠ 0, ∃ b c,
      ∀ k, ¬(n : ℤ) ∣ (a * k ^ 2 + b * k + c) * (f k - (a * k ^ 2 + b * k + c)) := by
  refine ⟨?_, ?_⟩
  ---- The `→` direction.
  · rintro ⟨a, ha, b, c, h⟩
    refine ⟨-a, Int.neg_ne_zero.mpr ha, -b, -c, λ k ↦ ?_⟩
    rw [neg_mul, neg_mul, ← neg_add, ← neg_add, neg_mul, dvd_neg, sub_neg_eq_add]
    exact h k
  ---- The `←` direction; basically the same proof.
  · rintro ⟨a, ha, b, c, h⟩
    refine ⟨-a, Int.neg_ne_zero.mpr ha, -b, -c, λ k ↦ ?_⟩
    rw [neg_mul, neg_mul, ← neg_add, ← neg_add, neg_mul, dvd_neg, ← sub_eq_add_neg]
    exact h k

/-- If `n > 0`, the condition `a ≠ 0` on `natGood f n` is superficial. -/
theorem natGood_iff_of_pos (hn : n > 0) :
    natGood n f ↔ ∃ a b c, ∀ k,
      ¬(n : ℤ) ∣ (a * k ^ 2 + b * k + c) * (f k - (a * k ^ 2 + b * k + c)) := by
  ---- Only the `←` direction is non-trivial.
  refine natGood_iff.trans ⟨λ h ↦ h.elim λ a ha ↦ ⟨a, ha.2⟩, ?_⟩
  rintro ⟨a, ha⟩
  ---- If `a ≠ 0`, we are done.
  obtain ha0 | rfl : a ≠ 0 ∨ a = 0 := ne_or_eq a 0
  · exact ⟨a, ha0, ha⟩
  ---- If `a = 0`, then replace it with `a = n`.
  rcases ha with ⟨b, c, h⟩
  simp only [zero_mul, zero_add] at h
  refine ⟨n, Int.natCast_ne_zero.mpr hn.ne.symm, b, c, λ k ↦ ?_⟩
  rw [Int.add_assoc, Int.add_mul, Int.mul_assoc, Int.dvd_self_mul_add, ← Int.sub_sub,
    Int.sub_eq_add_neg (a := f k), add_sub_right_comm, Int.mul_add, ← Int.mul_neg,
    Int.mul_left_comm, Int.add_comm, Int.dvd_self_mul_add]
  exact h k

/-- An integer polynomial `P` is `n`-good if and only if `φ(P)` is `good`,
  where `φ` is the canonical map from `ℤ` to `ℤ/nℤ`. -/
theorem natGood_polynomial_iff_good (hn : n > 0) (P : ℤ[X]) :
    natGood n P.eval ↔ good (P.map (Int.castRingHom (ZMod n))).eval := by
  set φ : ℤ →+* ZMod n := Int.castRingHom (ZMod n)
  have hφ : (φ : ℤ → ZMod n).Surjective := ZMod.ringHom_surjective φ
  rw [natGood_iff_of_pos hn, good, hφ.exists₃]
  refine exists_congr λ a ↦ exists_congr λ b ↦ exists_congr λ c ↦ ?_
  rw [hφ.forall]; refine forall_congr' λ k ↦ ?_
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_mul,
    Int.cast_sub, eq_intCast φ k, eval_intCast_map, Int.cast_eq]
  simp_rw [Int.cast_add, Int.cast_mul, Int.cast_pow, eq_intCast]

/-- Final solution -/
theorem final_solution (hn : n > 0) : (∀ P : ℤ[X], natGood n P.eval) ↔ n > 2 := by
  simp_rw [← ZMod_forall_polynomial_good_iff_two_lt hn, natGood_polynomial_iff_good hn]
  exact Iff.symm (map_surjective _ (ZMod.ringHom_surjective _)).forall
