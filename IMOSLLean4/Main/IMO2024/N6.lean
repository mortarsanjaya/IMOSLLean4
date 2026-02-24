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

Given a ring $R$, we say that a function $f : R → R$ is *good* if
  there exists $a, b, c ∈ R$ such that for any $r ∈ R$,
$$ (ar^2 + br + c)(f(r) - (ar^2 + br + c)) ≠ 0. $$
We say that $R$ is *nice* if every *polynomial* over $R$ is good.
The original problem is equivalent to finding all $n > 0$ for which $ℤ/nℤ$ is nice.

The official solution shows that $ℤ/nℤ$ is if and only if $n > 2$.
The method also shows that every finite field of characteristic not equal to $2$ is nice.
In the case $n = 4$, we show more: we claim that any function $f : ℤ/4ℤ → ℤ/4ℤ$ is good.
We show that there exists $a, c ∈ ℤ/4ℤ$ such that $Q(r)(f(r) - Q(r)) ≠ 0$
  for all $r ∈ ℤ/4ℤ$, where $Q(r) = a(1 - r^2) + cr^2$.
* If $\{f(0), f(2)\} ≠ \{1, 3\}$, pick any $a \in \{1, 3\} \setminus \{f(0), f(2)\}$.
* If $\{f(0), f(2)\} = \{1, 3\}$, pick $a = 2$.

We do similar procedure to pick $c$ but with $\{f(1), f(3)\}$ replacing $\{f(0), f(2)\}$.
Since $Q(0) = Q(2) = a$ and $Q(1) = Q(3) = c$, it can be checked that the choices work.

### Notes

It seems that the only part of the condition $0 ∉ f(F)$ that is needed is that $f(0) ≠ 0$,
The condition that $f$ attains all non-zero values is only
  used to pick $y ≠ 0$ such that $f(y) = (1 - r') f(0)$.

### Generalization

It turns out that a finite field is nice if and only if it has cardinality not equal to $2$.

See `IMOSLLean4/Generalization/IMO2024N6/IMO2024N6.lean` for the implementation.
-/

namespace IMOSL
namespace IMO2024N6

open Polynomial

/-! ### Definitions -/

/-- A function `f : R → R` is called `good` if there exists `a, b, c ∈ R`
  such that `(ar^2 + br + c)(f(r) - (ar^2 + br + c)) ≠ 0` for any `r ∈ R`. -/
def good [Ring R] (f : R → R) :=
  ∃ a b c : R, ∀ r : R, (a * r ^ 2 + b * r + c) * (f r - (a * r ^ 2 + b * r + c)) ≠ 0

/-- A ring `R` is called `nice` if every polynomial over `R` is good. -/
def nice (R) [Ring R] := ∀ P : R[X], good P.eval





/-!
### Boolean rings are not nice

This implies that `ZMod 1` and `ZMod 2` are not nice.
-/

/-- A ring `R` is called *boolean* if `r^2 = r` for all `r ∈ R`. See also `BooleanRing`. -/
def IsBoolean (R) [Ring R] := ∀ r : R, r ^ 2 = r

/-- Any trivial ring is boolean. -/
theorem IsBoolean_of_Subsingleton (R) [Ring R] [Subsingleton R] : IsBoolean R :=
  λ _ ↦ Subsingleton.allEq _ _

/-- The ring `ZMod 2` is boolean. -/
theorem IsBoolean_ZMod2 : IsBoolean (ZMod 2) :=
  λ r ↦ match r with | 0 => rfl | 1 => rfl


namespace IsBoolean

variable [Ring R] (hR : IsBoolean R)
include hR

/-- The constant function `1` over a boolean ring is not good. -/
theorem const_one_not_good : ¬good (λ _ : R ↦ 1) := by
  rintro ⟨_, _, c, h⟩
  refine h 0 ?_
  rw [sq, ← mul_assoc, ← add_mul, mul_zero, zero_add, mul_one_sub, ← sq, hR, sub_self]

/-- A boolean ring is not nice. -/
theorem not_nice : ¬nice R :=
  λ h ↦ hR.const_one_not_good (by simpa only [eval_one] using h 1)

end IsBoolean


/-- The ring `ZMod 1` is not nice. -/
theorem not_nice_ZMod1 : ¬nice (ZMod 1) :=
  (IsBoolean_of_Subsingleton _).not_nice

/-- The ring `ZMod 2` is not nice. -/
theorem not_nice_ZMod2 : ¬nice (ZMod 2) :=
  IsBoolean_ZMod2.not_nice





/-! ### The ring `ZMod 4` is nice -/

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

/-- `ZMod 4` is nice. -/
theorem ZMod4_nice : nice (ZMod 4) :=
  λ P ↦ ZMod4_good P.eval





/-!
### A ring that surjects into a nice ring is a nice ring

In particular, if `ZMod k` is nice and `k ∣ n`, then `ZMod n` is nice.
-/

section

variable [Ring R] [Ring S] (φ : R →+* S) (hφ : (⇑φ).Surjective)
include hφ

/-- A surjective ring homomorphism pulls good polynomials back to good polynomials. -/
theorem good.of_Polynomial_map (P : R[X]) (hP : good (P.map φ).eval) : good P.eval := by
  rcases hP with ⟨a', b', c', h⟩
  obtain ⟨a, rfl⟩ : ∃ a, φ a = a' := hφ a'
  obtain ⟨b, rfl⟩ : ∃ b, φ b = b' := hφ b'
  obtain ⟨c, rfl⟩ : ∃ c, φ c = c' := hφ c'
  replace h (r : R) :
      φ ((a * r ^ 2 + b * r + c) * (P.eval r - (a * r ^ 2 + b * r + c))) ≠ 0 :=
    calc φ ((a * r ^ 2 + b * r + c) * (P.eval r - (a * r ^ 2 + b * r + c)))
    _ = φ (a * r ^ 2 + b * r + c) * ((P.map φ).eval (φ r) - φ (a * r ^ 2 + b * r + c)) := by
      rw [φ.map_mul, φ.map_sub, eval_map_apply]
    _ = (φ a * φ r ^ 2 + φ b * φ r + φ c)
        * ((P.map φ).eval (φ r) - (φ a * φ r ^ 2 + φ b * φ r + φ c)) := by
      rw [φ.map_add, φ.map_add, φ.map_mul, φ.map_mul, φ.map_pow]
    _ ≠ 0 := h (φ r)
  exact ⟨a, b, c, λ r hr ↦ h r ((congrArg φ hr).trans φ.map_zero)⟩

/-- If `R` surjects into a nice ring, then `R` is nice. -/
theorem nice.of_surjection (hS : nice S) : nice R :=
  λ P ↦ (hS (P.map φ)).of_Polynomial_map φ hφ P

end


/-- If `ZMod k` is nice and `k ∣ n`, then `ZMod n` is nice. -/
theorem ZMod_nice_of_dvd (hk : nice (ZMod k)) (hkn : k ∣ n) : nice (ZMod n) :=
  hk.of_surjection (ZMod.castHom hkn (ZMod k)) (ZMod.castHom_surjective hkn)





/-! ### Good functions and linear transformations -/

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





/-!
### Reduction over finite fields

Let `F` be a finite field and `a, b ∈ F` be fixed elements.
The main statement is that to prove every function `f : F → F` is good,
  it suffices to check those with `f(F) = Fˣ` and `f(a) = f(b)`.
-/

/-- Let `R` be a domain. Suppose that every function `f : R → R` with `0 ∉ f(R)` is good.
  Then every function `f : R → R` is good. -/
theorem good_of_forall_map_ne_zero [Ring R] [IsDomain R] [DecidableEq R]
    (hR : ∀ f : R → R, (∀ r, f r ≠ 0) → good f) (f : R → R) : good f := by
  /- Define `g : R → R` by `g(r) = 1` for `f(r) = 0` and `g(r) = f(r)` otherwise.
    Then `g` takes only non-zero values, and so it is good. -/
  obtain ⟨a, b, c, hg⟩ : good (λ r ↦ if f r = 0 then 1 else f r) := by
    refine hR _ λ r ↦ ?_
    split_ifs with hr
    exacts [one_ne_zero, hr]
  /- Pick `a, b, c : R` such that `(ar^2 + br + c)(g(r) - (ar^2 + br + c)) ≠ 0` for all `r`.
    Then we claim that `(ar^2 + br + c)(f(r) - (ar^2 + br + c)) ≠ 0` for all `r`. -/
  refine ⟨a, b, c, λ r ↦ ?_⟩
  ---- Fix `r`, and let `s = ar^2 + br + c` for convenience.
  set s : R := a * r ^ 2 + b * r + c
  replace hg : s * ((if f r = 0 then 1 else f r) - s) ≠ 0 := hg r
  split_ifs at hg with hr
  ---- If `f(r) = 0`, then we had `s(1 - s) ≠ 0` while our goal is `s^2 ≠ 0`.
  · rw [hr, zero_sub, mul_neg, neg_ne_zero, mul_self_ne_zero]
    exact left_ne_zero_of_mul hg
  ---- If `f(r) ≠ 0`, then `s(f(r) - s) = s(g(r) - s) ≠ 0`.
  · exact hg

/-- Let `F` be a division ring. For any `a, b, c, d ∈ F` such that `a ≠ b` and `c ≠ d`,
  there exists `u ∈ Fˣ` and `v ∈ F` such that `uc + v = a` and `ud + v = b`. -/
theorem linear_transform_solver [DivisionRing F] {a b c d : F} (h : a ≠ b) (h0 : c ≠ d) :
    ∃ u : Fˣ, ∃ v : F, u * c + v = a ∧ u * d + v = b := by
  ---- Solving directly yields `u = (b - a)/(d - c)` and `v = a - uc`.
  replace h : b - a ≠ 0 := sub_ne_zero_of_ne h.symm
  replace h0 : d - c ≠ 0 := sub_ne_zero_of_ne h0.symm
  obtain ⟨u, hu⟩ : ∃ u : Fˣ, ↑u = (b - a) / (d - c) :=
    ⟨Units.mk0 ((b - a) / (d - c)) (div_ne_zero h h0), rfl⟩
  refine ⟨u, a - u * c, add_sub_cancel _ _, ?_⟩
  rw [add_sub_left_comm, ← mul_sub, hu, div_mul_cancel₀ _ h0, add_sub_cancel]

/-- Let `F` be a finite field, and fix two distinct elements `a, b ∈ F`.
  Suppose that every function `f : F → F` with `f(a) = f(b)` and `0 ∉ f(F)` is good.
  Then every function `f : F → F` is good. -/
theorem FiniteField.good_of_forall_map_pair_eq_map_ne_zero
    [Field F] [Fintype F] [DecidableEq F] {a b : F} (hab : a ≠ b)
    (hF : ∀ f : F → F, f a = f b → (∀ r, f r ≠ 0) → good f) :
    ∀ f : F → F, good f := by
  ---- Reduce to the case where `f` does not attain `0`.
  refine good_of_forall_map_ne_zero λ f hf ↦ ?_
  /- Then `f` is not surjective, and so it is not injective either.
    Let `c, d ∈ F` be two distinct elements such that `f(c) = f(d)`. -/
  obtain ⟨c, d, h1, h2⟩ : ∃ c d, f c = f d ∧ c ≠ d := by
    have h1 : ¬f.Surjective := λ h1 ↦ (h1 0).elim hf
    replace h1 : ¬f.Injective := Finite.surjective_of_injective.mt h1
    simpa only [Function.Injective, not_forall, exists_prop] using h1
  ---- Now find `u ∈ Rˣ` and `v ∈ R` such that `uc + v = a` and `ud + v = b`.
  obtain ⟨u, v, rfl, rfl⟩ : ∃ u : Fˣ, ∃ v : F, u * c + v = a ∧ u * d + v = b :=
    linear_transform_solver hab h2
  ---- Then `x ↦ f(u⁻¹(x - v))` being good implies that `f` is good.
  refine (good_shift_scale_iff (u := u⁻¹) (v := u⁻¹ * -v)).mp (hF _ ?_ (λ _ ↦ hf _))
  rwa [← mul_add, add_neg_cancel_right, Units.inv_mul_cancel_left,
    ← mul_add, add_neg_cancel_right, Units.inv_mul_cancel_left]

/-- If `R` is a domain and `f : R → R` does not attain some non-zero value, `f` is good. -/
theorem good_of_map_ne_of_ne_zero [Ring R] [NoZeroDivisors R]
    {u : R} (hu : u ≠ 0) {f : R → R} (hf : ∀ r, f r ≠ u) : good f := by
  refine ⟨0, 0, u, λ r ↦ ?_⟩
  rw [← mul_add, zero_mul, zero_add, mul_ne_zero_iff, sub_ne_zero]
  exact ⟨hu, hf r⟩

/-- Let `F` be a finite field, and fix two distinct elements `a, b ∈ F`.
  Suppose that every function `f : F → F` with `f(a) = f(b)` and `f(F) = Fˣ` is good.
  Then every function `f : F → F` is good. -/
theorem FiniteField.good_of_forall_map_pair_eq_of_image_eq_units
    [Field F] [Fintype F] [DecidableEq F] {a b : F} (hab : a ≠ b)
    (hF : ∀ f : F → F, f a = f b → (∀ r, f r ≠ 0) → (∀ x ≠ 0, ∃ r, f r = x) → good f) :
    ∀ f : F → F, good f := by
  ---- Reduce to the case where `f` does not attain zero.
  refine good_of_forall_map_pair_eq_map_ne_zero hab λ f hf hf0 ↦ ?_
  specialize hF f hf hf0
  ---- If `f` attains all non-zero values, we are done.
  by_cases h : ∀ x ≠ 0, ∃ r, f r = x
  · exact hF h
  ---- If `f` does not attain some non-zero value, we are also done.
  simp_rw [not_forall, exists_prop, not_exists] at h
  rcases h with ⟨u, hu, hu0⟩
  exact good_of_map_ne_of_ne_zero hu hu0





/-! ### Finite fields of characteristic not equal to $2$ are nice -/

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
  ---- Three cases to consider: `z = a`, `z = c`, and `z ≠ a, c`.
  obtain rfl | hza : z = a ∨ z ≠ a := dec_em _
  · exact hab0.trans_ne (hy0 b hbc hab.symm)
  obtain rfl | hzc : z = c ∨ z ≠ c := dec_em _
  · exact hcd0.trans_ne (hy0 d hcd.symm had.symm)
  · exact hy0 z hzc hza


namespace FiniteField

variable [Field F] [Fintype F] [DecidableEq F]

/-- Let `F` be a finite field of characteristic not equal to `2`.
  Then every function from `F` to itself is good. -/
theorem good_of_char_ne_two (hF : ringChar F ≠ 2) : ∀ f : F → F, good f := by
  ---- Reduce to the case where `f(-1) = f(1)` and `f(F) = Fˣ`.
  refine good_of_forall_map_pair_eq_of_image_eq_units (a := -1) (b := 1)
    (Ring.neg_one_ne_one_of_char_ne_two hF) (λ f hf hf0 hf1 ↦ ?_)
  ---- We can weaken `0 ∉ f(F)` to `f(0) ≠ 0`.
  replace hf0 : f 0 ≠ 0 := hf0 0
  ---- Let `r` be a non-square in `F`.
  obtain ⟨r', hr⟩ : ∃ r' : F, ¬IsSquare r' := FiniteField.exists_nonsquare hF
  ---- Choose `y` such that `f(y) = (1 - r') f(0)`.
  replace hf1 : ∃ y, f y = (1 - r') * f 0 :=
    hf1 _ (mul_ne_zero (sub_ne_zero.mpr λ hr0 ↦ hr (hr0 ▸ IsSquare.one)) hf0)
  rcases hf1 with ⟨y, hy⟩
  ---- Note that `r' ≠ 0` and `y ≠ 0`.
  have hr' : r' ≠ 0 := λ hr' ↦ hr (hr' ▸ IsSquare.zero)
  have hy0 : y ≠ 0 := by
    rintro rfl; rw [eq_comm, mul_eq_right₀ hf0, sub_eq_self] at hy
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
    have X : (1 : F) ≠ 0 := one_ne_zero
    refine exists_ne_map_ne_of_four (a := -1) (b := 1) (c := 0) (d := y)
      (Ring.neg_one_ne_one_of_char_ne_two hF) (neg_ne_zero.mpr X) X hy0.symm ?_ ?_ _
    -- Verify that `φ(-1) = φ(1)`.
    · rw [hf, neg_sq]
    -- Verify that `φ(0) = φ(y)`.
    · rw [hy, div_eq_div_iff (hr _) (hr _), zero_pow Nat.two_pos.ne.symm, zero_sub,
        mul_right_comm, mul_neg, one_sub_mul, neg_sub, mul_div_cancel₀ _ hr', mul_comm]
  ---- Then take `(a, b, c) = (a, 0, -ar)` and see that it works.
  refine ⟨a, 0, a * (-r), λ x ↦ ?_⟩
  rw [zero_mul, add_zero, ← mul_add, ← sub_eq_add_neg, mul_ne_zero_iff, sub_ne_zero]
  exact ⟨mul_ne_zero ha (hr x), λ h0 ↦ ha0 x (div_eq_of_eq_mul (hr x) h0)⟩

/-- A finite field of characteristic `≠ 2` is nice. -/
theorem nice_of_char_ne_two (hF : ringChar F ≠ 2) : nice F :=
  λ P ↦ good_of_char_ne_two hF P.eval

end FiniteField


/-- If `p` is an odd prime, then `ZMod p` is nice. -/
theorem ZMod_nice_of_prime_ne_two (p) [Fact (Nat.Prime p)] (hp : p ≠ 2) : nice (ZMod p) :=
  FiniteField.nice_of_char_ne_two ((ZMod.ringChar_zmod_n p).trans_ne hp)





/-! ### Summary for the `ZMod` case -/

/-- For any `k`, `ZMod 2^k` is nice if and only if `k > 1`. -/
theorem ZMod_two_pow_nice_iff {k : ℕ} : nice (ZMod (2 ^ k)) ↔ 1 < k := by
  ---- If `k ≥ 2`, then `ZMod 2^k` surjects into `ZMod 4`, which is nice.
  refine Iff.symm ⟨λ hk ↦ ?_, λ hk ↦ Nat.lt_of_not_le λ hk0 ↦ ?_⟩
  · exact ZMod_nice_of_dvd ZMod4_nice (Nat.pow_dvd_pow 2 hk)
  ---- If `k < 2`, then `2^k` is either `1` or `2`, so `ZMod 2^k` is not nice.
  obtain rfl | rfl : k = 0 ∨ k = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hk0
  exacts [not_nice_ZMod1 hk, not_nice_ZMod2 hk]

/-- If `n > 0`, then `ZMod n` is nice if and only if `n > 2`. -/
theorem ZMod_nice_iff {n : ℕ} (hn : n > 0) : nice (ZMod n) ↔ n > 2 := by
  ---- The case where `n` is a power of `2` is covered by `ZMod_two_pow_nice_iff`.
  obtain ⟨k, rfl⟩ | ⟨p, hp, hpn, hp0⟩ :
      (∃ k, n = 2 ^ k) ∨ (∃ p, Nat.Prime p ∧ p ∣ n ∧ Odd p) :=
    Nat.eq_two_pow_or_exists_odd_prime_and_dvd n
  · rw [ZMod_two_pow_nice_iff, ← Nat.pow_lt_pow_iff_right Nat.one_lt_two]
  ---- Otherwise `n` has an odd prime factor and we are done using surjection.
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  replace hp0 : p ≠ 2 := λ h ↦ Nat.not_even_iff_odd.mpr hp0 (h ▸ even_two)
  have hp1 : p > 2 := hp.two_le.lt_of_ne' hp0
  replace hp0 : nice (ZMod p) := ZMod_nice_of_prime_ne_two p hp0
  exact iff_of_true (ZMod_nice_of_dvd hp0 hpn) (hp1.trans_le (Nat.le_of_dvd hn hpn))





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
  have h0 : ((n * k ^ 2 + b * k + c : ℤ) : ZMod n) = (b * k + c : ℤ) := by
    rw [Int.add_assoc, Int.cast_add, Int.cast_mul, Int.cast_natCast,
      CharP.cast_eq_zero, zero_mul, zero_add]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_mul, Int.cast_sub, h0,
    ← Int.cast_sub, ← Int.cast_mul,ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact h k

/-- An integer polynomial `P` is `n`-good if and only if `φ(P)` is `good`,
  where `φ` is the canonical map from `ℤ` to `ℤ/nℤ`. -/
theorem natGood_polynomial_iff_good (hn : n > 0) (P : ℤ[X]) :
    natGood n P.eval ↔ good (P.map (Int.castRingHom (ZMod n))).eval := by
  set φ : ℤ →+* ZMod n := Int.castRingHom (ZMod n)
  have hφ : (φ : ℤ → ZMod n).Surjective := ZMod.ringHom_surjective φ
  rw [natGood_iff_of_pos hn, good, hφ.exists₃]
  conv_rhs =>
    right; ext a; right; ext b; right; ext c
    rw [hφ.forall]; intro x
    rw [← φ.map_pow, ← φ.map_mul, ← φ.map_mul, ← φ.map_add, ← φ.map_add, eval_map_apply,
      ← φ.map_sub, ← φ.map_mul, eq_intCast, Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- Final solution -/
theorem final_solution (hn : n > 0) : (∀ P : ℤ[X], natGood n P.eval) ↔ n > 2 := by
  simp_rw [← ZMod_nice_iff hn, natGood_polynomial_iff_good hn]
  exact Iff.symm (map_surjective _ (ZMod.ringHom_surjective _)).forall
