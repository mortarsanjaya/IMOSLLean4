/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2024.N6

/-!
# IMO 2024 N6 (Generalization)

Given a ring $R$, we say that a function $f : R → R$ is *good* if
  there exists $a, b, c ∈ R$ such that for any $r ∈ R$,
$$ (ar^2 + br + c)(f(r) - (ar^2 + br + c)) ≠ 0. $$
We say that $R$ is *nice* if every polynomial over $R$ is good.
Given a finite commutative ring $R$, determine whether $R$ is nice or not.

### Progress

A finite field is nice if and only if it has cardinality not equal to $2$.

### Notes

Throughout the documentation in this file,
  `F` denotes a finite field and `q` denotes its cardinality.
-/

namespace IMOSL
namespace IMO2024N6

open Polynomial

/-!
### Every finite field of characteristic 2 other than `𝔽₂` is good

Throughout this section, we assume `F` has characteristic `2`.
-/

/-- We have `a^2 + a = b^2 + b` iff `a = b` or `a = b + 1`. -/
theorem sq_add_self_eq_sq_add_self_iff [CommRing R] [IsDomain R] [CharP R 2] {a b : R} :
    a ^ 2 + a = b ^ 2 + b ↔ a = b ∨ a = b + 1 := by
  rw [← CharTwo.add_eq_zero, add_add_add_comm, ← CharTwo.add_sq, sq, ← mul_add_one,
    mul_eq_zero, CharTwo.add_eq_zero, add_assoc, CharTwo.add_eq_zero]


namespace FiniteField

variable {F} [Field F] [Fintype F] [DecidableEq F]
local notation "q" => Fintype.card F


namespace CharTwo

open Finset

variable [CharP F 2]

/-- The set of `x : F` such that `x^2 + x = t^2 + t` is `{t, t + 1}`. -/
theorem filter_sq_add_self_eq (t : F) :
    ({x | x ^ 2 + x = t ^ 2 + t} : Finset F) = {t, t + 1} := by
  refine Finset.ext λ x ↦ ?_
  rw [mem_filter_univ, sq_add_self_eq_sq_add_self_iff, mem_insert, mem_singleton]

/-- If `y = x^2 + x` for some `x : F`, then there are two choices of `x` that work. -/
theorem card_sq_add_self_eq {y : F} (hy : ∃ t, t ^ 2 + t = y) :
    #{x | x ^ 2 + x = y} = 2 := by
  rcases hy with ⟨t, rfl⟩
  rw [filter_sq_add_self_eq, card_pair (succ_ne_self t).symm]

/-- The set of elements of `F` of the form `x^2 + x` has cardinality `q/2`. -/
theorem two_mul_card_image_sq_add_self : 2 * #(univ.image λ x : F ↦ x ^ 2 + x) = q :=
  calc 2 * #(univ.image λ x : F ↦ x ^ 2 + x)
  _ = ∑ y ∈ univ.image λ x ↦ x ^ 2 + x, 2 := by
    rw [Nat.mul_comm, sum_const]; rfl
  _ = ∑ y ∈ univ.image λ x ↦ x ^ 2 + x, #{x | x ^ 2 + x = y} := by
    refine sum_congr rfl λ y hy ↦ (card_sq_add_self_eq ?_).symm
    rwa [mem_image_univ_iff_mem_range, Set.mem_range] at hy
  _ = q := (card_eq_sum_card_image _ _).symm

/-- The set of elements of `F` of the form `x^2 + x` has cardinality `q/2`. -/
theorem card_image_sq_add_self : #(univ.image λ x : F ↦ x ^ 2 + x) = q / 2 := by
  rw [← two_mul_card_image_sq_add_self, Nat.mul_div_cancel_left _ Nat.two_pos]

/-- If `q ≠ 2`, then there exists `x₀ ≠ 1` in `F` not of the form `x^2 + x`. -/
theorem exists_ne_one_ne_sq_add_self (hF : q ≠ 2) : ∃ x₀ ≠ 1, ∀ x : F, x ^ 2 + x ≠ x₀ := by
  ---- It suffices to show that `#({1} ∪ {x^2 + x : x ∈ F}) < q`.
  suffices #(insert 1 (univ.image λ x : F ↦ x ^ 2 + x)) < q by
    obtain ⟨x₀, -, hx₀⟩ : ∃ x₀ ∈ univ, x₀ ∉ insert 1 (univ.image λ x : F ↦ x ^ 2 + x) :=
      exists_mem_notMem_of_card_lt_card this
    rw [mem_insert, mem_image_univ_iff_mem_range, Set.mem_range, not_or, not_exists] at hx₀
    exact ⟨x₀, hx₀⟩
  ---- Note that `2 ∣ q` and `q/2 > 1`.
  have hF0 : ringChar F = 2 := ringChar.eq F 2
  replace hF0 : 2 ∣ q := Nat.dvd_of_mod_eq_zero (FiniteField.even_card_of_char_two hF0)
  replace hF : 1 < q / 2 :=
    (Nat.lt_div_iff_mul_lt' hF0 1).mpr (Nat.lt_of_le_of_ne Fintype.one_lt_card hF.symm)
  ---- Now we calculate.
  calc #(insert 1 (univ.image λ x : F ↦ x ^ 2 + x))
    _ ≤ #(univ.image λ x : F ↦ x ^ 2 + x) + 1 := card_insert_le _ _
    _ = q / 2 + 1 := by rw [card_image_sq_add_self]
    _ < q / 2 + q / 2 := Nat.add_lt_add_left hF _
    _ = q := by rw [← Nat.two_mul, Nat.mul_div_cancel' hF0]

omit [DecidableEq F] in
/-- If `x₀` is not of the form `x^2 + x`, then `∏_{x ∈ F} (x^2 + x - x₀) = 1`. -/
theorem prod_sq_add_self_sub_eq_one {x₀ : F} (hx₀ : ∀ x, x ^ 2 + x ≠ x₀) :
    ∏ x, (x ^ 2 + x - x₀) = 1 := by
  suffices (∏ x, (x ^ 2 + x - x₀)) ^ 2 = ∏ x, (x ^ 2 + x - x₀) by
    rw [sq, mul_left_eq_self₀] at this
    exact this.resolve_right (prod_ne_zero_iff.mpr λ x _ ↦ sub_ne_zero_of_ne (hx₀ x))
  calc (∏ x, (x ^ 2 + x - x₀)) ^ 2
    _ = ∏ x, (x ^ 2 + x - x₀) ^ 2 := (prod_pow _ _ _).symm
    _ = ∏ x, ((x ^ 2) ^ 2 + x ^ 2 + x₀ ^ 2) := by
      simp_rw [CharTwo.sub_eq_add, CharTwo.add_sq]
    _ = ∏ x, (x ^ 2 + x + x₀ ^ 2) :=
      (frobeniusEquiv F 2).prod_comp (λ x ↦ x ^ 2 + x + x₀ ^ 2)
    _ = ∏ x, ((x + x₀) ^ 2 + (x + x₀) + x₀ ^ 2) :=
      (Equiv.prod_comp (Equiv.addRight x₀) _).symm
    _ = ∏ x, (x ^ 2 + x - x₀) := by
      refine Fintype.prod_congr _ _ λ x ↦ ?_
      rw [CharTwo.add_sq, add_add_add_comm, add_assoc, CharTwo.sub_eq_add,
        add_right_inj, add_comm, CharTwo.add_cancel_left]

omit [CharP F 2] in
/-- Let `f : F → F` be a function such that `f(0) = f(1)` and `f(F) = Fˣ`.
  Then `∏_{x ≠ 0} f(x) = ∏_{x ≠ 0} x`. (This holds even if `char(F) ≠ 2`.) -/
theorem prod_univ_erase_zero_eq_one_of_image
    {f : F → F} (hf : f 0 = f 1) (hf0 : ∀ r, f r ≠ 0) (hf1 : ∀ x ≠ 0, ∃ r, f r = x) :
    ∏ x with x ≠ 0, f x = ∏ x with x ≠ 0, x := by
  ---- Define `g : F → F` by `g(x) = f(x)` if `x ≠ 0` and `g(0) = 0`.
  let g (x : F) : F := if x = 0 then 0 else f x
  ---- Then `g` is surjective.
  have hg : g.Surjective := by
    intro y
    obtain rfl | hy : y = 0 ∨ y ≠ 0 := eq_or_ne _ _
    · exact ⟨0, if_pos rfl⟩
    obtain ⟨x, rfl⟩ : ∃ x, f x = y := hf1 y hy
    obtain rfl | hx : x = 0 ∨ x ≠ 0 := eq_or_ne _ _
    exacts [⟨1, (if_neg one_ne_zero).trans hf.symm⟩, ⟨x, if_neg hx⟩]
  ---- But then `g` is bijective.
  replace hg : g.Bijective := hg.bijective_of_finite
  ---- Now do the calculations.
  calc ∏ x with x ≠ 0, f x
    _ = ∏ x with x ≠ 0, g x :=
      prod_congr rfl λ x hx ↦ (if_neg ((mem_filter_univ x).mp hx)).symm
    _ = ∏ x with x ≠ 0, x := by
      refine prod_bijective g hg (λ r ↦ ?_) (λ _ _ ↦ rfl)
      simp_rw [g, mem_filter_univ, Ne, ite_eq_left_iff, _root_.not_imp, iff_self_and]
      rintro -; exact hf0 r

/-- If `q ≠ 2`, then every function from `F` to itself is good. -/
theorem good_of_card_ne_two (hF : q ≠ 2) : ∀ f : F → F, good f := by
  ---- Reduce to the case where `f(0) = f(1)` and `f(F) = Fˣ`.
  refine good_of_forall_map_pair_eq_of_image_eq_units zero_ne_one λ f hf hf0 hf1 ↦ ?_
  ---- Pick some `x₀ ≠ 1` such that `x₀ ≠ x^2 + x` for all `x`.
  obtain ⟨x₀, hx₀1, hx₀⟩ : ∃ x₀ ≠ 1, ∀ x : F, x ^ 2 + x ≠ x₀ :=
    exists_ne_one_ne_sq_add_self hF
  ---- Define `g(x) = f(x)/(x^2 + x - x₀)` for every `x : F`.
  let g (x : F) : F := f x / (x ^ 2 + x - x₀)
  ---- Then it suffices to show that `g` does not attain some non-zero value.
  suffices ∃ a ≠ 0, ∀ x, g x ≠ a by
    rcases this with ⟨a, ha, ha0⟩
    refine ⟨a, a, a * -x₀, λ x ↦ ?_⟩
    have hx : x ^ 2 + x - x₀ ≠ 0 := sub_ne_zero_of_ne (hx₀ x)
    have hx0 : f x ≠ a * (x ^ 2 + x - x₀) := mt (div_eq_of_eq_mul hx) (ha0 x)
    rw [← mul_add, ← mul_add, ← sub_eq_add_neg, mul_ne_zero_iff]
    exact ⟨mul_ne_zero ha hx, sub_ne_zero_of_ne hx0⟩
  ---- Suppose for the sake of contradiction that every `a ≠ 0` takes that form.
  by_contra! hg1
  ---- Note that `g(0) = g(1)` and `g` cannot attain zero.
  have hg : g 0 = g 1 := by
    refine congrArg₂ _ hf ?_
    rw [sq, zero_mul, zero_add, one_pow, CharTwo.add_self_eq_zero]
  have hg0 (r : F) : g r ≠ 0 :=
    div_ne_zero (hf0 r) (sub_ne_zero_of_ne (hx₀ r))
  ---- Thus we have `∏_{x ≠ 0} g(x) = ∏_{x ≠ 0} f(x) = ∏_{x ≠ 0} x`.
  replace h : ∏ x with x ≠ 0, g x = ∏ x with x ≠ 0, f x :=
    (prod_univ_erase_zero_eq_one_of_image hg hg0 hg1).trans
      (prod_univ_erase_zero_eq_one_of_image hf hf0 hf1).symm
  ---- But then `∏_{x ≠ 0} (x^2 + x - x₀) = 1`.
  replace h : ∏ x with x ≠ 0, (x ^ 2 + x - x₀) = 1 := by
    rw [prod_div_distrib, div_eq_mul_inv, mul_right_eq_self₀, inv_eq_one] at h
    exact h.resolve_right (prod_ne_zero_iff.mpr λ r _ ↦ hf0 r)
  ---- Thus `1 = ∏_x (x^2 + x - x₀) = x₀`; contradiction.
  replace h : x₀ = 1 := calc
    _ = (∏ x ≠ 0, (x ^ 2 + x - x₀)) * (0 ^ 2 + 0 - x₀) := by
      rw [← filter_ne', h, one_mul, sq, zero_mul, zero_add, zero_sub, CharTwo.neg_eq]
    _ = ∏ x, (x ^ 2 + x - x₀) := prod_erase_mul _ _ (mem_univ _)
    _ = 1 := prod_sq_add_self_sub_eq_one hx₀
  exact hx₀1 h

/-- If `q ≠ 2`, then `F` is nice. -/
theorem nice_of_card_ne_two (hF : q ≠ 2) : nice F :=
  λ P ↦ good_of_card_ne_two hF P.eval

end CharTwo





/-! ### Every finite field other than `𝔽₂` is good -/

/-- A finite field of cardinality `> 2` is nice. -/
theorem nice_of_card_ne_two (hF : q ≠ 2) : nice F := by
  obtain hF0 | hF0 : ringChar F = 2 ∨ ringChar F ≠ 2 := eq_or_ne _ _
  ---- Case 1: `char(F) = 2`.
  · haveI : CharP F 2 := CharP.congr _ hF0
    exact CharTwo.nice_of_card_ne_two hF
  ---- Case 2: `char(F) ≠ 2`.
  · exact nice_of_char_ne_two hF0

omit [DecidableEq F] in
/-- Let `F` be a finite field of cardinality `2`. Then `F` is not nice. -/
theorem not_nice_of_card_eq_two (hF : q = 2) : ¬nice F :=
  let φ : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two hF
  λ hF0 ↦ not_nice_ZMod2 (hF0.of_surjection φ φ.surjective)

/-- A finite field if nice if and only if it has cardinality not equal to `2`. -/
theorem nice_iff_card_ne_two : nice F ↔ Fintype.card F ≠ 2 :=
  ⟨λ hF hF0 ↦ not_nice_of_card_eq_two hF0 hF, nice_of_card_ne_two⟩

end FiniteField


/-- Final solution -/
theorem Generalization.final_solution [Field F] [Fintype F] [DecidableEq F] :
    nice F ↔ Fintype.card F ≠ 2 :=
  FiniteField.nice_iff_card_ne_two
