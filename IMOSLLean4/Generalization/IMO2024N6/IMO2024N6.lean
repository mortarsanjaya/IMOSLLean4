/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2024.N6
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.Algebra.CharP.CharAndCard

/-!
# IMO 2024 N6 (Generalization)

Given a ring $R$, we say that a function $f : R → R$ is *good* if
  there exists $a, b, c ∈ R$ such that for any $r ∈ R$,
$$ (ar^2 + br + c)(f(r) - (ar^2 + br + c)) ≠ 0. $$
We say that $R$ is *nice* if every polynomial over $R$ is good.
Given a finite commutative ring $R$, determine whether $R$ is nice or not.

### Answer

We say that a ring $R$ is *boolean* if $r^2 = r$ for all $r ∈ R$.
Then a finite commutative ring is nice if and only if it is not boolean.
-/

namespace IMOSL
namespace IMO2024N6

open Finset Polynomial

/-!
### Every finite field of characteristic 2 other than `𝔽₂` is good

Throughout this section, `F` is a finite field of characteristic `2`.
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

variable [CharP F 2]

/-- The set of `x : F` such that `x^2 + x = t^2 + t` is `{t, t + 1}`. -/
theorem filter_sq_add_self_eq (t : F) :
    ({x | x ^ 2 + x = t ^ 2 + t} : Finset F) = {t, t + 1} := by
  refine ext λ x ↦ ?_
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
    _ = ∏ x, ((x ^ 2) ^ 2 + x ^ 2 + x₀ ^ 2) :=
      Fintype.prod_congr _ _ λ _ ↦ by
        rw [CharTwo.sub_eq_add, CharTwo.add_sq, CharTwo.add_sq]
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





/-! ### More properties of boolean rings -/

namespace IsBoolean

/-- The product of boolean rings is boolean. -/
theorem Pi {R : ι → Type*} [∀ i, Ring (R i)] (hf : ∀ i, IsBoolean (R i)) :
    IsBoolean ((i : ι) → R i) :=
  λ x ↦ funext λ i ↦ hf i (x i)

/-- A ring that injects into a boolean ring is boolean. -/
theorem of_injection [Ring R] [Ring S] (hS : IsBoolean S)
    (φ : R →+* S) (hφ : Function.Injective φ) : IsBoolean R :=
  λ x ↦ hφ ((φ.map_pow x 2).trans (hS _))

/-- The boolean property is preserved under ring isomorphism. -/
theorem of_RingEquiv [Ring R] [Ring S] (hR : IsBoolean R) (φ : R ≃+* S) : IsBoolean S :=
  hR.of_injection φ.symm.toRingHom φ.symm.injective

/-- A ring of cardinality `2` is boolean. -/
theorem of_card_eq_two [Ring R] [Fintype R] (hR : Fintype.card R = 2) : IsBoolean R :=
  ZMod2.of_RingEquiv (ZMod.ringEquivOfPrime R Nat.prime_two hR)

/-- A reduced finite (commutative) ring whose maximal ideals have index `2` is boolean. -/
theorem of_reduced_maximal_quotient_card [CommRing R] [Fintype R] [IsReduced R]
    (hR : ∀ m : MaximalSpectrum R, Fintype.card (R ⧸ m.asIdeal) = 2) : IsBoolean R :=
  of_RingEquiv (Pi λ m ↦ of_card_eq_two (hR m)) (IsArtinianRing.equivPi R).symm

end IsBoolean





/-! ### More theory of Artinian rings -/

/-- The intersection of finitely many pairwise coprime ideals is equal to their product. -/
theorem Ideal_inf_eq_prod_of_pairwise_isCoprime [CommSemiring R] [DecidableEq ι]
    (S : Finset ι) (f : ι → Ideal R) (hf : Pairwise (Function.onFun IsCoprime f)) :
    S.inf f = ∏ i ∈ S, f i := by
  ---- Immediate by induction on `S`.
  induction S using Finset.induction with
  | empty => exact Ideal.one_eq_top.symm
  | insert i S hiS S_ih =>
      have h : IsCoprime (f i) (⨅ a ∈ S, f a) :=
        Ideal.isCoprime_biInf λ j hj ↦ hf (ne_of_mem_of_not_mem hj hiS).symm
      replace h : f i ⊓ ⨅ a ∈ S, f a = f i * ⨅ a ∈ S, f a := Ideal.inf_eq_mul_of_isCoprime h
      rw [inf_insert, prod_insert hiS, ← S_ih, Finset.inf_eq_iInf, h]

/-- The maximal ideals of a ring are pairwise coprime. -/
theorem Pairwise_isCoprime_maximalSpectrum [CommSemiring R] :
    Pairwise (Function.onFun IsCoprime (MaximalSpectrum.asIdeal (R := R))) :=
  λ _ _ h ↦ Ideal.isCoprime_of_isMaximal (mt MaximalSpectrum.ext_iff.mpr h)


section

open Classical

variable [CommRing R] [IsArtinianRing R]

/-- A local instance stating that `MaxSpec` of an artinian ring is a `Fintype`.
  We need this to express the Jacobson radical as a product. -/
noncomputable local instance : Fintype (MaximalSpectrum R) :=
  Fintype.ofFinite (MaximalSpectrum R)

/-- If `R` is artinian, its Jacobson radical is the product of all maximal ideals. -/
theorem jacobson_eq_prod_MaximalSpectrum :
    Ring.jacobson R = ∏ m : MaximalSpectrum R, m.asIdeal :=
  calc Ring.jacobson R
  _ = sInf {m : Ideal R | m.IsMaximal} := Ring.jacobson_eq_sInf_isMaximal R
  _ = ⨅ m : {m : Ideal R | m.IsMaximal}, ↑m := sInf_eq_iInf' _
  _ = iInf MaximalSpectrum.asIdeal :=
    (MaximalSpectrum.equivSubtype R).symm.iInf_congr λ _ ↦ rfl
  _ = univ.inf MaximalSpectrum.asIdeal := (inf_univ_eq_iInf _).symm
  _ = ∏ m : MaximalSpectrum R, m.asIdeal :=
    Ideal_inf_eq_prod_of_pairwise_isCoprime _ _ Pairwise_isCoprime_maximalSpectrum

/-- An artinian ring `R` such that `m^2 = m` for every maximal ideal `m` is reduced. -/
theorem reduced_of_forall_maximal_sq_eq_self
    (hR : ∀ m : MaximalSpectrum R, m.asIdeal ^ 2 = m.asIdeal) : IsReduced R := by
  ---- In this case the Jacobson radical `J` satisfies `J^2 = J`.
  replace hR : Ring.jacobson R ^ 2 = Ring.jacobson R := by
    simp_rw [jacobson_eq_prod_MaximalSpectrum, ← prod_pow, hR]
  ---- Letting `I` be the nilradical, in this case we have `J = I`, so `I^2 = I`.
  have h : Ring.jacobson R = nilradical R := by
    rw [← Ideal.jacobson_bot, IsArtinianRing.jacobson_eq_radical]; rfl
  replace hR : nilradical R ^ 2 = nilradical R := by rw [← h, hR]
  ---- By induction, we have `I^{n + 1} = I` for all `n`.
  replace hR (n : ℕ) : nilradical R ^ (n + 1) = nilradical R := by
    induction n with
    | zero => exact pow_one _
    | succ n n_ih => rw [pow_succ, n_ih, ← sq, hR]
  ---- But `I` is nilpotent, so the above equality implies `I = 0` and we are done.
  obtain ⟨n, hn⟩ : IsNilpotent (nilradical R) := IsArtinianRing.isNilpotent_nilradical
  replace hR : nilradical R = 0 := by rw [← hR n, pow_succ, hn, zero_mul]
  exact nilradical_eq_bot_iff.mp hR

end





/-! ### All non-boolean rings are nice -/

/-- If `m` is a maximal ideal, `a ∉ m^2`, and `b ∉ m`, then `ab ∉ m^2`. -/
theorem mul_notMem_sq_of_left [CommSemiring R] {m : Ideal R} (hm : m.IsMaximal)
    {a b : R} (ha : a ∉ m ^ 2) (hb : b ∉ m) : a * b ∉ m ^ 2 := by
  intro hab
  have ha0 : a * b ∈ m := m.pow_le_self (Nat.succ_ne_zero 1) hab
  replace ha0 : a ∈ m := by_contra λ h ↦ hm.isPrime.mul_notMem h hb ha0
  obtain ⟨c, d, hd, h⟩ : ∃ c, ∃ d ∈ m, c * b + d = 1 := hm.exists_inv hb
  have h0 : c * (a * b) + a * d ∈ m ^ 2 :=
    add_mem (Ideal.mul_mem_left _ _ hab) (sq m ▸ Ideal.mul_mem_mul ha0 hd)
  rw [mul_left_comm, ← mul_add, h, mul_one] at h0
  exact ha h0

/-- If `m` is a ideal such that `R/m` has characteristic `2`,
  then for any `a, b : R` with `a - b ∈ m`, we have `a^2 - b^2 ∈ m^2`. -/
theorem sq_sub_sq_mem_sq [CommRing R] (m : Ideal R) [CharP (R ⧸ m) 2]
    {a b : R} (hab : a - b ∈ m) : a ^ 2 - b ^ 2 ∈ m ^ 2 := by
  have hm : 2 ∈ m := Ideal.Quotient.eq_zero_iff_mem.mp (CharP.ofNat_eq_zero _ 2)
  have hab0 : a + b ∈ m := by
    rw [← sub_add_add_cancel a b b, ← two_mul, m.add_mem_iff_right hab]
    exact m.mul_mem_right _ hm
  rw [sq_sub_sq, sq]
  exact Ideal.mul_mem_mul hab0 hab

/-- If `m^2 < m` and `#(R/m) = 2` for some maximal ideal `m < R`, then `R` is nice. -/
theorem nice_of_maximal_sq_lt_card_quotient [CommRing R] [Fintype R] [DecidableEq R]
    {m : Ideal R} (hm : m.IsMaximal) (hm0 : m ^ 2 < m) (hm1 : Fintype.card (R ⧸ m) = 2) :
    nice R := by
  haveI : CharP (R ⧸ m) 2 := charP_of_card_eq_prime hm1
  ---- For convenience, let `φ : R → R/m` denote the projection map.
  let φ : R →+* R ⧸ m := Ideal.Quotient.mk m
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  ---- Also, we note that `R/m = {0, 1}`, so for all `r`, one of `r` or `r - 1` is in `m`.
  have hm2 (x : R ⧸ m) : x = 0 ∨ x = 1 :=
    eq_zero_or_one_of_sq_eq_self (IsBoolean.of_card_eq_two hm1 x)
  have hm3 (r : R) : r ∈ m ∨ r - 1 ∈ m :=
    (hm2 (φ r)).imp Ideal.Quotient.eq_zero_iff_mem.mp
      (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mp
  ---- Now start; fix a polynomial `P : R[X]`.
  intro P
  ---- Find `a, c : R` with `c, a + c ∉ m^2` and `φ(P(0) - c) = φ(P(1) - (a + c)) = 1`.
  obtain ⟨a, c, hm4, hm5⟩ : ∃ a c, (c ∉ m ^ 2 ∧ a + c ∉ m ^ 2) ∧
      ((P.map φ).eval 0 - φ c = 1 ∧ (P.map φ).eval 1 - φ (a + c) = 1) := by
    -- Take an arbitrary `π ∈ m \ m^2` and prove some miscellaneous lemmas.
    obtain ⟨π, hπm, hπm0⟩ : ∃ π ∈ m, π ∉ m ^ 2 := Set.exists_of_ssubset hm0
    have hπm1 : φ π = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hπm
    have hm4 : 1 ∉ m := λ h ↦ hm.ne_top (m.eq_top_iff_one.mpr h)
    have hm5 {r} (hr : r ∉ m) : r ∉ m ^ 2 := λ h ↦ hr (hm0.le h)
    -- Now we divide into four cases based on `φ(P(0))` and `φ(P(1))`.
    obtain hP0 | hP0 : (P.map φ).eval 0 = 0 ∨ (P.map φ).eval 0 = 1 := hm2 _
    all_goals obtain hP1 | hP1 : (P.map φ).eval 1 = 0 ∨ (P.map φ).eval 1 = 1 := hm2 _
    -- Case 1: `φ(P(0)) = 0` and `φ(P(1)) = 0`; then choose `a = 0` and `c = 1`.
    · refine ⟨0, 1, ?_⟩
      rw [zero_add, and_self, hP0, hP1, and_self, zero_sub, φ.map_one]
      exact ⟨hm5 hm4, CharTwo.neg_eq _⟩
    -- Case 2: `φ(P(0)) = 0` and `φ(P(1)) = 1`; then choose `a = 1` and `c = π - 1`.
    · refine ⟨1, π - 1, ?_⟩
      rw [add_sub_cancel, hP0, hP1, φ.map_sub, hπm1, φ.map_one]
      exact ⟨⟨hm5 λ h ↦ hm4 ((m.sub_mem_iff_right hπm).mp h), hπm0⟩,
        ⟨sub_sub_cancel _ _, sub_zero _⟩⟩
    -- Case 3: `φ(P(0)) = 1` and `φ(P(1)) = 0`; then choose `a = 1` and `c = π`.
    · refine ⟨1, π, ⟨hπm0, hm5 λ h ↦ hm4 ((m.add_mem_iff_left hπm).mp h)⟩, ?_⟩
      rw [hP0, hP1, φ.map_add, hπm1, φ.map_one, sub_add_cancel_right]
      exact ⟨sub_zero _, CharTwo.neg_eq _⟩
    -- Case 4: `φ(P(0)) = 1` and `φ(P(1)) = 1`; then choose `a = 0` and `c = π`.
    · refine ⟨0, π, ?_⟩
      rw [zero_add, and_self, hP0, hP1, and_self, hπm1]
      exact ⟨hπm0, sub_zero _⟩
  ---- From `a, a + c ∉ m^2` we get `ar^2 + c ∉ m^2` for any `r : R`.
  replace hm4 (r : R) : a * r ^ 2 + c ∉ m ^ 2 := by
    intro hr
    obtain hr0 | hr0 : r ∈ m ∨ r - 1 ∈ m := hm3 r
    -- If `r ∈ m` then `ar^2 + c ≡ c ≢ 0 (mod m^2)`.
    · replace hr0 : r ^ 2 ∈ m ^ 2 := Ideal.pow_mem_pow hr0 2
      exact hm4.1 ((Ideal.add_mem_iff_right _ (Ideal.mul_mem_left _ a hr0)).mp hr)
    -- If `r - 1 ∈ m` then `ar^2 + c ≡ a + c ≢ 0 (mod m^2)`.
    · replace hr0 : r ^ 2 - 1 ^ 2 ∈ m ^ 2 := sq_sub_sq_mem_sq _ hr0
      replace hr0 : a * r ^ 2 + c - a * (r ^ 2 - 1 ^ 2) ∈ m ^ 2 :=
        Ideal.sub_mem _ hr (Ideal.mul_mem_left _ a hr0)
      rw [one_pow, mul_sub_one, add_sub_sub_cancel, add_comm] at hr0
      exact hm4.2 hr0
  ---- From `φ(P(0) - c) = φ(P(1) - (a + c)) = 1` we get `P(r) - (ar^2 + c) ∉ m` for any `r`.
  replace hm5 (r : R) : P.eval r - (a * r ^ 2 + c) ∉ m := by
    intro hr
    replace hr : (P.map φ).eval (φ r) - (φ a * φ r ^ 2 + φ c) = 0 := by
      rw [eval_map_apply, ← φ.map_pow, ← φ.map_mul, ← φ.map_add, ← φ.map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hr
    obtain hr0 | hr0 : r ∈ m ∨ r - 1 ∈ m := hm3 r
    -- If `r ∈ m` then `P(r) - (ar^2 + c) ≡ P(0) - c ≢ 0 (mod m)`.
    · replace hr0 : φ r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hr0
      rw [hr0, sq, zero_mul, mul_zero, zero_add, hm5.1] at hr
      exact one_ne_zero hr
    -- If `r ∈ m` then `P(r) - (ar^2 + c) ≡ P(1) - (a + c) ≢ 0 (mod m)`.
    · replace hr0 : φ r = 1 := (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr hr0
      rw [hr0, one_pow, mul_one, ← φ.map_add, hm5.2] at hr
      exact one_ne_zero hr
  ---- Thus picking the same `a` and `c` with `b = 0` works.
  refine ⟨a, 0, c, λ r hr ↦ ?_⟩
  replace hr : (a * r ^ 2 + c) * (P.eval r - (a * r ^ 2 + c)) = 0 := by
    rwa [zero_mul, add_zero] at hr
  replace h : (a * r ^ 2 + c) * (P.eval r - (a * r ^ 2 + c)) ∉ m ^ 2 :=
    mul_notMem_sq_of_left hm (hm4 r) (hm5 r)
  exact h (hr ▸ Ideal.zero_mem _)

open Classical in
/-- A finite commutative ring that is not nice is boolean. -/
theorem IsBoolean.of_not_nice [CommRing R] [Fintype R] [DecidableEq R] (hR : ¬nice R) :
    IsBoolean R := by
  ---- For any maximal ideal `m`, since `R/m` is a field and not nice, `#(R/m) = 2`.
  have hR0 (m : MaximalSpectrum R) : Fintype.card (R ⧸ m.asIdeal) = 2 := by
    have h : nice (R ⧸ m.asIdeal) ↔ Fintype.card (R ⧸ m.asIdeal) ≠ 2 :=
      @FiniteField.nice_iff_card_ne_two _ (Ideal.Quotient.field m.asIdeal) _ _
    have h0 : ¬nice (R ⧸ m.asIdeal) :=
      λ hm ↦ hR (hm.of_surjection _ Ideal.Quotient.mk_surjective)
    exact (iff_not_comm.mp h).mpr h0
  ---- By `nice_of_maximal_sq_lt_card_quotient`, we have `m^2 = m` for all `m`.
  replace hR (m : MaximalSpectrum R) : m.asIdeal ^ 2 = m.asIdeal :=
    (Ideal.pow_le_self (Nat.succ_ne_zero 1)).lt_or_eq.resolve_left
      λ hm ↦ hR (nice_of_maximal_sq_lt_card_quotient m.isMaximal hm (hR0 m))
  ---- Since `R` is artinian (finite), we get that `R` is reduced.
  haveI : IsReduced R := reduced_of_forall_maximal_sq_eq_self hR
  ---- We are now done by `IsBoolean.of_reduced_maximal_quotient_card`.
  exact of_reduced_maximal_quotient_card hR0





/-! ### Summary -/

section

variable [CommRing R] [Fintype R] [DecidableEq R]

/-- A finite commutative ring is nice iff it is not boolean. -/
theorem nice_iff_not_IsBoolean : nice R ↔ ¬IsBoolean R :=
  ⟨λ hR hR0 ↦ hR0.not_nice hR, λ hR ↦ by_contra λ hR0 ↦ hR (IsBoolean.of_not_nice hR0)⟩

/-- Final solution to the generalized version -/
theorem Generalization.final_solution : nice R ↔ ¬∀ r : R, r ^ 2 = r :=
  nice_iff_not_IsBoolean

end
