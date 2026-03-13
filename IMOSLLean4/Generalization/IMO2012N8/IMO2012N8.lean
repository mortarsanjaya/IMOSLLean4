/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2012.N8
import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# IMO 2012 N8 (Generalization)

Find all finite fields $F$ with the following property:
  for any $r ∈ F$, there exists $a, b ∈ F$ such that $a^2 + b^5 = r$.

### Answer

Any field of cardinality $q ≠ 11$.

### Implementation details

The condition being asked on $F$ is implemented via the predicate `good`.
For the case $q = 11$ and $q = 31$, we show that `good` is preserved under field isomorphisms
  via `good.of_RingEquiv`, so we just have to check the fields `ZMod 11` and `ZMod 31`.
For `ZMod 11`, we show by computer search that $a^2 + b^5 ≠ 7$ for any $a, b ∈ F$.
For `ZMod 31`, we show that every element of $𝔽_{31}$, other than $22 = 4^2 - 5^5$ and
  $27 = 1^2 + 6^5$, takes the form $a^2$, $a^2 + 1$, or $a^2 - 6^5$ for some $a ∈ 𝔽_{31}$.
-/

namespace IMOSL
namespace IMO2012N8

open Finset

/--
A finite field `F` is called *good* if every element of `F`
  can be written as `a^2 + b^5` for some `a, b : F`.

This is an auxiliary definition, which is not given in the main file since
  they aren't as focused on representing elements of `F` specifically as `a^2 + b^5`.
-/
def good (R) [Add R] [Monoid R] := ∀ r : R, ∃ a b, a ^ 2 + b ^ 5 = r

/-- If two rings, `R` and `S`, are isomorphic and `R` is good, then `S` is good. -/
theorem good.of_RingEquiv [Semiring R] [Semiring S] (hR : good R) (φ : R ≃+* S) :
    good S := by
  ---- Pick any `s ∈ S` and write `s = φ(r)` for some `r ∈ R`.
  intro s; obtain ⟨r, rfl⟩ : ∃ r : R, φ r = s := φ.surjective s
  ---- Now `r = a^2 + b^5` for some `a, b ∈ R`.
  obtain ⟨a, b, rfl⟩ : ∃ a b : R, a ^ 2 + b ^ 5 = r := hR r
  ---- Then `s = φ(r) = φ(a)^2 + φ(b)^5`.
  refine ⟨φ a, φ b, ?_⟩
  rw [φ.map_add, φ.map_pow, φ.map_pow]



/-! ### Classifying good finite fields -/

variable {F} [Field F] [Fintype F] [DecidableEq F]
local notation "q" => Fintype.card F

/-- A finite field of cardinality `q > 40` is good. -/
theorem good_of_card_big_enough (hF : 40 < q) : good F := by
  obtain hF0 | hF0 : ringChar F ≠ 2 ∨ ringChar F = 2 := ne_or_eq _ _
  ---- We have done the `char(F) ≠ 2` case.
  · exact IMO2012N8.exists_eq_sq_add_pow_five hF0 hF
  ---- If `char(F) = 2`, then everything is already a square and we are done.
  · intro r
    obtain ⟨a, rfl⟩ : ∃ a, r = a ^ 2 := (FiniteField.isSquare_of_char_two hF0 r).exists_sq r
    refine ⟨a, 0, ?_⟩
    rw [zero_pow (Nat.succ_ne_zero 4), add_zero]

/-- If `n` is coprime with `q - 1`, then every element of `F` is an `n`th power. -/
theorem exists_eq_pow_n_of_gcd_eq_one (hn : n ≠ 0) (h : Nat.Coprime n (q - 1)) (x : F) :
    ∃ y : F, y ^ n = x := by
  ---- If `x = 0` then the statement is trivial.
  obtain rfl | hx : x = 0 ∨ IsUnit x := (eq_or_ne x 0).imp_right Ne.isUnit
  · exact ⟨0, zero_pow hn⟩
  ---- If `x` is a unit then `x^k` works where `k` is an integer with `nk ≡ 1 (mod q - 1)`.
  lift x to Fˣ using hx
  refine ⟨x ^ n.gcdA (q - 1), ?_⟩
  calc (x.1 ^ n.gcdA (q - 1)) ^ n
    _ = x.1 ^ (n * n.gcdA (q - 1)) := by rw [Int.mul_comm, zpow_mul, zpow_natCast]
    _ = (x ^ (n * n.gcdA (q - 1))).1 := by rw [Units.val_zpow_eq_zpow_val]
    _ = x.1 := congrArg Units.val ?_
  calc x ^ (n * n.gcdA (q - 1))
    _ = x ^ (n.gcd (q - 1) - (q - 1 : ℕ) * n.gcdB (q - 1) : ℤ) := by
      rw [Nat.gcd_eq_gcd_ab, Int.add_sub_cancel]
    _ = x * ((x ^ (q - 1)) ^ n.gcdB (q - 1))⁻¹ := by
      rw [zpow_sub, h, Int.natCast_one, zpow_one, zpow_mul, zpow_natCast]
    _ = x := by rw [← Fintype.card_units, pow_card_eq_one, one_zpow, inv_one, mul_one]

/-- A finite field of cardinality `q ≢ 1 (mod 2)` is good. -/
theorem good_of_card_mod_2_ne_one (hF : ¬2 ∣ q - 1) : good F := by
  intro r
  ---- Find `a ∈ F` such that `a^2 = r`.
  obtain ⟨a, rfl⟩ : ∃ a, a ^ 2 = r :=
    exists_eq_pow_n_of_gcd_eq_one (Nat.succ_ne_zero 1)
      (Nat.prime_two.coprime_iff_not_dvd.mpr hF) _
  ---- Then `b = 0` works, as `a^2 + 0^5 = r`.
  refine ⟨a, 0, ?_⟩
  rw [zero_pow (Nat.succ_ne_zero 4), add_zero]

/-- A finite field of cardinality `q ≢ 1 (mod 5)` is good. -/
theorem good_of_card_mod_5_ne_one (hF : ¬5 ∣ q - 1) : good F := by
  intro r
  ---- Find `b ∈ F` such that `b^5 = r`.
  obtain ⟨b, rfl⟩ : ∃ b, b ^ 5 = r :=
    exists_eq_pow_n_of_gcd_eq_one (Nat.succ_ne_zero 4)
      (Nat.prime_five.coprime_iff_not_dvd.mpr hF) _
  ---- Then `a = 0` works, as `0^2 + b^5 = r`.
  refine ⟨0, b, ?_⟩
  rw [zero_pow (Nat.succ_ne_zero 1), zero_add]

/-- A finite field of cardinality `q ≢ 1 (mod 10)` is good. -/
theorem good_of_card_mod_10_ne_one (hF : ¬10 ∣ q - 1) : good F := by
  obtain h | h : ¬2 ∣ q - 1 ∨ ¬5 ∣ q - 1 := by rwa [← not_and_or, ← Nat.lcm_dvd_iff]
  exacts [good_of_card_mod_2_ne_one h, good_of_card_mod_5_ne_one h]

/-- The field `ZMod 11` is not good. -/
theorem ZMod11_is_not_good : ¬good (ZMod 11) :=
  not_forall_of_exists_not ⟨7, by decide⟩

omit [DecidableEq F] in
/-- A field of cardinality `11` is not good. -/
theorem not_good_of_card_eq_11 (hF : q = 11) : ¬good F :=
  λ h ↦ ZMod11_is_not_good
    (h.of_RingEquiv (ZMod.ringEquivOfPrime F Nat.prime_eleven hF).symm)

/-- The field `ZMod 31` is good. -/
theorem ZMod31_is_good : good (ZMod 31) := by
  intro r
  /- All elements of `𝔽_{31}` are of the form
    `a^2`, `a^2 + 1`, or `a^2 + 5`, except `22` and `27`. -/
  obtain ⟨a, rfl | rfl | rfl⟩ | rfl | rfl :
    (∃ a, a ^ 2 = r ∨ a ^ 2 + 1 = r ∨ a ^ 2 + 5 = r) ∨ (r = 22 ∨ r = 27) := by
      decide +revert
  ---- Now just brute force all the cases.
  exacts [⟨a, 0, add_zero _⟩, ⟨a, 1, rfl⟩, ⟨a, -6, rfl⟩, ⟨4, -5, rfl⟩, ⟨1, 6, rfl⟩]

/-- The integer `31` is prime. -/
theorem prime_31 : Nat.Prime 31 := by decide

omit [DecidableEq F] in
/-- A field of cardinality `31` is good. -/
theorem good_of_card_eq_31 (hF : q = 31) : good F :=
  ZMod31_is_good.of_RingEquiv (ZMod.ringEquivOfPrime F prime_31 hF)

/-- The integer `21` is not a prime power. -/
theorem not_IsPrimePow_21 : ¬IsPrimePow 21 := by
  ---- Somehow direct decision procedute doesn't work anymore...
  intro h
  replace h0 : Nat.Coprime 3 7 := rfl
  replace h : 21 ∣ 3 ∨ 21 ∣ 7 := (h0.isPrimePow_dvd_mul h).mp (Nat.dvd_refl 21)
  revert h; decide

/-- Final solution to the generalized version -/
theorem Generalization.final_solution : good F ↔ ¬q = 11 := by
  ---- As fields of cardinality `11` are not good, we now assume `q ≠ 11`.
  refine ⟨λ hF hF0 ↦ not_good_of_card_eq_11 hF0 hF, λ hF ↦ ?_⟩
  ---- If `10 ∤ q - 1`, then we proved that `F` is good.
  obtain hF0 | ⟨k, h⟩ : ¬10 ∣ q - 1 ∨ 10 ∣ q - 1 := dec_em' _
  · exact good_of_card_mod_10_ne_one hF0
  ---- Now write `q = 10k + 1`.
  replace h : q = 10 * k + 1 := Nat.eq_add_of_sub_eq Fintype.card_pos h
  ----  If `k ≥ 4` then `q > 40` and so `F` is good.
  obtain h0 | h0 : 4 ≤ k ∨ k < 4 := le_or_gt _ _
  · apply good_of_card_big_enough
    calc 40 ≤ 10 * k := Nat.mul_le_mul_left 10 h0
         _  < 10 * k + 1 := Nat.lt_succ_self _
         _  = q := h.symm
  ---- If `k < 4`, then divide into four cases: `q = 1, 11, 21, 31`, respectively.
  lift k to Fin 4 using h0
  fin_cases k
  exacts [
    absurd h Fintype.one_lt_card.ne.symm,
    absurd h hF,
    absurd (FiniteField.isPrimePow_card F) (h ▸ not_IsPrimePow_21),
    good_of_card_eq_31 h]
