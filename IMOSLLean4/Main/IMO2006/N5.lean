/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.BigOperators.ModEq

/-!
# IMO 2006 N5

Determine all pairs $(x, y)$ of integers such that
$$ \sum_{k = 0}^6 x^k = y^5 - 1. $$

### Answer

No such pairs.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2006SL.pdf).
We show more: for any prime $p > 3$, there exist no pairs $(x, y)$ of integers with
$$ \sum_{k = 0}^{p - 1} x^k = y^{p - 2} - 1. $$
We formalize this stronger version instead of the original version.
We modify the solution in the case $y ≡ 2 \pmod{p}$ a bit; instead of looking at
  $y^{p - 3} + y^{p - 4} + … + 1$ mod $p$, we look at $y^{p - 2} - 1$ mod $p$.
-/

namespace IMOSL
namespace IMO2006N5

open Finset

/-- Let `p` be a prime and `F` be a finite field. Suppose that there exists `x : F`
  with `x ≠ 1` such that `∑_{i = 0}^{p - 1} x^i = 0`. Then `|F| ≡ 1 (mod p)`. -/
theorem FiniteField_prime_geom_sum_eq_zero_imp [Field F] [Fintype F] [DecidableEq F]
    (hp : Nat.Prime p) {x : F} (hx : x ≠ 1) (hx0 : ∑ i ∈ range p, x ^ i = 0) :
    Fintype.card F ≡ 1 [MOD p] := by
  haveI : Fact p.Prime := ⟨hp⟩
  replace hx0 : x ^ p = 1 := by rw [← sub_eq_zero, ← geom_sum_mul, hx0, zero_mul]
  lift x to Fˣ using IsUnit.mk0 x ((pow_ne_zero_iff hp.ne_zero).mp (hx0.trans_ne one_ne_zero))
  replace hx1 : orderOf x = p :=
    orderOf_eq_prime (Units.val_inj.mp hx0) (mt Units.val_inj.mpr hx)
  replace hx1 : p ∣ Fintype.card Fˣ := hx1.symm.dvd.trans orderOf_dvd_card
  rwa [Fintype.card_eq_card_units_add_one, Nat.add_modEq_right_iff]

/-- Let `p` and `q` be prime with `p ∣ ∑_{i = 0}^{q - 1} x^i` for sone `x : ℤ`.
  Then `p` is either equal to `q` or congruent to `1 (mod q)`. -/
theorem Nat_prime_dvd_prime_geom_sum_imp
    (hp : Nat.Prime p) (hq : Nat.Prime q) {x : ℤ} (hx : (p : ℤ) ∣ ∑ i ∈ range q, x ^ i) :
    p = q ∨ p ≡ 1 [MOD q] := by
  haveI : Fact p.Prime := ⟨hp⟩
  ---- First, work over `𝔽_p`; we have `∑_{i = 0}^{q - 1} x^i = 0`.
  replace hx : ∑ i ∈ range q, (x : ZMod p) ^ i = 0 :=
    calc ∑ i ∈ range q, (x : ZMod p) ^ i
    _ = ∑ i ∈ range q, ((x ^ i : ℤ) : ZMod p) :=
      sum_congr rfl λ i _ ↦ (Int.cast_pow x i).symm
    _ = ∑ i ∈ range q, (x ^ i : ℤ) := (Int.cast_sum _ _).symm
    _ = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hx
  ---- Now split into two cases: `x = 1` or `x ≠ 1` (in `𝔽_p`).
  generalize (x : ZMod p) = x at hx
  obtain rfl | hx0 : x = 1 ∨ x ≠ 1 := eq_or_ne _ _
  ---- If `x = 1` then we get `q ≡ 0 (mod p)` and so `p = q`.
  · replace hx : (q : ZMod p) = 0 := calc
      _ = ∑ i ∈ range q, 1 := by rw [sum_const, card_range, nsmul_one]
      _ = ∑ i ∈ range q, (1 : ZMod p) ^ i := sum_congr rfl λ _ _ ↦ (one_pow _).symm
      _ = 0 := hx
    left; rwa [ZMod.natCast_eq_zero_iff, Nat.prime_dvd_prime_iff_eq hp hq] at hx
  ---- If `x ≠ 1` then as we proved before, `p ≡ 1 (mod q)`.
  · right; calc p
      _ = Fintype.card (ZMod p) := (ZMod.card p).symm
      _ ≡ 1 [MOD q] := FiniteField_prime_geom_sum_eq_zero_imp hq hx0 hx

/-- Let `d : ℕ` and `p` be prime with `d ∣ ∑_{i = 0}^{p - 1} x^i` for sone `x : ℤ`.
  Then either `p ∣ d` or `d ≡ 1 (mod p)`. -/
theorem Nat_dvd_prime_geom_sum_imp
    (hp : Nat.Prime p) {d : ℕ} {x : ℤ} (hx : (d : ℤ) ∣ ∑ i ∈ range p, x ^ i) :
    p ∣ d ∨ d ≡ 1 [MOD p] := by
  ---- We may assume `p ∤ d`.
  refine Decidable.or_iff_not_imp_left.mpr λ hd ↦ ?_
  ---- Then the prime factors of `d` are all `1 (mod q)`.
  have h (q : ℕ) (hq : q ∈ Nat.primeFactorsList d) : q ≡ 1 [MOD p] := by
    obtain ⟨hq0, hqd, -⟩ : Nat.Prime q ∧ q ∣ d ∧ d ≠ 0 := Nat.mem_primeFactorsList'.mp hq
    replace hx : (q : ℤ) ∣ ∑ i ∈ range p, x ^ i := (Int.ofNat_dvd.mpr hqd).trans hx
    exact (Nat_prime_dvd_prime_geom_sum_imp hq0 hp hx).resolve_left
      (λ h ↦ hd (h.symm.dvd.trans hqd))
  ---- This implies `d ≡ 1 (mod q)`.
  calc d
    _ = d.primeFactorsList.prod :=
      (Nat.prod_primeFactorsList λ h ↦ hd ⟨0, h.trans p.mul_zero.symm⟩).symm
    _ ≡ 1 [MOD p] := Nat.ModEq.listProd_one h

/-- Let `d ≥ 0` and `p` be prime with `d ∣ ∑_{i = 0}^{p - 1} x^i` for sone `x : ℤ`.
  Then either `p ∣ d` or `d ≡ 1 (mod p)`. -/
theorem Int_dvd_prime_geom_sum_imp
    (hp : Nat.Prime p) {d : ℤ} (hd : d ≥ 0) {x : ℤ} (hx : (d : ℤ) ∣ ∑ i ∈ range p, x ^ i) :
    (p : ℤ) ∣ d ∨ d ≡ 1 [ZMOD p] := by
  lift d to ℕ using hd
  exact (Nat_dvd_prime_geom_sum_imp hp hx).imp Int.ofNat_dvd.mpr Int.natCast_modEq_iff.mpr

/-- Let `d ≥ 0` and `p` be prime with `d ∣ ∑_{i = 0}^{p - 1} x^i` for sone `x : ℤ`.
  Then in `ZMod p`, `d` is either equal to `0` or `1`. -/
theorem Int_dvd_prime_geom_sum_imp_ZMod
    (hp : Nat.Prime p) {d : ℤ} (hd : d ≥ 0) {x : ℤ} (hx : (d : ℤ) ∣ ∑ i ∈ range p, x ^ i) :
    (d : ZMod p) = 0 ∨ (d : ZMod p) = 1 := by
  refine (Int_dvd_prime_geom_sum_imp hp hd hx).imp
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr λ h ↦ ?_
  rwa [← Int.cast_one, ZMod.intCast_eq_intCast_iff']

/-- Final solution -/
theorem final_solution (hp : Nat.Prime p) (hp0 : p > 3) (x y : ℤ) :
    ¬∑ i ∈ range p, x ^ i = y ^ (p - 2) - 1 := by
  ---- Suppose for the sake of contradiction that `∑_{i = 0}^{p - 1} x^i = y^{p - 2} - 1`.
  intro h
  ---- We gather some properties of `p`.
  have hp1 : p > 2 := Nat.lt_of_succ_lt hp0
  have hp2 : Odd p := hp.eq_two_or_odd'.resolve_left hp1.ne.symm
  have hp3 : Odd (p - 2) := by
    rw [← Nat.sub_add_cancel hp1.le, Nat.odd_add] at hp2
    exact hp2.mpr even_two
  ---- First note that `y > 0` since `p` (and `p - 2`) is odd.
  have hy : 0 < y ^ (p - 2) - 1 := hp2.geom_sum_pos.trans_eq h
  have h0 : y > 0 := hp3.pow_pos_iff.mp (Int.zero_lt_one.trans (Int.lt_of_sub_pos hy))
  ---- Next note that every non-negative divisor of `y^{p - 2} - 1` is `0, 1 (mod p)`.
  replace h {d} (hd : d ≥ 0) (hy : d ∣ y ^ (p - 2) - 1) :
      (d : ZMod p) = 0 ∨ (d : ZMod p) = 1 :=
    Int_dvd_prime_geom_sum_imp_ZMod hp hd (hy.trans h.symm.dvd)
  ---- In particular, we have `y - 1 ≡ 0, 1 (mod p)`.
  replace h0 : ((y - 1 : ℤ) : ZMod p) = 0 ∨ ((y - 1 : ℤ) : ZMod p) = 1 :=
    h (Int.sub_nonneg_of_le h0) (sub_one_dvd_pow_sub_one y _)
  ---- Before case division, we note `2 ≢ 0 (mod p)` and `2 ≢ -1 (mod p)`.
  have hp4 : (2 : ZMod p) ≠ 0 := by
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt Nat.two_pos hp1
  have hp5 : (2 : ZMod p) ≠ -1 := by
    rw [Ne, eq_neg_iff_add_eq_zero, two_add_one_eq_three,
      ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos 2) hp0
  rcases h0 with h0 | h0
  ---- If `y - 1 ≡ 0 (mod p)`, then `∑_{i = 0}^{p - 3} y^i ≡ -2 ≢ 0, 1 (mod p)`.
  · replace h0 : (y : ZMod p) = 1 := by rwa [Int.cast_sub, Int.cast_one, sub_eq_zero] at h0
    -- Let `T = ∑_{i = 0}^{p - 3} y^i` mod `p`, for convenience.
    let T : ZMod p := (∑ i ∈ range (p - 2), y ^ i : ℤ)
    -- First since `y ≡ 1 (mod p)`, we have `T = -2`.
    replace hT : T = -2 := calc
      _ = ∑ i ∈ range (p - 2), ((y ^ i : ℤ) : ZMod p) := Int.cast_sum _ _
      _ = ∑ i ∈ range (p - 2), 1 := sum_congr rfl λ _ _ ↦ by rw [Int.cast_pow, h0, one_pow]
      _ = (p - 2 : ℕ) := by rw [sum_const, card_range, nsmul_one]
      _ = -2 := by rw [Nat.cast_sub hp1.le, CharP.cast_eq_zero, zero_sub, Nat.cast_two]
    -- But `∑_{i = 0}^{p - 3} y^i ∣ y^{p - 2} - 1`, so `T ∈ {0, 1}`.
    replace h : T = 0 ∨ T = 1 := h hp3.geom_sum_pos.le ⟨y - 1, (geom_sum_mul y _).symm⟩
    -- Now we already have `T = -2`, so we are ready to obtain contradiction.
    clear_value T; subst hT
    rcases h with h | h
    exacts [hp4 (neg_eq_zero.mp h), hp5 (neg_eq_iff_eq_neg.mp h)]
  ---- If `y - 2 ≡ 0 (mod p)`, then `2(y^{p - 2} - 1) ≡ -1 ≢ 0, 2 (mod p)`.
  · haveI : Fact (Nat.Prime p) := ⟨hp⟩
    replace h0 : (y : ZMod p) = 2 := by
      rwa [Int.cast_sub, Int.cast_one, sub_eq_iff_eq_add, one_add_one_eq_two] at h0
    -- We have `2^{p - 2} - 1 ≡ y^{p - 2} - 1 ≡ 0, 1 (mod p)`.
    specialize h hy.le (Int.dvd_refl _)
    replace h : (2 ^ (p - 2) - 1 : ZMod p) = 0 ∨ (2 ^ (p - 2) - 1 : ZMod p) = 1 := by
      rwa [Int.cast_sub, Int.cast_one, Int.cast_pow, h0] at h
    replace h0 : (2 : ZMod p) * (2 ^ (p - 2) - 1) = -1 := calc
      _ = (2 : ZMod p) ^ (p - 2 + 1) - (1 + 1) := by rw [mul_sub, ← pow_succ', two_mul]
      _ = (2 : ZMod p) ^ (p - 1) - (1 + 1) :=
        congrArg (λ n ↦ (2 : ZMod p) ^ n - (1 + 1)) (Nat.sub_add_cancel hp.pred_pos)
      _ = -1 := by rw [ ZMod.pow_card_sub_one_eq_one hp4, sub_add_cancel_right]
    rcases h with h | h
    -- Case 1: `2^{p - 2} - 1 ≡ 0 (mod p)`; then `1 ≡ 2^{p - 1} ≡ 2 (mod p)`, contradiction.
    · replace h : (-1 : ZMod p) = 0 := by rw [← h0, h, mul_zero]
      exact one_ne_zero (neg_eq_zero.mp h)
    -- Case 2: `2^{p - 2} - 1 ≡ 1 (mod p)`; then `1 ≡ 2^{p - 1} ≡ 4 (mod p)`, contradiction.
    · replace h : (-1 : ZMod p) = 2 := by rw [← h0, h, mul_one]
      exact hp5 h.symm
