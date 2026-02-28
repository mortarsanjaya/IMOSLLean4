/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Fintype.Units
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Nat.PrimeFin

/-!
# IMO 2011 N3

Let $n$ be an odd positive integer.
Find all functions $f : ℤ → ℤ$ such that $f(x) - f(y) ∣ x^n - y^n$ for all $x, y ∈ ℤ$.

### Answer

$f(x) = αx^d + c$ for some $α ∈ ℤˣ$, $c ∈ ℤ$, and a positive factor $d$ of $n$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2011SL.pdf).
-/

namespace IMOSL
namespace IMO2011N3

/-- Given a ring `R`, a function `f : R → R` is called `n`-*good*
  if `f(x) - f(y) ∣ x^n - y^n` for all `x, y : ℤ`. -/
def good (n : ℕ) [Ring R] (f : R → R) := ∀ x y, f x - f y ∣ x ^ n - y ^ n


namespace good

section

variable [CommRing R]

/-- If `d ∣ n`, then the function `x ↦ x^d` is `n`-good. -/
theorem of_dvd {d n : ℕ} (hdn : d ∣ n) : good n (λ x : R ↦ x ^ d) := by
  intro x y; calc x ^ d - y ^ d
    _ ∣ (x ^ d) ^ (n / d) - (y ^ d) ^ (n / d) := sub_dvd_pow_sub_pow _ _ _
    _ = x ^ n - y ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_div_cancel' hdn]

/-- If `f : R → R` is `n`-good, then `f + c` is `n`-good for any `c : R`. -/
theorem add_right {f : R → R} (hf : good n f) (c) : good n (f · + c) := by
  intro x y; calc f x + c - (f y + c)
    _ = f x - f y := add_sub_add_right_eq_sub _ _ c
    _ ∣ x ^ n - y ^ n := hf _ _

/-- If `f : R → R` is `n`-good, then `εf` is `n`-good for any unit `ε : Rˣ`. -/
theorem mul_unit_left {f : R → R} (hf : good n f) (ε : Rˣ) : good n (ε * f ·) := by
  intro x y; calc ε * f x - ε * f y
    _ = ε * (f x - f y) := (mul_sub _ _ _).symm
    _ ∣ f x - f y := ⟨(ε⁻¹ : Rˣ), by rw [mul_right_comm, Units.mul_inv, one_mul]⟩
    _ ∣ x ^ n - y ^ n := hf _ _

/-- If `f : R → R` is `n`-good and `f(0) = 0`, then for any prime element `p`,
  there exists `d ≤ n` such that `f(p)` and `p^d` are associated. -/
theorem map_prime_of_map_zero [NoZeroDivisors R] (hn : n ≠ 0)
    {f : R → R} (hf : good n f) (hf0 : f 0 = 0) {p : R} (hp : Prime p) :
    ∃ d ≤ n, Associated (f p) (p ^ d) := by
  specialize hf p 0
  rwa [hf0, sub_zero, zero_pow hn, sub_zero, dvd_prime_pow hp] at hf

end


section

variable (hn : n ≠ 0) {f : ℤ → ℤ} (hf : good n f) (hf0 : f 0 = 0)
include hn hf hf0

/-- If `f : ℤ → ℤ` is `n`-good with `f(0) = 0`, then there exists an integer `d ≤ n`
  and a unit `ε : ℤˣ` such that `f(p) = εp^d` for infinitely many `p : ℕ`. -/
theorem Int_exists_infinite_nat_map_eq_unit_mul_pow :
    ∃ d ≤ n, ∃ ε : ℤˣ, ∀ N : ℕ, ∃ p : ℕ, f p = ε * p ^ d ∧ p > N := by
  /- The proof uses pigeonhole, so first construct a function `T : Fin (n + 1) × ℤˣ`
    such that `f(p) = T(p).2 p^{T(p).1}` for all primes `p`. -/
  obtain ⟨T, hT⟩ : ∃ T : Nat.Primes → Fin (n + 1) × ℤˣ,
      ∀ p : Nat.Primes, f p = (T p).2 * p ^ (T p).1.1 := by
    suffices ∀ p : Nat.Primes, ∃ t : Fin (n + 1) × ℤˣ, f p = t.2 * p ^ t.1.1
      from Classical.axiomOfChoice this
    intro p
    obtain ⟨d, hd, ε, hε⟩ : ∃ d ≤ n, Associated (f p) (p ^ d) :=
      hf.map_prime_of_map_zero hn hf0 (Nat.prime_iff_prime_int.mp p.2)
    refine ⟨⟨⟨d, Nat.lt_add_one_of_le hd⟩, ε⁻¹⟩, ?_⟩
    rw [← hε, Int.mul_left_comm, Units.inv_mul, Int.mul_one]
  ---- Then `T^{-1}(d, ε)` is infinite for some `d : Fin (n + 1)` and `ε : ℤˣ`.
  obtain ⟨⟨d, ε⟩, h⟩ : ∃ β, Infinite {p | T p = β} := Finite.exists_infinite_fiber T
  replace h : Infinite {p : ℕ | f p = ε * p ^ d.1} := by
    refine h.of_injective (f := λ p ↦ ⟨p.1.1, (hT p).trans (by rw [p.2])⟩) (λ p q hpq ↦ ?_)
    rwa [Subtype.mk.injEq, Nat.Primes.coe_nat_inj, SetCoe.ext_iff] at hpq
  replace h : {p : ℕ | f p = ε * p ^ d.1}.Infinite := Set.infinite_coe_iff.mp h
  ---- Now this choice of `d` and `ε` works, and we are done.
  exact ⟨d, Nat.le_of_lt_add_one d.2, ε, λ N ↦ h.exists_gt N⟩

/-- If `f : ℤ → ℤ` is `n`-good with `f(0) = 0`, then there exists an integer `d ∣ n`
  and a unit `ε : ℤˣ` such that `(ε f(x))^{n / d} = x^n` for all `x : ℤ`. -/
theorem Int_exists_exponent_dvd_and_unit_f_formula :
    ∃ d, d ∣ n ∧ ∃ ε : ℤˣ, ∀ x : ℤ, (ε * f x) ^ (n / d) = x ^ n := by
  ---- Pick `d ≤ n` and a unit `ε` such that `f(p) = εp^d` for infinitely many `p : ℕ`.
  obtain ⟨d, hd, ε, hS⟩ :
      ∃ d ≤ n, ∃ ε : ℤˣ, ∀ N : ℕ, ∃ p : ℕ, p ∈ {p : ℕ | f p = ε * p ^ d} ∧ p > N :=
    hf.Int_exists_infinite_nat_map_eq_unit_mul_pow hn hf0
  ---- For convenience, set `S = {p : ℕ | f(p) = εp^d}`.
  set S : Set ℕ := {p | f p = ε * p ^ d}
  ---- We claim that the same `d` and `ε⁻¹` in place of `ε` works.
  suffices d ∣ n ∧ ∀ x, (ε.inv * f x) ^ (n / d) = x ^ n from ⟨d, this.1, ε⁻¹, this.2⟩
  ---- First we must have `d > 0`.
  have hd0 : d > 0 := by
    refine Nat.pos_of_ne_zero λ hd0 ↦ ?_
    obtain ⟨p, hp, -⟩ : ∃ p : ℕ, f p = ε * p ^ d ∧ p > 0 := hS 0
    obtain ⟨q, hq, hpq⟩ : ∃ q : ℕ, f q = ε * q ^ d ∧ q > p := hS p
    have h0 : f p - f q ∣ p ^ n - q ^ n := hf p q
    rw [hp, hq, hd0, Int.pow_zero, Int.pow_zero, Int.sub_self, Int.zero_dvd, Int.sub_eq_zero,
      ← Int.natCast_pow, ← Int.natCast_pow, Int.natCast_inj, Nat.pow_left_inj hn] at h0
    exact hpq.ne h0
  ---- For any `x : ℤ` and `p ∈ S` large, we have `p^{n % d} (ε⁻¹ f(x))^{n / d} = x^n`.
  have hS0 (x : ℤ) :
      ∃ N, ∀ p ∈ S, p > N → p ^ (n % d) * (ε.inv * f x) ^ (n / d) = x ^ n := by
    /- By working out the near future, we pick `N = |f(x)|^{n / d} + |x|^n + |f(x)|`,
      which works since `p^{n % d} (ε⁻¹ f(x))^{n / d} ≡ x^n (mod εp^d - f(x))`. -/
    refine ⟨(f x).natAbs ^ (n / d) + x.natAbs ^ n + (f x).natAbs,
      λ p hpS hpN ↦ Int.eq_of_sub_eq_zero <|
        Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (d := ε * p ^ d - f x) ?_ ?_⟩
    -- Check that `p^{n % d} (ε⁻¹ f(x))^{n / d} ≡ x^n (mod εp^d - f(x))`.
    · refine (Int.ModEq.symm ?_).dvd
      calc p ^ (n % d) * (ε.inv * f x) ^ (n / d)
        _ ≡ p ^ (n % d) * (p ^ d) ^ (n / d) [ZMOD ε * p ^ d - f x] := by
          refine ((Int.modEq_iff_dvd.mpr ⟨ε.inv, ?_⟩).pow _).mul_left _
          rw [Int.sub_mul, Int.mul_right_comm, Units.val_inv, Int.one_mul, Int.mul_comm]
        _ = p ^ n := by rw [← Int.pow_mul, ← Int.pow_add, Nat.mod_add_div]
        _ ≡ x ^ n [ZMOD ε * p ^ d - f x] := by
          rw [Int.modEq_iff_dvd, ← hpS, dvd_sub_comm]
          exact hf p x
    -- Check that `|p^{n % d} (ε⁻¹ f(x))^{n / d} - x^n| < |εp^d - f(x)|`.
    · have hp : p > 0 := Nat.zero_lt_of_lt hpN
      have hpnd : p ^ (n % d) > 0 := Nat.pow_pos hp
      refine Nat.lt_of_add_lt_add_right (n := (f x).natAbs) ?_
      calc (p ^ (n % d) * (ε.inv * f x) ^ (n / d) - x ^ n).natAbs + (f x).natAbs
        _ ≤ (p ^ (n % d) * (((ε⁻¹ : ℤˣ) : ℤ) * f x) ^ (n / d)).natAbs
            + (x ^ n).natAbs + (f x).natAbs :=
          Nat.add_le_add_right (Int.natAbs_sub_le _ _) _
        _ = p ^ (n % d) * (f x).natAbs ^ (n / d) + x.natAbs ^ n + (f x).natAbs := by
          simp only [Int.natAbs_mul, Int.natAbs_pow]
          rw [Int.natAbs_natCast, Int.natAbs_of_isUnit (ε⁻¹).isUnit, Nat.one_mul]
        _ ≤ p ^ (n % d) * ((f x).natAbs ^ (n / d) + x.natAbs ^ n + (f x).natAbs) := by
          have h (z : ℕ) : z ≤ p ^ (n % d) * z := Nat.le_mul_of_pos_left _ hpnd
          rw [Nat.mul_add, Nat.mul_add]
          exact Nat.add_le_add (Nat.add_le_add_left (h _) _) (h _)
        _ < p ^ (n % d) * p := Nat.mul_lt_mul_of_pos_left hpN hpnd
        _ = p ^ (n % d + 1) := (Nat.pow_succ _ _).symm
        _ ≤ p ^ d := Nat.pow_le_pow_right hp (Nat.mod_lt n hd0)
        _ = (ε * (p : ℤ) ^ d - f x + f x).natAbs := by
          rw [Int.sub_add_cancel, Int.natAbs_mul, Int.natAbs_pow,
            Int.natAbs_natCast, Int.natAbs_of_isUnit ε.isUnit, Nat.one_mul]
        _ ≤ (ε * (p : ℤ) ^ d - f x).natAbs + (f x).natAbs := Int.natAbs_add_le _ _
  ---- For `x ≠ 0`, the previous statement implies `d ∣ n` and `(ε⁻¹ f(x))^{n / d} = x^n`.
  replace hS0 (x) (hx : x ≠ 0) : d ∣ n ∧ (ε.inv * f x) ^ (n / d) = x ^ n := by
    specialize hS0 x; rcases hS0 with ⟨N, hN⟩
    obtain ⟨p, hpS, hpN⟩ : ∃ p ∈ S, p > N := hS N
    obtain ⟨q, hqS, hqp⟩ : ∃ q ∈ S, q > p := hS p
    replace hpS : p ^ (n % d) * (ε.inv * f x) ^ (n / d) = x ^ n := hN p hpS hpN
    replace hqS : q ^ (n % d) * (ε.inv * f x) ^ (n / d) = x ^ n := hN q hqS (hpN.trans hqp)
    have h : (ε.inv * f x) ^ (n / d) ≠ 0 := by
      refine Int.pow_ne_zero (Int.mul_ne_zero (ε⁻¹).ne_zero λ hx0 ↦ hx ?_)
      have h : f x - f 0 ∣ x ^ n - 0 ^ n := hf x 0
      rw [hx0, hf0, Int.sub_zero, Int.zero_dvd, Int.zero_pow hn, Int.sub_zero] at h
      exact eq_zero_of_pow_eq_zero h
    replace h : p ^ (n % d) = q ^ (n % d) := by
      rw [← Int.natCast_inj, Int.natCast_pow, Int.natCast_pow,
        ← Int.mul_eq_mul_right_iff h, hpS, hqS]
    replace h : n % d = 0 := not_not.mp λ h0 ↦ hqp.ne ((Nat.pow_left_inj h0).mp h)
    refine ⟨Nat.dvd_of_mod_eq_zero h, ?_⟩
    rw [← hpS, h, Int.pow_zero, Int.one_mul]
  ---- Now we finish accordingly.
  refine ⟨(hS0 1 Int.one_ne_zero).1, λ x ↦ ?_⟩
  obtain rfl | hx : x = 0 ∨ x ≠ 0 := eq_or_ne _ _
  · rw [hf0, Int.mul_zero, Int.zero_pow hn]
    exact Int.zero_pow (Nat.div_ne_zero_iff.mpr ⟨hd0.ne.symm, hd⟩)
  · exact (hS0 x hx).2

end


/-- If `f : ℤ → ℤ` is `n`-good with `n` odd and `f(0) = 0`, then there exists an
  integer `d ∣ n` and a unit `ε : ℤˣ` such that `f(x) = εx^d` for all `x : ℤ`. -/
theorem Int_eq_unit_mul_pow
    (hn : Odd n) {f : ℤ → ℤ} (hf : good n f) (hf0 : f 0 = 0) :
    ∃ d, d ∣ n ∧ ∃ ε : ℤˣ, ∀ x, f x = ε * x ^ d := by
  have hn0 : n ≠ 0 := hn.pos.ne.symm
  ---- Pick `d ∣ n` and `ε : ℤˣ` such that `(ε f(x))^{n / d} = x^n` for all `x : ℤ`.
  obtain ⟨d, hd, ε, h⟩ : ∃ d, d ∣ n ∧ ∃ ε : ℤˣ, ∀ x : ℤ, (ε * f x) ^ (n / d) = x ^ n :=
    hf.Int_exists_exponent_dvd_and_unit_f_formula hn0 hf0
  ---- The same `d` and `ε⁻¹` in place of `ε` works since `n` is odd.
  refine ⟨d, hd, ε⁻¹, λ x ↦ ?_⟩
  replace h : (ε * f x) ^ (n / d) = (x ^ d) ^ (n / d) := by
    rw [h, ← Int.pow_mul, Nat.mul_div_cancel' hd]
  have h0 : Odd (n / d) := by
    rcases hd with ⟨m, rfl⟩
    have hd0 : d > 0 := Nat.pos_of_ne_zero (Nat.ne_zero_of_mul_ne_zero_left hn0)
    exact Nat.mul_div_cancel_left _ hd0 ▸ Nat.Odd.of_mul_right hn
  rwa [Units.eq_inv_mul_iff_mul_eq, ← h0.pow_inj]

end good


/-- Final solution -/
theorem final_solution {n : ℕ} (hn : Odd n) {f : ℤ → ℤ} :
    good n f ↔ ∃ c : ℤ, ∃ d, d ∣ n ∧ ∃ ε : ℤˣ, f = λ x ↦ ε * x ^ d + c := by
  refine ⟨λ hf ↦ ?_, ?_⟩
  ---- The `→` direction.
  · obtain ⟨d, hd, ε, hf0⟩ :
        ∃ d, d ∣ n ∧ ∃ ε : ℤˣ, ∀ x,f x + -f 0 = ε.val * x ^ d :=
      (hf.add_right _).Int_eq_unit_mul_pow hn (add_neg_cancel _)
    exact ⟨f 0, d, hd, ε, funext λ x ↦ eq_add_of_add_neg_eq (hf0 x)⟩
  ---- The `←` direction.
  · rintro ⟨c, d, hd, ε, rfl⟩
    exact ((good.of_dvd hd).mul_unit_left ε).add_right c
