/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.FieldTheory.Finite.Basic

/-!
# IMO 2012 N6

Let $x$ and $y$ be positive integers.
Suppose that $2^n y + 1 ∣ x^{2^n} - 1$ for every $n > 0$.
Prove that $x = 1$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2012SL.pdf).
-/

namespace IMOSL
namespace IMO2012N6

/-- Let `p ≡ 3 (mod 4)` be a prime number and `x` be a non-negative integer.
  If `p ∣ x^{2^n} - 1` for some `n : ℕ`, then `p ∣ x^2 - 1`.
  (We do not require `x = 0` due to how subtraction works over `ℕ`.) -/
theorem prime_dvd_sq_sub_one_of_dvd_two_pow_sub_one
    {p x : ℕ} (hp : Nat.Prime p) (hp0 : p % 4 = 3) (hpx : p ∣ x ^ (2 ^ n) - 1) :
    p ∣ x ^ 2 - 1 := by
  ---- First we discharge the case `x = 0`.
  obtain rfl | hx : x = 0 ∨ x > 0 := Nat.eq_zero_or_pos x
  · rwa [Nat.zero_pow (Nat.two_pow_pos n)] at hpx
  ---- For `x > 0`, notice that the order of `x` mod `p` divides `2^n`.
  replace hpx : (x : ZMod p) ^ (2 ^ n) = 1 := by
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact ((Nat.modEq_iff_dvd' (Nat.pow_pos hx)).mpr hpx).symm
  ---- The order also divides `p - 1`, so this order divides `gcd(2^n, p - 1)`.
  have hx0 : (x : ZMod p) ^ (p - 1) = 1 := by
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    refine ZMod.pow_card_sub_one_eq_one λ h ↦ zero_ne_one' (ZMod p) ?_
    rwa [h, zero_pow (Nat.two_pow_pos n).ne.symm] at hpx
  replace hpx : orderOf (x : ZMod p) ∣ Nat.gcd (2 ^ n) (p - 1) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hpx) (orderOf_dvd_of_pow_eq_one hx0)
  ---- Since `p - 1 ≡ 2 (mod 4)`, we have `gcd(2^n, p - 1) = 2`.
  replace hx0 : Nat.gcd (2 ^ n) (p - 1) ∣ 2 := by
    obtain ⟨i, -, hi⟩ : ∃ i ≤ n, Nat.gcd (2 ^ n) (p - 1) = 2 ^ i :=
      (Nat.dvd_prime_pow Nat.prime_two).mp (Nat.gcd_dvd_left _ _)
    suffices i ≤ 1 from (dvd_of_eq hi).trans (Nat.pow_dvd_pow 2 this)
    refine Nat.le_of_not_gt λ hi0 ↦ ?_
    replace hi : 4 ∣ p - 1 := calc
      _ ∣ 2 ^ i := Nat.pow_dvd_pow 2 hi0
      _ = Nat.gcd (2 ^ n) (p - 1) := hi.symm
      _ ∣ p - 1 := Nat.gcd_dvd_right _ _
    replace hi : 3 = 1 := hp0.symm.trans ((Nat.modEq_iff_dvd' hp.one_le).mpr hi).symm
    revert hi; decide
  ---- Thus we get `x^2 ≡ 1 (mod p)`, and finally transfer back into `ℕ`.
  replace hpx : (x : ZMod p) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hpx.trans hx0)
  rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff] at hpx
  exact (Nat.modEq_iff_dvd' (Nat.pow_pos hx)).mp hpx.symm

/-- If `a, b ≠ 0`, `a ≡ b (mod c)` and `ν_p(b) < ν_p(c)`, then `ν_p(a) = ν_p(b)`. -/
theorem factorization_eq_of_modeq_of_lt (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a ≡ b [MOD c]) (h0 : Nat.factorization b p < Nat.factorization c p) :
    Nat.factorization a p = Nat.factorization b p := by
  ---- First note that one of the hypothesis already forces `p` to be prime.
  have hp : Nat.Prime p :=
    by_contra λ h1 ↦ Nat.ne_zero_of_lt h0 (Nat.factorization_eq_zero_of_not_prime c h1)
  refine eq_of_le_of_not_lt' ?_ (λ h1 ↦ ?_)
  ---- We have `ν_p(b) ≤ ν_p(a)` since `p^{ν_p(b)} ∣ a`.
  · have h1 : ordProj[p] b ∣ c := Nat.pow_dvd_of_le_of_pow_dvd h0.le (Nat.ordProj_dvd c p)
    replace h : ordProj[p] b ∣ a := (h.symm.dvd_iff h1).mp (Nat.ordProj_dvd b p)
    exact (hp.pow_dvd_iff_le_factorization ha).mp h
  ---- If `ν_p(a) > ν_p(b)`, since `ν_p(c) ≥ ν_p(b) + 1`, we would have `ν_p(b) > ν_p(b)`.
  · set t := b.factorization p
    have hc : c ≠ 0 := by
      rintro rfl; exact Nat.ne_zero_of_lt h0 (Finsupp.ext_iff.mp Nat.factorization_zero p)
    replace h1 : p ^ (t + 1) ∣ a := (hp.pow_dvd_iff_le_factorization ha).mpr h1
    replace h0 : p ^ (t + 1) ∣ c := (hp.pow_dvd_iff_le_factorization hc).mpr h0
    replace h : p ^ (t + 1) ∣ b := (h.dvd_iff h0).mp h1
    exact Nat.pow_succ_factorization_not_dvd hb hp h

open Finset in
/-- Custom factorization lemma. -/
lemma Nat_prod_pow_range_factorization {m n : ℕ} (hn : n ≠ 0) (hnm : n < m) :
    ∏ p ∈ range m, p ^ Nat.factorization n p = n := by
  ---- The proof is essentially "transfer the product to a version with `padicValNat`".
  refine (prod_congr_of_eq_on_inter ?_ ?_ ?_).trans
    (Nat.prod_pow_prime_padicValNat _ hn _ hnm)
  ---- Checking the RHS term is `1` on the set difference.
  · intro p hp hp0
    replace hp0 : ¬Nat.Prime p := by rwa [mem_filter, and_iff_right hp] at hp0
    rw [Nat.factorization_eq_zero_of_not_prime _ hp0, Nat.pow_zero]
  ---- Checking the LHS term is `1` on the set difference (the difference is empty).
  · intro p hp; exact absurd (mem_of_mem_filter p hp)
  ---- Checking term equality on intersection.
  · rintro p - hp; exact congrArg (p ^ ·) (Nat.factorization_def n (mem_filter.mp hp).2)

open Finset in
/-- For any positive integer `y`, there exists infinitely many primes
  `p ≡ 3 (mod 4)` such that `p ∣ 2^n y + 1` for some `n : ℕ`. -/
theorem exists_infinite_prime_3mod4_dvd_two_pow_mul_add_one {y : ℕ} (hy : y > 0) (N) :
    ∃ p ≥ N, Nat.Prime p ∧ p % 4 = 3 ∧ ∃ n, p ∣ 2 ^ n * y + 1 := by
  ---- WLOG assume that `y` is odd.
  wlog hy0 : ¬2 ∣ y
  · replace hy : y ≠ 0 := hy.ne.symm
    -- Pick a suitable `p ≥ max{N, y + 1}` and `n` such that `p ∣ 2^n y/2^{ν_2(y)} + 1`.
    obtain ⟨p, hp, hp0, hp1, n, hn⟩ :
        ∃ p ≥ max N (y + 1), Nat.Prime p ∧ p % 4 = 3 ∧ ∃ n, p ∣ 2 ^ n * ordCompl[2] y + 1 :=
      this (Nat.ordCompl_pos _ hy) _ (Nat.not_dvd_ordCompl Nat.prime_two hy)
    -- The condition `p > y` guarantees that `n ≥ ν_2(y)`.
    refine ⟨p, le_of_max_le_left hp, hp0, hp1, n - y.factorization 2, ?_⟩
    have hn0 : y.factorization 2 ≤ n := by
      have hn0 : y + 1 ≤ 2 ^ n * ordCompl[2] y + 1 :=
        (le_of_max_le_right hp).trans (Nat.le_of_dvd (Nat.succ_pos _) hn)
      replace hn0 : ordProj[2] y * ordCompl[2] y ≤ 2 ^ n * ordCompl[2] y :=
        (Nat.ordProj_mul_ordCompl_eq_self y 2).trans_le (Nat.le_of_succ_le_succ hn0)
      rwa [Nat.mul_le_mul_right_iff (Nat.ordCompl_pos 2 hy),
        Nat.pow_le_pow_iff_right Nat.one_lt_two] at hn0
    -- Thus we get `p ∣ 2^{n - ν_2(y)} y + 1`.
    calc p
      _ ∣ 2 ^ n * ordCompl[2] y + 1 := hn
      _ = 2 ^ (n - y.factorization 2) * ordProj[2] y * ordCompl[2] y + 1 := by
        rw [← Nat.pow_add, Nat.sub_add_cancel hn0]
      _ = 2 ^ (n - y.factorization 2) * y + 1 := by
        rw [Nat.mul_assoc, Nat.ordProj_mul_ordCompl_eq_self]
  replace hy0 : y ≡ 1 [MOD 2] := Nat.two_dvd_ne_zero.mp hy0
  ---- Suppose for the sake of contradiction that all such primes `p` are less than `N`.
  by_contra! hy1
  ---- Then for `p ≥ N` with `p ≢ 1 (mod 4)`, we have `ν_p(2^{n + 1} y + 1) = 0`.
  replace hy1 (p) (hp : p ≥ N) (hp0 : p % 4 ≠ 1) (n) :
      Nat.factorization (2 ^ (n + 1) * y + 1) p = 0 := by
    -- The case where `p` is not prime follows by how `Nat.factorization` is defined.
    obtain hp1 | hp1 : ¬Nat.Prime p ∨ Nat.Prime p := dec_em' _
    · exact Nat.factorization_eq_zero_of_not_prime _ hp1
    -- The case `p = 2` follows since `2^{n + 1} y + 1` is odd.
    obtain rfl | hp2 : p = 2 ∨ p ≠ 2 := eq_or_ne _ _
    · rw [Nat.pow_succ', Nat.mul_assoc]
      exact Nat.factorization_eq_zero_of_not_dvd (Nat.not_two_dvd_bit1 _)
    -- Otherwise this is a rewording of the original contrapositive assumption.
    replace hp2 : p % 4 = 1 ∨ p % 4 = 3 := by
      rwa [← hp1.mod_two_eq_one_iff_ne_two, Nat.odd_mod_four_iff] at hp2
    exact Nat.factorization_eq_zero_of_not_dvd (hy1 p hp hp1 (hp2.resolve_left hp0) _)
  ---- Set `V = 2y + 1`, `T = VN!/2^{ν_2(N!)}`, `U = 2^{φ(T) + 1} y + 1`.
  let V : ℕ := 2 * y + 1
  let T : ℕ := V * ordCompl[2] (Nat.factorial N)
  let U : ℕ := 2 ^ (Nat.totient T + 1) * y + 1
  ---- We start by noticing that `U ≡ V (mod T)`.
  have hN : N.factorial ≠ 0 := Nat.factorial_ne_zero N
  have hT : Odd T := by
    refine Nat.odd_mul.mpr ⟨odd_two_mul_add_one y, ?_⟩
    rw [Nat.odd_iff, ← Nat.mod_two_not_eq_zero, ← Nat.dvd_iff_mod_eq_zero]
    exact Nat.not_dvd_ordCompl Nat.prime_two hN
  have hT0 : U ≡ V [MOD T] :=
    calc 2 ^ (Nat.totient T + 1) * y + 1
    _ = 2 ^ Nat.totient T * (2 * y) + 1 := by rw [Nat.pow_succ, Nat.mul_assoc]
    _ ≡ 1 * (2 * y) + 1 [MOD T] :=
      ((Nat.ModEq.pow_totient (Nat.coprime_two_left.mpr hT)).mul_right _).add_right 1
    _ = 2 * y + 1 := by rw [Nat.one_mul]
  ---- Since `T = VN!/2^{ν_2(N!)}`, we get `ν_p(U) = ν_p(V)` for all primes `p ≤ N`.
  have X (n) : n + 1 ≠ 0 := Nat.succ_ne_zero _
  replace hT0 (p) (hp : p ≤ N) : U.factorization p = V.factorization p := by
    -- If `p` is not prime then both sides are zero by definition.
    obtain hp0 | hp0 : ¬Nat.Prime p ∨ Nat.Prime p := dec_em' _
    · iterate 2 rw [Nat.factorization_eq_zero_of_not_prime _ hp0]
    -- The same holds if `p = 2`, so now assume `p` is an odd prime.
    obtain rfl | hp1 : p = 2 ∨ p ≠ 2 := dec_em _
    · have h (n) : (2 * n + 1).factorization 2 = 0 :=
        (Nat.factorization_eq_zero_iff _ _).mpr (Or.inr (Or.inl (Nat.not_two_dvd_bit1 n)))
      dsimp only [U, V]
      rw [h, Nat.pow_succ', Nat.mul_assoc, h]
    -- For `p` odd prime, follows from `factorization_eq_of_modeq_of_lt`.
    refine factorization_eq_of_modeq_of_lt (X _) (X _) hT0 ?_
    rw [Nat.factorization_mul (X _) (Nat.ordCompl_pos _ hN).ne.symm, Finsupp.add_apply,
      Nat.lt_add_right_iff_pos, Nat.factorization_ordCompl, Finsupp.erase_apply, if_neg hp1]
    exact hp0.factorization_pos_of_dvd hN (Nat.dvd_factorial hp0.pos hp)
  ---- Working modulo `4` gives `U ≡ V (mod 4)`.
  replace hT0 (A : ℕ) :
      ∏ p ∈ range A, ((p ^ Nat.factorization U p : ℕ) : ZMod 4)
        = ∏ p ∈ range A, ((p ^ Nat.factorization V p : ℕ) : ZMod 4) := by
    refine prod_congr rfl λ p _ ↦ ?_
    -- If `p ≤ N` then as we have shown, the exponents are equal.
    obtain hp | hp : p ≤ N ∨ p ≥ N := Nat.le_total p N
    · exact congrArg (λ e ↦ ((p ^ e : ℕ) : ZMod 4)) (hT0 p hp)
    -- If `p ≥ N` and `p ≢ 1 (mod 4)` then the exponents are both zero.
    obtain hp0 | hp0 : p % 4 ≠ 1 ∨ p % 4 = 1 := ne_or_eq _ _
    · specialize hy1 p hp hp0
      exact congrArg (λ e ↦ ((p ^ e : ℕ) : ZMod 4)) ((hy1 _).trans (hy1 0).symm)
    -- If `p ≡ 1 (mod 4)`, then both sides are equal to `1` mod `4`.
    replace hp0 : (p : ZMod 4) = 1 := ZMod.val_injective _ hp0
    rw [Nat.cast_pow, Nat.cast_pow, hp0, one_pow, one_pow]
  replace hT0 : (U : ZMod 4) = V := by
    obtain ⟨A, hAU, hAV⟩ : ∃ A > U, A > V :=
      ⟨max U V + 1, max_lt_iff.mp (Nat.lt_succ_self _)⟩
    calc (U : ZMod 4)
      _ = (∏ p ∈ range A, p ^ Nat.factorization U p : ℕ) :=
        congrArg Nat.cast (Nat_prod_pow_range_factorization (X _) hAU).symm
      _ = ∏ p ∈ range A, ((p ^ Nat.factorization U p : ℕ) : ZMod 4) := prod_natCast _ _
      _ = ∏ p ∈ range A, ((p ^ Nat.factorization V p : ℕ) : ZMod 4) := hT0 A
      _ = (∏ p ∈ range A, p ^ Nat.factorization V p : ℕ) := (prod_natCast _ _).symm
      _ = V := congrArg Nat.cast (Nat_prod_pow_range_factorization (X _) hAV)
  replace hT0 : U ≡ V [MOD 4] := congrArg ZMod.val hT0
  ---- However, `U ≡ 1 (mod 4)` and `V ≡ 3 (mod 4)`; contradiction.
  clear hN X hy1 hy
  replace hT : T.totient > 0 := Nat.totient_pos.mpr hT.pos
  replace hT : 4 ∣ 2 ^ (Nat.totient T + 1) := Nat.pow_dvd_pow 2 (Nat.succ_le_succ hT)
  replace hT0 : 1 ≡ 3 [MOD 4] := calc
    1 ≡ 2 ^ (Nat.totient T + 1) * y + 1 [MOD 4] :=
      Nat.right_modEq_add_iff.mpr (Nat.dvd_mul_right_of_dvd hT _)
    _ ≡ 2 * y + 1 [MOD 4] := hT0
    _ ≡ 3 [MOD 4] := (hy0.mul_left' 2).add_right 1
  revert hT0; decide

/-- If `2^n y + 1 ∣ x^{2^n} - 1` for all `n` (including `n = 0`), then `x = 1`. -/
theorem eq_one_of_two_pow_mul_add_one_dvd_pow_two_pow_sub_one
    (hx : x > 0) (hy : y > 0) (h : ∀ n, 2 ^ n * y + 1 ∣ x ^ (2 ^ n) - 1) : x = 1 := by
  ---- Pick a prime `p > x^2 - 1` dividing some `2^n y + 1`.
  obtain ⟨p, hp, hp0, hp1, n, hpn⟩ :
      ∃ p > x ^ 2 - 1, Nat.Prime p ∧ p % 4 = 3 ∧ ∃ n, p ∣ 2 ^ n * y + 1 :=
    exists_infinite_prime_3mod4_dvd_two_pow_mul_add_one hy _
  ---- But then we get `p ∣ x^{2^n} - 1` and then `p ∣ x^2 - 1`.
  replace h : p ∣ x ^ (2 ^ n) - 1 := hpn.trans (h n)
  replace h : p ∣ x ^ 2 - 1 := prime_dvd_sq_sub_one_of_dvd_two_pow_sub_one hp0 hp1 h
  ---- This forces `x^2 - 1 = 0 ↔ x = 1`.
  replace h : x ^ 2 - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h hp
  rw [Nat.sub_eq_zero_iff_le, Nat.pow_le_one_iff (Nat.succ_ne_zero 1)] at h
  exact Nat.le_antisymm h hx

/-- Final solution -/
theorem final_solution {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (h : ∀ n > 0, 2 ^ n * y + 1 ∣ x ^ (2 ^ n) - 1) : x = 1 := by
  ---- Work with `2y` and `x^2` instead of `y` and `x`.
  replace h (n) : 2 ^ n * (2 * y) + 1 ∣ (x ^ 2) ^ (2 ^ n) - 1 := by
    rw [← Nat.mul_assoc, ← Nat.pow_succ, ← Nat.pow_mul, ← Nat.pow_succ']
    exact h (n + 1) (Nat.succ_pos n)
  ---- Then we get `x^2 = 1`, which still implies `x = 1`.
  replace h : x ^ 2 = 1 :=
    eq_one_of_two_pow_mul_add_one_dvd_pow_two_pow_sub_one
      (Nat.pow_pos hx) (Nat.mul_pos Nat.two_pos hy) h
  exact (Nat.pow_eq_one.mp h).resolve_right (Nat.succ_ne_zero 1)
