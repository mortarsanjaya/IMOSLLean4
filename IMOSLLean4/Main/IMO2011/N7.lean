/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Prime.Factorial

/-!
# IMO 2011 N7

Let $p$ be an odd prime number.
For every integer $a$, define
$$ S_a = \sum_{i = 1}^{p - 1} \frac{a^i}{i}. $$
Let $m$ and $n$ be integers such that $\gcd(m, n) = 1$ and
$$ S_3 + S_4 - 3S_2 = \frac{m}{n}. $$
Prove that $p ∣ m$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2011SL.pdf).
Throughout the documentation of this formalization, $G_d$ denotes the subgroup of $ℚ$
  consisting of rational numbers whose numerator (after normalizing) is divisible by $d$.
-/

namespace IMOSL
namespace IMO2011N7

open Finset

/-! ### Subgroup of the rationals defined by numerator divisible by a fixed number -/

/-- If `d` divides the numerator of a rational number, `d` is coprime to the denominator. -/
theorem coprime_den_of_dvd_num {d : ℤ} {q : ℚ} (h : d ∣ q.num) : q.den.Coprime d.natAbs :=
  (q.reduced.coprime_dvd_left (Int.natAbs_dvd_natAbs.mpr h)).symm

/-- The subgroup `G_d` of rational numbers whose numerator is divisible by `d`. -/
def NumDvdSubgroup (d : ℤ) : AddSubgroup ℚ where
  carrier := {q : ℚ | d ∣ q.num}
  zero_mem' := Int.dvd_zero d
  neg_mem' := Int.dvd_neg.mpr
  add_mem' := by
    intro a b (ha : d ∣ a.num) (hb : d ∣ b.num)
    let N : ℤ := a.num * b.den + b.num * a.den
    have h : d ∣ N := Int.dvd_add (Int.dvd_mul_of_dvd_left ha) (Int.dvd_mul_of_dvd_left hb)
    replace ha : a.den.Coprime d.natAbs := coprime_den_of_dvd_num ha
    replace hb : b.den.Coprime d.natAbs := coprime_den_of_dvd_num hb
    have h0 : (a.den * b.den).Coprime d.natAbs := ha.mul_left hb
    replace h0 : (N.natAbs.gcd (a.den * b.den)).Coprime d.natAbs := h0.gcd_left N.natAbs
    replace h0 : N.natAbs.gcd (a.den * b.den) * d.natAbs ∣ N.natAbs :=
      h0.mul_dvd_of_dvd_of_dvd (Nat.gcd_dvd_left _ _) (Int.natAbs_dvd_natAbs.mpr h)
    replace h0 : N.natAbs.gcd (a.den * b.den) * d ∣ N := by
      rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_mul, Int.natAbs_natCast]
    rw [Set.mem_setOf_eq, Rat.num_add]
    exact Int.dvd_div_of_mul_dvd h0

/-- Definition of membership on `NumDvdSubgroup`. -/
theorem mem_NumDvdSubgroup_iff : q ∈ NumDvdSubgroup d ↔ d ∣ q.num := Iff.rfl

/-- If `k : ℕ` is coprime to `d`, then `kq ∈ G_d` iff `q ∈ G_d`. -/
theorem mul_mem_NumDvdSubgroup_iff_of_coprime
    {k : ℕ} {d : ℤ} (h : k.Coprime d.natAbs) {q : ℚ} :
    k * q ∈ NumDvdSubgroup d ↔ q ∈ NumDvdSubgroup d := by
  refine ⟨λ h0 ↦ ?_, λ h0 ↦ AddSubgroup.nsmul_mem _ h0 k⟩
  let N : ℕ := (k * q.num).natAbs.gcd q.den
  replace h0 : d ∣ (k : ℤ) * q.num / N := by
    rwa [mem_NumDvdSubgroup_iff, Rat.num_mul,
      Rat.num_natCast, Rat.den_natCast, one_mul] at h0
  replace h0 : d ∣ (k : ℤ) * q.num :=
    (Int.dvd_mul_left N d).trans (Int.mul_dvd_of_dvd_ediv (Rat.normalize.dvd_num rfl) h0)
  replace h : IsCoprime (k : ℤ) d := Int.isCoprime_iff_gcd_eq_one.mpr h
  exact h.symm.dvd_of_dvd_mul_left h0





/-! ### Start of the problem -/

/-- The rational number `S_a = ∑_{i = 1}^{p - 1} a^i/i`. -/
abbrev S (p : ℕ) (a : ℤ) : ℚ := ∑ k ∈ Ico 1 p, (a ^ k : ℚ) / k


variable [Fact (Nat.Prime p)]

/-- For any `k < p` we have `(p - 1)(p - 2) … (p - k) ≡ (-1)^k k! (mod p)`. -/
theorem descFactorial_prime_sub_one_ZMod {k : ℕ} (hkp : k < p) :
    (Nat.descFactorial (p - 1) k : ZMod p) = (-1) ^ k * Nat.factorial k := by
  ---- Induction on `k`, where the base case is trivial.
  induction k with
  | zero => rw [Nat.descFactorial_zero, pow_zero, one_mul, Nat.factorial_zero]
  | succ k k_ih => ?_
  ---- Now do a lot of calculations for the induction step.
  calc ((p - 1).descFactorial (k + 1) : ZMod p)
    _ = (p - 1 - k : ℕ) * ((-1) ^ k * Nat.factorial k) := by
      rw [Nat.descFactorial_succ, Nat.cast_mul, k_ih (Nat.lt_of_succ_lt hkp)]
    _ = -(k + 1 : ℕ) * ((-1) ^ k * Nat.factorial k) := by
      rw [Nat.sub_sub, Nat.add_comm, Nat.cast_sub hkp.le, CharP.cast_eq_zero, zero_sub]
    _ = (-1) ^ (k + 1) * (k + 1).factorial := by
      rw [Nat.factorial_succ, Nat.cast_mul, neg_mul,
        mul_left_comm, pow_succ, mul_neg_one, neg_mul]

/-- For any non-negative integer `k < p`, we have `C(p - 1, k) ≡ (-1)^k (mod p)`. -/
theorem choose_prime_sub_one_left_ZMod {k : ℕ} (hkp : k < p) :
    (Nat.choose (p - 1) k : ZMod p) = (-1) ^ k := by
  have h : (Nat.descFactorial (p - 1) k : ZMod p) = (-1) ^ k * Nat.factorial k :=
    descFactorial_prime_sub_one_ZMod hkp
  have h0 : (Nat.factorial k : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.natCast_eq_zero_iff, Nat.Prime.dvd_factorial Fact.out, Nat.not_le]
  rwa [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    mul_comm, mul_eq_mul_right_iff, or_iff_left h0] at h

/-- For any `k` with `0 < k < p`, we have `1/k + (-1)^k C(p, k)/p ∈ G_p`. -/
theorem inv_add_sub_choose_div_prime_mem_NumDvdSubgroup (hk : 0 < k) (hkp : k < p) :
    (k : ℚ)⁻¹ + (-1) ^ k * Nat.choose p k / p ∈ NumDvdSubgroup p := by
  ---- Multiply the left hand side by `k`, which is coprime to `p`.
  have hp : Nat.Prime p := Fact.out
  have hk0 : k ≠ 0 := hk.ne.symm
  have hkp0 : k.Coprime p := (Nat.coprime_of_lt_prime hk0 hkp hp).symm
  refine (mul_mem_NumDvdSubgroup_iff_of_coprime hkp0).mp (?_ : (p : ℤ) ∣ _)
  ---- Note that `k` times LHS is equal to `1 + (-1)^k C(p - 1, k - 1)`.
  have h : (k : ℚ) * ((k : ℚ)⁻¹ + (-1) ^ k * Nat.choose p k / p)
      = (1 + (-1) ^ k * (p - 1).choose (k - 1) : ℤ) :=
    calc (k : ℚ) * ((k : ℚ)⁻¹ + (-1) ^ k * Nat.choose p k / p)
    _ = 1 + k * ((-1) ^ k * Nat.choose p k / p) := by
      rw [mul_add, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hk0)]
    _ = 1 + (-1) ^ k * (k * Nat.choose p k : ℕ) / p := by
      rw [← mul_div_assoc, mul_left_comm, Nat.cast_mul]
    _ = 1 + (-1) ^ k * (Nat.choose (p - 1 + 1) (k - 1 + 1) * (k - 1 + 1) : ℕ) / p := by
      rw [Nat.sub_add_cancel hp.pos, Nat.sub_add_cancel hk, Nat.mul_comm]
    _ = 1 + (-1) ^ k * (p * Nat.choose (p - 1) (k - 1) : ℕ) / p := by
      rw [← Nat.add_one_mul_choose_eq, Nat.sub_add_cancel hp.pos]
    _ = 1 + (-1) ^ k * (p * Nat.choose (p - 1) (k - 1) / p) := by
      rw [Nat.cast_mul, mul_div_assoc]
    _ = 1 + (-1) ^ k * Nat.choose (p - 1) (k - 1) := by
      rw [mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hp.ne_zero)]
    _ = (1 + (-1) ^ k * (p - 1).choose (k - 1) : ℤ) := by
      rw [Int.cast_add, Int.cast_mul, Int.cast_pow, Int.cast_neg]; rfl
  ---- But `C(p - 1, k - 1) ≡ (-1)^{k - 1} ≡ -(-1)^k (mod p)`, so we are done.
  suffices ((1 + (-1) ^ k * (p - 1).choose (k - 1) : ℤ) : ZMod p) = 0 by
    rw [h, Rat.num_intCast, ← ZMod.intCast_zmod_eq_zero_iff_dvd, this]
  calc ((1 + (-1) ^ k * (p - 1).choose (k - 1) : ℤ) : ZMod p)
    _ = 1 + (-1) ^ k * (p - 1).choose (k - 1) := by
      rw [Int.cast_add, Int.cast_mul, Int.cast_pow,
        Int.cast_neg, Int.cast_one, Int.cast_natCast]
    _ = 1 + (-1) ^ k * (-1) ^ (k - 1) :=
      congrArg (λ x : ZMod p ↦ 1 + (-1) ^ k * x)
        (choose_prime_sub_one_left_ZMod (Nat.sub_lt_of_lt hkp))
    _ = 1 + (-1) ^ (2 * (k - 1) + 1) := by
      rw [Nat.two_mul, Nat.add_assoc, Nat.sub_add_cancel hk, pow_add, mul_comm]
    _ = 0 := by rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, add_neg_cancel]


variable (hp : Odd p)
include hp

/-- We have `S_a + (a^p - (a - 1)^p - 1)/p ∈ G_p`. -/
theorem S_add_mem_NumDvdSubgroup (a : ℕ) :
    S p a + (a ^ p - (a - 1) ^ p - 1) / p ∈ NumDvdSubgroup p := by
  ---- It suffices to show that the LHS is `∑_{k = 1}^p a^k (1/k + (-1)^k C(p, k)/p)`.
  suffices S p a + (a ^ p - (a - 1) ^ p - 1) / p
      = ∑ k ∈ Ico 1 p, (a ^ k : ℚ) * ((k : ℚ)⁻¹ + (-1) ^ k * Nat.choose p k / p) by
    refine this ▸ AddSubgroup.sum_mem _ λ k hk ↦ ?_
    replace hk : 0 < k ∧ k < p := mem_Ico.mp hk
    rw [← Rat.natCast_pow, ← nsmul_eq_mul]
    have h := inv_add_sub_choose_div_prime_mem_NumDvdSubgroup hk.1 hk.2
    exact AddSubgroup.nsmul_mem _ h _
  ---- Now do the calculations; start by isolating `S_a` from the RHS.
  symm; calc ∑ k ∈ Ico 1 p, (a ^ k : ℚ) * ((k : ℚ)⁻¹ + (-1) ^ k * Nat.choose p k / p)
    _ = ∑ k ∈ Ico 1 p, ((a ^ k : ℚ) / k + (-a) ^ k * Nat.choose p k / p) := by
      refine sum_congr rfl λ k _ ↦ ?_
      rw [mul_add, ← div_eq_mul_inv, neg_pow (a : ℚ),
        mul_assoc, mul_left_comm, ← mul_div_assoc]
    _ = S p a + (∑ k ∈ Ico 1 p, (-a : ℚ) ^ k * Nat.choose p k) / p := by
      rw [sum_add_distrib, sum_div]; rfl
    _ = S p a + (a ^ p - (a - 1) ^ p - 1) / p := congrArg (S p a + · / p) ?_
  ---- It remains to show `∑_{k = 1}^p (-a)^k C(p, k) = a^p - (a - 1)^p - 1`.
  let f (k : ℕ) : ℚ := (-a) ^ k * Nat.choose p k
  calc ∑ k ∈ Ico 1 p, f k
    _ = ∑ k ∈ Ico 0 p, f k - (-a) ^ 0 * Nat.choose p 0 :=
      eq_sub_of_add_eq' (sum_eq_sum_Ico_succ_bot hp.pos f).symm
    _ = ∑ k ∈ range p, f k - 1 := by
      rw [Nat.Ico_zero_eq_range, pow_zero, one_mul, Nat.choose_zero_right, Nat.cast_one]
    _ = ∑ k ∈ range (p + 1), f k - (-a) ^ p * Nat.choose p p - 1 :=
      congrArg (· - 1) (sum_range_succ_sub_top _).symm
    _ = a ^ p + ∑ k ∈ range (p + 1), f k - 1 := by
      rw [hp.neg_pow, Nat.choose_self, Nat.cast_one, mul_one, sub_neg_eq_add, add_comm]
    _ = a ^ p + ∑ k ∈ range (p + 1), (-a : ℚ) ^ k * 1 ^ (p - k) * Nat.choose p k - 1 := by
      simp_rw [f, one_pow, mul_one]
    _ = a ^ p - (a - 1) ^ p - 1 := by
      rw [← add_pow, neg_add_eq_sub, ← neg_sub _ 1, hp.neg_pow, ← sub_eq_add_neg]

/-- We have `S_{a + 1} + ((a + 1)^p - a^p - 1)/p ∈ G_p`. -/
theorem S_add_mem_NumDvdSubgroup2 (a : ℕ) :
    S p (a + 1 : ℕ) + ((a + 1 : ℕ) ^ p - a ^ p - 1) / p ∈ NumDvdSubgroup p := by
  simpa only [Nat.cast_succ, add_sub_cancel_right] using S_add_mem_NumDvdSubgroup hp (a + 1)

omit hp in
/-- We have `p ∣ 2^p - 2`. -/
theorem prime_dvd_two_pow_sub_two : (p : ℤ) ∣ 2 ^ p - 2 := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, Int.cast_pow, ZMod.pow_card]

/-- We have `S_3 + S_4 - 3S_2 ∈ G_p`. -/
theorem S3_add_S4_sub_three_mul_S2_mem_NumDvdSubgroup :
    S p 3 + S p 4 - 3 * S p 2 ∈ NumDvdSubgroup p := by
  set G : AddSubgroup ℚ := NumDvdSubgroup p
  /- First we have `S_3 + S_4 - 3S_2 + L ∈ G_p`,
    where `L = (3^p - 2^p - 1)/p + (4^p - 3^p - 1)/p - 3(2^p - 2)/p`. -/
  let L : ℚ :=
    (3 ^ p - 2 ^ p - 1) / p + (4 ^ p - 3 ^ p - 1) / p - 3 * ((2 ^ p - 1 ^ p - 1) / p)
  have h (a : ℕ) : S p (a + 1 : ℕ) + ((a + 1 : ℕ) ^ p - a ^ p - 1) / p ∈ G :=
    S_add_mem_NumDvdSubgroup2 hp a
  replace h : S p 3 + S p 4 - 3 * S p 2 + L ∈ G := by
    rw [sub_add_sub_comm, add_add_add_comm, ← mul_add]
    exact G.sub_mem (G.add_mem (h 2) (h 3)) (G.nsmul_mem (h 1) 3)
  ---- Thus it suffices to show `L ∈ G_p`.
  suffices L ∈ G from (AddSubgroup.add_mem_cancel_right G this).mp h
  ---- Rearranging gives `L = (2^p - 2)^2/p`.
  replace h : L = (2 ^ p - 2 : ℤ) ^ 2 / p :=
    calc L
    _ = ((3 ^ p - 2 ^ p - 1) + (4 ^ p - 3 ^ p - 1) - 3 * (2 ^ p - 1 ^ p - 1)) / p := by
      rw [sub_div, add_div, mul_div_assoc]
    _ = (4 ^ p - 2 ^ p - 2 - 3 * (2 ^ p - 2)) / p := by
      rw [sub_add_sub_comm, sub_add_sub_cancel', one_pow, sub_sub _ 1 1, one_add_one_eq_two]
    _ = ((2 * 2) ^ p + 2 ^ p - 2 ^ p * 2 - 2 - 3 * (2 ^ p - 2)) / p := by
      have h0 : (2 : ℚ) * 2 = 4 := by rw [two_mul, two_add_two_eq_four]
      rw [h0, mul_two, add_sub_add_right_eq_sub]
    _ = ((2 ^ p + 1) * (2 ^ p - 2) - (2 + 1) * (2 ^ p - 2)) / p := by
      rw [two_add_one_eq_three, mul_pow, ← add_one_mul,
        sub_sub _ _ 2, ← add_one_mul, ← mul_sub]
    _ = (2 ^ p - 2) ^ 2 / p := by rw [← sub_mul, add_sub_add_right_eq_sub, ← sq]
    _ = (2 ^ p - 2 : ℤ) ^ 2 / p := by rw [Int.cast_sub, Int.cast_pow, Int.cast_two]
  clear_value L; subst h
  ---- But `p ∣ 2^p - 2`, so we definitely have `(2^p - 2)^2/p ∈ G`.
  obtain ⟨k, hk⟩ : (p : ℤ) ∣ 2 ^ p - 2 := prime_dvd_two_pow_sub_two
  replace hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.pos.ne.symm
  replace hp : ((2 ^ p - 2 : ℤ) : ℚ) ^ 2 / p = (p * k ^ 2 : ℤ) := by
    rw [hk, Int.cast_mul, Int.cast_mul, Int.cast_natCast, mul_pow,
      sq, mul_assoc, mul_div_cancel_left₀ _ hp, Int.cast_pow]
  rw [hp, mem_NumDvdSubgroup_iff, Rat.num_intCast]
  exact Int.dvd_mul_right _ _

/-- Final solution -/
theorem final_solution : (p : ℤ) ∣ (S p 3 + S p 4 - 3 * S p 2).num :=
  S3_add_S4_sub_three_mul_S2_mem_NumDvdSubgroup hp
