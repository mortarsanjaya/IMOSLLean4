/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# IMO 2023 N3

For any positive integer $n$ and $k ≥ 2$, define $ν_k(n)$
  as the largest exponent $r$ such that $k^r ∣ n$.
Prove the following:
1. there are infinitely many $n$ such that $ν_{10}(n!) > ν_9(n!)$; and
2. there are infinitely many $n$ such that $ν_{10}(n!) < ν_9(n!)$.
-/

namespace IMOSL
namespace IMO2023N3

set_option backward.isDefEq.respectTransparency false

/-! ### Extra lemmas -/

lemma le_padicValNat_iff (ha : 1 < a) (hb : 0 < b) : n ≤ padicValNat a b ↔ a ^ n ∣ b :=
  (Nat.pow_dvd_iff_le_padicValNat ha.ne.symm hb.ne.symm).symm

lemma padicValNat_eq_iff (ha : a ≠ 1) (hb : b ≠ 0) :
    padicValNat a b = n ↔ a ^ n ∣ b ∧ ¬a ^ (n + 1) ∣ b := by
  rw [Nat.pow_dvd_iff_le_padicValNat ha hb, Nat.pow_dvd_iff_le_padicValNat ha hb,
    Nat.not_le, Nat.lt_succ_iff, ← Nat.le_antisymm_iff, eq_comm]

lemma padicValNat_pow_left (a b k) : padicValNat (a ^ k) b = padicValNat a b / k := by
  ---- Side case 1: `k = 0`.
  obtain rfl | hk : k = 0 ∨ k ≠ 0 := eq_or_ne _ _
  · rw [Nat.pow_zero, padicValNat_one_left, Nat.div_zero]
  ---- Side case 2: `a = 1`.
  obtain rfl | ha : a = 1 ∨ a ≠ 1 := eq_or_ne _ _
  · rw [Nat.one_pow, padicValNat_one_left, Nat.zero_div]
  ---- Side case 3: `b = 0`.
  obtain rfl | hb : b = 0 ∨ b ≠ 0 := eq_or_ne _ _
  · rw [padicValNat_zero_right, padicValNat_zero_right, Nat.zero_div]
  ---- Main case: `a ≠ 1`, `b ≠ 0`, and `k ≠ 0`.
  refine (padicValNat_eq_iff (mt Nat.pow_eq_one.mp (not_or.mpr ⟨ha, hk⟩)) hb).mpr ⟨?_, ?_⟩
  · rw [← Nat.pow_mul, Nat.pow_dvd_iff_le_padicValNat ha hb]
    exact Nat.mul_div_le _ _
  · rw [← Nat.pow_mul, Nat.pow_dvd_iff_le_padicValNat ha hb, Nat.not_le,
      Nat.mul_comm, ← Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_ne_zero hk)]
    exact Nat.lt_succ_self _

lemma padicValNat_prime_mul_left
    [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (h : p ≠ q) (n : ℕ) :
    padicValNat (p * q) n = min (padicValNat p n) (padicValNat q n) := by
  obtain rfl | hn : n = 0 ∨ n ≠ 0 := eq_or_ne n 0
  · simp only [padicValNat_zero_right]; rfl
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  have hp0 : p ≠ 1 := hp.ne_one
  have hq0 : q ≠ 1 := hq.ne_one
  refine (padicValNat_eq_iff (λ h ↦ hp0 (Nat.eq_one_of_mul_eq_one_right h)) hn).mpr
    ⟨?_, λ h0 ↦ ?_⟩
  · have h0 : p.Coprime q :=
      hp.coprime_iff_not_dvd.mpr λ h0 ↦ h ((Nat.prime_dvd_prime_iff_eq hp hq).mp h0)
    rw [Nat.mul_pow]; apply (h0.pow _ _).mul_dvd_of_dvd_of_dvd
    exacts [Nat.pow_dvd_of_le_of_pow_dvd (min_le_left _ _) pow_padicValNat_dvd,
      Nat.pow_dvd_of_le_of_pow_dvd (min_le_right _ _) pow_padicValNat_dvd]
  · wlog h1 : padicValNat p n ≤ padicValNat q n
    · refine this h.symm n hn hq hp hq0 hp0 ?_ (Nat.le_of_not_le h1)
      rwa [min_comm, Nat.mul_comm]
    rw [min_eq_left h1, Nat.mul_pow] at h0
    replace h0 : p ^ (padicValNat p n + 1) ∣ n := dvd_of_mul_right_dvd h0
    rw [Nat.pow_dvd_iff_le_padicValNat hp0 hn, Nat.add_one_le_iff] at h0
    exact h0.ne rfl

lemma padicValNat_factorial_prime_le
    [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (h : p ≤ q) (n : ℕ) :
    padicValNat q n.factorial ≤ padicValNat p n.factorial := by
  obtain ⟨M, hp, hq⟩ : ∃ M, p.log n < M ∧ q.log n < M :=
    ⟨max (p.log n) (q.log n) + 1, max_lt_iff.mp (Nat.lt_succ_self _)⟩
  rw [padicValNat_factorial hp, padicValNat_factorial hq]
  refine Finset.sum_le_sum λ i _ ↦ Nat.div_le_div_left (Nat.pow_le_pow_left h i) ?_
  have h : p.Prime := Fact.out; exact Nat.pow_pos h.pos

lemma padicValNat_prime_mul_factorial_of_lt
    [Fact (Nat.Prime p)] [Fact (Nat.Prime q)] (h : p < q) (n : ℕ) :
    padicValNat (p * q) n.factorial = padicValNat q n.factorial := by
  rw [padicValNat_prime_mul_left h.ne, min_eq_right (padicValNat_factorial_prime_le h.le n)]

instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

lemma padicValNat_9_eq (n : ℕ) : padicValNat 9 n = padicValNat 3 n / 2 :=
  padicValNat_pow_left 3 n 2

lemma padicValNat_9_factorial_eq (n : ℕ) :
    padicValNat 9 n.factorial = (n - (Nat.digits 3 n).sum) / 4 := by
  rw [padicValNat_9_eq, ← sub_one_mul_padicValNat_factorial,
    ← Nat.div_div_eq_div_mul _ 2 2, Nat.mul_div_cancel_left _ Nat.two_pos]

lemma padicValNat_10_factorial_eq' (n : ℕ) :
    padicValNat 10 n.factorial = padicValNat 5 n.factorial :=
  padicValNat_prime_mul_factorial_of_lt (by norm_num : 2 < 5) n

lemma padicValNat_10_factorial_eq (n : ℕ) :
    padicValNat 10 n.factorial = (n - (Nat.digits 5 n).sum) / 4 := by
  rw [padicValNat_10_factorial_eq', ← sub_one_mul_padicValNat_factorial,
    Nat.mul_div_cancel_left _ (Nat.succ_pos 3)]

lemma Nat_digits_self_pow {b : ℕ} (hb : 1 < b) :
    ∀ n, b.digits (b ^ n) = List.replicate n 0 ++ [1] := by
  refine Nat.rec ?_ λ n hn ↦ ?_
  · rw [Nat.pow_zero, Nat.digits_of_lt _ _ Nat.one_ne_zero hb]; rfl
  · have hb0 : 0 < b := Nat.zero_lt_of_lt hb
    rw [Nat.digits_of_two_le_of_pos hb (Nat.pow_pos hb0), Nat.pow_succ,
      Nat.mul_mod_left, Nat.mul_div_left _ hb0, hn]; rfl

lemma Nat_ofDigits_replicate_zero (b) : ∀ n, Nat.ofDigits b (List.replicate n 0) = 0 := by
  refine Nat.rec rfl λ n hn ↦ ?_
  rw [List.replicate_succ, Nat.ofDigits_cons, hn, Nat.mul_zero]

lemma Nat_digits_sum_pos (b : ℕ) {n : ℕ} (h : 0 < n) : 0 < (b.digits n).sum := by
  rw [Nat.pos_iff_ne_zero, Ne, List.sum_eq_zero_iff]
  intro h0; apply h.ne.symm
  rw [← b.ofDigits_digits n, List.eq_replicate_of_mem h0, Nat_ofDigits_replicate_zero]





/-! ### Start of the problem -/

lemma Nat_digits3_5pow (k : ℕ) : 1 < (Nat.digits 3 (5 ^ (k + 1))).sum := by
  have h : 0 < 5 := Nat.succ_pos 4
  rw [Nat.digits_of_two_le_of_pos (Nat.le_succ 2) (Nat.pow_pos h), List.sum_cons]
  refine Nat.add_le_add (Nat.emod_pos_of_not_dvd λ h ↦ ?_) (Nat_digits_sum_pos _ ?_)
  · exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by decide)
  · refine Nat.div_pos ?_ (Nat.succ_pos 2)
    exact (Nat.le_add_right 3 2).trans (Nat.le_mul_of_pos_left _ (Nat.pow_pos h))

lemma main_step1 (N : ℕ) :
    padicValNat 9 (5 ^ (N + 1)).factorial < padicValNat 10 (5 ^ (N + 1)).factorial := by
  have h : 1 < 5 := by norm_num
  rw [padicValNat_9_factorial_eq, padicValNat_10_factorial_eq]
  refine Nat.div_lt_div_of_lt_of_dvd ⟨_, (sub_one_mul_padicValNat_factorial _).symm⟩ ?_
  rw [Nat_digits_self_pow h, List.sum_append, List.sum_replicate]
  exact Nat.sub_lt_sub_left (Nat.one_lt_pow N.succ_ne_zero h) (Nat_digits3_5pow _)

/-- Final solution, part 1 -/
theorem final_solution_part1 (N : ℕ) :
    ∃ n > N, padicValNat 9 n.factorial < padicValNat 10 n.factorial :=
  ⟨5 ^ (N + 1), N.lt_succ_self.trans (Nat.lt_pow_self (by norm_num)), main_step1 N⟩

lemma Nat_digits5_3pow (k : ℕ) : 5 ≤ (Nat.digits 5 (3 ^ (2 * (2 * k + 1)))).sum := by
  have h : 0 < 3 := Nat.succ_pos 2
  rw [Nat.digits_of_two_le_of_pos (by norm_num) (Nat.pow_pos h), List.sum_cons, Nat.pow_mul]
  refine Nat.add_le_add (?_ : 4 ≤ _) (?_ : 0 < _)
  · rw [Nat.pow_succ, Nat.pow_mul, Nat.mul_mod, Nat.pow_mod, Nat.one_pow k]
  · refine Nat_digits_sum_pos _ (Nat.div_pos ?_ (Nat.succ_pos 4))
    refine (by norm_num : 5 ≤ 9).trans (Nat.le_mul_of_pos_left _ ?_)
    exact Nat.pow_pos (Nat.pow_pos h)

lemma main_step2 (N : ℕ) :
    padicValNat 10 (3 ^ (2 * (2 * N + 1))).factorial
      < padicValNat 9 (3 ^ (2 * (2 * N + 1))).factorial := by
  have h : 1 < 3 := by norm_num
  rw [padicValNat_9_factorial_eq, padicValNat_10_factorial_eq,
    Nat_digits_self_pow h, List.sum_append, List.sum_replicate,
    ← Nat.add_one_le_iff, ← Nat.add_div_right _ (Nat.succ_pos 3)]
  refine Nat.div_le_div_right (Nat.le_sub_of_add_le (?_ : _ - _ + 5 ≤ _))
  rw [← Nat.sub_add_comm (Nat.digit_sum_le _ _)]
  exact Nat.sub_le_of_le_add (Nat.add_le_add_left (Nat_digits5_3pow _) _)

/-- Final solution, part 2 -/
theorem final_solution_part2 (N : ℕ) :
    ∃ n > N, padicValNat 10 n.factorial < padicValNat 9 n.factorial := by
  refine ⟨3 ^ (2 * (2 * N + 1)), ?_, main_step2 _⟩; calc
    _ = 9 ^ (2 * N + 1) := Nat.pow_mul 3 2 _
    _ > 2 * N + 1 := Nat.lt_pow_self (by norm_num)
    _ > 2 * N := (2 * N).lt_succ_self
    _ ≥ N := Nat.le_mul_of_pos_left N Nat.two_pos
