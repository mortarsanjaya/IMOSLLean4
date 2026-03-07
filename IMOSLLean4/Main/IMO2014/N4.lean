/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.ModEq

/-!
# IMO 2014 N4

Prove that for any integer $n > 1$, there exists infinitely many
  positive integers $k$ such that $⌊n^k/k⌋$ is odd.

### Solution

We follow Solution 2 of the
  [official solution](https://www.imo-official.org/problems/IMO2014SL.pdf),
  but for $n > 2$ even, we use $n - 1$ in place of a prime divisor of $n - 1$.
That is, we take $k$ to be powers of $n - 1$.
It can be proved by induction on $m$ that $(d + 1)^{d^m} ≡ 1 \pmod{d^{m + 1}}$ for any $d$.
-/

namespace IMOSL
namespace IMO2014N4

/-- If `n` is odd, then `⌊n^{n^k}/n^k⌋` is odd for any `k : ℕ`. -/
theorem case_odd (hn : n > 1) (h : n % 2 = 1) (k) : n ^ (n ^ k) / n ^ k % 2 = 1 :=
  calc n ^ (n ^ k) / n ^ k % 2
  _ = n ^ (n ^ k - k) % 2 :=
    congrArg (· % 2) (Nat.pow_div (Nat.le_of_lt (Nat.lt_pow_self hn)) (Nat.zero_lt_of_lt hn))
  _ = 1 := by rw [Nat.pow_mod, h, Nat.one_pow]

/-- An auxiliary lemma: if `a` is even and `a % b = 1`, then `⌊a/b⌋` is odd. -/
theorem div_odd_of_even_mod_eq_one (ha : 2 ∣ a) (hab : a % b = 1) : a / b % 2 = 1 := by
  obtain hb | hb : b % 2 = 0 ∨ b % 2 = 1 := Nat.mod_two_eq_zero_or_one b
  ---- If `b` is even then `a % b` is even and cannot be `1`; contradiction.
  · rcases ha with ⟨c, rfl⟩
    obtain ⟨d, rfl⟩ : 2 ∣ b := Nat.dvd_of_mod_eq_zero hb
    replace hab : 2 ∣ 1 := ⟨c % d, hab.symm.trans (Nat.mul_mod_mul_left _ _ _)⟩
    have h : ¬2 ∣ 1 := by decide
    exact absurd hab h
  ---- If `b` is odd then the calculations below work out.
  · calc a / b % 2
    _ = (b * (a / b) + a % b + 1) % 2 := by
      rw [Nat.add_assoc, hab, Nat.add_mod_right, ← Nat.mod_mul_mod, hb, Nat.one_mul]
    _ = 1 := by rw [Nat.div_add_mod, ← Nat.mod_add_mod, Nat.mod_eq_zero_of_dvd ha]

/-- The number `⌊2^{3 4^k}/(3 4^k)⌋` is odd for any `k > 0`. -/
theorem case_two (hk : k > 0) : 2 ^ (3 * 4 ^ k) / (3 * 4 ^ k) % 2 = 1 := by
  ---- The reason is that `3 4^k - 2k` is a positive even integer.
  have hk0 : 2 * k < 3 * 4 ^ k :=
    Nat.mul_lt_mul'' (Nat.lt_succ_self 2) (Nat.lt_pow_self (by decide))
  let e : Nat := 3 * 4 ^ k - 2 * k
  have he : e > 0 := Nat.zero_lt_sub_of_lt hk0
  have he0 : 2 ∣ e := by
    refine Nat.dvd_sub (Nat.dvd_mul_left_of_dvd ⟨2 * 4 ^ (k - 1), ?_⟩ _) ⟨k, rfl⟩
    rw [← Nat.mul_assoc, ← Nat.pow_add_one', Nat.sub_add_cancel hk]
  replace he0 : 2 ^ e % 3 = 1 := calc
    _ = 4 ^ (e / 2) % 3 := by rw [← Nat.pow_mul 2 2, Nat.mul_div_cancel' he0]
    _ = 1 := by rw [Nat.pow_mod, Nat.one_pow]
  ---- Now do the calculations.
  calc 2 ^ (3 * 4 ^ k) / (3 * 4 ^ k) % 2
    _ = 2 ^ e / 3 % 2 := by
      rw [← Nat.pow_div (Nat.le_of_lt hk0) Nat.two_pos,
        Nat.div_div_eq_div_mul, Nat.pow_mul 2 2, Nat.mul_comm _ 3]
    _ = 1 := div_odd_of_even_mod_eq_one (Nat.div_pow_of_pos _ _ he) he0

/-- If `k > 0`, then `(mn^k + 1)^b ≡ mbn^k + 1 (mod n^{k + 1})`. -/
theorem pow_mod_eq_of_modeq_mul_pow_add_one (hk : k > 0) (n m b : ℕ) :
    (m * n ^ k + 1) ^ b ≡ m * b * n ^ k + 1 [MOD n ^ (k + 1)] := by
  ---- Induction on `b`; the base case is trivial.
  induction b with
  | zero => rw [Nat.pow_zero, Nat.mul_zero, Nat.zero_mul]
  | succ b b_ih => ?_
  ---- For the induction step, just do a lot of calculations.
  calc (m * n ^ k + 1) ^ b * (m * n ^ k + 1)
    _ ≡ (m * b * n ^ k + 1) * (m * n ^ k + 1) [MOD n ^ (k + 1)] := b_ih.mul_right _
    _ = m * b * n ^ k * (m * n ^ k) + (m * (b + 1) * n ^ k + 1) := by
      rw [Nat.succ_mul, Nat.mul_succ, Nat.add_assoc,
        Nat.mul_succ, Nat.add_mul, Nat.add_assoc]
    _ = m * b * m * n ^ (k - 1) * n ^ (k + 1) + (m * (b + 1) * n ^ k + 1) := by
      rw [Nat.add_left_inj, Nat.mul_mul_mul_comm, ← Nat.pow_add, Nat.mul_assoc (_ * m),
        ← Nat.pow_add, Nat.add_left_comm, Nat.sub_add_cancel hk]
    _ ≡ m * (b + 1) * n ^ k + 1 [MOD n ^ (k + 1)] := Nat.mul_modulus_add_modEq_iff.mpr rfl

/-- If `k > 0` and `a ≡ 1 (mod n^k)`, then `a^n ≡ 1 (mod n^{k + 1})`. -/
theorem pow_modeq_one_of_modeq_one (hk : k > 0) (h : a ≡ 1 [MOD n ^ k]) :
    a ^ n ≡ 1 [MOD n ^ (k + 1)] := by
  cases a with
  | zero =>
      replace h : n ^ k ∣ 1 := Nat.dvd_of_mod_eq_zero h.symm
      rw [Nat.dvd_one, Nat.pow_eq_one, or_iff_left hk.ne.symm] at h
      rw [h, Nat.one_pow]; rfl
  | succ b =>
      obtain ⟨m, rfl⟩ : n ^ k ∣ b := Nat.add_modEq_right_iff.mp h
      calc (n ^ k * m + 1) ^ n
        _ = (m * n ^ k + 1) ^ n := by rw [Nat.mul_comm]
        _ ≡ m * n * n ^ k + 1 [MOD n ^ (k + 1)] :=
          pow_mod_eq_of_modeq_mul_pow_add_one hk _ _ _
        _ ≡ 1 [MOD n ^ (k + 1)] := by
          rw [Nat.mul_assoc, ← Nat.pow_add_one', Nat.add_modEq_right_iff]
          exact Nat.dvd_mul_left _ _

/-- If `k > 0` and `a ≡ 1 (mod n^k)`, then `a^{n^t} ≡ 1 (mod n^{k + t})`. -/
theorem pow_pow_modeq_one_of_modeq_one (hk : k > 0) (h : a ≡ 1 [MOD n ^ k]) (t) :
    a ^ (n ^ t) ≡ 1 [MOD n ^ (k + t)] := by
  induction t with
  | zero => rwa [Nat.pow_zero, Nat.pow_one, Nat.add_zero]
  | succ t t_ih => calc a ^ (n ^ t * n)
      _ = (a ^ (n ^ t)) ^ n := Nat.pow_mul _ _ _
      _ ≡ 1 [MOD n ^ (k + t + 1)] := pow_modeq_one_of_modeq_one (Nat.add_pos_left hk t) t_ih

/-- For any `k`, we have `(n + 1)^{n^k} ≡ 1 (mod n^{k + 1})`. -/
theorem add_one_pow_pow_modeq_one (n k) : (n + 1) ^ (n ^ k) ≡ 1 [MOD n ^ (k + 1)] := by
  refine Nat.add_comm k 1 ▸ pow_pow_modeq_one_of_modeq_one Nat.one_pos ?_ k
  rw [Nat.pow_one, Nat.add_modEq_right_iff]

/-- If `n > 1` and `k > 0`, then `(n + 1)^{n^k} % n^k = 1`. -/
theorem add_one_pow_pow_mod_pow_eq_one (hn : n > 1) (hk : k > 0) :
    (n + 1) ^ (n ^ k) % n ^ k = 1 := by
  calc (n + 1) ^ (n ^ k) % n ^ k
    _ = 1 % n ^ k := (add_one_pow_pow_modeq_one _ _).of_dvd ⟨n, rfl⟩
    _ = 1 := Nat.mod_eq_of_lt (Nat.one_lt_pow (Nat.ne_zero_of_lt hk) hn)

/-- If `n > 1` is odd and `k > 0`, then `⌊(n + 1)^{n^k}/n^k⌋` is odd. -/
theorem case_even (hn : n > 1) (hn0 : 2 ∣ n + 1) (hk : k > 0) :
    (n + 1) ^ (n ^ k) / n ^ k % 2 = 1 :=
  div_odd_of_even_mod_eq_one
    (Nat.dvd_trans hn0 (Nat.div_pow_of_pos _ _ (Nat.pow_pos (Nat.zero_lt_of_lt hn))))
    (add_one_pow_pow_mod_pow_eq_one hn hk)

/-- Final solution -/
theorem final_solution (hn : n > 1) (N) : ∃ k > N, n ^ k / k % 2 = 1 := by
  ---- If `n` is odd, pick `k = n^N`.
  obtain hn0 | hn0 : n % 2 = 1 ∨ n % 2 = 0 := (Nat.mod_two_eq_zero_or_one n).symm
  · exact ⟨n ^ N, Nat.lt_pow_self hn, case_odd hn hn0 N⟩
  ---- If `n = 2`, then pick `k = 3 4^{N + 1}`.
  obtain rfl | hn1 : 2 = n ∨ n > 2 := Nat.eq_or_lt_of_le hn
  · refine ⟨3 * 4 ^ (N + 1), ?_, case_two (Nat.succ_pos N)⟩
    calc N
      _ < 4 ^ N := Nat.lt_pow_self (by decide)
      _ ≤ 12 * 4 ^ N := Nat.le_mul_of_pos_left _ (by decide)
      _ = 3 * 4 ^ (N + 1) := by rw [Nat.pow_succ', ← Nat.mul_assoc]
  ---- If `n > 2`, then pick `k = (n - 1)^{N + 1}`.
  cases n with | zero => exact absurd hn1 (Nat.not_lt_zero _) | succ n => ?_
  replace hn1 : n > 1 := Nat.succ_lt_succ_iff.mp hn1
  exact ⟨n ^ (N + 1), Nat.lt_of_add_right_lt (Nat.lt_pow_self hn1),
    case_even hn1 (Nat.dvd_of_mod_eq_zero hn0) (Nat.succ_pos N)⟩
