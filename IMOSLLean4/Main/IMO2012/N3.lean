/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
# IMO 2012 N3

Determine all integers $m > 1$ such that $n ∣ \binom{n}{m - 2n}$ for every $n ≤ m/2$.

### Answer

Primes.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2012SL.pdf).
Note that the original problem restricts $n$ to the range $m/3 ≤ n ≤ m/2$.
We do not add the restriction since we use the convention $\binom{n}{k} = 0$ for $k > n$.
This is also the convention used by `Nat.choose`.
-/

namespace IMOSL
namespace IMO2012N3

/-! ### Extra lemmas -/

/-- For `p, k, r ∈ ℕ` with `p` prime and `r < p`, we have `p ∤ (pk + 1) … (pk + r)`. -/
theorem prime_not_dvd_ascFactorial (hp : Nat.Prime p) (k : ℕ) (hr : r < p) :
    ¬p ∣ (p * k + 1).ascFactorial r := by
  ---- The proof is by induction on `r`; the details are easy.
  induction r with | zero => exact hp.not_dvd_one | succ r r_ih => ?_
  refine hp.not_dvd_mul ?_ (r_ih (Nat.lt_of_succ_lt hr))
  rw [Nat.add_right_comm, Nat.add_assoc, Nat.dvd_add_right ⟨k, rfl⟩]
  exact Nat.not_dvd_of_pos_of_lt (Nat.succ_pos r) hr

/-- If `p` is prime and `k ≠ 0` then `pk ∤ C(pk, p)`. -/
theorem prime_choose_not_dvd (hp : Nat.Prime p) (hk : k ≠ 0) :
    ¬(p * k) ∣ (p * k).choose p := by
  intro h
  have h0 : p * k.pred + p = p * k := by rw [← Nat.mul_succ, Nat.succ_pred hk]
  replace h : p * (p * k) ∣ (p * k.pred + 1).ascFactorial (p - 1) * (p * k) := calc
    _ ∣ p.factorial * (p * k).choose p :=
      Nat.mul_dvd_mul (Nat.dvd_factorial hp.pos (Nat.le_refl p)) h
    _ = p.factorial * (p * k.pred + p).choose p := by rw [h0]
    _ = (p * k.pred + 1).ascFactorial (p - 1 + 1) := by
      rw [Nat.ascFactorial_eq_factorial_mul_choose, Nat.sub_add_cancel hp.one_le]
    _ = (p * k.pred + 1).ascFactorial (p - 1) * (p * k) := by
      rw [Nat.ascFactorial_succ, Nat.add_assoc,
        Nat.add_sub_cancel' hp.one_le, h0, Nat.mul_comm]
  replace h : p ∣ (p * k.pred + 1).ascFactorial (p - 1) :=
    Nat.dvd_of_mul_dvd_mul_right (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hk)) h
  exact prime_not_dvd_ascFactorial hp k.pred (Nat.pred_lt hp.ne_zero) h





/-! ### Start of the problem -/

/-- A non-negative integer `m` is called *good* if `n ∣ C(n, m - 2n)` for all `n ≤ m/2`. -/
def good (m : ℕ) := ∀ n ≤ m / 2, n ∣ Nat.choose n (m - 2 * n)

/-- A prime number is good. -/
theorem prime_is_good (hp : Nat.Prime p) : good p := by
  ---- If `p = 2`, then we only need to check `n = 0` and `n = 1`.
  obtain rfl | ⟨k, rfl⟩ : p = 2 ∨ Odd p := hp.eq_two_or_odd'
  · intro n hn
    obtain rfl | rfl : n = 0 ∨ n = 1 := Nat.le_one_iff_eq_zero_or_eq_one.mp hn
    all_goals exact Nat.dvd_refl _
  ---- Now suppose `p = 2k + 1` is odd. If `n = 0` then we are done since `p > 0`.
  intro n hnk
  obtain rfl | hn : n = 0 ∨ n > 0 := Nat.eq_zero_or_pos n
  · exact Nat.dvd_refl 0
  ---- Now suppose `n > 0`. First note that `n ≤ p/2` implies `2n ≤ 2k`.
  replace hnk : n ≤ k := by rwa [Nat.mul_add_div Nat.two_pos] at hnk
  replace hnk : 2 * n ≤ 2 * k := Nat.mul_le_mul_left 2 hnk
  ---- Consider `n ∣ (p - 2n) C(n, p - 2n)`; the ratio is `C(n - 1, p - 2n - 1)`.
  have h : n ∣ n.choose (2 * k + 1 - 2 * n) * (2 * k + 1 - 2 * n) := by
    refine ⟨n.pred.choose (2 * k - 2 * n), ?_⟩
    replace hn : n.pred.succ = n := Nat.succ_pred_eq_of_pos hn
    calc n.choose (2 * k + 1 - 2 * n) * (2 * k + 1 - 2 * n)
      _ = n.pred.succ.choose (2 * k - 2 * n + 1) * (2 * k - 2 * n + 1) := by
        rw [hn, Nat.sub_add_comm hnk]
      _ = n * n.pred.choose (2 * k - 2 * n) := by
        rw [← Nat.add_one_mul_choose_eq, ← Nat.succ_eq_add_one, hn]
  ---- But `n` and `p - 2n` are coprime.
  have h0 : Nat.Coprime (2 * k + 1 - 2 * n) n := by
    replace hnk : 2 * n ≤ 2 * k + 1 := hnk.trans (Nat.le_succ _)
    have hnk0 : n < 2 * k + 1 := calc
      n < 2 * n := (Nat.lt_mul_iff_one_lt_left hn).mpr Nat.one_lt_two
      _ ≤ 2 * k + 1 := hnk
    rw [← Nat.coprime_add_mul_right_left _ _ 2,
      Nat.sub_add_cancel hnk, hp.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt hn hnk0
  ---- Thus we are done.
  exact h0.symm.dvd_of_dvd_mul_right h

/-- If `2k` is good, then `k = 1`. -/
theorem good_two_mul_imp (hk : good (2 * k)) : k = 1 := by
  ---- Indeed, just plug `n = k` and see.
  specialize hk k (Nat.mul_div_right k Nat.two_pos).ge
  rwa [Nat.sub_self, Nat.choose_zero_right, Nat.dvd_one] at hk

/-- If `p(2k + 1)` is good where `p` is prime, then `k = 0`. -/
theorem good_prime_mul_odd_imp (hp : Nat.Prime p) (hpk : good (p * (2 * k + 1))) :
    k = 0 := by
  ---- Suppose for the sake of contradiction that `k ≠ 0`.
  by_contra hk
  ---- Plug `n = pk`; we first need to check that `pk ≤ p(2k + 1)/2`.
  specialize hpk (p * k) ?_
  · calc p * k
      _ = p * ((2 * k + 1) / 2) := by rw [Nat.mul_add_div Nat.two_pos]; rfl
      _ ≤ p * (2 * k + 1) / 2 := Nat.mul_div_le_mul_div_assoc _ _ _
  ---- Then `pk` divides `C(pk, p)`.
  replace hpk : p * k ∣ (p * k).choose p := by
    rwa [Nat.mul_succ, Nat.mul_left_comm, Nat.add_sub_cancel_left] at hpk
  ---- This is known to be false for `k > 0`; see `prime_choose_not_dvd`.
  exact prime_choose_not_dvd hp hk hpk

/-- Final solution -/
theorem final_solution (hm : 1 < m) : good m ↔ Nat.Prime m := by
  ---- The `←` direction is solved via `prime_is_good`, so now focus on `→`.
  refine ⟨λ hm0 ↦ ?_, prime_is_good⟩
  ---- First solve the case where `m` is even using `good_two_mul_imp`.
  obtain ⟨k, rfl⟩ | hm1 : 2 ∣ m ∨ ¬2 ∣ m := dec_em _
  · obtain rfl : k = 1 := good_two_mul_imp hm0
    exact Nat.prime_two
  ---- Now suppose `m` is odd. Write `m = p(2k + 1)` where `p` is a prime.
  obtain ⟨p, hp, l, rfl⟩ : ∃ p, Nat.Prime p ∧ p ∣ m :=
    Nat.exists_prime_and_dvd hm.ne.symm
  obtain ⟨k, rfl⟩ : ∃ k, l = 2 * k + 1 := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd, Nat.odd_mul] at hm1
    exact hm1.2
  ---- By `good_prime_mul_odd_imp`, `k = 0`, so `m = p` is prime.
  obtain rfl : k = 0 := good_prime_mul_odd_imp hp hm0
  rwa [Nat.mul_one]
