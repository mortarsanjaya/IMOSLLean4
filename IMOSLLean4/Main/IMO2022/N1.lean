/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Bounds.Defs
import Mathlib.Tactic.NormNum.Prime

/-!
# IMO 2022 N1

Find the smallest positive integer $N$ with the following property: there exist
  positive divisors $d_1 > d_2 > d_3$ of $N$ satisfying $d_1 + d_2 + d_3 = 2022$.

### Answer

$1344$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2022SL.pdf).
Given a positive integer $n$, a positive integer $N$ is called $n$-`Norwegian` if
  there exist positive divisors $d_1 > d_2 > d_3$ of $N$ satisfying $d_1 + d_2 + d_3 = n$.
Using the official solution, we show that if $p > 19$ is a prime with $p ≡ 1 \pmod{6}$,
  then the smallest $6p$-Norwegian integer is $4(p - 1)$.
This more general version is implemented as
  `IMOSL.IMO2022N1.IsLeast_Norwegian_prime_one_mod_six`.
-/

namespace IMOSL
namespace IMO2022N1

/-! ### Extra lemmas -/

/-- If `k ≤ 4` and `k ≡ 2 (mod 3)`, then `k = 2`. -/
theorem eq_two_of_le_four_modeq_three : ∀ {k}, (hk : k ≤ 4) → (hk0 : k % 3 = 2) → k = 2 := by
  decide

/-- If `3q + 2 ∣ 12`, then `q = 0`. -/
theorem eq_zero_of_three_mul_add_two_dvd_12 (hq : 3 * q + 2 ∣ 12) : q = 0 := by
  have hq0 : 3 * q < 12 := calc
    3 * q < 3 * q + 2 := Nat.lt_add_of_pos_right Nat.two_pos
    _     ≤ 12 := Nat.le_of_dvd (Nat.succ_pos 11) hq
  replace hq0 : q < 4 := Nat.lt_of_mul_lt_mul_left hq0
  revert hq; revert q; decide

/-- If `(3q + 2)d = 12p` where `p` is prime and `p ≡ 1 (mod 6)`, then `q = 0` or `d = 6`. -/
theorem q_eq_zero_or_d_eq_six_of_Diophantine
    (hp : Nat.Prime p) (hp0 : p % 6 = 1) (h : (3 * q + 2) * d = 12 * p) :
    q = 0 ∨ d = 6 := by
  ---- We claim that `p ∣ d` yields `q = 0` while `gcd(p, d) = 1` yields `d = 6`.
  apply (Nat.coprime_or_dvd_of_prime hp d).symm.imp (λ h0 ↦ ?_) (λ h0 ↦ ?_)
  ---- Case 1: `p ∣ d`.
  · -- Then `3q + 2 ∣ 12`, forcing `q = 0`.
    replace hp : 0 < d :=
      Nat.pos_of_mul_pos_left ((Nat.mul_pos (Nat.zero_lt_succ 11) hp.pos).trans_eq h.symm)
    replace h : (3 * q + 2) * d ∣ 12 * d := h.dvd.trans (Nat.mul_dvd_mul_left 12 h0)
    replace h : 3 * q + 2 ∣ 12 := Nat.dvd_of_mul_dvd_mul_right hp h
    exact eq_zero_of_three_mul_add_two_dvd_12 h
  ---- Case 2: `gcd(p, d) = 1`.
  · -- Working mod `3` on the equality `(3q + 2)d = 12p` gives `3 ∣ d`. Now write `d = 3t`.
    obtain ⟨t, rfl⟩ : 3 ∣ d := by
      replace h0 : Nat.Coprime 3 (3 * q + 2) := by
        rw [Nat.Coprime, Nat.gcd_mul_left_add_right]; rfl
      exact h0.dvd_of_dvd_mul_left ⟨4 * p, h.trans (Nat.mul_assoc 3 4 p)⟩
    -- Then the new equality is `(3q + 2)t = 4p`.
    replace h : (3 * q + 2) * t = 4 * p := by
      rw [← Nat.mul_right_inj (Nat.succ_ne_zero 2), Nat.mul_left_comm, h, ← Nat.mul_assoc]
    -- Since `gcd(p, 3t) = 1`, `(3q + 2)t = 4p` gives `t ∣ 4` and then `t ≤ 4`.
    replace h0 : p.Coprime t := h0.coprime_mul_left_right
    replace h0 : t ∣ 4 := h0.symm.dvd_of_dvd_mul_right ⟨_, h.symm.trans (Nat.mul_comm _ _)⟩
    replace h0 : t ≤ 4 := Nat.le_of_dvd (Nat.succ_pos 3) h0
    -- Since `(3q + 2)t = 4p`, working mod `3` gives `t ≡ 2 (mod 3)`.
    replace h : (2 * t) % 3 = 1 :=
      calc (2 * t) % 3
      _ = ((3 * q + 2) % 3 * t) % 3 := by rw [Nat.mul_add_mod]
      _ = (4 * p) % 3 := by rw [Nat.mod_mul_mod, h]
      _ = p % 3 := by rw [← Nat.mod_mul_mod, Nat.one_mul]
      _ = (p % 6) % 3 := (Nat.mod_mod_of_dvd _ ⟨2, rfl⟩).symm
      _ = 1 % 3 := congrArg (· % 3) hp0
    replace h : t % 3 = 2 := by
      calc t % 3
      _ = (4 * t) % 3 := by rw [← Nat.mod_mul_mod, Nat.one_mul]
      _ = 2 := by rw [Nat.mul_assoc 2 2, ← Nat.mul_mod_mod, h]
    -- Since `t ≤ 4` and `t ≡ 2 (mod 3)`, we get `t = 2`, and we are done.
    exact congrArg (3 * ·) (eq_two_of_le_four_modeq_three h0 h)





/-! ### Start of the problem -/

/-- A positive integer `N` is called `n`-*Norwegian* if there exist
  positive divisors `d_1 > d_2 > d_3` of `N` such that `d_1 + d_2 + d_3 = n`.
We implement it as a data containing three positive integers instead of a proposition.
Then being `n`-Norwegian corresponds to `Nonempty (Norwegian n N)`. -/
@[ext] structure Norwegian (n N : ℕ) where
  divisor : Fin 3 → ℕ
  divisor2lt1 : divisor 2 < divisor 1
  divisor1lt0 : divisor 1 < divisor 0
  divisor_spec : ∀ i, divisor i ∣ N
  divisor_sum : divisor 0 + divisor 1 + divisor 2 = n

/-- `(24k, 12k, 6)` is a Norwegian data for `6(6k + 1)`. -/
def Norwegian_std_six_times_6k_add_one (k : ℕ) (hk : 0 < k) :
    Norwegian (6 * (6 * k + 1)) (24 * k) where
  divisor := ![24 * k, 12 * k, 6]
  divisor2lt1 := (by decide : 6 < 12).trans_le (Nat.le_mul_of_pos_right 12 hk)
  divisor1lt0 := Nat.mul_lt_mul_of_pos_right (by decide) hk
  divisor_spec i := match i with
    | 0 => Nat.dvd_refl (24 * k)
    | 1 => ⟨2, (Nat.mul_right_comm 12 k 2).symm⟩
    | 2 => ⟨4 * k, Nat.mul_assoc 6 4 k⟩
  divisor_sum := calc 24 * k + 12 * k + 6
    _ = 4 * (6 * k) + 2 * (6 * k) + 6 := by rw [← Nat.mul_assoc, ← Nat.mul_assoc]
    _ = 6 * (6 * k + 1) := by rw [Nat.mul_succ, ← Nat.add_mul]


namespace Norwegian

section

variable (hN : 0 < N) (X : Norwegian n N)
include hN

/-! ### Basic properties -/

/-- The `d_i`'s are positive. -/
theorem divisor_pos (i) : 0 < X.divisor i :=
  Nat.pos_of_dvd_of_pos (X.divisor_spec i) hN

/-- The `d_i`'s are less than or equal to `N`. -/
theorem divisor_le (i) : X.divisor i ≤ N :=
  Nat.le_of_dvd hN (X.divisor_spec i)

/-- The "quotient" of the divisors: `q_i = N/d_i`. -/
def divisor_quot (i : Fin 3) : ℕ := N / X.divisor i

omit hN in
/-- The number `q_i` sastisfies `q_i d_i = N`. -/
theorem divisor_quot_spec (i) : X.divisor_quot i * X.divisor i = N :=
  Nat.div_mul_cancel (X.divisor_spec i)

/-- The number `q_i` is positive. -/
theorem divisor_quot_pos (i) : 0 < X.divisor_quot i :=
  Nat.div_pos (X.divisor_le hN i) (X.divisor_pos hN i)

/-- We have `q_0 < q_1`. -/
theorem divisor_quot0lt1 : X.divisor_quot 0 < X.divisor_quot 1 :=
  (Nat.div_lt_div_left hN.ne.symm (X.divisor_spec 0) (X.divisor_spec 1)).mpr X.divisor1lt0

/-- We have `q_1 < q_2`. -/
theorem divisor_quot1lt2 : X.divisor_quot 1 < X.divisor_quot 2 :=
  (Nat.div_lt_div_left hN.ne.symm (X.divisor_spec 1) (X.divisor_spec 2)).mpr X.divisor2lt1

/-- We have `q_1 ≥ 2`. -/
theorem two_le_divisor_quot1 : 2 ≤ X.divisor_quot 1 := calc
  1 ≤ X.divisor_quot 0 := X.divisor_quot_pos hN 0
  _ < X.divisor_quot 1 := X.divisor_quot0lt1 hN

end





/-! ### Solution for the main problem -/

/-- If `13N < 12n`, then `q_0 = 1`. -/
theorem divisor0_eq_one_of_13N_lt_12n
    (hN : 0 < N) (h : 13 * N < 12 * n) (X : Norwegian n N) :
    X.divisor_quot 0 = 1 := by
  ---- Since `q_0 > 0`, we only have to show that `q_0 > 1` does not hold.
  refine Nat.eq_of_le_of_lt_succ (X.divisor_quot_pos hN 0) (Nat.lt_of_not_le λ h0 ↦ ?_)
  ---- Suppose that `q_0 > 1`. Then `q_1 ≥ 3` and `q_2 ≥ 4`.
  have h1 : 3 ≤ X.divisor_quot 1 := Nat.lt_of_le_of_lt h0 (X.divisor_quot0lt1 hN)
  have h2 : 4 ≤ X.divisor_quot 2 := Nat.lt_of_le_of_lt h1 (X.divisor_quot1lt2 hN)
  ---- Then `12d_0 ≤ 6N`, `12d_1 ≤ 4N`, and `12d_2 ≤ 3N`, but their sum is `12n > 13N`.
  apply h.not_ge
  calc 12 * n
  _ = 12 * (X.divisor 0 + X.divisor 1 + X.divisor 2) := by rw [X.divisor_sum]
  _ = 12 * X.divisor 0 + 12 * X.divisor 1 + 12 * X.divisor 2 := by
    rw [Nat.mul_add, Nat.mul_add]
  _ = 6 * (2 * X.divisor 0) + 4 * (3 * X.divisor 1) + 3 * (4 * X.divisor 2) := by
    iterate 3 rw [← Nat.mul_assoc]
  _ ≤ 6 * (X.divisor_quot 0 * X.divisor 0) + 4 * (X.divisor_quot 1 * X.divisor 1)
      + 3 * (X.divisor_quot 2 * X.divisor 2) := by
    refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
    all_goals exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by assumption))
  _ = 6 * N + 4 * N + 3 * N := by iterate 3 rw [X.divisor_quot_spec]
  _ = 13 * N := by rw [← Nat.add_mul, ← Nat.add_mul]

/-- If `3N ≤ 2n`, then `q_1 ≤ 3`. -/
theorem divisor1_le_three_of_3N_le_2n (hN : 0 < N) (h : 3 * N ≤ 2 * n) (X : Norwegian n N) :
    X.divisor_quot 1 ≤ 3 := by
  ---- Assume `q_1 ≥ 4`, and get `q_2 > 4`.
  refine Nat.le_of_not_lt λ (h0 : 4 ≤ X.divisor_quot 1) ↦ ?_
  have h1 : 4 < X.divisor_quot 2 := Nat.lt_of_le_of_lt h0 (X.divisor_quot1lt2 hN)
  ---- Then `4d_0 ≤ 4N` and `4d_2 < 4d_1 ≤ N`, but their sum is `4n ≥ 6N`.
  apply (Nat.mul_le_mul_left 2 h).not_gt
  calc 2 * (2 * n)
  _ = 4 * (X.divisor 0 + X.divisor 1 + X.divisor 2) := by rw [← Nat.mul_assoc, X.divisor_sum]
  _ = 4 * X.divisor 0 + 4 * X.divisor 1 + 4 * X.divisor 2 := by rw [Nat.mul_add, Nat.mul_add]
  _ < 4 * N + X.divisor_quot 1 * X.divisor 1 + X.divisor_quot 2 * X.divisor 2 := by
    refine Nat.add_lt_add_of_le_of_lt (Nat.add_le_add ?_ ?_) ?_
    exacts [Nat.mul_le_mul_left 4 (X.divisor_le hN 0), Nat.mul_le_mul_right _ h0,
      Nat.mul_lt_mul_of_pos_right h1 (X.divisor_pos hN 2)]
  _ = 4 * N + N + N := by rw [X.divisor_quot_spec, X.divisor_quot_spec]
  _ = 6 * N := by rw [← Nat.succ_mul, ← Nat.succ_mul]
  _ = 2 * (3 * N) := Nat.mul_assoc 2 3 N

/-- If `3N < 2n` and `q_1 = 3`, then `q_2 ≤ 5`. -/
theorem divisor2_le_five_of_3N_lt_2n_and_divisor1_eq_three
    (hN : 0 < N) (h : 3 * N < 2 * n) (X : Norwegian n N) (hXq1 : X.divisor_quot 1 = 3) :
    X.divisor_quot 2 ≤ 5 := by
  ---- If `q_2 ≥ 6`, we claim that `3N ≥ 2n` from `9N ≥ 6n`.
  refine Nat.le_of_not_lt λ h0 ↦ h.not_ge (Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos 2))
  ---- Now calculate to prove `9N ≥ 6n`.
  calc 3 * (2 * n)
    _ = 6 * n := (Nat.mul_assoc 3 2 n).symm
    _ = 6 * (X.divisor 0 + X.divisor 1 + X.divisor 2) := by rw [X.divisor_sum]
    _ = 6 * X.divisor 0 + 6 * X.divisor 1 + 6 * X.divisor 2 := by simp_rw [Nat.mul_add]
    _ ≤ 6 * N + 2 * N + N := by
      ---- Split into `6q_0 ≤ 6N`, `6q_1 = 2N`, and `6q_2 ≤ N`, respectively.
      refine Nat.add_le_add (Nat.add_le_add ?_ ?_) ?_
      · exact Nat.mul_le_mul_left _ (X.divisor_le hN 0)
      · calc _ = 2 * (3 * X.divisor 1) := Nat.mul_assoc 2 3 _
             _ = 2 * N := by simp_rw [← hXq1, X.divisor_quot_spec]
             _ ≤ 2 * N := Nat.le_refl _
      · exact (Nat.mul_le_mul_right _ h0).trans_eq (X.divisor_quot_spec 2)
    _ = 3 * (3 * N) := by rw [← Nat.add_mul, ← Nat.succ_mul, ← Nat.mul_assoc]

/-- If `19 ∤ n`, `q_0 = 1`, and `q_1 = 3`, then `q_2 ≠ 4`. -/
theorem divisor2_ne_four_of_divisor01_eq_one_three (hn19 : ¬19 ∣ n)
    (X : Norwegian n N) (hXq0 : X.divisor_quot 0 = 1) (hXq1 : X.divisor_quot 1 = 3) :
    X.divisor_quot 2 ≠ 4 := by
  ---- Suppose that `q_2 = 4`. Write down `d_0 = 3d_1 = 4d_2 = N`.
  intro hXq2
  replace hXq0 : X.divisor 0 = N := by simp_rw [← X.divisor_quot_spec 0, hXq0, Nat.one_mul]
  replace hXq1 : 3 * X.divisor 1 = N := by simp_rw [← X.divisor_quot_spec 1, hXq1]
  replace hXq2 : 4 * X.divisor 2 = N := by simp_rw [← X.divisor_quot_spec 2, hXq2]
  ---- Then direct calculation implies `19N = 12n`.
  have h : 12 * n = 19 * N := calc
    _ = 12 * (X.divisor 0 + X.divisor 1 + X.divisor 2) := by rw [X.divisor_sum]
    _ = 12 * X.divisor 0 + 12 * X.divisor 1 + 12 * X.divisor 2 := by simp_rw [Nat.mul_add]
    _ = 12 * X.divisor 0 + 4 * (3 * X.divisor 1) + 3 * (4 * X.divisor 2) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc]
    _ = 19 * N := by rw [hXq0, hXq1, hXq2, ← Nat.add_mul, ← Nat.add_mul]
  ---- Thus `19 ∣ 8 * 12n`,  which implies `19 ∣ n` as `8 * 12 ≡ 1 (mod 19)`.
  refine hn19 (Nat.dvd_iff_mod_eq_zero.mpr ?_)
  calc n % 19
  _ = 8 * (12 * n) % 19 := by rw [← Nat.mul_assoc, ← Nat.mod_mul_mod, Nat.one_mul]
  _ = 0 := by rw [h, ← Nat.mul_mod_mod, Nat.mul_mod_right]

/-- If `23 ∤ n`, `q_0 = 1`, and `q_1 = 3`, then `q_2 ≠ 5`. -/
theorem divisor2_ne_five_of_divisor01_eq_one_three (hn23 : ¬23 ∣ n)
    (X : Norwegian n N) (hXq0 : X.divisor_quot 0 = 1) (hXq1 : X.divisor_quot 1 = 3) :
    X.divisor_quot 2 ≠ 5 := by
  ---- Suppose that `q_2 = 4`. Write down `d_0 = 3d_1 = 4d_2 = N`.
  intro hXq2
  replace hXq0 : X.divisor 0 = N := by simp_rw [← X.divisor_quot_spec 0, hXq0, Nat.one_mul]
  replace hXq1 : 3 * X.divisor 1 = N := by simp_rw [← X.divisor_quot_spec 1, hXq1]
  replace hXq2 : 5 * X.divisor 2 = N := by simp_rw [← X.divisor_quot_spec 2, hXq2]
  ---- Then direct calculation implies `19N = 12n`.
  have h : 15 * n = 23 * N := calc
    _ = 15 * (X.divisor 0 + X.divisor 1 + X.divisor 2) := by rw [X.divisor_sum]
    _ = 15 * X.divisor 0 + 15 * X.divisor 1 + 15 * X.divisor 2 := by simp_rw [Nat.mul_add]
    _ = 15 * X.divisor 0 + 5 * (3 * X.divisor 1) + 3 * (5 * X.divisor 2) := by
      rw [← Nat.mul_assoc, ← Nat.mul_assoc]
    _ = 23 * N := by rw [hXq0, hXq1, hXq2, ← Nat.add_mul, ← Nat.add_mul]
  ---- Thus `23 ∣ 20 * 15n`, which implies `23 ∣ n` as `20 * 15 ≡ 1 (mod 23)`.
  refine hn23 (Nat.dvd_iff_mod_eq_zero.mpr ?_)
  calc n % 23
  _ = 20 * (15 * n) % 23 := by rw [← Nat.mul_assoc, ← Nat.mod_mul_mod, Nat.one_mul]
  _ = 0 := by rw [h, ← Nat.mul_mod_mod, Nat.mul_mod_right]

/-- If `3N < 2n`, `19 ∤ n`, and `23 ∤ n`, then `q_0 = 1` and `q_1 = 2`. -/
theorem divisor01_eq_of_3N_le_2n_of_19_and_23_not_dvd_n
    (hN : 0 < N) (h : 3 * N < 2 * n) (hn19 : ¬19 ∣ n) (hn23 : ¬23 ∣ n) (X : Norwegian n N) :
    X.divisor_quot 0 = 1 ∧ X.divisor_quot 1 = 2 := by
  ---- First show that `q_0 = 1`.
  have h0 : X.divisor_quot 0 = 1 := by
    refine X.divisor0_eq_one_of_13N_lt_12n hN ?_
    calc 13 * N
    _ < 18 * N := Nat.mul_lt_mul_of_pos_right (by decide) hN
    _ = 6 * (3 * N) := Nat.mul_assoc 6 3 N
    _ ≤ 6 * (2 * n) := Nat.mul_le_mul_left 6 h.le
    _ = 12 * n := (Nat.mul_assoc 6 2 n).symm
  ---- Since `q_1 ≥ 2`, it remains to show that `q_1 < 3`.
  refine ⟨h0, ((X.two_le_divisor_quot1 hN).eq_of_not_lt λ h1 ↦ ?_).symm⟩
  ---- Suppose `q_1 ≥ 3`. We had `q_1 ≤ 3`, so now we have `q_1 = 3`.
  replace h1 : X.divisor_quot 1 = 3 := (X.divisor1_le_three_of_3N_le_2n hN h.le).antisymm h1
  ---- Then `q_2` is either `4`, `5`, or `> 5`.
  obtain h2 | h2 | h2 :
      X.divisor_quot 2 = 4 ∨ X.divisor_quot 2 = 5 ∨ 5 < X.divisor_quot 2 := by
    have h2 : 4 ≤ X.divisor_quot 2 := h1.symm.trans_lt (X.divisor_quot1lt2 hN)
    exact h2.eq_or_lt'.imp_right λ (h3 : 5 ≤ _) ↦ h3.eq_or_lt'
  ---- We have done all these cases before.
  exacts [X.divisor2_ne_four_of_divisor01_eq_one_three hn19 h0 h1 h2,
    X.divisor2_ne_five_of_divisor01_eq_one_three hn23 h0 h1 h2,
    h2.not_ge (X.divisor2_le_five_of_3N_lt_2n_and_divisor1_eq_three hN h h1)]

/-- If `n = 6p` and `N < 4p` where `p > 23` is prime, then `q_0 = 1` and `q_1 = 2`. -/
theorem divisor01_eq_of_n_eq_six_times_prime (hp : Nat.Prime p) (hp0 : 23 < p)
    (hN : 0 < N) (hN0 : N < 4 * p) (X : Norwegian (6 * p) N) :
    X.divisor_quot 0 = 1 ∧ X.divisor_quot 1 = 2 := by
  refine X.divisor01_eq_of_3N_le_2n_of_19_and_23_not_dvd_n hN ?_ ?_ ?_
  ---- First show that `3N < 2n = 12p`.
  · calc 3 * N
      _ < 3 * (4 * p) := Nat.mul_lt_mul_of_pos_left hN0 (Nat.succ_pos 2)
      _ = 2 * (6 * p) := by rw [← Nat.mul_assoc, ← Nat.mul_assoc]
  ---- Next show that `19 ∤ n = 6p`; follows since `p` is prime.
  · have h19 : Nat.Prime 19 := by decide
    replace hp0 : 19 < p := (by decide : 19 < 23).trans hp0
    exact h19.not_dvd_mul (by decide) λ h ↦ hp0.ne ((hp.dvd_iff_eq (by decide)).mp h).symm
  ---- Finally show that `23 ∤ n = 6p`; follows since `p` is prime.
  · have h23 : Nat.Prime 23 := by decide
    exact h23.not_dvd_mul (by decide) λ h ↦ hp0.ne ((hp.dvd_iff_eq (by decide)).mp h).symm

/-- If `n = 6p` and `N < 4p` with `p > 23` prime and `p ≡ 1 (mod 6)`, then `N = 4(p - 1)`. -/
theorem eq_Norwegian_std_six_times_6k_add_one
    (hp : Nat.Prime p) (hp0 : 23 < p) (hp1 : p % 6 = 1)
    (hN : 0 < N) (hN0 : N < 4 * p) (X : Norwegian (6 * p) N) :
    N = 4 * (p - 1) := by
  ---- We have `3N + 2d_2 = 2n = 12p`.
  have h : 3 * N + 2 * X.divisor 2 = 12 * p := by
    -- Recall that `q_0 = 1` and `q_1 = 2`.
    obtain ⟨hXq0, hXq1⟩ : X.divisor_quot 0 = 1 ∧ X.divisor_quot 1 = 2 :=
      X.divisor01_eq_of_n_eq_six_times_prime hp hp0 hN hN0
    -- Now do the calculations using `N = d_0 = 2d_1`.
    calc 3 * N + 2 * X.divisor 2
    _ = 2 * (X.divisor_quot 0 * X.divisor 0)
        + X.divisor_quot 1 * X.divisor 1 + 2 * X.divisor 2 := by
      rw [X.divisor_quot_spec, X.divisor_quot_spec, Nat.succ_mul]
    _ = 2 * X.divisor 0 + 2 * X.divisor 1 + 2 * X.divisor 2 := by
      rw [hXq0, hXq1, Nat.one_mul]
    _ = 2 * (6 * p) := by rw [← Nat.mul_add, ← Nat.mul_add, X.divisor_sum]
    _ = 12 * p := (Nat.mul_assoc 2 6 _).symm
  ---- It suffices to show that `d_2 = 6`.
  suffices X.divisor 2 = 6 by
    replace h : 3 * N = 12 * p - 2 * X.divisor 2 := Nat.eq_sub_of_add_eq h
    rwa [this, ← Nat.mul_pred, Nat.mul_assoc 3 4,
      Nat.mul_left_cancel_iff (Nat.succ_pos 2)] at h
  ---- Now rewrite the equality as `(3q_2 + 2) d_2 = 12p`.
  replace h : (3 * X.divisor_quot 2 + 2) * X.divisor 2 = 12 * p := by
    rwa [Nat.add_mul, Nat.mul_assoc, X.divisor_quot_spec]
  /- We have shown separately that this equation forces `q_2 = 0` or `d_2 = 2`.
    But `q_2 > 0`, so `d_2 = 2`. -/
  exact (q_eq_zero_or_d_eq_six_of_Diophantine hp hp1 h).resolve_left
    (X.divisor_quot_pos hN 2).ne.symm

end Norwegian





/-! ### Summary -/

/-- If `p = 6k + 1` is prime, where `k ≥ 4`,
  then the smallest `6(6k + 1)`-Norwegian number is `24k`. -/
theorem IsLeast_Norwegian_prime_one_mod_six (hk : Nat.Prime (6 * k + 1)) (hk0 : 4 ≤ k) :
    IsLeast {N > 0 | Nonempty (Norwegian (6 * (6 * k + 1)) N)} (24 * k) := by
  ---- First show that `24k` is positive and `6(6k + 1)`-Norwegian.
  refine ⟨?_, ?_⟩
  · have hk1 : 0 < k := Nat.zero_lt_of_lt hk0
    exact ⟨Nat.mul_pos (Nat.succ_pos 23) hk1, ⟨Norwegian_std_six_times_6k_add_one k hk1⟩⟩
  ---- Now suppose that `N` is `6(6k + 1)`-Norwegian.
  rintro N ⟨hN, ⟨X⟩⟩
  ---- Edit `24k` to `4(6k)`.
  suffices 4 * (6 * k) ≤ N by rwa [Nat.mul_assoc 4 6 k]
  ---- If `N ≥ 4(6k + 1)`, then trivially `N ≥ 24k`, so now assume `N < 4(6k + 1)`.
  obtain h | h : 4 * (6 * k + 1) ≤ N ∨ N < 4 * (6 * k + 1) := le_or_gt _ _
  · exact Nat.le_of_add_right_le h
  ---- Then as we worked up earlier, we actually get `N = 24k`.
  · replace hk0 : 23 < 6 * k + 1 := calc
      _ < 25 := Nat.lt_add_of_pos_right Nat.two_pos
      _ ≤ 6 * k + 1 := Nat.succ_le_succ (Nat.mul_le_mul_left 6 hk0)
    have hk1 : (6 * k + 1) % 6 = 1 := Nat.mul_add_mod_self_left _ _ _
    refine (X.eq_Norwegian_std_six_times_6k_add_one hk hk0 hk1 hN h).ge

/-- Final solution -/
theorem final_solution : IsLeast {N > 0 | Nonempty (Norwegian 2022 N)} 1344 :=
  IsLeast_Norwegian_prime_one_mod_six (k := 56) (by norm_num) (by decide)
