/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Prime
import Mathlib.FieldTheory.Finite.Basic

/-!
# IMO 2015 N7

Find all positive integers $k$ such that there is a function $f : ℕ⁺ → ℕ⁺$
  satisfying $\gcd(f(m) + n, f(n) + m) ≤ k$ for all $m ≠ n$.

### Answer

$k ≥ 2$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2015SL.pdf).
As in the official booklet, functions satisfying the given condition is called $k$-*good*.
We tweak the definition of $g$ a bit: we use $g(1) = 24$.
This allows us to extend the definition of $g$ to the naturals, using $g(0) = 1$.
For the final contradiction, we directly show that the only possible odd divisor of
  $\gcd(f(m) + n, f(n) + m)$ is $1$, instead of looking at any odd prime divisor.
The occurences of $p - 1$ is replaced by totient function evaluated at the odd divisor.
-/

namespace IMOSL
namespace IMO2015N7

/-- A function `f : ℕ+ → ℕ+` is called `k`-good if
  `gcd(f(m) + n, f(n) + m) ≤ k` for all `m ≠ n`. -/
def good (k : ℕ+) (f : ℕ+ → ℕ+) := ∀ m n, m ≠ n → (f m + n).gcd (f n + m) ≤ k

/-- If `f` is `k`-good and `t ≥ k`, then `f` is `t`-good. -/
theorem good.of_ge (hf : good k f) (htk : t ≥ k) : good t f :=
  λ m n h ↦ (hf m n h).trans htk

/-- There exists no `1`-good function. -/
theorem not_good_one (f) : ¬good 1 f := by
  ---- Suppose `f` is `1`-good, which means `2 ∤ gcd(f(m) + n, f(n) + m)` for `m ≠ n`.
  intro h
  replace h (m n) (hmn : m ≠ n) : (f m + n).val % 2 = 1 ∨ (f n + m).val % 2 = 1 := by
    rw [← Nat.two_dvd_ne_zero, ← Nat.two_dvd_ne_zero, ← not_and_or, ← Nat.dvd_gcd_iff,
      ← PNat.gcd_coe, PNat.le_one_iff.mp (h m n hmn), Nat.two_dvd_ne_zero]; rfl
  ---- There exists `m` such that `f(2m)` is odd.
  obtain ⟨m, hm⟩ : ∃ m, (f (2 * m) : ℕ) % 2 = 1 := by
    obtain h0 | h0 : (f 2 + 4 : ℕ) % 2 = 1 ∨ (f 4 + 2 : ℕ) % 2 = 1 := h 2 4 (by decide)
    exacts [⟨1, (Nat.add_mul_mod_self_right _ 2 2).symm.trans h0⟩,
      ⟨2, (Nat.add_mul_mod_self_right _ 1 2).symm.trans h0⟩]
  ---- There exists `n` such that `f(2n + 1)` is even.
  obtain ⟨n, hn⟩ : ∃ n, (f (2 * n + 1) : ℕ) % 2 = 0 := by
    obtain h0 | h0 : (f 3 + 5 : ℕ) % 2 = 1 ∨ (f 5 + 3 : ℕ) % 2 = 1 := h 3 5 (by decide)
    · rw [Nat.succ_mod_two_eq_one_iff, Nat.add_mul_mod_self_right _ 2 2] at h0
      exact ⟨1, h0⟩
    · rw [Nat.succ_mod_two_eq_one_iff, Nat.add_mul_mod_self_right _ 1 2] at h0
      exact ⟨2, h0⟩
  ---- Then `f(2m) + (2n + 1)` and `f(2n + 1) + 2m` are both even; contradiction.
  apply Nat.zero_ne_one
  obtain h0 | h0 :
      (f (2 * m) + (2 * n + 1) : ℕ) % 2 = 1 ∨ (f (2 * n + 1) + 2 * m : ℕ) % 2 = 1 :=
    h (2 * m) (2 * n + 1) λ h0 ↦ Nat.two_mul_ne_two_mul_add_one (PNat.coe_inj.mpr h0)
  · rwa [← Nat.mod_add_mod, hm, Nat.add_left_comm, ← Nat.mul_succ, Nat.mul_mod_right] at h0
  · rwa [← Nat.mod_add_mod, hn, Nat.zero_add, Nat.mul_mod_right] at h0





/-! ### Construction of the $2$-good function -/

/-- The function `g : ℕ → ℕ` defined by `g(0) = 0` and `g(n + 1) = (2^{g(n) + 1})!`. -/
def goodHelperNat (n : ℕ) : ℕ := (λ n ↦ (2 ^ (n + 1)).factorial)^[n] 1

/-- `g(0) = 1`. -/
theorem goodHelperNat_zero : goodHelperNat 0 = 1 := rfl

/-- `g(n + 1) = (2^{g(n) + 1})!`. -/
theorem goodHelperNat_succ (n) :
    goodHelperNat (n + 1) = (2 ^ (goodHelperNat n + 1)).factorial :=
  Function.iterate_succ_apply' _ n 1

/-- `g` is strictly increasing. -/
theorem goodHelperNat_strictMono : StrictMono goodHelperNat := by
  refine strictMono_nat_of_lt_succ λ n ↦ ?_
  let N := goodHelperNat n
  calc N
    _ < N + 1 := N.lt_succ_self
    _ < 2 ^ (N + 1) := Nat.lt_two_pow_self
    _ ≤ (2 ^ (N + 1)).factorial := Nat.self_le_factorial (2 ^ (N + 1))
    _ = goodHelperNat (n + 1) := (goodHelperNat_succ n).symm

/-- For any `n`, we have `g(n) > n`. -/
theorem goodHelperNat_gt_self (n) : goodHelperNat n > n :=
  calc n
  _ < n + goodHelperNat 0 := Nat.lt_succ_self n
  _ ≤ goodHelperNat n := goodHelperNat_strictMono.add_le_nat n 0

/-- For any `n`, we have `g(n) > 0`. -/
theorem goodHelperNat_pos (n) : goodHelperNat n > 0 :=
  Nat.zero_lt_of_lt (goodHelperNat_gt_self n)

/-- For any `n`, we have `n + 1 < 2^{g(n) + 1}`. -/
theorem succ_lt_two_pow_goodHelperNat_succ (n) : n + 1 < 2 ^ (goodHelperNat n + 1) :=
  calc n + 1
  _ < goodHelperNat n + 1 := Nat.succ_lt_succ (goodHelperNat_gt_self n)
  _ < 2 ^ (goodHelperNat n + 1) := Nat.lt_two_pow_self



/-- The function `f(n) = 2^{g(n) + 1} - (n + 1)`, which we claim is `2`-good. -/
def goodFnNat (n : ℕ) := 2 ^ (goodHelperNat n + 1) - (n + 1)

/-- Over `ℕ`, it is convenient to write `f(n) + n + 1 = 2^{g(n) + 1}`. -/
theorem goodFnNat_spec (n) : goodFnNat n + (n + 1) = 2 ^ (goodHelperNat n + 1) :=
  Nat.sub_add_cancel (succ_lt_two_pow_goodHelperNat_succ n).le

/-- For any `n`, we have `f(n) > 0` -/
theorem goodFnNat_pos (n) : goodFnNat n > 0 :=
  Nat.sub_pos_of_lt (succ_lt_two_pow_goodHelperNat_succ n)

/-- For any `n`, we have `(f(n) + n) % 4 = 3`. -/
theorem goodFnNat_add_self_mod_four_eq_three (n) : (goodFnNat n + n) % 4 = 3 := by
  obtain ⟨k, hk⟩ : 4 ∣ 2 ^ (goodHelperNat n + 1) :=
    Nat.pow_dvd_pow 2 (Nat.succ_le_succ (goodHelperNat_pos n))
  rw [← Nat.add_mod_right, ← Nat.add_assoc _ 1 3, Nat.add_assoc _ n,
    goodFnNat_spec, hk, Nat.mul_add_mod_self_left]

/-- For any `m` and `n`, we have `4 ∤ gcd(f(m) + n, f(n) + m)`. -/
theorem not_four_dvd_gcd_goodFnNat_cross_add (m n) :
    ¬4 ∣ (goodFnNat m + n).gcd (goodFnNat n + m) := by
  ---- If `4 ∣ gcd(f(m) + n, f(n) + m)`, then `4 ∣ f(m) + n + f(n) + m`.
  intro h
  replace h : 4 ∣ (goodFnNat m + n) + (goodFnNat n + m) :=
    h.trans (Nat.dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _))
  ---- But `f(m) + n + f(n) + m ≡ 2 (mod 4)`; contradiction.
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_comm _ m, Nat.add_add_add_comm,
    Nat.add_comm n, Nat.add_mod, goodFnNat_add_self_mod_four_eq_three,
    goodFnNat_add_self_mod_four_eq_three] at h
  exact Nat.succ_ne_zero 1 h

/-- For any `m ≠ n`, the only odd number dividing `gcd(f(m) + n, f(n) + m)` is `1`. -/
theorem odd_dvd_gcd_goodFnNat_cross_add_imp (h : m ≠ n) (ht : Odd t)
    (h0 : t ∣ (goodFnNat m + n).gcd (goodFnNat n + m)) : t = 1 := by
  ---- WLOG assume `m > n`.
  wlog h1 : m > n
  · exact this h.symm ht (Nat.gcd_comm _ _ ▸ h0) ((Nat.lt_or_gt_of_ne h).resolve_right h1)
  ---- We note that `t ∣ f(n) + m`...
  replace h : t ∣ goodFnNat n + m := h0.trans (Nat.gcd_dvd_right _ _)
  ---- ... and `2^{g(m) + 1} + 2^{g(n) + 1} ≡ 2 (mod t)`.
  replace h0 : 2 ^ (goodHelperNat m + 1) + 2 ^ (goodHelperNat n + 1) ≡ 2 [MOD t] := calc
    _ = (goodFnNat m + m + 1) + (goodFnNat n + n + 1) := by
      iterate 2 rw [Nat.add_assoc _ _ 1, goodFnNat_spec]
    _ = (goodFnNat m + n) + (goodFnNat n + m) + 2 := by
      rw [Nat.add_add_add_comm, Nat.add_comm _ n, Nat.add_add_add_comm _ m, Nat.add_comm m]
    _ ≡ 0 + 2 [MOD t] :=
      ((h0.trans (Nat.gcd_dvd_left _ _)).modEq_zero_nat.add h.modEq_zero_nat).add_right 2
  ---- Since `m > n` and `g` is strictly increasing, we have `φ(t) ≤ t ≤ 2^{g(m - 1) + 1}`.
  replace h : Nat.totient t ≤ 2 ^ (goodHelperNat (m - 1) + 1) := calc
    Nat.totient t ≤ t := Nat.totient_le t
    _ ≤ goodFnNat n + m := Nat.le_of_dvd (Nat.add_pos_left (goodFnNat_pos n) m) h
    _ = m - (n + 1) + 2 ^ (goodHelperNat n + 1) := by
      rw [Nat.add_comm, goodFnNat, ← Nat.sub_add_comm h1,
        ← Nat.add_sub_assoc (succ_lt_two_pow_goodHelperNat_succ n).le]
    _ ≤ 2 ^ (goodHelperNat (m - (n + 1) + n) + 1) := by
      have h2 : StrictMono (λ t ↦ 2 ^ (goodHelperNat t + 1)) :=
        (pow_right_strictMono₀ Nat.one_lt_two).comp
          (add_left_strictMono.comp goodHelperNat_strictMono)
      exact h2.add_le_nat _ _
    _ = 2 ^ (goodHelperNat (m - 1) + 1) := by
      rw [← Nat.sub_add_comm h1, Nat.succ_eq_one_add, Nat.add_sub_add_right]
  ---- Then `φ(t)` divides `g(m) = (2^{g(m - 1) + 1})!`.
  obtain ⟨K, hK⟩ : Nat.totient t ∣ goodHelperNat m := calc
    Nat.totient t ∣ (2 ^ (goodHelperNat (m - 1) + 1)).factorial :=
      Nat.dvd_factorial (Nat.totient_pos.mpr ht.pos) h
    _ = goodHelperNat (m - 1 + 1) := (goodHelperNat_succ _).symm
    _ = goodHelperNat m := by rw [Nat.sub_add_cancel (Nat.one_le_of_lt h1)]
  ---- Note that `2` and `t` are coprime.
  replace ht : Nat.Coprime 2 t := Nat.coprime_two_left.mpr ht
  ---- Since `t` is odd, this implies `2^{g(m) + 1} ≡ 2 (mod t)`.
  replace h : 2 ^ (goodHelperNat m + 1) ≡ 2 [MOD t] := by
    rw [hK, Nat.pow_succ, Nat.mul_comm _ K, Nat.pow_mul]
    exact (Nat.ModEq.pow_totient (ht.pow_left _)).mul_right 2
  ---- Then `t` divides `2^{g(n) + 1}`.
  replace h0 : t ∣ 2 ^ (goodHelperNat n + 1) :=
    Nat.modEq_zero_iff_dvd.mp (h.add_left_cancel h0)
  ---- But `t` is coprime to `2`; this forces `t = 1`.
  exact (ht.symm.pow_right _).eq_one_of_dvd h0

/-- For any `m ≠ n`, the number `gcd(f(m) + n, f(n) + m)` is a power of `2`. -/
theorem gcd_goodFnNat_cross_add_eq_two_pow (h : m ≠ n) :
    ∃ k, (goodFnNat m + n).gcd (goodFnNat n + m) = 2 ^ k := by
  obtain ⟨k, t, ht, h1⟩ :
      ∃ k t, Odd t ∧ (goodFnNat m + n).gcd (goodFnNat n + m) = 2 ^ k * t :=
    Nat.exists_eq_two_pow_mul_odd
      (Nat.gcd_pos_of_pos_left _ (Nat.add_pos_left (goodFnNat_pos m) n)).ne.symm
  obtain rfl : t = 1 :=
    odd_dvd_gcd_goodFnNat_cross_add_imp h ht ⟨2 ^ k, h1.trans (Nat.mul_comm _ _)⟩
  exact ⟨k, h1.trans (Nat.mul_one _)⟩

/-- For any `m ≠ n`, we have `gcd(f(m) + n, f(n) + m) ≤ 2`. -/
theorem gcd_goodFnNat_cross_add_le_two (h : m ≠ n) :
    (goodFnNat m + n).gcd (goodFnNat n + m) ≤ 2 := by
  obtain ⟨k, hk⟩ : ∃ k, (goodFnNat m + n).gcd (goodFnNat n + m) = 2 ^ k :=
    gcd_goodFnNat_cross_add_eq_two_pow h
  replace h : ¬2 ^ 2 ∣ (goodFnNat m + n).gcd (goodFnNat n + m) :=
    not_four_dvd_gcd_goodFnNat_cross_add m n
  have h0 : 1 < 2 := Nat.one_lt_two
  rw [hk, Nat.pow_dvd_pow_iff_le_right h0, Nat.not_le, Nat.lt_succ_iff] at h
  exact hk.trans_le (Nat.pow_le_pow_of_le h0 h)



/-- `goodFnNat`, but over `ℕ+`. -/
def goodFn (n : ℕ+) : ℕ+ := ⟨goodFnNat n, goodFnNat_pos n⟩

/-- `goodFn` is indeed `2`-good. -/
theorem good_two_goodFn : good 2 goodFn :=
  λ _ _ h ↦ gcd_goodFnNat_cross_add_le_two (mt PNat.eq h)





/-! ### Summary -/

/-- Final solution -/
theorem final_solution : (∃ f, good k f) ↔ k ≥ 2 := by
  refine ⟨?_, λ hk ↦ ?_⟩
  · change _ → 1 < k
    rw [lt_iff_not_ge, PNat.le_one_iff]
    rintro ⟨f, hf⟩ rfl
    exact not_good_one f hf
  · exact ⟨goodFn, good_two_goodFn.of_ge hk⟩
