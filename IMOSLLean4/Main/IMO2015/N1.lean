/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Logic.Function.Iterate

/-!
# IMO 2015 N1

Define the function $f : ℤ → ℤ$ by $f(n) = n ⌊n/2⌋$.
Find all integers $M$ such that $f^k(M)$ is even for some $k ∈ ℕ$.

### Answer

$3$.

### Solution

We follow and modify Solution 2 of the
  [official solution](https://www.imo-official.org/problems/IMO2015SL.pdf).

### Notes

Our formulation is noticably different from the original formulation, but it is stronger.
The original formulation only asks for odd and positive $M$; our $M$ corresponds to $2M + 1$.
We make no attempt to formalize the original formulation.
-/

namespace IMOSL
namespace IMO2015N1

/-- The function `f : ℤ → ℤ` defined by `f(n) = n ⌊n/2⌋`. -/
abbrev f (n : Int) : Int := n * (n / 2)

/-- The main claim: if `2c` divides `m - 3` and `f(m) - 3`, then `4c` divides `m - 3`. -/
theorem main_claim (h : 2 * c ∣ m - 3) (h0 : 2 * c ∣ f m - 3) : 2 * (2 * c) ∣ m - 3 := by
  ---- The case `c = 0` is trivial.
  obtain rfl | hc : c = 0 ∨ c ≠ 0 := Decidable.em _
  · exact h
  ---- Now suppose `c ≠ 0`, and write `m = 2cd + 3`.
  rcases h with ⟨d, hd⟩
  obtain rfl : m = 2 * c * d + 3 := Int.sub_eq_iff_eq_add.mp hd
  ----- Note that `f(m) = (2cd + 3)(cd + 1)`.
  replace h : f (2 * c * d + 3) = (2 * c * d + 3) * (c * d + 1) := by
    refine congrArg ((2 * c * d + 3) * ·) ?_
    calc (2 * c * d + (2 + 1)) / 2
      _ = (2 * (c * d + 1) + 1) / 2 := by
        rw [Int.mul_add, Int.add_assoc, Int.mul_one, Int.mul_assoc]
      _ = c * d + 1 + 0 := Int.mul_add_ediv_left _ _ (by decide)
      _ = c * d + 1 := Int.add_zero _
  ---- Thus `f(m) ≡ 3 (mod 2c)` gives `2c ∣ cd` and so `2 ∣ d`.
  replace hd : c * 2 ∣ c * ((2 + 1) * d) := by
    rwa [h, Int.add_mul, Int.mul_assoc, Int.add_sub_assoc, Int.dvd_self_mul_add,
      Int.mul_add, Int.mul_one, Int.add_sub_cancel, Int.mul_left_comm, Int.mul_comm] at h0
  replace hd : 2 ∣ d := by
    rwa [Int.mul_dvd_mul_iff_left hc, Int.add_mul, Int.one_mul, Int.dvd_self_mul_add] at hd
  ---- Now we finish.
  rw [Int.add_sub_cancel, Int.mul_comm]
  exact Int.mul_dvd_mul_left _ hd

/-- `f^k(M)` is odd for all `M` if and only if `M = 3`. -/
theorem f_iterate_odd_iff : (∀ k : ℕ, ¬2 ∣ f^[k] M) ↔ M = 3 := by
  ---- The `←` direction is easy since `f(3) = 3`.
  refine Iff.symm ⟨?_, λ hM ↦ ?_⟩
  · rintro rfl k
    rw [Function.iterate_fixed (rfl : f 3 = 3)]
    decide
  ---- For the `→` direction, first we have `2 ∣ f^k(M) - 3` for all `k`.
  replace hM (k) : 2 ∣ f^[k] M - 3 := by
    obtain hk | hk : f^[k] M % 2 = 0 ∨ f^[k] M % 2 = 1 := Int.emod_two_eq _
    · exact absurd (Int.dvd_of_emod_eq_zero hk) (hM k)
    · calc (2 : Int)
      _ ∣ f^[k] M - 1 + 2 * (-1) :=
        Int.dvd_add_self_mul.mpr (Int.dvd_self_sub_of_emod_eq hk)
      _ = f^[k] M - 3 := by rw [Int.mul_neg, ← Int.sub_eq_add_neg, Int.sub_sub]; rfl
  ---- By induction, we get `2^(n + 1) ∣ f^k(M) - 3` for any `n` and `k`.
  replace hM (n k) : 2 ^ (n + 1) ∣ f^[k] M - 3 := by
    induction n generalizing k with | zero => exact hM k | succ n n_ih => ?_
    replace n_ih (k) : 2 * 2 ^ n ∣ f^[k] M - 3 := Int.pow_succ' _ _ ▸ n_ih k
    rw [Int.pow_succ', Int.pow_succ']
    exact main_claim (n_ih k) (f.iterate_succ_apply' _ _ ▸ n_ih _)
  ---- Taking `k = 0` and `n = |M - 3|` forces `M = 3`.
  replace hM : 2 ^ ((M - 3).natAbs + 1) ∣ M - 3 := hM _ 0
  exact Int.eq_of_sub_eq_zero (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hM
    (Nat.lt_trans (Nat.lt_succ_self _) Nat.lt_two_pow_self))

/-- Final solution -/
theorem final_solution : (∃ k : ℕ, 2 ∣ f^[k] M) ↔ M ≠ 3 := by
  rw [iff_not_comm, not_exists, f_iterate_odd_iff]
