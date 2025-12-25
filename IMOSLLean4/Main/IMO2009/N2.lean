/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Fintype.Pigeonhole

/-!
# IMO 2009 N2

For each $n ∈ ℕ^+$, let $Ω(n)$ denote the number of prime factors of $n$ with multiplicity.
For convenience, we denote $Ω(0) = 0$.
1. Prove that for any $N ∈ ℕ$, there exists $a, b ∈ ℕ$ distinct such that
    $Ω((a + k)(b + k))$ is even for all $k < N$.
2. Prove that, if $Ω((a + k)(b + k))$ is even for all $k ∈ ℕ$, then $a = b$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
-/

namespace IMOSL
namespace IMO2009N2

open ArithmeticFunction
open scoped ArithmeticFunction.Omega

/-- Given `a, b ∈ ℕ`, `a + b` is even if and only if `a ≡ b (mod 2)`. -/
theorem even_add_iff_mod_two_eq {a b : ℕ} : Even (a + b) ↔ a % 2 = b % 2 := by
  rw [Nat.even_iff, Nat.add_mod]
  have ha : a % 2 < 2 := Nat.mod_lt _ Nat.two_pos
  have hb : b % 2 < 2 := Nat.mod_lt _ Nat.two_pos
  generalize a % 2 = a' at ha ⊢
  generalize b % 2 = b' at hb ⊢
  revert a' b'; decide

/-- For any `N`, there exists `n ≥ N` such that `Ω(n(n + 1))` is not even. -/
theorem infinite_cardFactors_mul_succ_self_not_even (N) :
    ∃ n ≥ N, ¬Even (Ω (n * (n + 1))) := by
  ---- Suppose not; then `Ω(n) ≡ Ω(n + 1) (mod 2)` for every `n ≥ N + 1`.
  by_contra! h
  replace h (n) (hn : n ≥ N + 1) : Ω n % 2 = Ω (n + 1) % 2 := by
    rw [← even_add_iff_mod_two_eq, ← cardFactors_mul (Nat.ne_zero_of_lt hn) n.succ_ne_zero]
    exact h n (Nat.le_of_succ_le hn)
  ---- By induction, we get `Ω(n) ≡ Ω(N + 1) (mod 2)` for all `n ≥ N + 1`.
  replace h (n) (hn : n ≥ N + 1) : Ω n % 2 = Ω (N + 1) % 2 := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn h0 => rw [← h0, h n hn]
  ---- Then `Ω(p) ≡ Ω((N + 1)^2) (mod 2)`, where `p` is a prime `≥ N + 1`.
  obtain ⟨p, hp, hp0⟩ := Nat.exists_infinite_primes (N + 1)
  replace h : Ω p % 2 = Ω ((N + 1) * (N + 1)) % 2 :=
    (h p hp).trans (h _ (Nat.le_mul_self _)).symm
  ---- But `Ω(p) = 1` and `Ω((N + 1)^2) = 2Ω(N + 1)` is even; contradiction.
  have hN : N + 1 ≠ 0 := Nat.succ_ne_zero N
  rw [cardFactors_apply_prime hp0, cardFactors_mul hN hN,
    ← Nat.two_mul, Nat.mul_mod_right] at h
  exact Nat.one_ne_zero h

/-- Final solution, part 1 -/
theorem final_solution_part1 (N) :
    ∃ a b, a ≠ b ∧ ∀ k < N, Even (Ω ((a + k) * (b + k))) := by
  ---- There exists `a ≠ b` such that `Ω(a + k + 1) ≡ Ω(b + k + 1) (mod 2)` for all `k < N`.
  let f (a : ℕ) (k : Fin N) : Fin 2 := Fin.ofNat 2 (Ω (a + 1 + k))
  obtain ⟨a, b, h, hab⟩ : ∃ a b, a ≠ b ∧ f a = f b :=
    Finite.exists_ne_map_eq_of_infinite f
  replace hab (k) (hk : k < N) : Ω (a + 1 + k) % 2 = Ω (b + 1 + k) % 2 :=
    congrArg Fin.val (congrFun hab ⟨k, hk⟩)
  ---- Then the pair `(a + 1, b + 1)` works.
  refine ⟨a + 1, b.succ, Nat.succ_ne_succ_iff.mpr h, λ k hk ↦ ?_⟩
  have X (c : ℕ) : c + 1 + k ≠ 0 := (c.succ_add k).trans_ne (c + k).succ_ne_zero
  rw [cardFactors_mul (X _) (X _), even_add_iff_mod_two_eq, hab k hk]

/-- Final solution, part 2 -/
theorem final_solution_part2 (h : ∀ n, Even (Ω ((a + n) * (b + n)))) : a = b := by
  ---- WLOG let `a ≤ b`.
  wlog h0 : a ≤ b
  · exact (this (λ n ↦ Nat.mul_comm _ _ ▸ h n) (Nat.le_of_not_ge h0)).symm
  ---- Write `b = c + a` for some `c ≥ 0`; we're done if `c = 0`.
  obtain ⟨c, rfl⟩ : ∃ c, b = a + c := Nat.exists_eq_add_of_le h0
  obtain rfl | hc : c = 0 ∨ c ≠ 0 := eq_or_ne c 0
  · rfl
  ---- If `c ≠ 0`, then `Ω(k(k + 1))` is even for `k` large enough.
  replace h (k) (hk : k > a) : Even (Ω (k * (k + 1))) := by
    specialize h (k * c - a)
    have hk0 : k * c ≥ a :=
      hk.le.trans (Nat.le_mul_of_pos_right k (Nat.zero_lt_of_ne_zero hc))
    replace hk : k ≠ 0 := Nat.ne_zero_of_lt hk
    replace h0 : k + 1 ≠ 0 := Nat.succ_ne_zero k
    rwa [Nat.add_right_comm, Nat.add_sub_cancel' hk0, ← Nat.succ_mul, Nat.mul_mul_mul_comm,
      cardFactors_mul (Nat.mul_ne_zero hk h0) (Nat.mul_ne_zero hc hc), Nat.even_add,
      cardFactors_mul hc hc, iff_true_right (Even.add_self _)] at h
  ---- By `infinite_cardFactors_mul_succ_self_not_even`, contradiction!
  obtain ⟨n, hn, hn0⟩ : ∃ n ≥ a + 1, ¬Even (Ω (n * (n + 1))) :=
    infinite_cardFactors_mul_succ_self_not_even _
  exact absurd (h n hn) hn0
