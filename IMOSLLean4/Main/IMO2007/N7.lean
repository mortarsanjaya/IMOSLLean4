/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Finite.Prod

/-!
# IMO 2007 N7

Let $d$ be a positive integer and $p_1, …, p_k$ be primes.
Show that there exists infinitely many non-negative integers $n$ such that
  $d$ divides $ν_{p_i}(n!)$ for all $i = 1, 2, …, k$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2007SL.pdf).
We modify the sequence a bit; instead of taking powers with base $p_1 … p_k$,
  we take powers with base number $2 p_1 … p_k$.
-/

namespace IMOSL
namespace IMO2007N7

open Finset

/-- If `r < p^k` and `p^k ∣ m`, then `ν_p((m + r)!) = ν_p(m) + ν_p(r)`. -/
theorem padicValNat_add_factorial_of_lt_dvd
    [hp : Fact (Nat.Prime p)] (hr : r < p ^ k) (hm : p ^ k ∣ m) :
    padicValNat p (m + r).factorial
      = padicValNat p m.factorial + padicValNat p r.factorial := by
  have hp0 : p > 0 := hp.out.pos
  ---- Induction on `k`, with the base case `k = 0` obvious as then `r = 0`.
  induction k generalizing r m with
    | zero => rw [Nat.lt_one_iff.mp hr, Nat.factorial_zero, padicValNat.one]; rfl
    | succ k k_ih => ?_
  ---- Write `r = pq + s` and `m = pn`, where `q < p^k`, `p^k ∣ n`, and `s < p`.
  obtain ⟨q, s, hs, rfl⟩ : ∃ q, ∃ s < p, q * p + s = r :=
    ⟨r / p, r % p, Nat.mod_lt _ hp0, Nat.div_add_mod' r p⟩
  replace hr : q < p ^ k := Nat.lt_of_mul_lt_mul_right (Nat.lt_of_add_right_lt hr)
  obtain ⟨n, rfl⟩ : p ∣ m := dvd_of_mul_left_dvd hm
  replace hm : p ^ k ∣ n := by rwa [Nat.pow_succ', Nat.mul_dvd_mul_iff_left hp0] at hm
  ---- Now do some rewritings and apply the induction hypothesis.
  rw [← Nat.add_assoc, Nat.mul_comm q p, ← Nat.mul_add, padicValNat_factorial_mul]
  iterate 2 rw [padicValNat_factorial_mul_add _ hs, padicValNat_factorial_mul]
  rw [Nat.add_add_add_comm, k_ih hr hm]


variable [Fintype ι] (p : ι → ℕ) [hp : ∀ i, Fact (Nat.Prime (p i))]

/-- Given a finite list `p : ι → ℕ` of primes, we construct the sequence
    `(n_k)_{k ≥ 0}` by `n_0 = 1` and `n_{k + 1} = (2 ∏_i p_i)^{n_k}`. -/
def stdSeq (n : ℕ) : ℕ := ((2 * ∏ i, p i) ^ ·)^[n] 1

/-- Given a finite list `p : ι → ℕ` of primes, we have `1 < 2 ∏_i p_i`. -/
theorem one_lt_two_mul_prod_prime : 1 < 2 * ∏ i, p i :=
  Nat.le_mul_of_pos_right _ <| Nat.pos_of_ne_zero <|
    prod_ne_zero_iff.mpr λ i _ ↦ (hp i).out.ne_zero

omit hp in
/-- We have `stdSeq p (n + 1) = (2 ∏_i p_i)^{stdSeq p n}`. -/
theorem stdSeq_succ (n) : stdSeq p (n + 1) = (2 * ∏ i, p i) ^ stdSeq p n :=
  Function.iterate_succ_apply' _ _ _

/-- The function `stdSeq p` is strictly monotone. -/
theorem stdSeq_strictMono : StrictMono (stdSeq p) := by
  refine strictMono_of_lt_add_one λ n _ ↦ ?_
  calc stdSeq p n
    _ < (2 * ∏ i, p i) ^ stdSeq p n := Nat.lt_pow_self (one_lt_two_mul_prod_prime p)
    _ = stdSeq p (n + 1) := (stdSeq_succ p n).symm

/-- We have `2 * stdSeq p n ≤ stdSeq p (n + 1)`. -/
theorem two_mul_stdSeq_le_stdSeq_succ (n) : 2 * stdSeq p n ≤ stdSeq p (n + 1) :=
  calc 2 * stdSeq p n
  _ ≤ 2 ^ stdSeq p n := Nat.mul_le_pow (Nat.succ_ne_self 1) _
  _ ≤ (2 * ∏ i, p i) ^ stdSeq p n :=
    Nat.pow_le_pow_left (one_lt_two_mul_prod_prime p) _
  _ = stdSeq p (n + 1) := (stdSeq_succ p n).symm

/-- For any `n`, we have `∑_{j < n} stdSeq p j < stdSeq p n`. -/
theorem sum_stdSeq_range_lt_stdSeq (n) : ∑ j ∈ range n, stdSeq p j < stdSeq p n := by
  induction n with | zero => exact Nat.zero_lt_one | succ n n_ih => ?_
  calc ∑ j ∈ range (n + 1), stdSeq p j
    _ = ∑ j ∈ range n, stdSeq p j + stdSeq p n := sum_range_succ _ _
    _ < stdSeq p n + stdSeq p n := Nat.add_lt_add_right n_ih _
    _ = 2 * stdSeq p n := (Nat.two_mul _).symm
    _ ≤ stdSeq p (n + 1) := two_mul_stdSeq_le_stdSeq_succ p n

/-- For any finite list `p : ι → ℕ` of primes, finite subset `S ⊆ ℕ`,
  and `i : ι`, we have `ν_{p_i}([∑_{k ∈ S} n_k]!) = ∑_{k ∈ S} ν_{p_i}(n_k!)`,
  where `(n_k)_{k ≥ 0}` is the `stdSeq` sequence defined above. -/
theorem padicValNat_sum_stdSeq (i : ι) (S : Finset ℕ) :
    padicValNat (p i) (∑ k ∈ S, stdSeq p k).factorial
      = ∑ k ∈ S, padicValNat (p i) (stdSeq p k).factorial := by
  ---- We induct with respect to the largest element of `S`, with the case `S = ∅` trivial.
  induction S using Finset.induction_on_max with
    | h0 => exact padicValNat.one
    | step m S hmS S_ih => ?_
  ---- If the largest element `m` is equal to `0` then `S = {0}` and we are done.
  obtain rfl | ⟨n, rfl⟩ : m = 0 ∨ ∃ n, m = n + 1 :=
    (Nat.eq_zero_or_eq_succ_pred m).imp_right λ hm ↦ ⟨Nat.pred m, hm⟩
  · obtain rfl : S = ∅ :=
      eq_empty_iff_forall_notMem.mpr λ j hj ↦ Nat.not_lt_zero j (hmS j hj)
    rfl
  ---- If `m = n + 1`, apply `padicValNat_add_factorial_of_lt_dvd` with `k := stdSeq p n`.
  have hmS0 : n + 1 ∉ S := λ h ↦ Nat.lt_irrefl _ (hmS _ h)
  rw [sum_insert hmS0, sum_insert hmS0, ← S_ih]
  refine padicValNat_add_factorial_of_lt_dvd (k := stdSeq p n) ?_ ?_
  ---- First prove `∑_{j ∈ S} stdSeq p j < p_i^{stdSeq p n}`.
  · calc ∑ j ∈ S, stdSeq p j
      _ ≤ ∑ j ∈ range (n + 1), stdSeq p j :=
        sum_le_sum_of_subset λ j hj ↦ mem_range.mpr (hmS j hj)
      _ = ∑ j ∈ range n, stdSeq p j + stdSeq p n := sum_range_succ _ _
      _ < stdSeq p n + stdSeq p n := Nat.add_lt_add_right (sum_stdSeq_range_lt_stdSeq _ _) _
      _ = 2 * stdSeq p n := (Nat.two_mul _).symm
      _ ≤ 2 ^ stdSeq p n := Nat.mul_le_pow (Nat.succ_ne_self 1) _
      _ ≤ p i ^ stdSeq p n := Nat.pow_le_pow_left (hp i).out.two_le _
  ---- Now prove `p_i ^ stdSeq p n ∣ stdSeq p (n + 1)`.
  · calc p i ^ stdSeq p n
      _ ∣ (2 * ∏ j, p j) ^ stdSeq p n :=
        pow_dvd_pow_of_dvd (Nat.dvd_mul_left_of_dvd (dvd_prod_of_mem _ (mem_univ _)) _) _
      _ = stdSeq p (n + 1) := (stdSeq_succ p n).symm

open Fin.NatCast in
/-- Final solution -/
theorem final_solution (d) [NeZero d] (N) :
    ∃ n ≥ N, ∀ i, d ∣ padicValNat (p i) (Nat.factorial n) := by
  ---- Define `f(n) = (∑_{j < n + N} ν_{p_i}([stdSeq p j]!) (mod d))_{i ∈ ι}`.
  let f (n : ℕ) (i : ι) : Fin d :=
    (∑ j ∈ range (n + N), padicValNat (p i) (stdSeq p j).factorial : ℕ)
  ---- Then `f(a) = f(b)` for some `a < b`.
  obtain ⟨a, b, hab, hab0⟩ : ∃ a b, a < b ∧ f a = f b :=
    Set.finite_univ.exists_lt_map_eq_of_forall_mem λ _ ↦ Set.mem_univ _
  replace hab : a + N < b + N := Nat.add_lt_add_right hab N
  ---- We pick `n = ∑_{a + N ≤ j < b + N} (stdSeq p j)`.
  refine ⟨∑ j ∈ Ico (a + N) (b + N), stdSeq p j, ?_, ?_⟩
  ---- First we show that this `n` satisfies `n ≥ N`.
  · calc N
      _ ≤ a + N := Nat.le_add_left _ _
      _ ≤ stdSeq p (a + N) := (stdSeq_strictMono p).id_le _
      _ ≤ ∑ j ∈ Ico (a + N) (b + N), stdSeq p j :=
        single_le_sum_of_canonicallyOrdered (left_mem_Ico.mpr hab)
  /- Second, for each `i`, we show that `f(a) = f(b)` implies
    `d ∣ ν_{p_i}([∑_{a + N ≤ j < b + N} (stdSeq p j)]!)`. -/
  · intro i
    replace hab0 :
        ∑ j ∈ range (a + N), padicValNat (p i) (stdSeq p j).factorial
            + ∑ j ∈ Ico (a + N) (b + N), padicValNat (p i) (stdSeq p j).factorial
          ≡ ∑ j ∈ range (a + N), padicValNat (p i) (stdSeq p j).factorial [MOD d] := calc
      _ = ∑ j ∈ range (b + N), padicValNat (p i) (stdSeq p j).factorial :=
        sum_range_add_sum_Ico _ (Nat.le_of_lt hab)
      _ ≡ ∑ j ∈ range (a + N), padicValNat (p i) (stdSeq p j).factorial [MOD d] :=
        congrArg Fin.val (congrFun hab0 i).symm
    rwa [Nat.add_modEq_left_iff, ← padicValNat_sum_stdSeq] at hab0
