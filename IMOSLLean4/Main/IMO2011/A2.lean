/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Pow

/-!
# IMO 2011 A2

Let $N$ be a non-negative integer.
Determine all sequences $(x_1, x_2, …, x_{N + 1})$ of positive integers such that
  for every positive integer $n$, there exists an integer $a$ with
$$ x_1^n + 2 x_2^n + … + (N + 1) x_{N + 1}^n = a^{n + 1} + 1. $$

### Answer

Those with $x_1 = 1$ and $x_2 = x_3 = … = x_{N + 1} = 2 + 3 + … + (N + 1) = N(N + 3)/2$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2011SL.pdf).
The official solution directly assumes $a$ is positive, which can indeed be assumed.
The sign of $a$ does not matter if $n$ is odd, and we must have $a > 0$ if $n$ is even.
-/

namespace IMOSL
namespace IMO2011A2

open Multiset

/-! ### Extra lemmas -/

/-- The supremum of a non-empty multiset belongs to the multiset. -/
theorem Multiset_sup_mem [LinearOrder α] [OrderBot α] {S : Multiset α} (hS : S ≠ 0) :
    S.sup ∈ S := by
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ S, ∀ y ∈ S, y ≤ x := exists_max_image id hS
  obtain rfl : x = S.sup := le_antisymm (le_sup hx) (sup_le.mpr hx0)
  exact hx

open Finset in
/-- We have the formula `∑_{i < N} (i + 2) = N(N + 3)/2`. -/
theorem Fin_sum_add_two (N : ℕ) : ∑ i : Fin N, (i.val + 2) = N * (N + 3) / 2 := calc
  _ = ∑ i ∈ range N, (i + 1 + 1) := Fin.sum_univ_eq_sum_range (· + 2) N
  _ = ∑ i ∈ range N, (i + 1) + ∑ _ ∈ range N, 1 := sum_add_distrib
  _ = (N + 1) * N / 2 + N :=
    congrArg₂ _ ((sum_range_succ' id _).symm.trans (sum_range_id _))
      ((card_eq_sum_ones _).symm.trans (Finset.card_range _))
  _ = N * (N + 1 + 2) / 2 := by
    rw [← Nat.add_mul_div_left _ _ Nat.two_pos, ← Nat.add_mul, Nat.mul_comm]





/-! ### Start of the problem -/

/-- For any `k > 0`, we have `2k^k ≤ (k + 1)^k`. -/
theorem two_mul_pow_self_le_succ_pow_self {k : ℕ} (hk : k > 0) : 2 * k ^ k ≤ (k + 1) ^ k :=
  calc 2 * k ^ k
  _ = k ^ k + k * k ^ (k - 1) * 1 := by
    rw [Nat.mul_one, ← Nat.pow_add_one', Nat.sub_add_cancel hk, Nat.two_mul]
  _ ≤ (k + 1) ^ k := pow_add_mul_le_add_pow (Nat.zero_le _) (Nat.zero_le _) _

/-- For any `m, x : ℕ`, there exists `N` such that `mx^n < (x + 1)^n` for all `n ≥ N`. -/
theorem exists_mul_pow_lt_succ_pow (m x : ℕ) : ∃ N, ∀ n ≥ N, m * x ^ n < (x + 1) ^ n := by
  obtain rfl | hx : x = 0 ∨ x > 0 := Nat.eq_zero_or_pos x
  ---- If `x = 0`, then `N = 1` works.
  · refine ⟨1, λ n hn ↦ ?_⟩
    rw [Nat.zero_pow hn, Nat.mul_zero, Nat.one_pow]
    exact Nat.one_pos
  ---- If `x > 0`, then `N = xm` works.
  · refine ⟨x * m, λ n hn ↦ ?_⟩
    calc m * x ^ n
      _ < 2 ^ m * x ^ n := Nat.mul_lt_mul_of_pos_right Nat.lt_two_pow_self (Nat.pow_pos hx)
      _ = (2 * x ^ x) ^ m * x ^ (n - x * m) := by
        rw [Nat.mul_pow, Nat.mul_assoc, ← Nat.pow_mul, ← Nat.pow_add, Nat.add_sub_cancel' hn]
      _ ≤ ((x + 1) ^ x) ^ m * (x + 1) ^ (n - x * m) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (two_mul_pow_self_le_succ_pow_self hx) _)
          (Nat.pow_le_pow_left (Nat.le_succ x) _)
      _ = (x + 1) ^ n := by rw [← Nat.pow_mul, ← Nat.pow_add, Nat.add_sub_cancel' hn]

/-- Let `S` be a multiset of non-negative integers. Let `a > 0` be an integer greater
  than all elements of `S`. Then `∑_{x ∈ S} x^n < a^n` for `n` large enough. -/
theorem exists_sum_map_pow_lt_pow_of_forall_mem_lt
    {S : Multiset ℕ} {a : ℕ} (ha : a > 0) (hSa : ∀ x ∈ S, x < a) :
    ∃ N, ∀ n ≥ N, (S.map (· ^ n)).sum < a ^ n := by
  ---- There exists `N` such that `|S| (a - 1)^n < a^n` for all `n ≥ N`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, S.card * (a - 1) ^ n < (a - 1 + 1) ^ n :=
    exists_mul_pow_lt_succ_pow _ _
  ---- It remains to see that this `N` works.
  refine ⟨N, λ n hn ↦ ?_⟩
  calc (S.map (· ^ n)).sum
    _ ≤ (S.map (· ^ n)).card * (a - 1) ^ n :=
      sum_le_card_nsmul _ _ <| forall_mem_map_iff.mpr λ x hx ↦
        Nat.pow_le_pow_left (Nat.le_pred_of_lt (hSa _ hx)) _
    _ = S.card * (a - 1) ^ n := by rw [Multiset.card_map]
    _ < (a - 1 + 1) ^ n := hN n hn
    _ = a ^ n := by rw [Nat.sub_add_cancel ha]

/-- Let `S` be a multiset of non-negative integers, and let `a > sup S`.
  Then `∑_{x ∈ S} x^n < a^n` for `n` large enough. -/
theorem exists_sum_map_pow_lt_pow_of_sup_lt {S : Multiset ℕ} {a : ℕ} (hSa : S.sup < a) :
    ∃ N, ∀ n ≥ N, (S.map (· ^ n)).sum < a ^ n :=
  exists_sum_map_pow_lt_pow_of_forall_mem_lt (Nat.zero_lt_of_lt hSa)
    (λ _ hxS ↦ hSa.trans_le' (le_sup hxS))

/-- Let `S` and `T` be multisets of non-negative integers such that there exists infinitely
  many `n` satisfying `∑_{x ∈ S} x^n = ∑_{x ∈ T} x^n`. Then `sup S = sup T`. -/
theorem sup_eq_of_infinite_sum_map_pow_eq {S T : Multiset ℕ}
    (hST : ∀ N, ∃ n ≥ N, (S.map (· ^ n)).sum = (T.map (· ^ n)).sum) : S.sup = T.sup := by
  ---- WLOG assume `sup S ≤ sup T`.
  wlog hST0 : S.sup ≤ T.sup
  · exact (this (λ N ↦ (hST N).imp λ n ↦ And.imp_right Eq.symm) (Nat.le_of_not_ge hST0)).symm
  ---- If `sup S = sup T` then we are done, so now assume `sup S < sup T`.
  refine hST0.eq_of_not_lt λ hST1 ↦ ?_
  ---- Take `N` large enough such that `∑_{x ∈ S} x^n < (sup T)^n` for all `n ≥ N`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, (S.map (· ^ n)).sum < T.sup ^ n :=
    exists_sum_map_pow_lt_pow_of_sup_lt hST1
  ---- But then `∑_{x ∈ S} x^n < (sup T)^n ≤ ∑_{x ∈ T} x^n` for `n > N`; contradiction.
  obtain ⟨n, hnN, hn⟩ : ∃ n > N, (S.map (· ^ n)).sum = (T.map (· ^ n)).sum := hST (N + 1)
  replace hST0 : T ≠ 0 := by rintro rfl; exact Nat.not_lt_zero _ hST1
  refine absurd hn (Nat.ne_of_lt ?_)
  calc (S.map (· ^ n)).sum
    _ < T.sup ^ n + ((T.erase T.sup).map (· ^ n)).sum := Nat.lt_add_right _ (hN n hnN.le)
    _ = ((T.sup ::ₘ T.erase T.sup).map (· ^ n)).sum := by rw [map_cons, sum_cons]
    _ = (T.map (· ^ n)).sum := congrArg _ (congrArg _ (cons_erase (Multiset_sup_mem hST0)))

/-- Let `S` and `T` be multisets of positive integers such that there exists infinitely
  many `n` satisfying `∑_{x ∈ S} x^n = ∑_{x ∈ T} x^n`. Then `S = T`. -/
theorem eq_of_infinite_sum_map_pow_eq {S T : Multiset ℕ} (hS : 0 ∉ S) (hT : 0 ∉ T)
    (hST : ∀ N, ∃ n ≥ N, (S.map (· ^ n)).sum = (T.map (· ^ n)).sum) : S = T := by
  ---- We proceed by induction on `|S|`.
  induction hS' : S.card using Nat.rec generalizing S T with | zero => ?_ | succ k k_ih => ?_
  ---- If `S = ∅`, then `T = ∅`.
  · obtain rfl : S = 0 := card_eq_zero.mp hS'
    obtain ⟨n, -, h⟩ : ∃ n ≥ 0, (map (· ^ n) 0).sum = (T.map (· ^ n)).sum := hST 0
    replace h {x} (hx : x ∈ T) : x = 0 := by
      rw [map_zero, sum_zero, eq_comm, sum_eq_zero_iff, forall_mem_map_iff] at h
      exact eq_zero_of_pow_eq_zero (h x hx)
    exact (eq_zero_of_forall_notMem λ x hx ↦ hT (h hx ▸ hx)).symm
  ---- If `S ≠ ∅`, then `m := sup S = sup T > 0` and IH yields `S - {m} = T - {m}`.
  · have hST0 : S.sup = T.sup := sup_eq_of_infinite_sum_map_pow_eq hST
    have hS0 : S.sup ∈ S :=
      Multiset_sup_mem (mt card_eq_zero.mpr (hS'.trans_ne (Nat.succ_ne_zero k)))
    have hT0 : S.sup ∈ T := by
      refine hST0 ▸ Multiset_sup_mem λ hT0 ↦ hS ?_
      rw [hT0, sup_zero, Nat.bot_eq_zero] at hST0
      exact hST0 ▸ hS0
    replace hS : 0 ∉ S.erase S.sup := λ h ↦ hS (mem_of_mem_erase h)
    replace hT : 0 ∉ T.erase S.sup := λ h ↦ hT (mem_of_mem_erase h)
    replace hST (N : ℕ) :
        ∃ n ≥ N, ((S.erase S.sup).map (· ^ n)).sum = ((T.erase S.sup).map (· ^ n)).sum := by
      obtain ⟨n, hnN, hn⟩ : ∃ n ≥ N, (S.map (· ^ n)).sum = (T.map (· ^ n)).sum := hST N
      refine ⟨n, hnN, ?_⟩
      rw [← Nat.add_right_inj (n := S.sup ^ n), sum_map_erase (f := λ x ↦ x ^ n) hS0,
        sum_map_erase (f := λ x ↦ x ^ n) hT0, hn]
    replace hS' : (S.erase S.sup).card = k := by
      rw [card_erase_of_mem hS0, hS', Nat.pred_succ]
    replace k_ih : S.erase S.sup = T.erase S.sup := k_ih hS hT hST hS'
    rw [← cons_erase hS0, k_ih, cons_erase hT0]

/-- Suppose that `|S| = k + 1`, and for every `n > 0`, there exists `a : ℕ` such that
  `∑_{x ∈ S} x^n = a^{n + 1} + 1`. Then `S = {1, k, …, k}` with `k` repeated `k` times. -/
theorem eq_cons_one_replicate_of_sum_map_pow_eq
    {S : Multiset ℕ} (hS : 0 ∉ S) (hS0 : S.card = k + 1)
    (hS1 : ∀ n > 0, ∃ a : ℕ, (S.map (· ^ n)).sum = a ^ (n + 1) + 1) :
    S = 1 ::ₘ replicate k k := by
  ---- It suffices to show that `S = {1, a, …, a}` for some `a`, as `a` is forced to be `k`.
  suffices ∃ a : ℕ, S = 1 ::ₘ replicate a a by
    rcases this with ⟨a, rfl⟩
    suffices a = k by rw [this]
    rwa [card_cons, card_replicate, Nat.succ_inj] at hS0
  /- From the previous lemma, it suffices to show that for some `a`,
    we have `∑_{x ∈ S} x^n = a^{n + 1} + 1` for infinitely many `n`. -/
  suffices ∃ a, ∀ N, ∃ n ≥ N, (S.map (· ^ n)).sum = a ^ (n + 1) + 1 by
    refine this.imp λ a ha ↦ eq_of_infinite_sum_map_pow_eq hS (λ h ↦ ?_) (λ N ↦ ?_)
    -- Show that `0 ∉ {1, a, …, a}`.
    · rw [mem_cons, or_iff_right Nat.zero_ne_one, mem_replicate] at h
      exact h.1 h.2.symm
    -- Show that `∑_{x ∈ S} x^n = ∑_{x ∈ {1, a, …, a}} x^n` (`a` repeats `a` times).
    · obtain ⟨n, hn, hn0⟩ : ∃ n ≥ N, (S.map (· ^ n)).sum = a ^ (n + 1) + 1 := ha N
      refine ⟨n, hn, ?_⟩
      rw [hn0, map_cons, sum_cons, Nat.one_pow, map_replicate,
        sum_replicate, Nat.pow_succ', Nat.nsmul_eq_mul, Nat.add_comm]
  ---- Note that for large `n` we must have `a ≤ sup S`.
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, (S.map (· ^ n)).sum < (S.sup + 1) ^ n :=
    exists_sum_map_pow_lt_pow_of_sup_lt (Nat.lt_succ_self S.sup)
  ---- Thus the last claim follows by pigeonhole principle.
  replace hN (n) :
      ∃ a : Fin (S.sup + 1), (S.map (· ^ (N + n + 1))).sum = a ^ (N + n + 2) + 1 := by
    obtain ⟨a, ha⟩ : ∃ a, (S.map (· ^ (N + n + 1))).sum = a ^ (N + n + 2) + 1 :=
      hS1 _ (Nat.succ_pos _)
    refine ⟨⟨a, (Nat.pow_lt_pow_iff_left (Nat.succ_ne_zero (N + n + 1))).mp ?_⟩, ha⟩
    calc a ^ (N + n + 2) + 1
      _ = (S.map (· ^ (N + n + 1))).sum := ha.symm
      _ ≤ (S.sup + 1) ^ (N + n + 1) := Nat.le_of_lt (hN _ (Nat.le_add_right N (n + 1)))
      _ ≤ (S.sup + 1) ^ (N + n + 2) := Nat.pow_le_pow_right (Nat.succ_pos _) (Nat.le_succ _)
  obtain ⟨y, hy⟩ : ∃ y : ℕ → Fin (S.sup + 1),
      ∀ n, (S.map (· ^ (N + n + 1))).sum = y n ^ (N + n + 2) + 1 :=
    Classical.axiom_of_choice hN
  obtain ⟨a, ha⟩ : ∃ a : Fin (S.sup + 1), Infinite {n | y n = a} :=
    Finite.exists_infinite_fiber y
  replace ha : {n | (S.map (· ^ n)).sum = a.val ^ (n + 1) + 1}.Infinite := by
    refine Set.infinite_of_injOn_mapsTo (f := λ n ↦ N + n + 1)
      (Set.injOn_of_injective (Nat.succ_injective.comp (add_right_injective N)))
      (λ n hn ↦ ?_) (Set.infinite_coe_iff.mp ha)
    rw [Set.mem_setOf_eq, ← hn, hy]
  exact ⟨a, λ M ↦ (ha.exists_gt M).imp λ n hn ↦ ⟨hn.2.le, hn.1⟩⟩

/-- Suppose that `∑_{i ≤ N} {x_i, …, x_i} = {1, a, …, a}`,
  where each `x_i` is repeated `i + 1` times and `a` is repeated `k` times.
  Then `k = N(N + 3)/2`, `x_0 = 1`, and `x_i = a` for all `i > 0`. -/
theorem sum_eq_cons_one_replicate {x : Fin (N + 1) → ℕ}
    (hx : ∑ i : Fin (N + 1), replicate (i + 1) (x i) = 1 ::ₘ replicate k a) :
    k = N * (N + 3) / 2 ∧ x = λ i ↦ if i = 0 then 1 else a := by
  ---- First, the value of `k` is obtained by cardinality counting.
  obtain rfl : k = N * (N + 3) / 2 := by
    refine Nat.succ_injective ?_
    calc k + 1
      _ = (1 ::ₘ replicate k a).card := by rw [card_cons, card_replicate]
      _ = (∑ i : Fin (N + 1), replicate (i + 1) (x i)).card := congrArg card hx.symm
      _ = ∑ i : Fin (N + 1), (replicate (i + 1) (x i)).card := card_sum _ _
      _ = ∑ i : Fin (N + 1), (i.val + 1) := Fintype.sum_congr _ _ λ _ ↦ card_replicate _ _
      _ = 1 + ∑ i : Fin N, (i.val + 2) := Fin.sum_univ_succ _
      _ = 1 + N * (N + 3) / 2 := congrArg (1 + ·) (Fin_sum_add_two N)
      _ = N * (N + 3) / 2 + 1 := Nat.add_comm _ _
  set k := N * (N + 3) / 2
  ---- Second, by occurrence counting, we get `x_i = a` for all `i ≠ 0`.
  have hx0 (i) : x i = 1 ∨ x i = a := by
    have hi : x i ∈ ∑ i : Fin (N + 1), replicate (i + 1) (x i) :=
      mem_sum.mpr ⟨i, Finset.mem_univ _, mem_replicate.mpr ⟨Nat.succ_ne_zero _, rfl⟩⟩
    rw [hx, mem_cons, mem_replicate] at hi
    exact hi.imp_right And.right
  replace hx0 (i) (hi : i ≠ 0) : x i = a := by
    refine (hx0 i).elim (λ hi0 ↦ ?_) id
    have hi1 : replicate 2 1 ≤ 1 ::ₘ replicate k a := calc
      _ ≤ replicate (i + 1) 1 := by
        rwa [replicate_le_replicate, Nat.succ_le_iff, Nat.lt_add_left_iff_pos,
          Nat.pos_iff_ne_zero, Fin.val_ne_zero_iff]
      _ = replicate (i + 1) (x i) := congrArg _ hi0.symm
      _ ≤ ∑ i : Fin (N + 1), replicate (i + 1) (x i) :=
        Finset.single_le_sum (f := λ i : Fin (N + 1) ↦ replicate (i + 1) (x i))
          (λ _ _ ↦ Multiset.zero_le _) (Finset.mem_univ _)
      _ = 1 ::ₘ replicate k a := hx
    rw [replicate_succ, cons_le_cons_iff, replicate_one, singleton_le, mem_replicate] at hi1
    exact hi0.trans hi1.2
  ---- Third, after simplifying, we get `x_0 = 1`.
  replace hx : x 0 ::ₘ replicate k a = 1 ::ₘ replicate k a := calc
    _ = x 0 ::ₘ replicate (∑ i : Fin N, (i + 2)) a :=
      congrArg (λ n ↦ x 0 ::ₘ replicate n a) (Fin_sum_add_two N).symm
    _ = x 0 ::ₘ ∑ i : Fin N, replicate (i + 2) a :=
      congrArg (x 0 ::ₘ ·) (map_sum (replicateAddMonoidHom a) _ _)
    _ = x 0 ::ₘ ∑ i : Fin N, replicate (i + 2) (x i.succ) :=
      congrArg (x 0 ::ₘ ·) <| Fintype.sum_congr _ _
        λ i ↦ congrArg _ (hx0 _ i.succ_ne_zero).symm
    _ = ∑ i : Fin (N + 1), replicate (i + 1) (x i) :=
      (Fin.sum_univ_succ λ i ↦ replicate (i + 1) (x i)).symm
    _ = 1 ::ₘ replicate k a := hx
  replace hx : x 0 = 1 := (cons_inj_left _).mp hx
  ---- Finally, put all the pieces together.
  refine ⟨rfl, funext λ i ↦ ?_⟩
  split_ifs with hi
  exacts [(congrArg x hi).trans hx, hx0 i hi]

/-- Let `x_0, x_1, …, x_N : ℕ`, and suppose that for every `n > 0`,
  there exists `a : ℕ` such that `∑_{i ≤ N} (i + 1) x_i^n = a^{n + 1} + 1`.
  Then `x_0 = 1` and `x_1 = … = x_N = N(N + 3)/2`. -/
theorem Nat_version {N : ℕ} {x : Fin (N + 1) → ℕ} (hx : ∀ i, x i > 0) :
    (∀ n > 0, ∃ a : ℕ, ∑ i, (i + 1) * x i ^ n = a ^ (n + 1) + 1)
      ↔ x = λ i ↦ if i = 0 then 1 else N * (N + 3) / 2 := by
  set k : ℕ := N * (N + 3) / 2
  refine ⟨λ hx0 ↦ ?_, ?_⟩
  ---- The `→` direction considers the multiset `S = ∑_{i ≤ N} replicate (i + 1) x_i`.
  · let S : Multiset ℕ := ∑ i : Fin (N + 1), replicate (i + 1) (x i)
    suffices S = 1 ::ₘ replicate k k from (sum_eq_cons_one_replicate this).2
    refine eq_cons_one_replicate_of_sum_map_pow_eq ?_ ?_ ?_
    -- First show that `0 ∉ S`.
    · rw [mem_sum, not_exists]; rintro i ⟨-, hi⟩
      exact (hx i).ne.symm (mem_replicate.mp hi).2.symm
    -- Next prove that `|S| = k + 1`, where `k := N(N + 3)/2`.
    · calc (∑ i : Fin (N + 1), replicate (i + 1) (x i)).card
      _ = ∑ i : Fin (N + 1), (replicate (i + 1) (x i)).card := card_sum _ _
      _ = ∑ i : Fin (N + 1), (i.val + 1) := Fintype.sum_congr _ _ (λ _ ↦ card_replicate _ _)
      _ = 1 + ∑ i : Fin N, (i.val + 2) := Fin.sum_univ_succ _
      _ = 1 + k := congrArg (1 + ·) (Fin_sum_add_two N)
      _ = k + 1 := Nat.add_comm _ _
    -- Finally, translate the given condition on `x` as `∑_{y ∈ S} y^n = a^{n + 1} + 1`.
    · intro n hn
      refine (hx0 n hn).imp λ a ha ↦ ?_
      calc (S.map (· ^ n)).sum
        _ = (∑ i : Fin (N + 1), (replicate (i + 1) (x i)).map (· ^ n)).sum :=
          congrArg _ (map_sum (mapAddMonoidHom _) _ _)
        _ = ∑ i : Fin (N + 1), ((replicate (i + 1) (x i)).map (· ^ n)).sum := sum_sum _ _
        _ = ∑ i : Fin (N + 1), (i + 1) * x i ^ n :=
          Fintype.sum_congr _ _ λ i ↦ by rw [map_replicate, sum_replicate, smul_eq_mul]
        _ = a ^ (n + 1) + 1 := ha
  ---- The `←` direction.
  · rintro rfl n -; refine ⟨k, ?_⟩
    calc ∑ i : Fin (N + 1), (i + 1) * (if i = 0 then 1 else k) ^ n
      _ = 1 * 1 ^ n + ∑ i : Fin N, (i + 2) * k ^ n := Fin.sum_univ_succ _
      _ = 1 ^ n + (∑ i : Fin N, (i.val + 2)) * k ^ n :=
        congrArg₂ _ (Nat.one_mul _) (Finset.sum_mul _ _ _).symm
      _ = 1 + k * k ^ n := congrArg₂ _ (Nat.one_pow _) (congrArg₂ _ (Fin_sum_add_two N) rfl)
      _ = k ^ (n + 1) + 1 := by rw [Nat.pow_succ', Nat.add_comm]

/-- Final solution -/
theorem final_solution {N : ℕ} {x : Fin (N + 1) → ℕ} (hx : ∀ i, x i > 0) :
    (∀ n > 0, ∃ a : ℤ, (∑ i, (i + 1) * x i ^ n : ℕ) = a ^ (n + 1) + 1)
      ↔ x = λ i ↦ if i = 0 then 1 else N * (N + 3) / 2 := by
  ---- The only work left is showing that allowing `a : ℤ` does not change the answer.
  refine Iff.trans (forall_congr' λ n ↦ imp_congr_right λ hn ↦ ?_) (Nat_version hx)
  ---- The `←` direction is easy.
  refine Iff.symm ⟨?_, ?_⟩
  · rintro ⟨a, ha⟩; refine ⟨a, ?_⟩
    rw [ha, Int.natCast_succ, Int.natCast_pow]
  ---- For the `→` direction, it suffices to show that `a^{n + 1} ≥ 0`.
  rintro ⟨a, ha⟩
  suffices 0 ≤ a ^ (n + 1) by
    refine ⟨Int.natAbs a, Int.natCast_inj.mp ?_⟩
    rw [ha, Int.natCast_succ, ← Int.natAbs_pow, Int.natAbs_of_nonneg this]
  ---- But this follows from `∑_{i ≤ N} (i + 1) x_i^n > 0`.
  have h : 0 < ∑ i : Fin (N + 1), (i + 1) * x i ^ n := calc
    _ < x 0 ^ n := Nat.pow_pos (hx 0)
    _ = 1 * x 0 ^ n := (Nat.one_mul _).symm
    _ ≤ (∑ k ∈ Finset.range N, if h : k + 1 < N + 1 then (k + 2) * x ⟨k + 1, h⟩ ^ n else 0)
          + 1 * x 0 ^ n :=
      Nat.le_add_left _ _
    _ = ∑ i : Fin (N + 1), (i + 1) * x i ^ n := by
      rw [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ', dif_pos (Nat.succ_pos N)]; rfl
  rwa [← Int.lt_add_one_iff, ← ha, Int.natCast_pos]
