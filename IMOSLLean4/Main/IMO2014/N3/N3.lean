/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Multiset.Fintype
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Multiset

/-!
# IMO 2014 N3 (P5)

Consider a collection $C$ of coins of value $1/n$ for some positive integer $n$.
A partition of $C$ into $N$ groups is called an *$N$-Cape Town* partition
  if the total value of coins in each group is at most $1$.
Prove that if the total value of coins in $C$ is at most $N + 1/2$,
  then $C$ has an $(N + 1)$-Cape Town partition.
-/

namespace IMOSL
namespace IMO2014N3

open Multiset

/-! ### Extra lemmas -/

theorem Multiset_mem_sum [DecidableEq α] {P : Multiset (Multiset α)} {a : α} :
    a ∈ P.sum ↔ ∃ M ∈ P, a ∈ M := by
  rw [sum_eq_sum_toEnumFinset, Finset.mem_sum]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨M, n⟩, h, h0⟩
    exact ⟨M, count_pos.mp (Nat.zero_lt_of_lt ((mem_toEnumFinset _ _).mp h)), h0⟩
  · rintro ⟨M, h, h0⟩
    refine ⟨⟨M, 0⟩, ?_, h0⟩
    rwa [mem_toEnumFinset, count_pos]

theorem sum_replicate_map_inv (hn : n ≠ 0) :
    ((replicate n n).map λ x : ℕ ↦ (x : ℚ)⁻¹).sum = 1 := by
  rw [map_replicate, sum_replicate, nsmul_eq_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hn)]

theorem sum_replicate_two_mul (n : ℕ) :
    ((replicate 2 (2 * n)).map λ x : ℕ ↦ (x : ℚ)⁻¹).sum = (n : ℚ)⁻¹ := by
  rw [map_replicate, sum_replicate, Nat.cast_mul, nsmul_eq_mul, mul_inv,
    mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero 1))]

theorem sum_map_sum [AddCommMonoid M] (P : Multiset (Multiset α)) (f : α → M) :
    (P.map λ i ↦ (i.map f).sum).sum = (P.sum.map f).sum := by
  revert P; refine Multiset.induction ?_ λ i P hP ↦ ?_
  · simp only [Multiset.map_zero, sum_zero]
  · rw [map_cons, sum_cons, hP, sum_cons, Multiset.map_add, sum_add]

theorem sum_map_replicate_two (C : Multiset ℕ) :
    ∀ N, replicate (C.count 0) 0 + sum ((range N).map λ i ↦
      replicate (C.count (2 * i + 1)) (2 * i + 1)
        + replicate (count (2 * i.succ) C) (2 * i.succ)) = C.filter λ n ↦ n ≤ 2 * N
  | 0 => by
      rw [range_zero, Multiset.map_zero, sum_zero, add_zero, mul_zero]
      simp only [nonpos_iff_eq_zero]; exact (filter_eq' C 0).symm
  | N + 1 => by
      rw [range_succ, map_cons, sum_cons, add_left_comm, sum_map_replicate_two]
      ext x; rw [count_add, count_add, count_replicate,
        count_replicate, count_filter, count_filter, Nat.mul_succ]
      obtain h | h : x ≤ 2 * N ∨ 2 * N < x := le_or_gt x (2 * N)
      · have h0 : x < 2 * N + 2 := h.trans_lt (Nat.lt_add_of_pos_right Nat.two_pos)
        rw [if_pos h, if_pos h0.le, add_eq_right, add_eq_zero]
        exact ⟨if_neg (Nat.lt_succ_of_le h).ne.symm, if_neg h0.ne.symm⟩
      rw [if_neg h.not_ge, add_zero]
      rw [Nat.lt_iff_add_one_le, le_iff_eq_or_lt, Nat.lt_iff_add_one_le, le_iff_eq_or_lt] at h
      rcases h with rfl | rfl | h
      · rw [if_pos rfl, if_neg (2 * N + 1).succ_ne_self,
          add_zero, if_pos (2 * N).succ.le_succ]
      · rw [if_neg (2 * N + 1).succ_ne_self.symm, zero_add, if_pos rfl, if_pos (le_refl _)]
      · rw [if_neg (Nat.lt_of_succ_lt h).ne, zero_add, if_neg h.ne, if_neg h.not_ge]





/-! ### Start of the problem -/

structure CapeTownPartition (N : ℕ) (C : Multiset ℕ) where
  part : Multiset (Multiset ℕ)
  card_part : card part = N.succ
  sum_part : part.sum = C
  total_bound : ∀ G ∈ part, (G.map λ x : ℕ ↦ (x : ℚ)⁻¹).sum ≤ 1


namespace CapeTownPartition

def add_replicate_self (P : CapeTownPartition N C) (k) :
    CapeTownPartition (N + 1) (C + replicate k k) where
  part := replicate k k ::ₘ P.part
  card_part := by rw [card_cons, P.card_part]
  sum_part := by rw [sum_cons, P.sum_part, add_comm]
  total_bound := by
    refine forall_mem_cons.mpr ⟨?_, P.total_bound⟩
    obtain rfl | h : k = 0 ∨ k ≠ 0 := eq_or_ne k 0
    · rw [replicate_zero, Multiset.map_zero, sum_zero]; exact zero_le_one
    · exact (sum_replicate_map_inv h).le

theorem nonempty_add_replicate_self (h : Nonempty (CapeTownPartition N C)) (k) :
    Nonempty (CapeTownPartition (N + 1) (C + replicate k k)) :=
  h.elim λ P ↦ ⟨add_replicate_self P k⟩

theorem nonempty_append_zeroes (h : Nonempty (CapeTownPartition N C)) (k) :
    Nonempty (CapeTownPartition N (C + replicate k 0)) := by
  rcases h with ⟨part', card_part', rfl, total_bound'⟩
  obtain ⟨G₀, part'', rfl⟩ : ∃ G part'', part' = G ::ₘ part'' := by
    obtain ⟨G, h0⟩ : ∃ G, G ∈ part' :=
      card_pos_iff_exists_mem.mp (N.succ_pos.trans_eq card_part'.symm)
    exact ⟨G, exists_cons_of_mem h0⟩
  refine ⟨(G₀ + replicate k 0) ::ₘ part'', ?_, ?_, ?_⟩
  · rw [card_cons, ← card_part', card_cons]
  · rw [sum_cons, sum_cons, add_right_comm]
  · refine forall_mem_cons.mpr ⟨?_, λ G hG ↦ total_bound' G (mem_cons_of_mem hG)⟩
    rw [Multiset.map_add, map_replicate, Nat.cast_zero,
      inv_zero, sum_add, sum_replicate, nsmul_zero, add_zero]
    exact total_bound' G₀ (mem_cons_self G₀ part'')

theorem nonempty_cons_zero (h : Nonempty (CapeTownPartition N C)) :
    Nonempty (CapeTownPartition N (0 ::ₘ C)) := by
  replace h := nonempty_append_zeroes h 1
  rwa [replicate_one, add_comm, singleton_add] at h

theorem nonempty_merge (h : Nonempty (CapeTownPartition N (n ::ₘ C)))
    {C' : Multiset ℕ} (h0 : (C'.map λ x : ℕ ↦ (x : ℚ)⁻¹).sum = (n : ℚ)⁻¹) :
    Nonempty (CapeTownPartition N (C + C')) := by
  rcases h with ⟨part', card_part', sum_part', total_bound'⟩
  obtain ⟨G₀, part'', rfl⟩ : ∃ G part'', part' = (n ::ₘ G) ::ₘ part'' := by
    obtain ⟨G, h, h0⟩ : ∃ G ∈ part', n ∈ G :=
      Multiset_mem_sum.mp (sum_part' ▸ mem_cons_self n C)
    obtain ⟨G', rfl⟩ : ∃ G', G = n ::ₘ G' := exists_cons_of_mem h0
    exact ⟨G', exists_cons_of_mem h⟩
  refine ⟨(G₀ + C') ::ₘ part'', ?_, ?_, ?_⟩
  · rw [card_cons, ← card_part', card_cons]
  · rw [sum_cons, cons_add, cons_inj_right] at sum_part'
    rw [sum_cons, ← sum_part', add_right_comm]
  · refine forall_mem_cons.mpr ⟨?_, λ G hG ↦ total_bound' G (mem_cons_of_mem hG)⟩
    apply (total_bound' (n ::ₘ G₀) (mem_cons_self _ _)).trans_eq'
    rw [Multiset.map_add, sum_add, h0, add_comm, map_cons, sum_cons]

theorem nonempty_replicate_two_mul (h : Nonempty (CapeTownPartition N (n ::ₘ C))) :
    Nonempty (CapeTownPartition N (C + replicate 2 (2 * n))) :=
  nonempty_merge h (sum_replicate_two_mul n)

theorem nonempty_of_restricted (hC : 0 ∉ C) (hC0 : ∀ n ≠ 0, C.count n < n)
    (hC1 : ∀ n, C.count (2 * n) ≤ 1) (hC2 : ∀ n ∈ C, n ≤ 2 * N.succ) :
    Nonempty (CapeTownPartition N C) := by
  refine ⟨(range N.succ).map λ i ↦
    replicate (C.count (2 * i + 1)) (2 * i + 1)
      + replicate (C.count (2 * i.succ)) (2 * i.succ), ?_, ?_, ?_⟩
  · rw [card_map, card_range]
  · have h := sum_map_replicate_two C N.succ
    rwa [count_eq_zero_of_notMem hC, replicate_zero, zero_add, filter_eq_self.mpr hC2] at h
  · intro G h; simp only [mem_map, mem_range] at h
    rcases h with ⟨i, -, rfl⟩
    rw [Multiset.map_add, sum_add, map_replicate, map_replicate, sum_replicate, sum_replicate]
    have h0 : C.count (2 * i + 1) ≤ 2 * i := Nat.lt_succ_iff.mp (hC0 _ (2 * i).succ_ne_zero)
    have X (n : ℕ) : 0 ≤ (n : ℚ)⁻¹ := inv_nonneg.mpr n.cast_nonneg
    apply (add_le_add (nsmul_le_nsmul_left (X _) h0) (nsmul_le_nsmul_left (X _) (hC1 _))).trans
    replace X : 0 < ((2 * i).succ : ℚ) := Nat.cast_pos.mpr (2 * i).succ_pos
    rw [one_nsmul, ← mul_inv_cancel₀ X.ne.symm,
      ← nsmul_eq_mul, succ_nsmul, add_le_add_iff_left]
    exact inv_anti₀ X (Nat.cast_le.mpr (2 * i).succ.le_succ)

theorem nonempty_of_sum_le {N : ℕ} (h : (map (λ x : ℕ ↦ (x : ℚ)⁻¹) C).sum ≤ N + 2⁻¹) :
    Nonempty (CapeTownPartition N C) := by
  ---- Formally running the steps would consist of strong induction on `|C|`
  generalize hK : card C = K
  induction' K using Nat.strong_induction_on with K K_ih generalizing C N
  subst hK
  ---- 1. Resolve case: `0 ∈ C`
  by_cases hC : 0 ∈ C
  · obtain ⟨C, rfl⟩ : ∃ C', C = 0 ::ₘ C' := exists_cons_of_mem hC
    refine nonempty_cons_zero (K_ih (card C) ?_ ?_ rfl)
    · rw [card_cons]; exact (card C).lt_succ_self
    · rwa [map_cons, Nat.cast_zero, inv_zero, sum_cons, zero_add] at h
  ---- 2. Resolve case: for some `n : ℕ`, `n` has multiplicity `≥ n` in `C`
  by_cases hC0 : ∃ n ≠ 0, n ≤ C.count n
  · rcases hC0 with ⟨n, h0, h1⟩
    rw [le_count_iff_replicate_le, Multiset.le_iff_exists_add] at h1
    rcases h1 with ⟨C, rfl⟩
    rw [Multiset.map_add, sum_add, sum_replicate_map_inv h0, add_comm] at h
    obtain ⟨N, rfl⟩ : ∃ N' : ℕ, N = N'.succ := by
      apply Nat.exists_eq_succ_of_ne_zero; rintro rfl
      refine h.not_gt (add_lt_add_of_le_of_lt ?_ (inv_lt_one_of_one_lt₀ one_lt_two))
      refine sum_nonneg λ x h1 ↦ ?_
      rw [mem_map] at h1; rcases h1 with ⟨y, -, rfl⟩
      exact inv_nonneg.mpr y.cast_nonneg
    rw [add_comm]; refine nonempty_add_replicate_self (K_ih (card C) ?_ ?_ rfl) n
    · rw [card_add, card_replicate]
      exact Nat.lt_add_of_pos_left (Nat.zero_lt_of_ne_zero h0)
    · rwa [N.cast_succ, add_right_comm, add_le_add_iff_right] at h
  simp only [not_exists, not_and, not_le] at hC0
  ---- 3. Resolve case: for some `n : ℕ`, `2n` has multiplicity `> 1` in `C`
  by_cases hC1 : ∃ n, 1 < C.count (2 * n)
  · rcases hC1 with ⟨n, h0⟩
    rw [← Nat.succ_le_iff, le_count_iff_replicate_le, Multiset.le_iff_exists_add] at h0
    rcases h0 with ⟨C, rfl⟩
    rw [add_comm]; refine nonempty_replicate_two_mul (K_ih (card _) ?_ (h.trans_eq' ?_) rfl)
    · rw [card_cons, card_add, card_replicate, Nat.add_comm 2]
      exact (card C).succ.lt_succ_self
    · rw [map_cons, sum_cons, Multiset.map_add, sum_add, sum_replicate_two_mul, add_comm]
  simp only [not_exists, not_lt] at hC1
  ---- 4. Resolve case: for some `n ∈ C`, we have `n > 2N`
  by_cases hC2 : ∃ n ∈ C, 2 * N.succ < n
  · rcases hC2 with ⟨n, h0, h1⟩
    obtain ⟨C, rfl⟩ : ∃ C', C = n ::ₘ C' := exists_cons_of_mem h0
    obtain ⟨part', card_part', rfl, total_bound'⟩ : Nonempty (CapeTownPartition N C) := by
      refine K_ih (card C) ?_ (h.trans' ?_) rfl
      · rw [card_cons]; exact (card C).lt_succ_self
      · rw [map_cons, sum_cons, le_add_iff_nonneg_left, inv_nonneg]
        exact n.cast_nonneg
    clear K_ih h0
    -- First find `G ∈ part'` such that `(G.map _).sum ≤ 1 - 1/(2N)`
    obtain ⟨G, hG, hG0⟩ :
        ∃ G ∈ part', (G.map λ x : ℕ ↦ (x : ℚ)⁻¹).sum ≤ 1 - ((2 * N.succ : ℕ) : ℚ)⁻¹ := by
      by_contra h0; simp only [not_exists, not_and, not_le] at h0
      have h2 : part' ≠ ∅ := by rw [empty_eq_zero, ← card_pos, card_part']; exact N.succ_pos
      apply (sum_lt_sum_of_nonempty h2 h0).not_ge
      replace h2 : (2 : ℚ)⁻¹ + 2⁻¹ = 1 := by rw [inv_eq_one_div, add_halves]
      rw [map_const', sum_replicate, card_part', nsmul_eq_mul, mul_one_sub, Nat.cast_mul,
        mul_inv_rev, mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr N.succ_ne_zero),
        N.cast_succ, ← h2, add_sub_assoc, Nat.cast_two, add_sub_cancel_right, sum_map_sum]
      apply h.trans'
      rw [map_cons, sum_cons]
      exact le_add_of_nonneg_left (inv_nonneg.mpr n.cast_nonneg)
    obtain ⟨part'', rfl⟩ : ∃ part'', part' = G ::ₘ part'' := exists_cons_of_mem hG
    -- Now add `n` to `G` and work out the rest
    refine ⟨(n ::ₘ G) ::ₘ part'', ?_, ?_, ?_⟩
    · rw [card_cons, ← card_part', card_cons]
    · rw [sum_cons, cons_add, sum_cons]
    · refine forall_mem_cons.mpr ⟨?_, λ G' hG' ↦ total_bound' G' (mem_cons_of_mem hG')⟩
      rw [map_cons, sum_cons, ← le_sub_iff_add_le']
      refine hG0.trans (sub_le_sub_left (inv_anti₀ ?_ (Nat.cast_le.mpr h1.le)) _)
      rw [Nat.cast_pos, Nat.mul_pos_iff_of_pos_left Nat.two_pos]; exact N.succ_pos
  simp only [not_exists, not_and, not_lt] at hC2
  ---- 5. Resolve the final case
  exact nonempty_of_restricted hC hC0 hC1 hC2

end CapeTownPartition





/-- Final solution -/
alias final_solution := CapeTownPartition.nonempty_of_sum_le
