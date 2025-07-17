/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Dist

/-!
# IMO 2023 A5

Let $N > 0$ and $(a_0, a_1, …, a_N)$ be a permutation of $(0, 1, …, N)$.
Suppose that $(|a_0 - a_1|, …, |a_{N - 1} - a_N|)$ is a permutation of $(1, 2, …, N)$.
Prove that $\max\{a_0, a_N\} ≥ \lfloor (N + 1)/4 \rfloor + 1$.

### Extra notes

The lower bound is known to be sharp when $N \equiv 2 \pmod{4}$.
We won't implement this at least until later when we figure out the other cases.
-/

namespace IMOSL
namespace IMO2023A5

/-! ### Extra lemmas -/

theorem two_mul_add_dist_sq_eq (k m : ℕ) :
    2 * k * m + k.dist m ^ 2 = k ^ 2 + m ^ 2 := by
  wlog h : k ≤ m
  · rw [(k ^ 2).add_comm, Nat.mul_right_comm, Nat.dist_comm]
    exact this m k (Nat.le_of_not_ge h)
  obtain ⟨n, rfl⟩ : ∃ n, m = k + n := Nat.exists_eq_add_of_le h
  rw [Nat.dist_eq_sub_of_le h, Nat.add_sub_cancel_left, Nat.mul_add, Nat.mul_assoc,
    ← Nat.pow_two, Nat.two_mul, Nat.add_assoc, Nat.add_assoc, add_sq, Nat.add_assoc]

theorem add_sq_add_dist_sq_eq (k m : ℕ) :
    (k + m) ^ 2 + k.dist m ^ 2 = 2 * (k ^ 2 + m ^ 2) := by
  rw [add_sq', Nat.add_assoc, two_mul_add_dist_sq_eq, Nat.two_mul]

theorem succ_div_two_eq (N) : (N + 1) / 2 = N / 2 + N % 2 := by
  rw [Nat.succ_div, Nat.add_left_cancel_iff]
  simp_rw [Nat.dvd_iff_mod_eq_zero, ← Nat.even_iff, Nat.even_add_one, Nat.not_even_iff]
  split_ifs with h; exacts [h.symm, (Nat.mod_two_ne_one.mp h).symm]

theorem div_two_add_succ_div_two (N) : N / 2 + (N + 1) / 2 = N := by
  rw [succ_div_two_eq, ← Nat.add_assoc, ← Nat.two_mul, Nat.div_add_mod]

theorem two_mul_succ_div_two (N) : 2 * ((N + 1) / 2) = N + N % 2 := by
  rw [succ_div_two_eq, Nat.mul_add, (N % 2).two_mul, ← Nat.add_assoc, Nat.div_add_mod]

theorem mod_two_sq_eq_self (N) : (N % 2) ^ 2 = N % 2 := by
  obtain h | h : N % 2 = 0 ∨ N % 2 = 1 := N.mod_two_eq_zero_or_one
  all_goals rw [h]; rfl

theorem add_div_two_lt_max_of_ne {x y : ℕ} (h : x ≠ y) : (x + y) / 2 < x.max y := by
  rw [Nat.div_lt_iff_lt_mul Nat.two_pos, Nat.mul_two]
  obtain h | h : x < y ∨ y < x := h.lt_or_gt
  · exact Nat.add_lt_add_of_lt_of_le (lt_sup_of_lt_right h) (x.le_max_right y)
  · exact Nat.add_lt_add_of_le_of_lt (x.le_max_left y) (lt_sup_of_lt_left h)





/-! ### Start of the problem -/

open Finset

structure nicePerm (N : ℕ) where
  toPerm : Fin (N + 1) ≃ Fin (N + 1)
  distPerm : Fin N ≃ Fin N
  distPerm_spec (i : Fin N) :
    Nat.dist (toPerm i.castSucc) (toPerm i.succ) = (distPerm i).val.succ


namespace nicePerm

variable (X : nicePerm N)

theorem sum_dist_abs_eq :
    2 * ∑ i : Fin N, Nat.dist (X.toPerm i.castSucc) (X.toPerm i.succ) = (N + 1) * N := by
  simp only [X.distPerm_spec, Nat.succ_eq_add_one]
  rw [sum_add_distrib, Fin.sum_const, smul_eq_mul, Nat.mul_one,
    Equiv.sum_comp, Nat.mul_add, mul_sum, Fin.sum_univ_eq_sum_range,
    ← sum_range_succ, ← mul_sum, Nat.mul_comm, sum_range_id_mul_two]; rfl

theorem sum_dist_rel_eq (hk : k ≤ N) :
    2 * ∑ i : Fin (N + 1), Nat.dist (X.toPerm i) k
      = (k + 1) * k + (N - k + 1) * (N - k) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = k + m := Nat.exists_eq_add_of_le hk
  rw [X.toPerm.sum_comp λ i ↦ i.val.dist k, Nat.add_assoc, Fin.sum_univ_add, Nat.mul_add]
  refine congrArg₂ _ ?_ ?_
  · suffices ∑ i : Fin k, i.val.dist k = ∑ i ∈ range (k + 1), i from
      (congrArg (2 * ·) this).trans (by rw [Nat.mul_comm, sum_range_id_mul_two]; rfl)
    rw [Fin.sum_univ_eq_sum_range λ i ↦ i.dist k, ← sum_flip, sum_range_succ, k.sub_self]
    exact sum_congr rfl λ i hi ↦ Nat.dist_eq_sub_of_le (mem_range.mp hi).le
  · change 2 * ∑ i : Fin (m + 1), (k + i).dist (k + 0) = _
    simp only [Nat.add_sub_cancel_left, Nat.dist_add_add_left, Nat.dist_zero_right]
    rw [mul_sum, Fin.sum_univ_eq_sum_range, ← mul_sum,
      Nat.mul_comm, sum_range_id_mul_two]; rfl

theorem sum_dist_abs_le_sum_dist_rel (k) :
    ∑ i : Fin N, Nat.dist (X.toPerm i.castSucc) (X.toPerm i.succ)
        + (Nat.dist (X.toPerm (Fin.last N)) k + Nat.dist (X.toPerm 0) k)
      ≤ 2 * ∑ i : Fin (N + 1), Nat.dist (X.toPerm i) k := by
  calc
    _ ≤ ∑ i : Fin N, (Nat.dist (X.toPerm i.castSucc) k + Nat.dist k (X.toPerm i.succ))
        + (Nat.dist (X.toPerm (Fin.last N)) k + Nat.dist (X.toPerm 0) k) :=
      Nat.add_le_add_right (sum_le_sum λ i _ ↦ Nat.dist.triangle_inequality _ _ _) _
    _ = (∑ i : Fin N, Nat.dist (X.toPerm i.castSucc) k + Nat.dist (X.toPerm (Fin.last N)) k)
        + (∑ i : Fin N, Nat.dist (X.toPerm i.succ) k + Nat.dist (X.toPerm 0) k) := by
      rw [sum_add_distrib, Nat.add_add_add_comm]; simp only [k.dist_comm]
    _ = _ + _ := congrArg₂ _ ?_ ?_
    _ = _ := (Nat.two_mul _).symm
  · rw [Fin.sum_univ_castSucc, Nat.add_comm]
  · rw [Fin.sum_univ_succ, Nat.add_comm]

theorem dist_rel_main_free_ineq (hk : k ≤ N) :
    2 * (Nat.dist (X.toPerm (Fin.last N)) k + Nat.dist (X.toPerm 0) k)
      ≤ k.dist (N - k) ^ 2 + N := by
  have h := Nat.mul_le_mul_left 2 (X.sum_dist_abs_le_sum_dist_rel k)
  rw [Nat.mul_add, X.sum_dist_abs_eq, X.sum_dist_rel_eq hk] at h
  generalize 2 * _ = a at h ⊢
  replace hk : k + (N - k) = N := Nat.add_sub_of_le hk
  generalize N - k = m at hk h; subst hk
  rw [Nat.succ_mul, k.succ_mul, m.succ_mul, Nat.add_add_add_comm, ← Nat.pow_two,
    ← Nat.pow_two, ← Nat.pow_two, Nat.mul_add, ← add_sq_add_dist_sq_eq, Nat.add_assoc,
    ((k + m) ^ 2).add_assoc, Nat.add_le_add_iff_left, Nat.two_mul, Nat.add_left_comm] at h
  exact Nat.le_of_add_le_add_left h

theorem toPerm_last_add_toPerm_zero_bound :
    (N + 1) / 2 ≤ X.toPerm (Fin.last N) + X.toPerm 0 := by
  let aN := X.toPerm (Fin.last N); let a0 := X.toPerm 0
  have h {k} (hk : k ≤ N) : 2 * (k + k) ≤ k.dist (N - k) ^ 2 + N + 2 * (aN + a0) := calc
    _ ≤ 2 * ((Nat.dist aN k + aN) + (Nat.dist a0 k + a0)) := by
      refine Nat.mul_le_mul_left 2 (Nat.add_le_add ?_ ?_)
      all_goals exact Nat.dist_tri_left _ k
    _ = 2 * (Nat.dist aN k + Nat.dist a0 k) + 2 * (aN + a0) := by
      rw [Nat.add_add_add_comm, Nat.mul_add]
    _ ≤ _ := Nat.add_le_add_right (X.dist_rel_main_free_ineq hk) _
  replace h := h (Nat.le_of_lt_succ (Nat.div_lt_self N.succ_pos Nat.one_lt_two))
  rw [← Nat.eq_sub_of_add_eq (div_two_add_succ_div_two N), ← (N / 2).add_zero,
    ← Nat.two_mul, succ_div_two_eq, Nat.dist_add_add_left, Nat.dist_zero_right,
    mod_two_sq_eq_self, (N % 2).add_comm, ← two_mul_succ_div_two,
    ← succ_div_two_eq, Nat.two_mul, Nat.add_le_add_iff_left] at h
  exact Nat.le_of_mul_le_mul_left h Nat.two_pos

theorem toPerm_last_max_toPerm_zero_bound :
    (if N = 0 then 0 else (N + 1) / 4 + 1)
      ≤ (X.toPerm (Fin.last N)).1.max (X.toPerm 0) := by
  split_ifs with h
  · exact Nat.zero_le _
  · calc (N + 1) / 4
      _ = (N + 1) / 2 / 2 := (Nat.div_div_eq_div_mul (N + 1) 2 2).symm
      _ ≤ _ / 2 := Nat.div_le_div_right X.toPerm_last_add_toPerm_zero_bound
      _ < _ := add_div_two_lt_max_of_ne λ h0 ↦
        h (Fin.last_eq_zero_iff.mp (X.toPerm.injective (Fin.eq_of_val_eq h0)))

end nicePerm





/-- Final solution -/
alias final_solution := nicePerm.toPerm_last_max_toPerm_zero_bound
