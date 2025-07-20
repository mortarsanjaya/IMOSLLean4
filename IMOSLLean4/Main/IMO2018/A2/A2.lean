/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Periodic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# IMO 2018 A2 (P2)

Let $R$ be a totally ordered commutative ring.
Find all periodic sequences $(a_k)_{k ≥ 0}$ such that for any $k ≥ 0$,
$$ a_{k + 2} = a_k a_{k + 1} + 1. $$

Original problem: Find all possible periods of such sequence.
-/

namespace IMOSL
namespace IMO2018A2

open Finset

/-! ### Extra lemmas -/

lemma sum_of_periodic [AddCommMonoid M] {a : ℕ → M} (hn : a.Periodic (n + 1)) :
    ∀ d, ∑ k ∈ range (n + 1), a (k + d) = ∑ k : Fin (n + 1), a k := by
  refine Nat.rec (sum_range a) λ d hd ↦ ?_
  rw [← hd, sum_range_succ, sum_range_succ', n.add_left_comm d 1, hn, d.zero_add]
  simp only [Nat.add_succ, Nat.succ_add]





/-! ### Start of the problem -/

def good [NonAssocSemiring R] (a : ℕ → R) := ∀ k, a (k + 2) = a k * a (k + 1) + 1


section

open Fin.NatCast

variable (R) [NonAssocRing R] (d : Fin 3)

def stdGoodSeq : ℕ → R := λ n ↦ ![2, -1, -1] (n + d)

theorem stdGoodSeq_is_good : good (stdGoodSeq R d) := λ k ↦ by
  unfold stdGoodSeq; rw [Nat.cast_add, Nat.cast_two, Nat.cast_succ,
    add_right_comm, add_right_comm (k : Fin 3) 1 d]
  generalize (k : Fin 3) + d = c
  match c with
  | 0 => show (-1 : R) = 2 * -1 + 1; rw [two_mul, neg_add_cancel_right]
  | 1 => show (2 : R) = -1 * -1 + 1; rw [neg_mul_neg, one_mul, one_add_one_eq_two]
  | 2 => show (-1 : R) = -1 * 2 + 1; rw [mul_two, neg_add_cancel_right]

theorem stdGoodSeq_periodic3 : (stdGoodSeq R d).Periodic 3 := λ n ↦ by
  unfold stdGoodSeq; rw [Nat.cast_add, add_right_comm]
  exact congrArg _ (add_zero _)

theorem stdGoodSeq_periodic_three_mul : ∀ k, (stdGoodSeq R d).Periodic (3 * k) := by
  refine Nat.rec (λ _ ↦ rfl) (λ k hk n ↦ ?_)
  rw [Nat.mul_succ, ← Nat.add_assoc, stdGoodSeq_periodic3, hk]

theorem stdGoodSeq_periodic_of_three_dvd (h : 3 ∣ k) : (stdGoodSeq R d).Periodic k := by
  rcases h with ⟨k, rfl⟩; exact stdGoodSeq_periodic_three_mul R d k

open Fin.CommRing in
theorem stdGoodSeq_periodic_iff_three_dvd (R)
    [Ring R] [LinearOrder R] [IsStrictOrderedRing R] {n} :
    (stdGoodSeq R d).Periodic n ↔ 3 ∣ n := by
  refine ⟨λ h ↦ ?_, λ ⟨k, hk⟩ ↦ hk ▸ stdGoodSeq_periodic_three_mul R d k⟩
  replace h : ![2, -1, -1] n = (2 : R) := by
    specialize h (2 * d.1); unfold stdGoodSeq at h
    have X : ((2 : ℕ) : Fin 3) + 1 = 0 := rfl
    rwa [Nat.cast_add, Nat.cast_mul, Fin.cast_val_eq_self,
      add_right_comm, ← add_one_mul, X, zero_mul, zero_add] at h
  rw [← Fin.natCast_eq_zero]; generalize (n : Fin 3) = k at h ⊢
  have X : (-1 : R) ≠ 2 := by norm_num
  match k with | 0 => rfl | 1 => exact absurd h X | 2 => exact absurd h X


end


namespace good

lemma eq1 [Semiring R] {a : ℕ → R} (ha : good a) (k) :
    a (k + 2) ^ 2 + a k = a k * a (k + 3) + a (k + 2) := by
  rw [ha (k + 1), mul_add_one (a k), add_right_comm, ← mul_assoc, ← add_one_mul, ← ha, sq]

lemma eq2 [Semiring R] [IsCancelAdd R] {a : ℕ → R} (ha : good a) (hn : a.Periodic (n + 1)) :
    ∑ k : Fin (n + 1), a k ^ 2 = ∑ k : Fin (n + 1), a k * a (k + 3) := by
  apply add_right_cancel (b := ∑ k : Fin (n + 1), a k); calc
    _ = ∑ k ∈ range (n + 1), a (k + 2) ^ 2 + ∑ k ∈ range (n + 1), a k :=
      congrArg₂ _ (sum_of_periodic (hn.comp _) 2).symm (sum_range _).symm
    _ = ∑ k ∈ range (n + 1), (a (k + 2) ^ 2 + a k) := sum_add_distrib.symm
    _ = ∑ k ∈ range (n + 1), (a k * a (k + 3) + a (k + 2)) := by simp only [ha.eq1]
    _ = ∑ k ∈ range (n + 1), _ + ∑ k ∈ range (n + 1), _ := sum_add_distrib
    _ = _ := congrArg₂ _ (sum_range _) (sum_of_periodic hn 2)

lemma eq3 [CommRing R] {a : ℕ → R} (ha : good a) (hn : a.Periodic (n + 1)) :
    ∑ k : Fin (n + 1), (a k - a (k + 3)) ^ 2 = 0 := calc
  _ = ∑ k : Fin (n + 1), a k ^ 2 + ∑ k : Fin (n + 1), a (k + 3) ^ 2
      - ∑ k : Fin (n + 1), 2 * (a k * a (k + 3)) := by
    simp only [sub_sq', mul_assoc]
    rw [sum_sub_distrib, sum_add_distrib]
  _ = 2 * ∑ k : Fin (n + 1), a k ^ 2 - 2 * ∑ k : Fin (n + 1), a k * a (k + 3) := by
    refine congrArg₂ _ ?_ (mul_sum _ _ _).symm
    rw [two_mul, add_right_inj, ← sum_range (λ x ↦ a (x + 3) ^ 2)]
    exact sum_of_periodic (hn.comp _) 3
  _ = _ := by rw [ha.eq2 hn, sub_self]


variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  {a : ℕ → R} (ha : good a) (hn : a.Periodic (n + 1))
include ha

open Fin.NatCast in
theorem exists_eq_stdGoodSeq_of_periodic3 (h : a.Periodic 3) : ∃ d, a = stdGoodSeq R d := by
  have X {x y z : R} (h : x * y + 1 = z) (h0 : y * z + 1 = x) : y = -1 ∨ x = z := by
    replace h0 : _ - _ = _ - _ := congrArg₂ (· - ·) h h0
    rwa [add_sub_add_right_eq_sub, mul_comm, ← mul_sub, ← neg_sub x,
      ← neg_one_mul, mul_eq_mul_right_iff, sub_eq_zero] at h0
  have h0 : a 0 = a 1 * a 2 + 1 := by rw [← ha, h]
  have h1 : a 1 = a 2 * a 0 + 1 := by rw [← h 1, ha 2, h]
  replace ha : a 2 = a 0 * a 1 + 1 := ha 0
  obtain h2 | h2 : a 0 = -1 ∨ a 2 = a 1 := X h1.symm ha.symm
  all_goals obtain h3 | h3 : a 1 = -1 ∨ a 0 = a 2 := X ha.symm h0.symm
  ---- Case 1: `a_0 = a_1 = -1`
  · rw [h2, h3, neg_mul_neg, one_mul, one_add_one_eq_two] at ha
    refine ⟨1, funext λ n ↦ ?_⟩
    rw [← h.map_mod_nat, ← Fin.val_natCast, stdGoodSeq]
    match (n : Fin 3) with | 0 => exact h2 | 1 => exact h3 | 2 => exact ha
  ---- Case 2: `a_0 = a_2 = -1`
  · rw [eq_comm, h2] at h3
    rw [h2, h3, neg_mul_neg, one_mul, one_add_one_eq_two] at h1
    refine ⟨2, funext λ n ↦ ?_⟩
    rw [← h.map_mod_nat, ← Fin.val_natCast, stdGoodSeq]
    match (n : Fin 3) with | 0 => exact h2 | 1 => exact h1 | 2 => exact h3
  ---- Case 3: `a_1 = a_2 = -1`
  · rw [h3] at h2; rw [h2, h3, neg_mul_neg, one_mul, one_add_one_eq_two] at h0
    refine ⟨0, funext λ n ↦ ?_⟩
    rw [← h.map_mod_nat, ← Fin.val_natCast, stdGoodSeq]
    match (n : Fin 3) with | 0 => exact h0 | 1 => exact h3 | 2 => exact h2
  ---- Case 4: `a_0 = a_1 = a_2`
  · rw [← h2, ← h3] at h0; clear h1 ha h2 h3 X h
    replace h0 : (2 * a 0 - 1) ^ 2 + 3 = 0 := calc
      _ = 4 * (a 0 * a 0 + 1 - a 0) := by ring
      _ = 0 := by rw [← h0, sub_self, mul_zero]
    exact absurd (add_pos_of_nonneg_of_pos (sq_nonneg _) three_pos) h0.not_gt

include hn

lemma periodic3_Fin_of_periodic (k : Fin (n + 1)) : a (k + 3) = a k := by
  have h := (sum_eq_zero_iff_of_nonneg λ k _ ↦ sq_nonneg _).mp (ha.eq3 hn) k (mem_univ k)
  rwa [sq_eq_zero_iff, sub_eq_zero, eq_comm] at h

open Fin.NatCast in
lemma periodic3_of_periodic : a.Periodic 3 := by
  intro m; have h := ha.periodic3_Fin_of_periodic hn m
  rwa [Fin.val_natCast, hn.map_mod_nat, ← hn.map_mod_nat,
    Nat.mod_add_mod, hn.map_mod_nat] at h

theorem three_dvd_period : 3 ∣ n + 1 := by
  obtain ⟨d, rfl⟩ := ha.exists_eq_stdGoodSeq_of_periodic3 (ha.periodic3_of_periodic hn)
  exact (stdGoodSeq_periodic_iff_three_dvd d R).mp hn

end good





/-! ### Final solution -/

theorem final_solution_general [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {a : ℕ → R} : (good a ∧ ∃ n, a.Periodic (n + 1)) ↔ ∃ d, a = stdGoodSeq R d :=
  ⟨λ ⟨ha, _, hn⟩ ↦ ha.exists_eq_stdGoodSeq_of_periodic3 (ha.periodic3_of_periodic hn),
    λ ⟨d, h⟩ ↦ h ▸ ⟨stdGoodSeq_is_good R d, 2, stdGoodSeq_periodic3 R d⟩⟩

theorem final_solution [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] {n : ℕ} :
    (∃ a : ℕ → R, good a ∧ a.Periodic (n + 1)) ↔ 3 ∣ n + 1 :=
  ⟨λ ⟨_, ha, hn⟩ ↦ ha.three_dvd_period hn,
  λ h ↦ ⟨stdGoodSeq R 0, stdGoodSeq_is_good R 0, stdGoodSeq_periodic_of_three_dvd R 0 h⟩⟩
