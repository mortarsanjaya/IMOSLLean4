/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Int.Init
import Mathlib.Data.Nat.Basic
import Mathlib.Logic.Function.Iterate
import IMOSLLean4.Extra.NatSequence.SeqMax
import Mathlib.Tactic.Lift

/-!
# IMO 2020 A6

Find all functions $f : ℤ → ℤ$ such that, for any $a, b ∈ ℤ$,
$$ f^{a^2 + b^2}(a + b) = a f(a) + b f(b). $$
-/

namespace IMOSL
namespace IMO2020A6

open Function

def good (f : ℤ → ℤ) := ∀ a b, f^[a.natAbs ^ 2 + b.natAbs ^ 2] (a + b) = a * f a + b * f b





/- ### Answer -/

theorem add_one_iterate : ∀ n (a : ℤ), (· + 1)^[n] a = a + n := by
  refine Nat.rec (λ a ↦ a.add_zero.symm) (λ n h a ↦ ?_)
  rw [iterate_succ_apply', h, Int.add_assoc]; rfl

theorem good_add_one : good (· + 1) := λ a b ↦ by
  have h (c : ℤ) : c + (c.natAbs ^ 2 : ℕ) = c * (c + 1) := by
    rw [Int.natCast_pow, Int.natAbs_sq, Int.pow_succ, Int.pow_succ,
      Int.pow_zero, c.one_mul, Int.mul_add, Int.mul_one, Int.add_comm]
  rw [add_one_iterate, Int.natCast_add, ← h, ← h,
    a.add_assoc, b.add_left_comm, ← a.add_assoc]

theorem const_iterate {α : Type*} (a b : α) :
    ∀ n, (λ _ ↦ b)^[n] a = bif n.beq 0 then a else b
  | 0 => rfl
  | _ + 1 => iterate_succ_apply' _ _ _

theorem good_zero : good (λ _ ↦ 0) := λ a b ↦ by
  rw [const_iterate, ← Int.add_mul, Int.mul_zero]
  cases h : (a.natAbs ^ 2 + b.natAbs ^ 2).beq 0 with | false => rfl | true => ?_
  have h0 (c : ℤ) : c.natAbs ^ 2 = 0 ↔ c = 0 := by
    rw [Nat.pow_eq_zero, and_iff_left (Nat.succ_ne_zero 1), Int.natAbs_eq_zero]
  rw [Nat.beq_eq, Nat.add_eq_zero, h0, h0] at h
  rw [h.1, h.2]; rfl





/- ### Solution -/

namespace good

variable (h : good f)
include h

theorem map_iterate_sq (a : ℤ) : f^[a.natAbs ^ 2] a = a * f a := by
  have h := h a 0; rwa [Int.zero_mul, Int.add_zero, Int.add_zero] at h

theorem map_neg_one : f (-1) = 0 := by
  have h : f (-1) = -1 * f (-1) := by exact map_iterate_sq h (-1)
  rw [Int.neg_mul, Int.one_mul, ← Int.add_left_inj (k := f (-1)),
    Int.add_left_neg, ← Int.two_mul, Int.mul_eq_zero] at h
  exact h.resolve_left (ne_of_beq_false rfl)

theorem map_iterate_sq_add_one (a : ℤ) :
    f^[(a + 1).natAbs ^ 2 + 1] a = f^[(a + 1).natAbs ^ 2] (a + 1) := by
  have h0 := h (a + 1) (-1)
  rwa [Int.add_neg_cancel_right, map_neg_one h,
    Int.mul_zero, Int.add_zero, ← map_iterate_sq h] at h0

theorem eq_add_one_of_injective (h0 : f.Injective) : f = (· + 1) :=
  funext λ a ↦ h0.iterate ((a + 1).natAbs ^ 2) (map_iterate_sq_add_one h a)

theorem exists_iter_add_large_eq (a : ℤ) : ∀ k, ∃ N, f^[N + k] a = f^[N] (a + k) := by
  refine Nat.rec ⟨0, a.add_zero.symm⟩ λ k h0 ↦ ?_
  rcases h0 with ⟨N, h0⟩
  refine ⟨N + (a + k + 1).natAbs ^ 2, ?_⟩
  rw [f.iterate_add_apply N, Int.natCast_succ, ← a.add_assoc,
    ← map_iterate_sq_add_one h, Commute.iterate_iterate_self, ← h0,
    ← iterate_add_apply, Nat.add_comm _ (N + k), Nat.add_add_add_comm]

theorem orbit_zero_bdd_of_not_injective (h0 : ¬f.Injective) :
    ∃ M, ∀ n, (f^[n] 0).natAbs < M := by
  ---- First get `f(a + k) = f(a)` for some `k > 0`
  replace h0 : ∃ (a : ℤ) (k : ℕ), 0 < k ∧ f (a + k) = f a := by
    simp only [Injective, not_forall] at h0
    obtain ⟨x, y, h0, h1⟩ : ∃ x y, x < y ∧ f x = f y := by
      rcases h0 with ⟨x, y, h0, h1⟩
      obtain h1 | h1 : x < y ∨ y < x := Int.lt_or_lt_of_ne h1
      exacts [⟨x, y, h1, h0⟩, ⟨y, x, h1, h0.symm⟩]
    replace h0 := Int.sub_pos_of_lt h0
    lift y - x to ℕ using Int.le_of_lt h0 with k hk
    refine ⟨x, k, Int.natCast_pos.mp h0, ?_⟩
    rw [hk, ← Int.add_sub_assoc, x.add_comm, y.add_sub_cancel, h1]
  ---- Upgrade to `f^k` having a fixed point of form `f^N(a)`
  replace h0 : ∃ a k N, 0 < k ∧ f^[N + k] a = f^[N] a := by
    rcases h0 with ⟨a, k, hk, h0⟩
    obtain ⟨N, h1⟩ := exists_iter_add_large_eq h a k
    refine ⟨a, k, N + 1, hk, ?_⟩
    rw [Nat.add_right_comm, f.iterate_succ_apply', h1, ← f.iterate_succ_apply']
    exact congrArg f^[N] h0
  ---- Upgrade to `f^k` having a fixed point of form `f^N(0)`
  replace h0 : ∃ k N, 0 < k ∧ f^[N + k] 0 = f^[N] 0 := by
    rcases h0 with ⟨a, k, N, hk, h0⟩
    obtain ⟨K, M, h1⟩ : ∃ K M, f^[K] a = f^[M] 0 := by
      obtain h1 | h1 : 0 ≤ -a ∨ 0 ≤ a :=
        (Int.le_total a 0).imp_left (Int.neg_nonneg_of_nonpos)
      · lift -a to ℕ using h1 with m hm
        rcases exists_iter_add_large_eq h a m with ⟨M, h2⟩
        rw [hm, Int.add_right_neg] at h2; exact ⟨M + m, M, h2⟩
      · lift a to ℕ using h1
        rcases exists_iter_add_large_eq h 0 a with ⟨M, h2⟩
        rw [Int.zero_add, eq_comm] at h2; exact ⟨M, M + a, h2⟩
    refine ⟨k, N + M, hk, ?_⟩
    rw [N.add_right_comm, f.iterate_add_apply, f.iterate_add_apply N M,
      ← h1, ← f.iterate_add_apply, Nat.add_comm, f.iterate_add_apply,
      h0, ← f.iterate_add_apply, ← f.iterate_add_apply, Nat.add_comm]
  ---- Now show that `|f^n(0)| < max{f^j(0) : j ≤ N + k} + 1` for all `n`
  rcases h0 with ⟨k, N, hk, h0⟩
  refine ⟨Extra.seqMax (λ n ↦ (f^[n] 0).natAbs) (N + k) + 1, ?_⟩
  suffices ∀ n, ∃ j ≤ N + k, f^[n] 0 = f^[j] 0 from λ n ↦ by
    obtain ⟨j, h1, h2⟩ := this n
    rw [h2, Nat.lt_succ_iff]
    exact Extra.le_seqMax_of_le (λ n ↦ (f^[n] 0).natAbs) h1
  ---- The goal reduces to `f^n(0) = f^j(0)` for some `j < N + k`
  refine Nat.rec ⟨0, (N + k).zero_le, rfl⟩ λ n ⟨j, hj, h1⟩ ↦ ?_
  obtain h2 | rfl : j < N + k ∨ j = N + k := Nat.lt_or_eq_of_le hj
  · refine ⟨j.succ, h2, ?_⟩
    rw [f.iterate_succ_apply', h1, f.iterate_succ_apply']
  · refine ⟨N + 1, Nat.add_le_add_left hk _, ?_⟩
    rw [f.iterate_succ_apply', h1, h0, f.iterate_succ_apply']

theorem eq_zero_of_not_injective (h0 : ∃ M, ∀ n, (f^[n] 0).natAbs < M) : f = λ _ ↦ 0 := by
  rcases h0 with ⟨M, h0⟩
  have h1 (a : ℤ) : f^[2 * a.natAbs ^ 2] 0 = a * (f a - f (-a)) := by
    have h1 := h a (-a); rwa [a.natAbs_neg, Int.add_right_neg,
      ← Nat.two_mul, Int.neg_mul, ← Int.sub_eq_add_neg, ← Int.mul_sub] at h1
  replace h0 (n) (ha : M ≤ n) : f^[2 * n ^ 2] 0 = 0 := by
    refine Int.natAbs_eq_zero.mp <| Nat.eq_zero_of_dvd_of_lt
      ⟨(f n - f (-n)).natAbs, ?_⟩ (Nat.lt_of_lt_of_le (h0 _) ha)
    have h2 : f^[2 * n ^ 2] 0 = _ := h1 n
    rw [h2, Int.natAbs_mul, Int.natAbs_natCast]
  replace h0 : f^[2] 0 = 0 := by
    have h2 : M ≤ M ^ 2 + 1 := M.pow_two ▸ Nat.le_succ_of_le M.le_mul_self
    replace h2 := h0 (M ^ 2 + 1) h2
    rwa [Nat.pow_two, (M ^ 2).succ_mul, ← Nat.add_assoc, ← Nat.mul_succ,
      Nat.mul_add_one, Nat.add_comm, f.iterate_add_apply, ← Nat.mul_assoc,
      f.iterate_mul, Function.iterate_fixed (h0 M M.le_refl)] at h2
  replace h1 (a : ℤ) (ha : a ≠ 0) : f a = 0 := by
    replace h1 : f a = f (-a) := by
      specialize h1 a
      rw [f.iterate_mul, Function.iterate_fixed h0, eq_comm, Int.mul_eq_zero] at h1
      exact Int.eq_of_sub_eq_zero (h1.resolve_left ha)
    have h2 := h.map_iterate_sq (-a)
    obtain ⟨n, h3⟩ : ∃ n : ℕ, a.natAbs ^ 2 = n.succ := by
      apply Nat.exists_eq_succ_of_ne_zero
      rw [Ne, Nat.pow_eq_zero, not_and_or, Int.natAbs_eq_zero]
      left; exact ha
    rwa [Int.natAbs_neg, h3, f.iterate_succ_apply, ← h1, ← f.iterate_succ_apply, ← h3,
      h.map_iterate_sq, Int.neg_mul, ← Int.add_left_inj (k := a * f a), Int.add_left_neg,
      ← Int.two_mul, Int.mul_eq_zero, or_iff_right (ne_of_beq_false (by rfl)),
      Int.mul_eq_zero, or_iff_right ha] at h2
  funext a; obtain ha | rfl : a ≠ 0 ∨ a = 0 := ne_or_eq a 0
  · exact h1 a ha
  · have h2 : f (f (-2)) = -1 * f (-1) + -1 * f (-1) := by exact h (-1) (-1)
    have h3 : (-2 : ℤ) ≠ 0 := ne_of_beq_false rfl
    rwa [h.map_neg_one, Int.mul_zero, Int.add_zero, h1 (-2) h3] at h2

end good





/-- Final solution -/
theorem final_solution {f : ℤ → ℤ} : good f ↔ f = (· + 1) ∨ f = λ _ ↦ 0 :=
  ⟨λ h ↦ (em f.Injective).imp h.eq_add_one_of_injective
    (λ h0 ↦ h.eq_zero_of_not_injective (h.orbit_zero_bdd_of_not_injective h0)),
  λ h ↦ h.elim (λ h0 ↦ h0 ▸ good_add_one) (λ h0 ↦ h0 ▸ good_zero)⟩
