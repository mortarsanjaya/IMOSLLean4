/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.NatSequence.SeqMax
import Mathlib.Algebra.Ring.Int
import Mathlib.Algebra.Order.Group.Int

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

theorem add_one_iterate : ∀ n (a : ℤ), (· + 1)^[n] a = a + n
  | 0, a => a.add_zero.symm
  | n + 1, a => by rw [iterate_succ_apply', add_one_iterate n a, add_assoc]; rfl

theorem good_add_one : good (· + 1) := λ a b ↦ by
  have h (c : ℤ) : c + (c.natAbs ^ 2 : ℕ) = c * (c + 1) := by
    rw [Int.natCast_pow, Int.natAbs_sq, sq, ← mul_one_add c, add_comm]
  rw [add_one_iterate, Int.ofNat_add, add_add_add_comm, h, h]

theorem const_iterate (a b : α) : ∀ n, (λ _ ↦ b)^[n] a = bif n.beq 0 then a else b
  | 0 => rfl
  | _ + 1 => iterate_succ_apply' _ _ _

theorem good_zero : good (λ _ ↦ 0) := λ a b ↦ by
  rw [const_iterate, ← Int.add_mul, Int.mul_zero]
  cases h : (a.natAbs ^ 2 + b.natAbs ^ 2).beq 0 with
  | false => rfl
  | true => have h0 (c : ℤ) : c.natAbs ^ 2 = 0 ↔ c = 0 := by
              rw [sq_eq_zero_iff, Int.natAbs_eq_zero]
            rw [Nat.beq_eq, add_eq_zero, h0, h0] at h
            rw [h.1, h.2]; rfl





/- ### Solution -/

namespace good

variable (h : good f)

theorem map_iterate_sq (a : ℤ) : f^[a.natAbs ^ 2] a = a * f a := by
  have h := h a 0; rwa [zero_mul, add_zero, add_zero] at h

theorem map_neg_one : f (-1) = 0 := by
  have h : f (-1) = -1 * f (-1) := by exact map_iterate_sq h (-1)
  rw [neg_one_mul, eq_neg_iff_add_eq_zero, ← two_mul, mul_eq_zero] at h
  exact h.resolve_left (OfNat.ofNat_ne_zero 2)

theorem map_iterate_sq_add_one (a : ℤ) :
    f^[(a + 1).natAbs ^ 2 + 1] a = f^[(a + 1).natAbs ^ 2] (a + 1) := by
  have h0 := h (a + 1) (-1)
  rwa [add_neg_cancel_right, map_neg_one h, mul_zero, add_zero, ← map_iterate_sq h] at h0

theorem eq_add_one_of_injective (h0 : f.Injective) : f = (· + 1) :=
  funext λ a ↦ h0.iterate ((a + 1).natAbs ^ 2) (map_iterate_sq_add_one h a)

theorem exists_iter_add_large_eq (a : ℤ) : ∀ k, ∃ N, f^[N + k] a = f^[N] (a + k) := by
  refine Nat.rec ⟨0, a.add_zero.symm⟩ λ k h0 ↦ ?_
  rcases h0 with ⟨N, h0⟩
  refine ⟨N + (a + k + 1).natAbs ^ 2, ?_⟩
  rw [f.iterate_add_apply N, Nat.cast_succ, ← add_assoc a,
    ← map_iterate_sq_add_one h, Commute.iterate_iterate_self, ← h0,
    ← iterate_add_apply, add_comm _ (N + k), add_add_add_comm]

theorem orbit_zero_bdd_of_not_injective (h0 : ¬f.Injective) :
    ∃ M, ∀ n, (f^[n] 0).natAbs < M := by
  ---- First get `f(a + k) = f(a)` for some `k > 0`
  replace h0 : ∃ (a : ℤ) (k : ℕ), 0 < k ∧ f (a + k) = f a := by
    simp only [Injective, not_forall] at h0
    rcases h0 with ⟨x, y, h0, h1⟩
    wlog h2 : x < y
    · exact this h y x h0.symm (Ne.symm h1) ((Ne.lt_or_lt h1).resolve_left h2)
    apply sub_pos_of_lt at h2
    refine ⟨x, (y - x).natAbs, Int.natAbs_pos.mpr h2.ne.symm, ?_⟩
    rw [Int.natCast_natAbs, abs_of_pos h2, add_sub_cancel, h0]
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
    obtain ⟨K, M, h3⟩ : ∃ K M, f^[K] a = f^[M] 0 := by
      rcases le_total a 0 with h3 | h3
      · rcases exists_iter_add_large_eq h a a.natAbs with ⟨M, h4⟩
        rw [Int.natCast_natAbs, abs_of_nonpos h3, add_neg_self] at h4
        exact ⟨_, _, h4⟩
      · rcases exists_iter_add_large_eq h 0 a.natAbs with ⟨M, h4⟩
        rw [Int.natCast_natAbs, abs_of_nonneg h3, zero_add] at h4
        exact ⟨_, _, h4.symm⟩
    refine ⟨k, N + M, hk, ?_⟩
    rw [N.add_right_comm, f.iterate_add_apply, f.iterate_add_apply N M, ← h3,
      ← f.iterate_add_apply, Nat.add_comm, f.iterate_add_apply, h0,
      ← f.iterate_add_apply, ← f.iterate_add_apply, Nat.add_comm]
  ---- Now show that `|f^n(0)| < max{f^j(0) : j ≤ N + k} + 1` for all `n`
  rcases h0 with ⟨k, N, hk, h0⟩
  refine ⟨Extra.seqMax (λ n ↦ (f^[n] 0).natAbs) (N + k) + 1, ?_⟩
  suffices ∀ n, ∃ j ≤ N + k, f^[n] 0 = f^[j] 0 from λ n ↦ by
    obtain ⟨j, h1, h2⟩ := this n
    rw [h2, Nat.lt_succ_iff]
    exact Extra.le_seqMax_of_le (λ n ↦ (f^[n] 0).natAbs) h1
  ---- The goal reduces to `f^n(0) = f^j(0)` for some `j < N + k`
  refine Nat.rec ⟨0, (N + k).zero_le, rfl⟩ λ n ⟨j, hj, h1⟩ ↦ ?_
  obtain h2 | rfl : j < N + k ∨ j = N + k := hj.lt_or_eq
  · refine ⟨j.succ, h2, ?_⟩
    rw [f.iterate_succ_apply', h1, f.iterate_succ_apply']
  · refine ⟨N + 1, Nat.add_le_add_left hk _, ?_⟩
    rw [f.iterate_succ_apply', h1, h0, f.iterate_succ_apply']

theorem eq_zero_of_not_injective (h0 : ∃ M, ∀ n, (f^[n] 0).natAbs < M) : f = 0 := by
  rcases h0 with ⟨M, h0⟩
  have h1 (a : ℤ) : f^[2 * a.natAbs ^ 2] 0 = a * (f a - f (-a)) := by
    have h1 := h a (-a); rwa [a.natAbs_neg, add_neg_self,
      ← two_mul, neg_mul, ← sub_eq_add_neg, ← mul_sub] at h1
  replace h0 (n) (ha : M ≤ n) : f^[2 * n ^ 2] 0 = 0 := by
    refine Int.natAbs_eq_zero.mp <| Nat.eq_zero_of_dvd_of_lt
      ⟨(f n - f (-n)).natAbs, ?_⟩ ((h0 _).trans_le ha)
    have h2 : f^[2 * n ^ 2] 0 = _ := h1 n
    rw [h2, Int.natAbs_mul, Int.natAbs_ofNat]
  replace h0 : f^[2] 0 = 0 := by
    have h2 : M ≤ M ^ 2 + 1 := sq M ▸ Nat.le_succ_of_le M.le_mul_self
    replace h2 := h0 (M ^ 2 + 1) h2
    rwa [add_sq, sq, Nat.mul_one, ← Nat.add_mul, one_pow, Nat.mul_add_one,
      Nat.add_comm, f.iterate_add_apply, ← Nat.mul_assoc, Nat.mul_right_comm,
      f.iterate_mul, Function.iterate_fixed (h0 M M.le_refl)] at h2
  replace h1 (a : ℤ) (ha : a ≠ 0) : f a = 0 := by
    replace h1 : f a = f (-a) := by
      specialize h1 a
      rw [f.iterate_mul, Function.iterate_fixed h0, eq_comm, Int.mul_eq_zero] at h1
      exact eq_of_sub_eq_zero (h1.resolve_left ha)
    have h2 := h.map_iterate_sq (-a)
    obtain ⟨n, h3⟩ : ∃ n : ℕ, a.natAbs ^ 2 = n.succ :=
      Nat.exists_eq_succ_of_ne_zero (pow_ne_zero 2 (Int.natAbs_ne_zero.mpr ha))
    rwa [Int.natAbs_neg, h3, f.iterate_succ_apply, ← h1, ← f.iterate_succ_apply, ← h3,
      h.map_iterate_sq, neg_mul, eq_neg_iff_add_eq_zero, ← Int.two_mul, Int.mul_eq_zero,
      or_iff_right (OfNat.ofNat_ne_zero 2), Int.mul_eq_zero, or_iff_right ha] at h2
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
