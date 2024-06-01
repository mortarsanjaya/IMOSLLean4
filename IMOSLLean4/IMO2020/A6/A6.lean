/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.RingTheory.Int.Basic
import Mathlib.Dynamics.PeriodicPts
import IMOSLLean4.Extra.SeqMax

/-!
# IMO 2020 A6

Find all functions $f : ℤ → ℤ$ such that, for any $a, b ∈ ℤ$,
$$ f^{a^2 + b^2}(a + b) = a f(a) + b f(b). $$
-/

namespace IMOSL
namespace IMO2020A6

open Function

def good (f : ℤ → ℤ) :=
  ∀ a b : ℤ, f^[a.natAbs ^ 2 + b.natAbs ^ 2] (a + b) = a * f a + b * f b





/- ## Answer -/

theorem add_one_iterate : ∀ n (a : ℤ), (· + 1)^[n] a = a + n
  | 0, a => a.add_zero.symm
  | n + 1, a => by rw [iterate_succ_apply', add_one_iterate n a, add_assoc]; rfl

theorem good_add_one : good (· + 1) := λ a b ↦ by
  have h (c : ℤ) : c + ((c.natAbs ^ 2 : ℕ) : ℤ) = c * (c + 1) := by
    rw [Int.natCast_pow, Int.natAbs_sq, sq, ← mul_one_add, add_comm]
  rw [add_one_iterate, Int.ofNat_add, add_add_add_comm, h, h]

theorem const_iterate (a b : α) :
    ∀ n, (λ _ ↦ b)^[n] a = bif n.beq 0 then a else b
  | 0 => rfl
  | _ + 1 => iterate_succ_apply' _ _ _

theorem good_zero : good (λ _ ↦ 0) := λ a b ↦ by
  rw [const_iterate, ← Int.add_mul, Int.mul_zero]
  cases h : (a.natAbs ^ 2 + b.natAbs ^ 2).beq 0
  · rfl
  · have h0 : ∀ c : ℤ, c.natAbs ^ 2 = 0 ↔ c = 0 :=
      λ c ↦ by rw [sq_eq_zero_iff, Int.natAbs_eq_zero]
    rw [Nat.beq_eq, add_eq_zero, h0, h0] at h
    rw [h.1, h.2]; rfl





/- ## Solution -/

section Solution

variable (h : good f)

theorem map_iterate_sq (a : ℤ) : f^[a.natAbs ^ 2] a = a * f a := by
  have h := h a 0; rwa [zero_mul, add_zero, add_zero] at h

theorem map_neg_one : f (-1) = 0 :=
  eq_zero_of_neg_eq <| (neg_eq_neg_one_mul _).trans (map_iterate_sq h (-1)).symm

theorem map_iterate_sq_add_one (a : ℤ) :
    f^[(a + 1).natAbs ^ 2 + 1] a = f^[(a + 1).natAbs ^ 2] (a + 1) := by
  have h0 := h (a + 1) (-1)
  rwa [add_neg_cancel_right, map_neg_one h,
    mul_zero, add_zero, ← map_iterate_sq h] at h0

theorem eq_add_one_of_injective (h0 : f.Injective) : f = (· + 1) :=
  funext λ a ↦ h0.iterate ((a + 1).natAbs ^ 2) <| map_iterate_sq_add_one h a

theorem exists_iter_add_large_eq (a : ℤ) :
    ∀ k : ℕ, ∃ N : ℕ, f^[N + k] a = f^[N] (a + k)
  | 0 => ⟨0, a.add_zero.symm⟩
  | k + 1 => by
      rcases exists_iter_add_large_eq a k with ⟨N, h0⟩
      refine ⟨N + (a + k + 1).natAbs ^ 2, ?_⟩
      rw [f.iterate_add_apply N, Nat.cast_succ, ← add_assoc a,
        ← map_iterate_sq_add_one h, Commute.iterate_iterate_self, ← h0,
        ← iterate_add_apply, add_comm _ (N + k), add_add_add_comm]

theorem orbit_zero_bdd_of_not_injective (h0 : ¬f.Injective) :
    ∃ M : ℤ, ∀ n : ℕ, |f^[n] 0| < M := by
  ---- Reduce to show that the the orbit of `0` eventually repeats
  suffices ∃ N : ℕ, 0 < f.minimalPeriod (f^[N] 0) by
    rcases this with ⟨N, h1⟩
    let k := f.minimalPeriod (f^[N] 0)
    let F := λ n ↦ |f^[n] 0|
    refine ⟨Extra.seqMax F (N + k) + 1, λ n ↦ Int.lt_add_one_of_le <|
      (n.le_total (N + k)).elim (Extra.le_seqMax_of_le F) (λ h2 ↦ ?_)⟩
    rw [le_iff_exists_add] at h2; rcases h2 with ⟨c, rfl⟩
    rw [add_rotate, iterate_add_apply, ← iterate_mod_minimalPeriod_eq,
      Nat.add_mod_left, ← iterate_add_apply, add_comm]
    exact Extra.le_seqMax_of_le F (add_le_add_left (c.mod_lt h1).le N)
  ---- Find `a : ℤ` and `k > 0` such that `f(a + k) = f(a)`
  obtain ⟨a, k, h1, h2⟩ : ∃ (a : ℤ) (k : ℕ), 0 < k ∧ f (a + k) = f a := by
    suffices ∃ a b, a < b ∧ f a = f b by
      rcases this with ⟨a, b, h1, h2⟩
      apply sub_pos_of_lt at h1
      refine ⟨a, (b - a).natAbs, Int.natAbs_pos.mpr h1.ne.symm, ?_⟩
      rw [Int.natCast_natAbs, abs_of_pos h1, add_sub_cancel, h2]
    simp_rw [Injective, not_forall] at h0
    rcases h0 with ⟨a, b, h0, h1⟩
    rcases ne_iff_lt_or_gt.mp h1 with h2 | h2
    exacts [⟨a, b, h2, h0⟩, ⟨b, a, h2, h0.symm⟩]
  -- Find `K M : ℕ` such that `f^[K] a = f^[M] 0`
  obtain ⟨K, M, h3⟩ : ∃ K M, f^[K] a = f^[M] 0 := by
    rcases le_total a 0 with h3 | h3
    · rcases exists_iter_add_large_eq h a a.natAbs with ⟨N, h4⟩
      rw [Int.natCast_natAbs, abs_of_nonpos h3, add_neg_self] at h4
      exact ⟨_, _, h4⟩
    · rcases exists_iter_add_large_eq h 0 a.natAbs with ⟨N, h4⟩
      rw [Int.natCast_natAbs, abs_of_nonneg h3, zero_add] at h4
      exact ⟨_, _, h4.symm⟩
  -- Finishing
  rcases exists_iter_add_large_eq h a k with ⟨N, h4⟩
  refine ⟨N + 1 + M, IsPeriodicPt.minimalPeriod_pos h1 ?_⟩
  rw [iterate_add_apply, ← h3, Commute.iterate_iterate_self]
  refine IsPeriodicPt.apply_iterate ?_ _
  rw [IsPeriodicPt, IsFixedPt, ← iterate_add_apply,
    iterate_succ_apply, ← h2, Commute.iterate_self, ← h4,
    add_left_comm, ← add_assoc, iterate_succ_apply']

theorem eq_zero_of_not_injective (h0 : ∃ M : ℤ, ∀ n : ℕ, |f^[n] 0| < M) :
    f = 0 := by
  -- Start with `f^2(0) = 0` and `∀ a, a ≠ 0 → f(-a) = f(a)`
  rcases h0 with ⟨M, h0⟩
  have h1 (a : ℤ) : f^[2 * a.natAbs ^ 2] 0 = a * (f a - f (-a)) := by
    have h := h a (-a); rwa [a.natAbs_neg, add_neg_self,
      ← two_mul, neg_mul, ← sub_eq_add_neg, ← mul_sub] at h
  replace h0 (a : ℤ) (h2 : M ≤ a) : f.IsPeriodicPt (2 * a.natAbs ^ 2) 0 :=
    Int.eq_zero_of_abs_lt_dvd ⟨_, h1 a⟩ ((h0 _).trans_le h2)
  replace h0 : f.IsPeriodicPt 2 0 := by
    have h2 := (h0 _ M.le_refl).gcd (h0 _ M.lt_succ.le)
    have h3 : IsCoprime M (M + 1) :=
      ⟨-1, 1, by rw [one_mul, neg_one_mul, neg_add_cancel_left]⟩
    rwa [Nat.gcd_mul_left, ← Int.natAbs_pow, ← Int.natAbs_pow,
      ← Int.gcd_eq_natAbs, Int.gcd_eq_one_iff_coprime.mpr h3.pow, mul_one] at h2
  replace h1 (a : ℤ) (h3 : a ≠ 0) : f a = f (-a) := by
    specialize h1 a
    rw [h0.mul_const, zero_eq_mul] at h1
    exact eq_of_sub_eq_zero (h1.resolve_left h3)
  -- Now prove that `f = 0`
  suffices h2 : ∀ a : ℤ, a ≠ 0 → f a = 0 by
    have h3 : f (f 2) = 1 * f 1 + 1 * f 1 := h 1 1
    rw [h2 1 one_ne_zero, h2 _ two_ne_zero] at h3
    exact funext λ a ↦ (ne_or_eq a 0).elim (h2 a) (λ h4 ↦ h4.symm ▸ h3)
  intro a h2
  obtain ⟨n, h3⟩ : ∃ n : ℕ, a.natAbs ^ 2 = n.succ :=
    Nat.exists_eq_succ_of_ne_zero (pow_ne_zero 2 <| Int.natAbs_ne_zero.mpr h2)
  have h4 := map_iterate_sq h (-a)
  rw [Int.natAbs_neg, h3, iterate_succ_apply, ← h1 a h2, ← iterate_succ_apply,
    ← h3, map_iterate_sq h, neg_mul, eq_neg_self_iff, mul_eq_zero] at h4
  exact h4.resolve_left h2

end Solution





/-- Final solution -/
theorem final_solution {f : ℤ → ℤ} : good f ↔ f = (· + 1) ∨ f = λ _ ↦ 0 :=
  ⟨λ h ↦ (em f.Injective).imp (eq_add_one_of_injective h)
    (λ h0 ↦ eq_zero_of_not_injective h <| orbit_zero_bdd_of_not_injective h h0),
  λ h ↦ h.elim (λ h0 ↦ h0 ▸ good_add_one) (λ h0 ↦ h0 ▸ good_zero)⟩
