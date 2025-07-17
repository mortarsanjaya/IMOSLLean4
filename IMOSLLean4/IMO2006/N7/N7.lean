/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Finset.Card

/-!
# IMO 2006 N7

Prove that for any $b ∈ ℕ$ and $n ∈ ℕ^+$, there exists $m ∈ ℕ$ such that $n ∣ b^m + m$.
-/

namespace IMOSL
namespace IMO2006N7

/-! ### Extra lemmas -/

section

open Finset

/-- Given `b n : ℕ` with `n > 1`, there exists `M k : ℕ`
  with `0 < k < n` such that `b^{M + k} ≡ b^M (mod n)`. -/
theorem exists_ne_pow_eq (hn : 1 < n) (b) :
    ∃ M k, 0 < k ∧ k < n ∧ b ^ (M + k) % n = b ^ M % n := by
  ---- If `n ∣ b^M` for some `M`, we are done
  obtain ⟨M, h⟩ | h : (∃ M, b ^ M % n = 0) ∨ (∀ M, b ^ M % n ≠ 0) :=
    Classical.exists_or_forall_not _
  · refine ⟨M, 1, Nat.one_pos, hn, ?_⟩
    rw [Nat.pow_succ, ← Nat.mod_mul_mod, h, Nat.zero_mul, Nat.zero_mod]
  ---- Now assume that `n ∤ b^M` for all `M`
  obtain ⟨x, hx, y, hy, h0, h1⟩ :
      ∃ x ∈ range n, ∃ y ∈ range n, x ≠ y ∧ b ^ x % n = b ^ y % n := by
    replace hn : 0 < n := Nat.zero_lt_of_lt hn
    refine exists_ne_map_eq_of_card_lt_of_maps_to (t := (range n).filter (· ≠ 0))
      (card_lt_card (filter_ssubset.mpr ⟨0, mem_range.mpr hn, λ h ↦ h rfl⟩)) ?_
    rintro M -; rw [coe_filter, Set.mem_setOf_eq, mem_range, ne_eq]
    exact ⟨Nat.mod_lt _ hn, h M⟩
  wlog h2 : x < y
  · exact this hn b h y hy x hx h0.symm h1.symm (h0.lt_or_gt.resolve_left h2)
  refine ⟨x, y - x, Nat.sub_pos_of_lt h2, (y.sub_le x).trans_lt (mem_range.mp hy), ?_⟩
  rw [Nat.add_sub_cancel' h2.le, h1]

theorem dvd_of_add_mod_eq_mod {a d k : ℕ} (h : (a + k) % d = a % d) : d ∣ k := by
  obtain rfl | hd : d = 0 ∨ 0 < d := d.eq_zero_or_pos
  · rwa [Nat.mod_zero, Nat.mod_zero, Nat.add_eq_left, ← Nat.zero_dvd] at h
  · replace h := Nat.add_mod_eq_add_mod_left (d.pred * a) h
    rwa [← Nat.add_assoc, ← Nat.succ_mul, Nat.succ_pred_eq_of_pos hd, ← Nat.mod_add_mod,
      Nat.mul_mod_right, Nat.zero_add, ← Nat.dvd_iff_mod_eq_zero] at h

theorem exists_mod_eq_mul_add_of_dvd (hn : 0 < n) (h : a % d = b % d) :
    ∃ t, a % n = (b + d * t) % n := by
  obtain ⟨k, rfl⟩ | ⟨k, rfl⟩ : (∃ k, a = b + k) ∨ (∃ k, b = a + k) :=
    (Nat.le_total b a).imp Nat.exists_eq_add_of_le Nat.exists_eq_add_of_le
  · obtain ⟨t, rfl⟩ : d ∣ k := dvd_of_add_mod_eq_mod h
    exact ⟨t, rfl⟩
  · obtain ⟨t, rfl⟩ : d ∣ k := dvd_of_add_mod_eq_mod h.symm
    refine ⟨t * n.pred, ?_⟩
    rw [← a.add_right_comm, a.add_assoc, ← d.mul_assoc, ← Nat.mul_succ,
      Nat.succ_pred_eq_of_pos hn, Nat.add_mul_mod_self_right]

end





/-! ### Start of the problem -/

/-- The general claim -/
theorem general_claim (hn : 0 < n) (b) : ∀ N r, ∃ m ≥ N, (b ^ m + m) % n = r % n := by
  ---- Step 1: Set up the induction and immediately solve the base case
  induction' n using Nat.strong_induction_on with n n_ih
  rw [← Nat.succ_le_iff, le_iff_eq_or_lt] at hn
  rcases hn with rfl | hn
  · refine λ N _ ↦ ⟨N, N.le_refl, ?_⟩
    rw [Nat.mod_one, Nat.mod_one]
  ---- Step 2: Get a period `k < n`, then deduce the IH on `k`
  obtain ⟨M, k, hk, hk0, h⟩ : ∃ M k, 0 < k ∧ k < n ∧ b ^ (M + k) % n = b ^ M % n :=
    exists_ne_pow_eq hn b
  replace n_ih : ∀ N r, ∃ m ≥ N, (b ^ m + m) % k = r % k := n_ih k hk0 hk
  ---- Step 3: Obtain `m' ≥ max{M, N}` such that `2^{m'} + m' ≡ r (mod d)`
  intro N r; obtain ⟨m', hm'N, hm'M, h0⟩ : ∃ m ≥ N, m ≥ M ∧ (b ^ m + m) % k = r % k := by
    obtain ⟨m', hm', h0⟩ := n_ih (M + N) r
    exact ⟨m', (N.le_add_left M).trans hm', Nat.le_of_add_right_le hm', h0⟩
  ---- Step 4: Prove the property `2^{m' + ks} ≡ 2^{m'} (mod d)` for all `s`
  replace h : ∀ s, b ^ (m' + k * s) % n = b ^ m' % n := by
    replace h : b ^ (m' + k) % n = b ^ m' % n := by
      rw [← Nat.add_sub_cancel' hm'M, Nat.add_right_comm, Nat.pow_add,
        ← Nat.mod_mul_mod, h, Nat.mod_mul_mod, Nat.pow_add]
    refine Nat.rec rfl λ s h1 ↦ ?_
    rw [Nat.mul_succ, ← Nat.add_assoc, Nat.pow_add,
      ← Nat.mod_mul_mod, h1, Nat.mod_mul_mod, ← Nat.pow_add, h]
  ---- Step 5: Find the desired `t` and `s`, and finish
  replace hn : 0 < n := hk.trans hk0
  obtain ⟨t, ht⟩ : ∃ t, (b ^ m' + m') % n = (r + k * t) % n :=
    exists_mod_eq_mul_add_of_dvd hn h0
  obtain ⟨s, C, hC⟩ : ∃ s, n ∣ k * t + k * s := by
    refine ⟨t * n.pred, ?_⟩
    rw [← Nat.mul_assoc, Nat.add_comm, ← Nat.mul_succ, Nat.succ_pred_eq_of_pos hn]
    exact ⟨k * t, (k * t).mul_comm n⟩
  refine ⟨m' + k * s, Nat.le_add_right_of_le hm'N, ?_⟩
  rw [← Nat.mod_add_mod, h, Nat.mod_add_mod, ← Nat.add_assoc, ← Nat.mod_add_mod,
    ht, Nat.mod_add_mod, Nat.add_assoc, hC, Nat.add_mul_mod_self_left]

/-- Final solution -/
theorem final_solution (hn : 0 < n) (b) : ∃ m, n ∣ b ^ m + m :=
  (general_claim hn b 0 0).imp λ _ h ↦ Nat.dvd_of_mod_eq_zero h.2
