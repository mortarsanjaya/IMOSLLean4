/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.NatSequence.AntitoneConst
import IMOSLLean4.Extra.NatSequence.EventuallyEqual
import IMOSLLean4.Extra.NatSequence.OfList.Basic
import IMOSLLean4.Extra.Infinitesimal.Archimedean

/-!
# IMO 2006 A1

Let $R$ be an archimedean ring with floor.
Denote $f(x) = ⌊x⌋ (x - ⌊x⌋)$ for any $x ∈ R$.
Prove that for any $r ∈ R$, there exists $N ∈ ℕ$ such that
  $f^{k + 2}(r) = f^k(r)$ for all $k ≥ N$.
-/

namespace IMOSL
namespace IMO2006A1

open Extra

variable [LinearOrderedRing R] [FloorRing R]

instance : Inhabited R := ⟨0⟩

abbrev f (r : R) := ⌊r⌋ * Int.fract r

theorem floor_f_nonneg {r : R} (h : 0 ≤ ⌊r⌋) : 0 ≤ ⌊f r⌋ :=
  Int.floor_nonneg.mpr <| mul_nonneg (Int.cast_nonneg.mpr h) (Int.fract_nonneg r)

theorem floor_f_nonpos {r : R} (h : ⌊r⌋ ≤ 0) : ⌊f r⌋ ≤ 0 :=
  Int.cast_le.mp <| (Int.floor_le _).trans <| Int.cast_zero (R := R) ▸
    mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr h) (Int.fract_nonneg r)

theorem floor_f_natAbs_le (r : R) : ⌊f r⌋.natAbs ≤ ⌊r⌋.natAbs := by
  rw [← Nat.cast_le (α := ℤ), Int.cast_natAbs, Int.cast_natAbs,
    Int.cast_abs, Int.cast_id, Int.cast_abs, Int.cast_id]
  rcases le_total 0 ⌊r⌋ with h | h
  · rw [abs_eq_self.mpr h, abs_eq_self.mpr (floor_f_nonneg h), ← Int.cast_le (R := R)]
    exact (Int.floor_le _).trans <| mul_le_of_le_one_right
      (Int.cast_nonneg.mpr h) (Int.fract_lt_one r).le
  · rw [abs_eq_neg_self.mpr h, abs_eq_neg_self.mpr (floor_f_nonpos h),
      neg_le_neg_iff, Int.le_floor]
    exact le_mul_of_le_one_right (Int.cast_nonpos.mpr h) (Int.fract_lt_one r).le

theorem floor_f_iter_natAbs_le (r : R) : ∀ k, ⌊f^[k] r⌋.natAbs ≤ ⌊r⌋.natAbs
  | 0 => le_refl _
  | k + 1 => (floor_f_iter_natAbs_le _ k).trans (floor_f_natAbs_le r)

theorem floor_f_iter_natAbs_eventually_const (r : R) :
    ∃ C, EventuallyEqual (⌊f^[·] r⌋.natAbs) (λ _ ↦ C) :=
  have ha : Antitone (λ k ↦ ⌊f^[k] r⌋.natAbs) := λ k m h0 ↦ by
    rcases Nat.exists_eq_add_of_le h0 with ⟨c, rfl⟩
    simp only; rw [Nat.add_comm, f.iterate_add_apply]
    exact floor_f_iter_natAbs_le _ c
  (NatSeq_antitone_imp_const ha).elim λ C ⟨N, ha⟩ ↦ ⟨C, N, 0, ha⟩

theorem floor_f_lt_of_floor_pos {r : R} (h : 0 < ⌊r⌋) : ⌊f r⌋ < ⌊r⌋ :=
  Int.floor_lt.mpr <| mul_lt_of_lt_one_right (Int.cast_pos.mpr h) (Int.fract_lt_one r)

theorem floor_f_iter_eventually_const (r : R) :
    ∃ C : ℕ, EventuallyEqual (⌊f^[·] r⌋) (λ _ ↦ -C) := by
  rcases floor_f_iter_natAbs_eventually_const r with ⟨C, N, K, h⟩
  refine ⟨C, N, K, λ n ↦ (Int.natAbs_eq_iff.mp (h n)).elim (λ h0 ↦ h0.trans ?_) id⟩
  simp only at h h0 ⊢; rcases C.eq_zero_or_pos with rfl | h1; rfl
  specialize h (n + 1); rw [Nat.add_right_comm, f.iterate_succ_apply'] at h
  replace h1 : 0 < ⌊f^[n + N] r⌋ := by rwa [h0, Nat.cast_pos]
  rw [← h, Int.natCast_natAbs, abs_eq_self.mpr (floor_f_nonneg h1.le)] at h0
  exact absurd h0.symm (floor_f_lt_of_floor_pos h1).ne

theorem case_floor_eventually_zero {r : R} (h : EventuallyEqual (⌊f^[·] r⌋) (λ _ ↦ 0)) :
    EventuallyEqual (f^[·] r) (λ _ ↦ 0) := by
  rw [EventuallyEqual.const_right_iff] at h ⊢
  rcases h with ⟨N, h⟩; refine ⟨N + 1, λ k ↦ ?_⟩
  rw [← Nat.add_assoc, f.iterate_succ_apply', f, h, Int.cast_zero, zero_mul]

theorem case_floor_eventually_neg_one {r : R} (h : EventuallyEqual (⌊f^[·] r⌋) (λ _ ↦ -1)) :
    ∃ s : R, (0 < s ∧ s < 1) ∧ EventuallyEqual (f^[·] r) (NatSeqOfList [-s, s - 1]) := by
  rw [EventuallyEqual.const_right_iff] at h; rcases h with ⟨N, h⟩
  refine ⟨-f^[N] r, ?_, ?_⟩
  ---- `0 < -f^N(r) < 1`; it suffices to check that `f^N(r) ≠ 1`
  · have h0 := h 0
    rw [Nat.zero_add, Int.floor_eq_iff, Int.cast_neg, Int.cast_one, and_comm] at h0
    revert h0; refine And.imp (λ h0 ↦ neg_pos_of_neg (h0.trans_eq <| neg_add_self 1))
      (λ h0 ↦ neg_lt_of_neg_lt (h0.lt_or_eq.resolve_right λ h1 ↦ ?_))
    replace h0 : Int.fract (-1 : R) = 0 := Int.fract_neg_eq_zero.mpr Int.fract_one
    specialize h 1; rw [f.iterate_add_apply, f.iterate_one,
      ← h1, f, h0, mul_zero, Int.floor_zero, zero_eq_neg] at h
    exact one_ne_zero h
  ---- Now check that `f^{k + N}(r)` equals `f^N(r)` if `k` is even and `-1 - f^N(r)` else
  · have h0 (k : ℕ) : f^[(k + 1) + N] r = -f^[k + N] r - 1 := by
      rw [Nat.add_right_comm, f.iterate_succ_apply', f, Int.fract, h,
        Int.cast_neg, Int.cast_one, neg_one_mul, neg_sub', neg_neg]
    replace h : (f^[· + N] r).Periodic 2 :=
      λ k ↦ (h0 _).trans <| by rw [h0, neg_sub, sub_neg_eq_add, add_sub_cancel_left]
    refine ⟨N, 0, λ k ↦ ?_⟩
    change f^[k + N] r = [_, _].getI (k % 2)
    rw [neg_neg, ← N.zero_add, ← h0, zero_add 1, ← add_assoc, k.add_zero, ← h.map_mod_nat]
    obtain h1 | h1 : k % 2 = 0 ∨ k % 2 = 1 := Nat.mod_two_eq_zero_or_one k
    all_goals rw [h1]; rfl

theorem f_alt_formula (r : R) :
    (⌊r⌋ - 1) * f r - ⌊r⌋ ^ 2 = ⌊r⌋ * ((⌊r⌋ - 1) * r - ⌊r⌋ ^ 2) := by
  rw [sq, f, Int.fract, mul_sub, mul_sub, sub_sub, ← add_one_mul (α := R), sub_add_cancel,
    mul_sub, sub_left_inj, ← mul_assoc, sub_one_mul, ← mul_sub_one, mul_assoc]

theorem case_floor_eventually_neg_of_one_lt {r : R} {C : ℕ} (hC : 1 < C)
    (h : EventuallyEqual (⌊f^[·] r⌋) (λ _ ↦ -C)) :
    ∃ ε : R, Infinitesimal ε ∧
      EventuallyEqual ((C + 1) * f^[·] r) (-C ^ 2 + (-C) ^ · * ε) := by
  rcases h with ⟨N, _, h⟩; simp only at h
  have h0 (k) : (C + 1) * f^[(k + 1) + N] r + C ^ 2
      = -C * ((C + 1) * f^[k + N] r + C ^ 2) := by
    have h0 := f_alt_formula (f^[k + N] r)
    rw [h, Int.cast_neg, Int.cast_natCast, neg_sq, ← neg_add', neg_mul, ← neg_add',
      neg_mul, neg_inj, neg_mul, ← neg_add', mul_neg, ← neg_mul] at h0
    rwa [Nat.add_right_comm, f.iterate_succ_apply']
  replace h0 : ∀ k, (C + 1) * f^[k + N] r + C ^ 2
      = (-C) ^ k * ((C + 1) * f^[N] r + C ^ 2) :=
    Nat.rec (by rw [Nat.zero_add, pow_zero, one_mul])
      (λ k h1 ↦ by rw [h0, h1, ← mul_assoc, ← pow_succ'])
  set ε := (C + 1) * f^[N] r + C ^ 2
  refine ⟨ε, ?_, N, 0, λ k ↦ eq_neg_add_of_add_eq <| (add_comm _ _).trans (h0 k)⟩
  ---- Remains to check that `ε = (C + 1) f^N(r) + C^2` is infinitesimal
  replace h0 (k) : |(C + 1) * Int.fract (f^[k + N] r) - C| = C ^ k • |ε| := by
    specialize h0 k
    rw [sq, ← Int.fract_add_floor (f^[k + N] r), h, Int.cast_neg, Int.cast_natCast, mul_add,
      mul_neg, add_one_mul (C : R) C, add_assoc, neg_add_rev, neg_add_cancel_right] at h0
    rw [sub_eq_add_neg, h0, abs_mul, abs_pow, abs_neg,
      Nat.abs_cast, nsmul_eq_mul, Nat.cast_pow]
  replace h (s : R) : |(C + 1) * Int.fract s - C| < ((C + 1 + C : ℕ) : R) := by
    apply (abs_sub _ _).trans_lt
    rw [Nat.abs_cast, Nat.cast_add, add_lt_add_iff_right, ← Nat.cast_succ,
      abs_mul, Nat.abs_cast, abs_eq_self.mpr (Int.fract_nonneg s)]
    exact mul_lt_of_lt_one_right (Nat.cast_pos.mpr C.succ_pos) (Int.fract_lt_one _)
  exact Infinitesimal.iff_nsmul_Nat_bdd.mpr ⟨C + 1 + C, λ k ↦
    (nsmul_le_nsmul_left (abs_nonneg ε) (Nat.lt_pow_self hC k).le).trans_lt <|
      (h0 _).symm.trans_lt (h (f^[k + N] r))⟩





/-! ### Summary -/

theorem final_solution_general (r : R) :
    EventuallyEqual (f^[·] r) (λ _ ↦ 0) ∨
    (∃ s : R, (0 < s ∧ s < 1) ∧ EventuallyEqual (f^[·] r) (NatSeqOfList [-s, s - 1])) ∨
    (∃ C : ℕ, 1 < C ∧ ∃ ε : R, Infinitesimal ε ∧
      EventuallyEqual ((C + 1) * f^[·] r) (-C ^ 2 + (-C) ^ · * ε)) := by
  rcases floor_f_iter_eventually_const r with ⟨C, h⟩
  refine C.eq_zero_or_pos.imp ?_ λ h0 ↦ (h0 : 1 ≤ C).eq_or_lt.imp ?_ ?_
  ---- Three cases: `C = 0`, `C = 1`, and `C > 1`, respectively
  · rintro rfl; exact case_floor_eventually_zero h
  · rintro rfl; exact case_floor_eventually_neg_one h
  · intro h0; exact ⟨C, h0, case_floor_eventually_neg_of_one_lt h0 h⟩

theorem Archimedean_f_iter_classification [Archimedean R] (r : R) :
    EventuallyEqual (f^[·] r) (λ _ ↦ 0) ∨
    (∃ s : R, (0 < s ∧ s < 1) ∧ EventuallyEqual (f^[·] r) (NatSeqOfList [-s, s - 1])) ∨
    (∃ C : ℕ, 1 < C ∧ EventuallyEqual ((C + 1) * f^[·] r) (λ _ ↦ -C ^ 2)) :=
  (final_solution_general r).imp_right <| Or.imp_right λ ⟨C, h, ε, h0, h1⟩ ↦
    ⟨C, h, by simpa only [h0.zero_of_Archimedean, mul_zero, add_zero] using h1⟩

theorem final_solution [Archimedean R] (r : R) :
    ∃ N, ∀ k, N ≤ k → f^[k + 2] r = f^[k] r := by
  rcases Archimedean_f_iter_classification r with
    ⟨N, _, h⟩ | ⟨s, -, N, M, h⟩ | ⟨C, hC, N, _, h⟩
  all_goals
    simp only at h; refine ⟨N, λ k h0 ↦ ?_⟩
    rcases Nat.exists_eq_add_of_le' h0 with ⟨k, rfl⟩
  ---- Three cases: `C = 0`, `C = 1`, and `C > 1`, respectively
  · rw [h, Nat.add_right_comm, h]
  · rw [h, Nat.add_right_comm, h, Nat.add_right_comm]
    exact NatSeqOfList.periodic [-s, s - 1] _
  · replace h0 := (h (k + 2)).trans (h k).symm
    rw [Nat.add_right_comm, mul_eq_mul_left_iff] at h0
    exact h0.resolve_right (add_pos (Nat.cast_pos.mpr (pos_of_gt hC)) one_pos).ne.symm
