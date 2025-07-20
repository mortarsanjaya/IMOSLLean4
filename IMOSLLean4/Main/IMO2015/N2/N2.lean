/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Choose.Basic

/-!
# IMO 2015 N2

Let $a, b ∈ ℕ$ such that $a! + b! ∣ a! b!$.
Prove that $3a ≥ 2b + 2$, and find all the equality cases.
-/

namespace IMOSL
namespace IMO2015N2

/-! ### Extra lemmas -/

theorem factorial_le_succ_ascFactorial (a) :
    ∀ n : ℕ, n.factorial ≤ (a + 1).ascFactorial n := by
  refine Nat.rec (Nat.le_refl 1) λ n ↦ Nat.mul_le_mul ?_
  rw [Nat.add_right_comm, Nat.add_assoc]
  exact n.succ.le_add_left a

theorem ascFactorial_succ_mono_right (a) (h : m ≤ n) :
    (a + 1).ascFactorial m ≤ (a + 1).ascFactorial n := by
  refine Nat.le_of_mul_le_mul_left ?_ a.factorial_pos
  rw [Nat.factorial_mul_ascFactorial, Nat.factorial_mul_ascFactorial]
  exact Nat.factorial_le (Nat.add_le_add_left h a)

theorem ascFactorial_mono_left {a b : ℕ} (h : a ≤ b) :
    ∀ n, a.ascFactorial n ≤ b.ascFactorial n :=
  Nat.rec (Nat.le_refl 1) λ n ↦ Nat.mul_le_mul (Nat.add_le_add_right h n)

theorem ascFactorial_succ' (n k) :
    n.ascFactorial (k + 1) = n * (n + 1).ascFactorial k := by
  obtain rfl | ⟨n, rfl⟩ : n = 0 ∨ ∃ n', n = n' + 1 :=
    n.eq_zero_or_pos.imp_right Nat.exists_eq_add_of_le'
  · rw [Nat.zero_ascFactorial, Nat.zero_mul]
  · rw [← Nat.mul_right_inj n.factorial_ne_zero, Nat.factorial_mul_ascFactorial,
      ← Nat.mul_assoc, n.factorial.mul_comm, ← Nat.factorial_succ,
      Nat.factorial_mul_ascFactorial, Nat.add_right_comm, Nat.add_assoc]

theorem add_one_dvd_of_dvd_mul (h : a ∣ b) (h0 : b + 1 ∣ a * c) : b + 1 ∣ c :=
  (Nat.dvd_add_right (Nat.dvd_trans h0 (Nat.mul_dvd_mul_right h c))).mp
    ⟨c, (b.succ_mul c).symm⟩





/-! ### Start of the problem -/

def good (c d : ℕ) := c + d ∣ c * d

lemma good_comm : good c d ↔ good d c := by
  rw [good, good, Nat.add_comm, Nat.mul_comm]

lemma good_iff : good c d ↔ c + d ∣ c * c := by
  have h : c + d ∣ c * c + c * d := ⟨c, by rw [← c.mul_add, c.mul_comm]⟩
  refine ⟨λ h0 ↦ (Nat.dvd_add_iff_left h0).mpr h, λ h0 ↦ (Nat.dvd_add_iff_right h0).mpr h⟩

lemma not_good_one_right (hc : 0 < c) : ¬good c 1 := by
  rw [good, c.mul_one]; exact Nat.not_dvd_of_pos_of_lt hc c.lt_succ_self

lemma not_good_one_left (hd : 0 < d) : ¬good 1 d :=
  mt good_comm.mp (not_good_one_right hd)

/-- Final solution -/
theorem final_solution (h : good a.factorial b.factorial) :
    2 * b + 2 ≤ 3 * a ∧ (2 * b + 2 = 3 * a ↔ a = 2 ∧ b = 2 ∨ a = 4 ∧ b = 5) := by
  ---- First, discharge the case `b < a`
  obtain h0 | ⟨c, rfl⟩ : b < a ∨ ∃ c, b = a + c :=
    (lt_or_ge b a).imp_right Nat.exists_eq_add_of_le
  · have h1 : 2 * b + 2 < 3 * a := by
      refine (Nat.add_lt_add_of_lt_of_le ?_ ?_).trans_eq (Nat.succ_mul 2 a).symm
      · exact Nat.mul_lt_mul_of_pos_left h0 Nat.two_pos
      · refine Nat.le_of_not_lt λ h1 ↦ not_good_one_left b.factorial_pos ?_
        rwa [← Nat.factorial_eq_one.mpr (Nat.le_of_lt_succ h1)]
    refine ⟨h1.le, iff_of_false h1.ne ?_⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact h0.ne rfl
    · exact h0.not_gt (Nat.lt_succ_self 4)
  ---- Now write `b = a + c` and continue
  replace h : (a + 1).ascFactorial c + 1 ∣ a.factorial := by
    rwa [good_iff, ← a.factorial_mul_ascFactorial, Nat.add_comm,
      ← Nat.mul_succ, Nat.mul_dvd_mul_iff_left a.factorial_pos] at h
  obtain ⟨d, rfl⟩ : ∃ d, a = c + d := by
    refine Nat.exists_eq_add_of_le (Nat.le_of_not_le λ h0 ↦ ?_)
    revert h; refine Nat.not_dvd_of_pos_of_lt a.factorial_pos (Nat.lt_succ_of_le ?_)
    exact (factorial_le_succ_ascFactorial a a).trans (ascFactorial_succ_mono_right a h0)
  ---- Write `a = c + d` and first simplify the goal
  suffices c + 2 ≤ d ∧ (c + 2 = d → c = 0 ∨ c = 1) by
    rw [Nat.mul_add, Nat.succ_mul 2, Nat.add_assoc, c.two_mul, Nat.add_assoc]
    revert this; refine And.imp (λ h0 ↦ ?_) (λ h0 ↦ ?_)
    · rwa [Nat.add_le_add_iff_left, Nat.add_le_add_iff_left]
    · rw [Nat.add_right_inj, Nat.add_right_inj]
      refine ⟨λ h1 ↦ ?_, λ h1 ↦ ?_⟩
      · refine (h0 h1).imp (λ h2 ↦ ?_) (λ h2 ↦ ?_)
        all_goals subst h1 h2; exact ⟨rfl, rfl⟩
      · rcases h1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, Nat.add_right_inj (k := 0)] at h2
          rw [h2, Nat.zero_add] at h1
          rw [h2, h1]
        · rw [h1, Nat.add_right_inj (k := 1)] at h2
          rw [h2, Nat.add_right_inj (k := 3)] at h1
          rw [h2, h1]
  ---- Continue with `h : (c + d + 1).ascFactorial c + 1 ∣ (c + 1).ascFactorial d`
  replace h : (c + d + 1).ascFactorial c + 1 ∣ (c + 1).ascFactorial d :=
    add_one_dvd_of_dvd_mul (Nat.factorial_dvd_ascFactorial _ _)
      (c.factorial_mul_ascFactorial d ▸ h)
  refine ⟨?_, ?_⟩
  ---- Show that `c + 2 ≤ d`
  · refine Nat.le_of_not_lt λ h0 ↦ ?_
    rw [Nat.lt_succ_iff, Nat.le_succ_iff] at h0
    rcases h0 with h0 | rfl
    -- Case 1: `d ≤ c`
    · revert h; apply Nat.not_dvd_of_pos_of_lt (Nat.ascFactorial_pos _ _)
      refine Nat.lt_succ_of_le ((ascFactorial_succ_mono_right _ h0).trans' ?_)
      exact ascFactorial_mono_left (Nat.succ_le_succ (c.le_add_right d)) d
    -- Case 2: `d = c + 1`
    · replace h : (2 * c + 2).ascFactorial c + 1 ∣ (c + 2).ascFactorial c := by
        rw [Nat.add_right_comm, ← Nat.two_mul, ascFactorial_succ'] at h
        revert h; apply add_one_dvd_of_dvd_mul
        obtain rfl | ⟨c, rfl⟩ : c = 0 ∨ ∃ c', c = c' + 1 :=
          c.eq_zero_or_pos.imp_right Nat.exists_eq_add_of_le'
        · exact Nat.one_dvd _
        · rw [ascFactorial_succ', Nat.mul_right_comm]
          exact Nat.dvd_mul_left _ _
      revert h; apply Nat.not_dvd_of_pos_of_lt (Nat.ascFactorial_pos _ _)
      refine Nat.lt_succ_of_le (ascFactorial_mono_left ?_ _)
      rw [ Nat.two_mul, Nat.add_assoc, Nat.add_assoc]
      exact Nat.le_add_left _ _
  ---- If `c + 2 = d`, then `c ∈ {0, 1}`
  · rintro rfl; obtain rfl | ⟨c, rfl⟩ : c = 0 ∨ ∃ c', c = c' + 1 :=
      c.eq_zero_or_pos.imp_right Nat.exists_eq_add_of_le'
    · left; rfl
    -- Now write `c → c + 1`, and reduce to the case `c ≥ 2`
    right; rw [Nat.add_left_inj, ← Nat.lt_one_iff, ← Nat.not_le,
      Nat.le_iff_lt_or_eq, ← Nat.succ_le_iff, or_comm]
    rintro (rfl | h0)
    · revert h; show ¬57 ∣ 360; decide
    -- Finally, focus on the case `c ≥ 2`
    replace h : (2 * c + 5).ascFactorial (c + 1) + 1 ∣ (c + 2) * (c + 5).ascFactorial c := by
      replace h : (2 * c + 5).ascFactorial (c + 1) + 1 ∣ (c + 2).ascFactorial (c + 3) := by
        rwa [Nat.add_assoc, c.add_add_add_comm 1 c 4, ← Nat.two_mul] at h
      rw [ascFactorial_succ' (c + 2), ascFactorial_succ' (c + 3),
        ascFactorial_succ' (c + 4), ← (c + 3).mul_assoc, Nat.mul_left_comm] at h
      revert h; apply add_one_dvd_of_dvd_mul
      obtain rfl | ⟨d, rfl⟩ : 2 = c ∨ ∃ d, c = d + 3 :=
        h0.eq_or_lt.imp_right Nat.exists_eq_add_of_le'
      -- In the case `c = 3`, the goal reduces to `30 ∣ 990`
      · show 30 ∣ 990; exact ⟨33, rfl⟩
      -- In the case `c ≥ 4`, we pull out the factors `2(c + 3)` and `2(c + 4)`
      · rw [Nat.mul_add 2, ascFactorial_succ']
        refine Nat.dvd_trans ?_ (Nat.dvd_mul_left _ _)
        rw [ascFactorial_succ']; refine Nat.mul_dvd_mul ⟨2, ?_⟩ ?_
        · rw [Nat.mul_comm, d.add_assoc, d.add_mul]
        rw [ascFactorial_succ']; refine Nat.dvd_trans ?_ (Nat.dvd_mul_left _ _)
        rw [ascFactorial_succ']; refine Nat.dvd_trans ⟨2, ?_⟩ (Nat.dvd_mul_right _ _)
        rw [Nat.mul_comm, d.add_assoc, d.add_mul]
    revert h; apply Nat.not_dvd_of_pos_of_lt
    · exact Nat.mul_pos (c + 1).succ_pos (Nat.ascFactorial_pos _ _)
    · rw [Nat.lt_succ_iff, Nat.ascFactorial_succ, Nat.two_mul, c.add_assoc]
      refine Nat.mul_le_mul ?_ (ascFactorial_mono_left (Nat.le_add_left _ _) _)
      rw [Nat.add_assoc, Nat.add_le_add_iff_left, Nat.add_right_comm]
      exact Nat.le_add_left 2 (c + c + 3)
