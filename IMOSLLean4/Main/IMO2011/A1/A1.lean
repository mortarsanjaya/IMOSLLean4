/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Prod

/-!
# IMO 2011 A1 (P1)

Consider an arbitrary set $A = \{a_1, a_2, a_3, a_4\}$ of four distinct positive integers.
Let $p_A$ be the number of pairs $(i, j)$ with $1 ≤ i < j ≤ 4$
  such that $a_i + a_j ∣ a_1 + a_2 + a_3 + a_4$.
Determine all sets $A$ of size $4$ such that $p_A ≥ p_B$ for all sets $B$ of size $4$.
-/

namespace IMOSL
namespace IMO2011A1

@[ext] structure Card4NatSet where
  f : Fin 4 → ℕ
  f_pos : ∀ i, 0 < f i
  f_strict_mono : StrictMono f


namespace Card4NatSet

open Finset

/-! ### The number `p_A` -/

def p_set (A : Card4NatSet) : Finset (Fin 4 × Fin 4) :=
  univ.filter λ (i, j) ↦ i < j ∧ A.f i + A.f j ∣ A.f 0 + A.f 1 + A.f 2 + A.f 3

def p_val (A : Card4NatSet) : ℕ := A.p_set.card

lemma mem_p_set_iff {A : Card4NatSet} :
    (i, j) ∈ A.p_set ↔ i < j ∧ A.f i + A.f j ∣ A.f 0 + A.f 1 + A.f 2 + A.f 3 := by
  rw [p_set, mem_filter, and_iff_right (mem_univ _)]



/-! ### Scaling of `A` be a positive integer -/

def nsmul (A : Card4NatSet) (hn : 0 < n) : Card4NatSet where
  f := n • A.f
  f_pos := λ i ↦ Nat.mul_pos hn (A.f_pos i)
  f_strict_mono := λ _ _ h ↦ Nat.mul_lt_mul_of_pos_left (A.f_strict_mono h) hn

lemma f_nsmul (A : Card4NatSet) (hn : 0 < n) : (A.nsmul hn).f = n • A.f := rfl

lemma f_nsmul_apply (A : Card4NatSet) (hn : 0 < n) (i) : (A.nsmul hn).f i = n * A.f i := rfl

lemma p_set_nsmul (A : Card4NatSet) (hn : 0 < n) : (A.nsmul hn).p_set = A.p_set := by
  refine Finset.ext λ (i, j) ↦ ?_
  simp only [mem_p_set_iff, f_nsmul_apply, ← Nat.mul_add]
  exact Iff.and Iff.rfl (Nat.mul_dvd_mul_iff_left hn)

lemma p_val_nsmul (A : Card4NatSet) (hn : 0 < n) : (A.nsmul hn).p_val = A.p_val :=
  congrArg Finset.card (A.p_set_nsmul hn)



/-! ### Construction of the maximum sets -/

def MaxSet1 : Card4NatSet where
  f := ![1, 5, 7, 11]
  f_pos := by decide
  f_strict_mono := by decide

def MaxSet2 : Card4NatSet where
  f := ![1, 11, 19, 29]
  f_pos := by decide
  f_strict_mono := by decide

lemma MaxSet1_p_val : MaxSet1.p_val = 4 := rfl

lemma MaxSet2_p_val : MaxSet2.p_val = 4 := rfl

lemma MaxSet1_nsmul_p_val (hn : 0 < n) : (MaxSet1.nsmul hn).p_val = 4 :=
  MaxSet1.p_val_nsmul hn

lemma MaxSet2_nsmul_p_val (hn : 0 < n) : (MaxSet2.nsmul hn).p_val = 4 :=
  MaxSet2.p_val_nsmul hn



/-! ### The bound `p_A ≤ 4` -/

lemma p_set_subset (A : Card4NatSet) : A.p_set ⊆ {(0, 1), (0, 2), (0, 3), (1, 2)}
  | (0, 0) => λ h ↦ absurd (mem_p_set_iff.mp h).1 (by decide)
  | (0, 1) => λ _ ↦ mem_insert_self _ _
  | (0, 2) => λ _ ↦ mem_insert_of_mem (mem_insert_self _ _)
  | (0, 3) => λ _ ↦ mem_insert_of_mem (mem_insert_of_mem (mem_insert_self _ _))
  | (1, 0) => λ h ↦ absurd (mem_p_set_iff.mp h).1 (by decide)
  | (1, 1) => λ h ↦ absurd (mem_p_set_iff.mp h).1 (by decide)
  | (1, 2) => λ _ ↦ by decide
  | (1, 3) => λ h ↦ absurd (mem_p_set_iff.mp h).2 λ h ↦ by
      rw [Nat.add_assoc, Nat.add_add_add_comm, Nat.dvd_add_self_right] at h
      exact (Nat.le_of_dvd (Nat.add_lt_add (A.f_pos 0) (A.f_pos 2)) h).not_gt
        (Nat.add_lt_add (A.f_strict_mono (by decide)) (A.f_strict_mono (by decide)))
  | (2, 0) => λ h ↦ absurd (mem_p_set_iff.mp h).1 (by decide)
  | (2, 1) => λ h ↦ absurd (mem_p_set_iff.mp h).1 (by decide)
  | (2, 2) => λ h ↦ absurd (mem_p_set_iff.mp h).1 (by decide)
  | (2, 3) => λ h ↦ absurd (mem_p_set_iff.mp h).2 λ h ↦ by
      rw [Nat.add_assoc, Nat.dvd_add_self_right] at h
      exact (Nat.le_of_dvd (Nat.add_lt_add (A.f_pos 0) (A.f_pos 1)) h).not_gt
        (Nat.add_lt_add (A.f_strict_mono (by decide)) (A.f_strict_mono (by decide)))
  | (3, 0) => λ h ↦ absurd (mem_p_set_iff.mp h).1 (by decide)
  | (3, 1) => λ h ↦ absurd (mem_p_set_iff.mp h).1 (by decide)
  | (3, 2) => λ h ↦ absurd (mem_p_set_iff.mp h).1 (by decide)
  | (3, 3) => λ h ↦ absurd (mem_p_set_iff.mp h).1 (by decide)

lemma p_val_le_four (A : Card4NatSet) : A.p_val ≤ 4 :=
  card_le_card A.p_set_subset



/-! ### The case `p_A ≥ 4` -/

lemma four_le_p_val_iff' {A : Card4NatSet} :
    4 ≤ A.p_val ↔ {(0, 1), (0, 2), (0, 3), (1, 2)} ⊆ A.p_set :=
  ⟨λ h ↦ subset_of_eq (eq_of_subset_of_card_le A.p_set_subset h).symm, card_le_card⟩

lemma four_le_p_val_imp₁ {A : Card4NatSet} (hA : 4 ≤ A.p_val) :
    A.f = A.f 0 • ![1, 5, 7, 11] ∨ A.f = A.f 0 • ![1, 11, 19, 29] := by
  rw [four_le_p_val_iff'] at hA
  ---- `a_0 + a_3 = a_1 + a_2`
  have h : A.f 0 + A.f 3 = A.f 1 + A.f 2 := by
    apply Nat.dvd_antisymm
    · rw [← Nat.dvd_add_self_left, Nat.add_right_comm, ← Nat.add_assoc]
      exact (mem_p_set_iff.mp (hA (by decide))).2
    · rw [← Nat.dvd_add_self_right, Nat.add_right_comm, ← Nat.add_assoc]
      exact (mem_p_set_iff.mp (hA (by decide))).2
  ---- `3(a_0 + a_2) = 2(a_1 + a_2)`
  have h0 : 2 * (A.f 1 + A.f 2) = 3 * (A.f 0 + A.f 2) := by
    obtain ⟨c, h0⟩ : A.f 0 + A.f 2 ∣ A.f 0 + A.f 1 + A.f 2 + A.f 3 :=
      (mem_p_set_iff.mp (hA (by decide))).2
    rw [(A.f 0).add_assoc, add_right_comm, h, ← Nat.mul_two] at h0
    suffices c = 3 by rw [mul_comm 3, mul_comm 2, h0, this]
    -- Now show that `c = 3`
    have h1 : 0 < A.f 0 + A.f 2 := Nat.add_lt_add (A.f_pos 0) (A.f_pos 2)
    refine Nat.eq_of_le_of_lt_succ (Nat.succ_le_of_lt ?_) ?_
    -- `c > 2`
    · rw [← Nat.mul_lt_mul_left h1, ← h0]
      refine Nat.mul_lt_mul_of_pos_right (Nat.add_lt_add_right ?_ _) Nat.two_pos
      exact A.f_strict_mono (by decide)
    -- `c < 4`
    · rw [← Nat.mul_lt_mul_left h1, ← h0, ← Nat.mul_assoc (A.f 0 + A.f 2) 2 2]
      refine Nat.mul_lt_mul_of_pos_right ?_ Nat.two_pos
      rw [Nat.add_mul, (A.f 2).mul_two]
      refine (Nat.le_add_left _ _).trans_lt' (Nat.add_lt_add_right ?_ _)
      exact A.f_strict_mono (by decide)
  ---- Simplify the above equality to `3a_0 + a_2 = 2a_1`
  have h0' : 2 * A.f 1 = 3 * A.f 0 + A.f 2 := by
    rwa [Nat.mul_add, Nat.mul_add, Nat.add_mul 1 2 (A.f 2),
      Nat.one_mul, ← add_assoc, add_left_inj] at h0
  ---- `2(a_1 + a_2) = 4(a_0 + a_1)` or `2(a_1 + a_2) = 5(a_0 + a_1)`
  obtain h1 | h1 : 2 * (A.f 1 + A.f 2) = 4 * (A.f 0 + A.f 1)
      ∨ 2 * (A.f 1 + A.f 2) = 5 * (A.f 0 + A.f 1) := by
    obtain ⟨c, h1⟩ : A.f 0 + A.f 1 ∣ A.f 0 + A.f 1 + A.f 2 + A.f 3 :=
      (mem_p_set_iff.mp (hA (by decide))).2
    rw [(A.f 0).add_assoc, add_right_comm, h, ← Nat.mul_two, mul_comm, mul_comm _ c] at h1
    -- Reduce to showing that `c = 4` or `c = 5`
    suffices c = 4 ∨ c = 5 by apply this.imp <;> rintro rfl <;> assumption
    have h2 : 0 < A.f 0 + A.f 1 := Nat.add_lt_add (A.f_pos 0) (A.f_pos 1)
    -- First, show that `c > 3`
    have h3 : 3 < c := by
      rw [← Nat.mul_lt_mul_right h2, ← h1, h0]
      refine Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add_left ?_ _) (Nat.succ_pos 2)
      exact A.f_strict_mono (by decide)
    -- Second, show that `c < 6`
    have h4 : c < 6 := by
      rw [← Nat.mul_lt_mul_right h2, ← h1, Nat.mul_assoc 2 3]
      refine Nat.mul_lt_mul_of_pos_left ?_ Nat.two_pos
      rw [Nat.mul_add, Nat.add_mul 1 2 (A.f 1), one_mul, h0',
        add_left_comm (A.f 1), ← add_assoc, ← Nat.add_mul]
      exact Nat.lt_add_of_pos_left (Nat.mul_pos (Nat.succ_pos 5) (A.f_pos 0))
    -- Now resolve the inequalities
    rw [Nat.lt_succ_iff_lt_or_eq, Nat.lt_succ] at h4
    exact h4.imp_left λ h4 ↦ h4.antisymm h3
  ---- Simplify the case `2(a_1 + a_2) = 4(a_0 + a_1)`
  · replace h1 : A.f 2 = 2 * A.f 0 + A.f 1 := by
      rwa [Nat.mul_assoc 2 2, Nat.mul_right_inj (Nat.succ_ne_zero 1),
        Nat.mul_add, (A.f 1).two_mul, add_left_comm, add_right_inj] at h1
    replace h0 : A.f 1 = 5 * A.f 0 := by
      rwa [Nat.two_mul, h1, ← add_assoc, ← Nat.add_mul, add_left_inj] at h0'
    replace h1 : A.f 2 = 7 * A.f 0 := by rwa [h0, ← Nat.add_mul] at h1
    replace h : A.f 3 = 11 * A.f 0 := by
      rwa [h0, h1, ← Nat.add_mul, Nat.succ_mul, add_comm, add_left_inj] at h
    left; ext i; match i with
      | 0 => exact (A.f 0).mul_one.symm
      | 1 => exact h0.trans (Nat.mul_comm _ _)
      | 2 => exact h1.trans (Nat.mul_comm _ _)
      | 3 => exact h.trans (Nat.mul_comm _ _)
  ---- Simplify the case `2(a_1 + a_2) = 5(a_0 + a_1)`
  · replace h1 : 2 * A.f 2 = 5 * A.f 0 + 3 * A.f 1 := by
      rw [Nat.mul_add, Nat.mul_add, Nat.add_mul 2 3 (A.f 1), add_left_comm] at h1
      exact Nat.add_left_cancel h1
    replace h0 : A.f 1 = 11 * A.f 0 := by
      apply congrArg (2 * ·) at h0'
      rwa [← mul_assoc, Nat.mul_add, ← mul_assoc, h1, ← add_assoc, ← Nat.add_mul,
        Nat.two_mul, Nat.add_mul 1 3, one_mul, add_left_inj] at h0'
    replace h1 : A.f 2 = 19 * A.f 0 := by
      rw [h0, ← mul_assoc, Nat.two_mul, Nat.add_mul 3 19 (A.f 0)] at h0'
      exact Nat.add_left_cancel h0'.symm
    replace h : A.f 3 = 29 * A.f 0 := by
      rwa [h0, h1, ← Nat.add_mul, Nat.succ_mul, add_comm, add_left_inj] at h
    right; ext i; match i with
      | 0 => exact (A.f 0).mul_one.symm
      | 1 => exact h0.trans (Nat.mul_comm _ _)
      | 2 => exact h1.trans (Nat.mul_comm _ _)
      | 3 => exact h.trans (Nat.mul_comm _ _)

lemma four_le_p_val_imp₂ {A : Card4NatSet} (hA : 4 ≤ A.p_val) :
    ∃ (n : ℕ) (hn : n > 0), A = MaxSet1.nsmul hn ∨ A = MaxSet2.nsmul hn :=
  ⟨A.f 0, A.f_pos 0, (four_le_p_val_imp₁ hA).imp Card4NatSet.ext Card4NatSet.ext⟩

lemma four_le_p_val_iff {A : Card4NatSet} :
    4 ≤ A.p_val ↔ ∃ (n : ℕ) (hn : n > 0), A = MaxSet1.nsmul hn ∨ A = MaxSet2.nsmul hn := by
  refine ⟨four_le_p_val_imp₂, ?_⟩; rintro ⟨_, hn, rfl | rfl⟩
  exacts [(MaxSet1_nsmul_p_val hn).ge, (MaxSet2_nsmul_p_val hn).ge]

end Card4NatSet





/-! ### Summary -/

/-- Final solution -/
theorem final_solution {A : Card4NatSet} :
    (∀ B : Card4NatSet, B.p_val ≤ A.p_val) ↔
      ∃ (n : ℕ) (_ : n > 0), A.f = n • ![1, 5, 7, 11] ∨ A.f = n • ![1, 11, 19, 29] := by
  have h : (∀ B : Card4NatSet, B.p_val ≤ A.p_val) ↔ 4 ≤ A.p_val :=
    ⟨λ h ↦ h Card4NatSet.MaxSet1, λ h B ↦ B.p_val_le_four.trans h⟩
  rw [h, Card4NatSet.four_le_p_val_iff]
  simp only [Card4NatSet.ext_iff]; rfl
