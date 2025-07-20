/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-!
# IMO 2016 A1

Let $R$ be a totally ordered commutative ring.
Let $a_1, a_2, …, a_n, c ∈ R$ non-negative such that $a_i a_j ≥ c$ whenever $i ≠ j$.
Let $r ∈ R$ non-negative such that $nr ≥ a_1 + a_2 + … + a_n$.
Prove that $$ \prod_{i = 1}^n (a_i^2 + c) ≤ (r^2 + c)^n. $$
-/

namespace IMOSL
namespace IMO2016A1

open Multiset

theorem ring_prod_le_pow_card [CommSemiring R] [PartialOrder R] [IsOrderedRing R]
    {M : Multiset R} (hM : ∀ x ∈ M, 0 ≤ x) (hr : ∀ x ∈ M, x ≤ r) :
    M.prod ≤ r ^ card M := by
  induction' M using Multiset.induction with a M M_ih
  · rw [prod_zero, card_zero, pow_zero]
  · rw [prod_cons, card_cons, pow_succ']
    rw [forall_mem_cons] at hM hr
    exact mul_le_mul hr.1 (M_ih hM.2 hr.2) (prod_nonneg hM.2) (hM.1.trans hr.1)

theorem ring_id [CommSemiring R] {x y z c : R} (h : x * y = c + z) :
    (x ^ 2 + c) * (y ^ 2 + c) = z ^ 2 + c * (x + y) ^ 2 := by
  rw [add_mul, mul_add, ← mul_pow, add_assoc, h, add_comm c, mul_comm, ← mul_add,
    add_sq, add_assoc, add_assoc, sq c, ← mul_add, ← mul_rotate, mul_assoc, ← mul_add]
  refine congrArg₂ _ rfl (congrArg₂ _ rfl ?_)
  rw [← add_rotate' c, ← add_assoc c, ← two_mul, ← add_assoc,
    ← mul_add, add_comm z, ← h, ← mul_assoc, add_comm, add_sq']





/-! ### Start of the problem -/

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]

theorem main_claim {x y z w c : R} (h : x + y = z + w) (h0 : c ≤ x * y) (h1 : x * y ≤ z * w) :
    (x ^ 2 + c) * (y ^ 2 + c) ≤ (z ^ 2 + c) * (w ^ 2 + c) := by
  obtain ⟨a, ha⟩ : ∃ a, x * y = c + a := exists_add_of_le h0
  rw [ha, le_add_iff_nonneg_right] at h0
  obtain ⟨b, hb⟩ : ∃ b, z * w = c + (a + b) :=
    (exists_add_of_le h1).imp λ b h2 ↦ by rw [h2, ha, add_assoc]
  rw [ha, hb, add_le_add_iff_left] at h1
  rw [ring_id ha, ring_id hb, h, add_le_add_iff_right]
  exact pow_le_pow_left₀ h0 h1 2

/-- Final solution -/
theorem final_solution {M : Multiset R} (hM : ∀ x ∈ M, 0 ≤ x) :
    ∀ {c} (_ : 0 ≤ c) (_ : ∀ x y, {x, y} ≤ M → c ≤ x * y) {r} (_ : M.sum ≤ card M • r),
    (M.map (· ^ 2 + c)).prod ≤ (r ^ 2 + c) ^ (card M) := by
  ---- Proceed by structural induction on `|M|`, clearing the base case first
  generalize hn : card M = n
  revert hM hn M; induction' n with n n_ih
  · rintro M - hM0 _ - - _ -
    rw [card_eq_zero.mp hM0, Multiset.map_zero, prod_zero, pow_zero]
  intro M hM hn c hc hc0 r hr
  ---- Next, clear the case where all elements of `|M|` are `≤ r`
  rcases em (∀ x ∈ M, x ≤ r) with h | h
  · rw [← hn, ← card_map (· ^ 2 + c)]
    refine ring_prod_le_pow_card ?_ ?_
    · simp only [mem_map]; rintro x ⟨x, -, rfl⟩
      exact add_nonneg (sq_nonneg x) hc
    · simp only [mem_map]; rintro x ⟨x, hx, rfl⟩
      exact add_le_add_right (pow_le_pow_left₀ (hM x hx) (h x hx) 2) c
  ---- Break `M` into `(a + r) ::ₘ M` for some `a > 0`, and substitute `n`
  simp only [not_forall, not_le] at h
  rcases h with ⟨a, haM, ha⟩
  apply exists_cons_of_mem at haM; rcases haM with ⟨M, rfl⟩
  obtain ⟨a, rfl⟩ := exists_add_of_le ha.le
  rw [lt_add_iff_pos_right] at ha
  rw [card_cons, Nat.succ_inj] at hn; subst hn
  ---- The new `M` must contain an element `b < r`; break `M` again and simplify `hr`
  rw [sum_cons, add_assoc, succ_nsmul', add_le_add_iff_left] at hr
  obtain ⟨b, hbM, hb⟩ : ∃ b ∈ M, b < r := by
    by_contra! h
    exact (lt_add_of_pos_left M.sum ha).not_ge (hr.trans (card_nsmul_le_sum h))
  apply exists_cons_of_mem at hbM; rcases hbM with ⟨M, rfl⟩
  rw [forall_mem_cons, forall_mem_cons] at hM
  rcases hM with ⟨-, hb0, hM⟩
  ---- Fill in the induction hypothesis for `(a + b) ::ₘ M`
  replace n_ih : (((a + b) ::ₘ M).map (· ^ 2 + c)).prod ≤ (r ^ 2 + c) ^ (card M + 1) := by
    -- First reduce to `{x, y} ≤ (a + b) ::ₘ M ⇒ xy ≥ c`
    rw [sum_cons, ← add_assoc, ← sum_cons] at hr
    rw [← card_cons b M]; refine n_ih ?_ ?_ hc (λ x y h ↦ ?_) hr
    · exact forall_mem_cons.mpr ⟨add_nonneg ha.le hb0, hM⟩
    · rw [card_cons, card_cons]
    rcases em' (a + b ∈ ({x, y} : Multiset R)) with h0 | h0
    -- Case 1: `a + b ∉ {x, y}`
    · exact hc0 x y ((le_cons_self _ _).trans'
        ((le_cons_self _ _).trans' ((le_cons_of_notMem h0).mp h)))
    -- Case 2: `a + b ∈ {x, y}`
    · have h1 (z) (h1 : z ∈ M) : c ≤ z * (a + b) := by
        apply (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left ha.le) (hM z h1)).trans'
        refine hc0 z b ((le_cons_self _ _).trans' ?_)
        rwa [pair_comm, insert_eq_cons, cons_le_cons_iff, singleton_le]
      rw [insert_eq_cons, mem_cons, mem_singleton] at h0
      rcases h0 with rfl | rfl
      · rw [insert_eq_cons, cons_le_cons_iff, singleton_le] at h
        rw [mul_comm]; exact h1 y h
      · rw [pair_comm, insert_eq_cons, cons_le_cons_iff, singleton_le] at h
        exact h1 x h
  ---- Solve the problem with calculations
  calc
  _ = ((r + a) ^ 2 + c) * (b ^ 2 + c) * (M.map (· ^ 2 + c)).prod := by
    rw [map_cons, map_cons, prod_cons, prod_cons, mul_assoc]
  _ ≤ (r ^ 2 + c) * ((a + b) ^ 2 + c) * (M.map (· ^ 2 + c)).prod := by
    refine mul_le_mul_of_nonneg_right ?_ ?_
    -- From main claim: `((a + r)^2 + c)(b^2 + c) ≤ (r^2 + c)((a + b)^2 + c)`
    · refine main_claim (add_assoc r a b) ?_ ?_
      · refine hc0 _ _ (Multiset.le_iff_exists_add.mpr ⟨M, ?_⟩)
        rw [insert_eq_cons, cons_add, singleton_add]
      · rw [add_mul, mul_add, add_comm, add_le_add_iff_right, mul_comm]
        exact mul_le_mul_of_nonneg_right hb.le ha.le
    -- `Π_{x ∈ M} (x^2 + c) ≥ 0`
    · apply prod_nonneg
      simp only [mem_map]; rintro x ⟨x, -, rfl⟩
      exact add_nonneg (sq_nonneg x) hc
  _ = (r ^ 2 + c) * (((a + b) ::ₘ M).map (· ^ 2 + c)).prod := by
    rw [map_cons, prod_cons, mul_assoc]
  _ ≤ (r ^ 2 + c) * (r ^ 2 + c) ^ (card M + 1) :=
    mul_le_mul_of_nonneg_left n_ih (add_nonneg (sq_nonneg r) hc)
  _ = _ := by rw [card_cons, pow_succ' (r ^ 2 + c) (card M + 1)]
