/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.BigInequalities.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Algebra.Group.Fin.Basic

/-!
# IMO 2007 A6

Let $R$ be a totally ordered commutative ring and $n ≥ 4$.
Prove that, for any $a_1, a_2, …, a_n ∈ R$,
$$ \left(3 \sum_{i = 1} a_i^2 a_{i + 1}\right)^2 ≤ 2 \left(\sum_{i = 1}^n a_i^2\right)^3. $$
-/

namespace IMOSL
namespace IMO2007A6

open Finset Extra.Finset

/-! ### Extra lemmas on sums over `Fin` -/

theorem Fin_exists_minimal [LinearOrder α] (a : Fin (n + 1) → α) : ∃ j, ∀ i, a j ≤ a i :=
  (exists_min_image univ a univ_nonempty).imp λ _ ⟨_, h⟩ i ↦ h i (mem_univ i)

theorem Fin_sum_shift [AddCommMonoid M] (a : Fin (n + 1) → M) (k) :
    ∑ i, a (i + k) = ∑ i, a i :=
  sum_equiv (Equiv.addRight k) (λ _ ↦ by simp only [mem_univ]) (λ _ _ ↦ rfl)





/-! ### The big claim on bounding a cyclic sum `∑ x_i x_{i + 1}` -/

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Nice temporary definition -/
abbrev niceTuple (a : Fin (n + 1) → R) :=
  2 ^ 2 * ∑ i, a i * a (i + 1) ≤ (∑ i, a i) ^ 2

theorem niceTuple.of_four [ExistsAddOfLE R] (a : Fin 4 → R) : niceTuple a := by
  rw [niceTuple, Fin.sum_univ_four, Fin.sum_univ_four]
  change 2 ^ 2 * (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 0) ≤ _
  rw [mul_comm (a 0), ← mul_add, add_assoc, mul_comm (a 2), ← mul_add,
    add_comm (a 2), ← add_mul, add_assoc, add_add_add_comm, add_comm (a 0 + a 2)]
  exact Extra.two_sq_AM_GM _ _

theorem cyclic_add_right_formula (a : Fin (n + 1) → R) (c : R) :
    ∑ i, (a i + c) * (a (i + 1) + c)
      = ∑ i, a i * a (i + 1) + (2 * ∑ i, a i) * c + (n + 1) • c ^ 2 := by
  simp only [mul_add, add_mul, sum_add_distrib]
  rw [← sq, Fin.sum_const, ← add_assoc, add_left_inj, add_assoc, add_right_inj,
    ← mul_sum, ← sum_mul, mul_comm, ← add_mul, Fin_sum_shift, ← two_mul]

theorem sum_sq_add_right_formula (a : Fin (n + 1) → R) (c : R) :
    (∑ i, (a i + c)) ^ 2
      = (∑ i, a i) ^ 2 + (n + 1) • ((2 * ∑ i, a i) * c) + (n + 1) ^ 2 • c ^ 2 := by
  rw [sum_add_distrib, Fin.sum_const, add_sq, nsmul_eq_mul, mul_left_comm,
    ← nsmul_eq_mul, add_right_inj, nsmul_eq_mul, mul_pow, Nat.cast_pow]

omit [IsStrictOrderedRing R] in
theorem niceTuple.of_add₁ {n} {a : Fin (n + 1) → R} (ha : niceTuple a) (j) :
    niceTuple (λ i ↦ a (i + j)) := by
  rw [niceTuple, Fin_sum_shift]; simp only [add_right_comm _ 1 j]
  rw [Fin_sum_shift (λ i ↦ a i * a (i + 1))]; exact ha

omit [IsStrictOrderedRing R] in
theorem niceTuple.of_add₁_iff {n} {a : Fin (n + 1) → R} {j} :
    niceTuple (λ i ↦ a (i + j)) ↔ niceTuple a := by
  refine ⟨λ h ↦ ?_, λ h ↦ h.of_add₁ j⟩
  replace h := h.of_add₁ (-j)
  simp only [neg_add_cancel_right] at h; exact h

theorem niceTuple.of_add₂ [ExistsAddOfLE R] (hn : 4 ≤ n + 1) (hc : 0 ≤ c)
    {a : Fin (n + 1) → R} (ha : niceTuple a) (ha0 : ∀ i, 0 ≤ a i) :
    niceTuple (λ i ↦ a i + c) := by
  rw [niceTuple, cyclic_add_right_formula, sum_sq_add_right_formula, mul_add, mul_add]
  have h : (2 : R) ^ 2 ≤ (n + 1 : ℕ) :=
    (Nat.cast_le.mpr hn).trans_eq' (by rw [Nat.cast_mul 2 2, sq, Nat.cast_two])
  refine add_le_add (add_le_add ha ?_) ?_
  · rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right h
      (mul_nonneg (mul_nonneg zero_le_two (sum_nonneg λ i _ ↦ ha0 i)) hc)
  · rw [sq (n + 1), mul_nsmul, nsmul_eq_mul _ (_ • _)]
    exact mul_le_mul_of_nonneg_right h (nsmul_nonneg (sq_nonneg c) _)

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem cyclic_cons_zero_formula (a : Fin (n + 1) → R) :
    let b := Fin.cons 0 a
    ∑ i, b i * b (i + 1) = ∑ i ∈ ({Fin.last n} : Finset _)ᶜ, a i * a (i + 1) := by
  refine (sum_of_injOn Fin.succ ?_ ?_ ?_ ?_).symm
  · exact Set.injOn_of_injective (Fin.succ_injective _)
  · rw [coe_univ]; exact Set.mapsTo_univ _ _
  · rintro i - h
    obtain (rfl | rfl) : i = 0 ∨ i = Fin.last (n + 1) := by
      apply i.eq_zero_or_eq_succ.imp_right; rintro ⟨j, rfl⟩
      rw [coe_compl, coe_singleton, Set.mem_image] at h; simp only [Fin.succ_inj] at h
      rw [exists_eq_right, Set.mem_compl_iff, not_not, Set.mem_singleton_iff] at h
      rw [h, Fin.succ_last]
    · rw [Fin.cons_zero, zero_mul]
    · rw [Fin.last_add_one, Fin.cons_zero, mul_zero]
  · intro i h; refine congrArg₂ _ rfl ?_
    rw [mem_compl, mem_singleton, ← Ne, ← Fin.exists_castSucc_eq] at h
    rcases h with ⟨j, rfl⟩
    rw [Fin.coeSucc_eq_succ, Fin.succ_castSucc, Fin.coeSucc_eq_succ]; rfl

theorem niceTuple.of_zero_cons [ExistsAddOfLE R]
    {a : Fin (n + 1) → R} (ha : niceTuple a) (ha0 : ∀ i, 0 ≤ a i) :
    niceTuple (Fin.cons 0 a) := by
  rw [niceTuple, cyclic_cons_zero_formula, Fin.sum_cons, zero_add]
  refine (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)).trans ha
  exact sum_le_univ_sum_of_nonneg λ i ↦ mul_nonneg (ha0 i) (ha0 (i + 1))

omit [IsStrictOrderedRing R] in
theorem Fin_cons_nonneg {a : Fin (n + 1) → R} (ha : ∀ i, 0 ≤ a i) (i) :
    0 ≤ (Fin.cons 0 a : _ → R) i := by
  obtain (rfl | ⟨j, rfl⟩) := i.eq_zero_or_eq_succ
  exacts [le_refl 0, ha j]

theorem niceTuple.of_three_le [ExistsAddOfLE R] :
    ∀ (n : ℕ) (_ : 3 ≤ n) {a : Fin n.succ → R} (_ : ∀ i, 0 ≤ a i), niceTuple a := by
  refine Nat.le_induction (λ _ ↦ of_four _) (λ n hn n_ih a ha ↦ ?_)
  wlog h : ∀ i, a 0 ≤ a i
  · obtain ⟨j, hj⟩ : ∃ j, ∀ i, a j ≤ a i := Fin_exists_minimal a
    exact of_add₁_iff.mp <| this _ hn n_ih (a := λ i ↦ a (i + j))
      (λ i ↦ ha _) (λ i ↦ (hj _).trans_eq' (congrArg a j.zero_add))
  specialize ha 0
  obtain ⟨b, hb, h0⟩ : ∃ b : Fin (n + 1) → R,
      (∀ i, 0 ≤ b i) ∧ ∀ i, a i = (Fin.cons 0 b : _ → R) i + a 0 := by
    obtain ⟨b, hb⟩ : ∃ b : Fin n.succ → R, ∀ i, a i.succ = a 0 + b i :=
      Classical.axiom_of_choice λ i ↦ exists_add_of_le (h _)
    refine ⟨b, λ i ↦ ?_, λ i ↦ ?_⟩
    · rw [← le_add_iff_nonneg_right (a 0), ← hb]; exact h _
    · obtain (rfl | ⟨j, rfl⟩) := i.eq_zero_or_eq_succ
      · exact (zero_add _).symm
      · rw [hb, add_comm, Fin.cons_succ]
  clear h; generalize a 0 = c at ha h0
  obtain rfl : a = ((Fin.cons 0 b : _ → R) · + c) := funext h0
  exact of_add₂ (Nat.le_succ_of_le (Nat.succ_le_succ hn))
    ha (of_zero_cons (n_ih hb) hb) (Fin_cons_nonneg hb)

/-- The main claim -/
theorem main_claim [ExistsAddOfLE R]
    (hn : 4 ≤ n + 1) {a : Fin (n + 1) → R} (ha : ∀ i, 0 ≤ a i) :
    2 ^ 2 * ∑ i, a i * a (i + 1) ≤ (∑ i, a i) ^ 2 :=
  niceTuple.of_three_le n (Nat.succ_le_succ_iff.mp hn) ha





/-! ### Start of the problem -/

open Fin.NatCast in
omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem id1 (a : Fin (n + 1) → R) :
    3 * ∑ i, a i ^ 2 * a (i + 1) = ∑ i, a (i + 1) * (a i ^ 2 + 2 * a (i + 1) * a (i + 2)) := by
  simp only [mul_add]
  rw [sum_add_distrib, ← two_add_one_eq_three, add_comm, one_add_mul (2 : R), mul_sum]
  refine congrArg₂ _ (sum_congr rfl λ i _ ↦ mul_comm _ _) ?_
  rw [← Fin_sum_shift _ 1]; refine sum_congr rfl λ i _ ↦ ?_
  rw [add_assoc, one_add_one_eq_two (R := Fin (n + 1)), mul_assoc, sq,
    mul_left_comm _ 2, ← mul_assoc (a (i + 1))]

theorem id2 [ExistsAddOfLE R] (a : Fin (n + 1) → R) :
    (3 * ∑ i, a i ^ 2 * a (i + 1)) ^ 2
      ≤ (∑ i, a i ^ 2) * ∑ i, (a i ^ 2 + 2 * a (i + 1) * a (i + 2)) ^ 2 := by
  rw [id1, ← Fin_sum_shift (λ i ↦ a i ^ 2) 1]
  exact CauchySchwarz_squares _ _ _

open Fin.NatCast in
theorem id3 [ExistsAddOfLE R] (a : Fin (n + 1) → R) :
    ∑ i, (a i ^ 2 + 2 * a (i + 1) * a (i + 2)) ^ 2
      ≤ ∑ i, (a i ^ 2) ^ 2 + 2 * ∑ i, a i ^ 2 * (a (i + 1) ^ 2 + a (i + 2) ^ 2)
        + 2 ^ 2 * ∑ i, a i ^ 2 * a (i + 1) ^ 2 := by
  simp only [add_sq, sum_add_distrib]
  refine add_le_add_three (le_refl _) ?_ (le_of_eq ?_)
  · rw [mul_sum]; refine sum_le_sum λ i _ ↦ ?_
    rw [← mul_assoc 2]; refine mul_le_mul_of_nonneg_left (two_mul_le_add_sq _ _) ?_
    exact mul_nonneg zero_le_two (sq_nonneg _)
  · simp only [mul_pow, mul_assoc]; rw [← mul_sum, eq_comm, ← Fin_sum_shift _ 1]
    refine congrArg₂ _ rfl (sum_congr rfl λ i _ ↦ ?_)
    rw [add_assoc, one_add_one_eq_two]

open Fin.NatCast in
omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem id4 (b : Fin (n + 1) → R) :
    ∑ i, b i ^ 2 + 2 * ∑ i, b i * (b (i + 1) + b (i + 2))
      = ∑ i, b (i + 2) * ∑ j : Fin 5, b (j.val + i) := by
  simp only [Fin.sum_univ_five, mul_add, sum_add_distrib]
  rw [two_mul, two_mul, add_add_add_comm, add_left_comm, ← add_assoc, ← add_assoc]
  refine congrArg₂ _ (congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_) ?_
  rw [add_comm]; apply congrArg₂
  · refine sum_congr rfl λ i _ ↦ ?_
    rw [Fin.val_zero, Nat.cast_zero, zero_add, mul_comm]
  · rw [← Fin_sum_shift _ 1]; refine sum_congr rfl λ i _ ↦ ?_
    rw [Fin.val_one, Nat.cast_one, add_assoc, add_comm, mul_comm, one_add_one_eq_two]
  · rw [← Fin_sum_shift _ 2]; refine sum_congr rfl λ i _ ↦ ?_
    rw [Fin.val_two, sq, Nat.cast_two, add_comm]
  · rw [← Fin_sum_shift _ 2]; refine sum_congr rfl λ i _ ↦ ?_
    rw [add_assoc, two_add_one_eq_three, add_comm i 3]; rfl
  · rw [← Fin_sum_shift _ 2]; refine sum_congr rfl λ i _ ↦ ?_
    change _ = _ * b ((2 + 2 : ℕ) + i)
    rw [add_assoc, add_comm _ i, Nat.cast_add 2 2]; rfl

theorem id5 (hn : 5 ≤ n + 1) {b : Fin (n + 1) → R} (hb : ∀ i, 0 ≤ b i) :
    ∑ i, b i ^ 2 + 2 * ∑ i, b i * (b (i + 1) + b (i + 2)) ≤ (∑ i, b i) ^ 2 := by
  rw [id4, sq, sum_mul, ← Fin_sum_shift (λ i ↦ b i * _) 2]
  refine sum_le_sum λ i _ ↦ mul_le_mul_of_nonneg_left ?_ (hb _)
  rw [← Fin_sum_shift _ i]
  apply (sum_le_univ_sum_of_nonneg (s := image (Fin.castLE hn) univ) (λ _ ↦ hb _)).trans_eq'
  refine Finset.sum_of_injOn (Fin.castLE hn) ?_ ?_ (λ j ↦ ?_) (λ j _ ↦ ?_)
  · exact Set.injOn_of_injective (Fin.castLE_injective _)
  · rw [coe_image]; exact Set.mapsTo_image (Fin.castLE hn) _
  · rw [coe_univ, Set.image_univ, mem_image_univ_iff_mem_range]; exact absurd
  · refine congrArg b (congrArg₂ _ ?_ rfl)
    rw [← Fin.val_inj, Fin.coe_castLE, Fin.val_natCast, Nat.mod_succ_eq_iff_lt]
    exact j.2.trans_le hn

/-- Final solution -/
theorem final_solution [ExistsAddOfLE R] (hn : 5 ≤ n + 1) (a : Fin (n + 1) → R) :
    (3 * ∑ i, a i ^ 2 * a (i + 1)) ^ 2 ≤ 2 * (∑ i, a i ^ 2) ^ 3 := by
  rw [pow_succ' _ 2, mul_left_comm, two_mul]
  have X (i) : 0 ≤ a i ^ 2 := sq_nonneg (a i)
  refine (id2 _).trans (mul_le_mul_of_nonneg_left ?_ (sum_nonneg λ _ _ ↦ X _))
  exact (id3 _).trans (add_le_add (id5 hn X) (main_claim (Nat.le_of_succ_le hn) X))
