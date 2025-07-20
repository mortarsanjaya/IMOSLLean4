/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Finset.Sort

/-!
# IMO 2021 A1

Let $n$ be an integer and $A$ be a subset of $\{0, 1, …, 5^n\}$ of size $4n + 2$.
Prove that there exists $a, b, c ∈ A$ such that $a < b < c$ and $c + 2a > 3b$.
-/

namespace IMOSL
namespace IMO2021A1

lemma List_sorted_cons_cons_imp (h : List.Sorted r (a :: b :: l)) : r a b :=
  (List.forall_mem_cons.mp (List.sorted_cons.mp h).1).1





/-! ### Start of the problem -/

open List

def good (c : ℕ) : List ℕ → Prop
  | [] => True
  | [_] => True
  | b :: a :: l => good c (a :: l) ∧ 3 * (c - b) ≤ 2 * (c - a)


namespace good

theorem general_ineq₁ {c a} :
    ∀ {l b}, good c (b :: concat l a) →
      3 ^ l.length.succ * (c - b) ≤ 2 ^ l.length.succ * (c - a)
  | [], b => λ h ↦ h.2
  | b' :: l, b => λ h ↦ by
      rw [l.length_cons, Nat.pow_succ, mul_assoc]
      apply (Nat.mul_le_mul_left _ h.2).trans
      rw [mul_left_comm, Nat.pow_succ' (m := 2), mul_assoc]
      exact Nat.mul_le_mul_left _ h.1.general_ineq₁

theorem general_ineq₂ (h : b < c) (h0 : good c (b :: l)) :
    3 ^ l.length ≤ 2 ^ l.length * c := by
  obtain rfl | ⟨l, a, rfl⟩ : l = [] ∨ ∃ l' a, l = concat l' a := l.eq_nil_or_concat
  · exact (Nat.zero_lt_of_lt h).trans_eq c.one_mul.symm
  · apply (Nat.le_mul_of_pos_right _ (Nat.zero_lt_sub_of_lt h)).trans
    rw [l.length_concat]; exact (h0.general_ineq₁).trans (Nat.mul_le_mul_left _ (c.sub_le a))

theorem of_sorted_ineq : ∀ {l},
    l.Sorted GT.gt → (∀ a ∈ l, ∀ b ∈ l, a < b → 3 * (c - b) ≤ 2 * (c - a)) → good c l
  | [] => λ _ _ ↦ trivial
  | [_] => λ _ _ ↦ trivial
  | b₀ :: a₀ :: _ => λ h h0 ↦
      ⟨of_sorted_ineq h.of_cons λ a ha b hb ↦
        h0 a (mem_cons_of_mem _ ha) b (mem_cons_of_mem _ hb),
      h0 a₀ (mem_cons_of_mem _ mem_cons_self) b₀
        mem_cons_self (List_sorted_cons_cons_imp h).lt⟩


end good



lemma five_pow_bound (hn : n ≠ 0) : 2 ^ (4 * n) * 5 ^ n < 3 ^ (4 * n) := by
  rw [Nat.pow_mul, ← Nat.mul_pow, Nat.pow_mul]
  exact Nat.pow_lt_pow_left (Nat.lt_succ_self 80) hn

/-- Final solution -/
theorem final_solution (hn : n ≠ 0) {A : Finset ℕ}
    (hA : A.card = 4 * n + 2) (hA0 : ∀ a ∈ A, a ≤ 5 ^ n) :
    ∃ a ∈ A, ∃ b ∈ A, ∃ c ∈ A, a < b ∧ b < c ∧ 3 * b < c + 2 * a := by
  contrapose! hA0
  replace hA : (A.sort GE.ge).length = 4 * n + 2 := (Finset.length_sort _).trans hA
  ---- Grab the head of `A.sort` and pick that to be the element greater than `5^n`
  obtain ⟨c, l, h⟩ : ∃ c l, A.sort GE.ge = c :: l :=
    exists_cons_of_length_pos ((4 * n + 1).succ_pos.trans_eq hA.symm)
  refine ⟨c, by rw [← Finset.mem_sort GE.ge, h]; exact mem_cons_self, ?_⟩
  rw [h, l.length_cons, Nat.succ_inj] at hA
  ---- Grab the second element and simplify `hA`
  obtain ⟨b, l, rfl⟩ : ∃ b l', l = b :: l' :=
    exists_cons_of_length_pos ((4 * n).succ_pos.trans_eq hA.symm)
  rw [l.length_cons, Nat.succ_inj] at hA
  ---- Now prove that `c > 5^n`
  have h0 : (∀ x ∈ b :: l, c > x) ∧ (b :: l).Sorted GT.gt :=
    sorted_cons.mp (h ▸ A.sort_sorted_gt)
  suffices good c (b :: l) by
    refine Nat.lt_of_mul_lt_mul_left ((five_pow_bound hn).trans_le ?_)
    rw [← hA]; exact this.general_ineq₂ (h0.1 b mem_cons_self)
  refine good.of_sorted_ineq h0.2 λ x hx y hy h1 ↦ ?_
  replace hA0 : c + 2 * x ≤ 3 * y := by
    have X {a} (ha : a ∈ b :: l) : a ∈ A := by
      rw [← A.mem_sort GE.ge, h]; exact mem_cons_of_mem c ha
    refine hA0 x (X hx) y (X hy) c ?_ h1 (h0.1 y hy)
    rw [← A.mem_sort GE.ge, h]; exact mem_cons_self
  replace hx : 2 * x ≤ 2 * c := Nat.mul_le_mul_left 2 (h0.1 x hx).le
  rw [Nat.mul_sub, Nat.mul_sub, Nat.sub_le_iff_le_add, Nat.succ_mul,
    ← Nat.sub_add_comm hx, Nat.add_sub_assoc (((2 * x).le_add_left c).trans hA0)]
  exact Nat.add_le_add_left (Nat.le_sub_of_add_le hA0) _
