/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.ModEq

/-!
# IMO 2021 C2

Fix some positive integer $n$, and denote $[n] = \{0, 1, …, n - 1\}$.
Find all positive integers $m ∈ ℕ$ such that there exists a
  function $f : ℤ/mℤ → [n]$ with the following property:
  for any $k ∈ ℤ/mℤ$ and $i ∈ [n]$, there exists $j ≤ n$ such that $f(k + j) = i$.

### TODO

Replace `Nat.Icc_insert_succ_right` with `Finset.insert_Icc_eq_Icc_succ_right`
-/

namespace IMOSL
namespace IMO2021C2

open Finset Fin.NatCast

def good (f : Fin (m + 1) → Fin n) := ∀ k i, ∃ j ≤ n, f (k + j) = i





/-! ### Addition on `Fin` as bijection -/

lemma Fin_add_comm (x y : Fin m) : x + y = y + x := by
  rw [Fin.ext_iff, Fin.val_add, Fin.val_add, Nat.add_comm]

lemma Fin_add_assoc (x y z : Fin m) : x + y + z = x + (y + z) := by
  simp only [Fin.ext_iff, Fin.val_add]
  rw [Nat.mod_add_mod, Nat.add_mod_mod, Nat.add_assoc]

lemma Fin_cast_mul_add_self (x : Fin m.succ) : ((m * x.1 : ℕ) : Fin m.succ) + x = 0 := by
  rw [Fin.ext_iff, Fin.val_add, Fin.val_natCast, Nat.mod_add_mod,
    Fin.val_zero, ← Nat.succ_mul, Nat.mul_mod_right]

def Fin_add_equiv (j : Fin (m + 1)) : Fin (m + 1) ≃ Fin (m + 1) where
  toFun := (· + j)
  invFun := (· + (m * j.1 : ℕ))
  left_inv := λ x ↦ by
    simp only; rw [Fin_add_assoc, Fin_add_comm j, Fin_cast_mul_add_self, Fin.add_zero]
  right_inv := λ x ↦ by simp only; rw [Fin_add_assoc, Fin_cast_mul_add_self, Fin.add_zero]

theorem good.mod_le_div {f : Fin (m + 1) → Fin n} (hf : good f) :
    (m + 1) % n ≤ (m + 1) / n := by
  match n with | 0 => exact (f 0).elim0 | n + 1 => ?_
  obtain ⟨i, hi⟩ : ∃ i, (univ.filter λ x ↦ f x = i).card ≤ m.succ / n.succ := by
    by_contra h; simp at h
    have X : ∑ i : Fin (n + 1), ((m + 1) / (n + 1) + 1) ≤ _ :=
      sum_le_sum (s := univ) (λ i _ ↦ h i)
    apply X.not_gt
    simp only [card_eq_sum_ones, sum_fiberwise]
    simp only [sum_const, card_univ, Fintype.card_fin]
    exact m.succ.mul_one.trans_lt (Nat.lt_mul_div_succ m.succ n.succ_pos)
  -- Now reduce to `qn + r = (n + 1)q` and do the inequality chain
  suffices m.succ ≤ (n.succ + 1) * (m.succ / n.succ) by
    rwa [← Nat.add_le_add_iff_left, Nat.div_add_mod, ← Nat.succ_mul]
  calc
    _ = ∑ k : Fin m.succ, 1 := by
      rw [sum_const, card_univ, Fintype.card_fin]; exact m.succ.mul_one.symm
    _ ≤ ∑ k : Fin m.succ, ∑ j ∈ range (n + 2), if f (k + j) = i then 1 else 0 := by
      refine sum_le_sum λ k _ ↦ ?_
      rw [← card_filter, Nat.succ_le, card_pos]
      obtain ⟨j, hj⟩ := hf k i; refine ⟨j, ?_⟩
      rwa [mem_filter, mem_range, Nat.lt_succ_iff]
    _ = ∑ j ∈ range (n + 2), ∑ k : Fin m.succ, if f (k + j) = i then 1 else 0 := sum_comm
    _ = ∑ _ ∈ range (n + 2), ∑ k : Fin m.succ, if f k = i then 1 else 0 :=
      sum_congr rfl λ j _ ↦
        Fintype.sum_bijective _ (Fin_add_equiv j).bijective _ _ λ _ ↦ rfl
    _ = (n + 2) * (univ.filter λ x ↦ f x = i).card := by
      rw [sum_const, card_range, card_filter]; rfl
    _ ≤ (n + 2) * (m.succ / n.succ) := Nat.mul_le_mul_left _ hi





/-! ### Properties of a special function -/

lemma image_mul_div (h : a ≤ b) (i : ℕ) :
    ∀ j ≥ i, (Icc i j).image (λ x ↦ a * x / b) = Icc (a * i / b) (a * j / b) := by
  ---- Induction on `n`; the base case `n = m` is immediate
  refine Nat.le_induction ?_ λ j hij hj ↦ ?_
  · rw [Icc_self, image_singleton, Icc_self]
  ---- Induction step
  obtain ⟨c, hc⟩ : ∃ c, a * (j + 1) / b = a * j / b + c :=
    Nat.exists_eq_add_of_le (Nat.div_le_div_right (Nat.le_add_right _ _))
  rw [← Nat.Icc_insert_succ_right (Nat.le_add_right_of_le hij), image_insert, hj, hc]
  replace hn : a * i / b ≤ a * j / b := Nat.div_le_div_right (Nat.mul_le_mul_left a hij)
  obtain rfl | rfl : c = 0 ∨ c = 1 := by
    rw [← Nat.le_one_iff_eq_zero_or_eq_one, ← Nat.add_le_add_iff_left, ← hc]
    obtain rfl | hb : b = 0 ∨ 0 < b := b.eq_zero_or_pos
    · rw [Nat.div_zero]; exact Nat.zero_le _
    · rw [← Nat.add_div_right _ hb]; exact Nat.div_le_div_right (Nat.add_le_add_left h _)
  ---- Case 1: `c = 0`
  · rw [Nat.add_zero, insert_eq_self, mem_Icc]
    exact ⟨hn, Nat.le_refl _⟩
  ---- Case 2: `c = 1`
  · exact Nat.Icc_insert_succ_right (Nat.le_succ_of_le hn)

lemma exists_le_mul_div_add_eq (h : a ≤ b) (x : ℕ) (h0 : c ≤ a * m / b) :
    ∃ k ≤ m, a * (x + k) / b = a * x / b + c := by
  replace h0 : a * x / b + c ∈ Icc (a * x / b) (a * (x + m) / b) :=
    mem_Icc.mpr ⟨Nat.le_add_right _ _,
      (Nat.add_le_add_left h0 _).trans
        (a.mul_add x m ▸ Nat.add_div_le_add_div (a * x) (a * m) b)⟩
  rw [← image_mul_div h x (x + m) (x.le_add_right m), mem_image, x.add_comm] at h0
  rcases h0 with ⟨l, h0, h1⟩; rw [mem_Icc] at h0
  refine ⟨l - x, Nat.sub_le_of_le_add h0.2, ?_⟩
  rw [Nat.add_sub_cancel' h0.1, h1]

lemma mul_div_Fin_eq_mod (n i m) :
    (((n + 1) * i / (m + 1) : ℕ) : Fin (n + 1)) = ↑((n + 1) * (i % (m + 1)) / (m + 1)) :=
  calc
    _ = ↑((n + 1) * (i / (m + 1)) + (n + 1) * (i % (m + 1)) / (m + 1)) := by
      rw [← Nat.mul_add_div m.succ_pos, Nat.mul_left_comm, ← Nat.mul_add, Nat.div_add_mod]
    _ = _ := by rw [← Fin.val_inj, Fin.val_natCast, Fin.val_natCast, Nat.mul_add_mod]

lemma mul_div_Fin_eq_mod2 (n T i m) :
    (((n + 1) * T * i / (m + 1) : ℕ) : Fin (n + 1))
      = ↑((n + 1) * T * (i % (m + 1)) / (m + 1)) := by
  rw [Nat.mul_assoc, Nat.mul_assoc, mul_div_Fin_eq_mod,
    ← Nat.mul_mod_mod, ← mul_div_Fin_eq_mod]

lemma mul_div_good_of_bound {n m : ℕ} (h : m.succ % n.succ ≤ m.succ / n.succ) :
    good λ x : Fin m.succ ↦
      ((n.succ * (m.succ / n.succ) * x.1 / m.succ : ℕ) : Fin n.succ) := by
  set a := n.succ * (m.succ / n.succ)
  replace h : n ≤ a * n.succ / m.succ := by
    have h0 : a + m.succ % n.succ = m.succ := Nat.div_add_mod m.succ n.succ
    rw [Nat.le_div_iff_mul_le m.succ_pos, ← h0, Nat.mul_add, Nat.mul_comm, a.mul_succ]
    exact Nat.add_le_add_left (Nat.mul_le_mul n.le_succ h) _
  intro k i; obtain ⟨x, rfl⟩ : ∃ x : Fin (n + 1), x + (a * k.1 / m.succ : ℕ) = i :=
    (Fin_add_equiv (m := n) (a * k / m.succ : ℕ)).surjective i
  obtain ⟨j, hj, hj0⟩ : ∃ j ≤ n.succ, a * (k.1 + j) / m.succ = a * k.1 / m.succ + x.1 :=
    exists_le_mul_div_add_eq (Nat.mul_div_le _ _) _ ((Fin.is_le _).trans h)
  generalize a * k.1 / m.succ = b at hj0 ⊢
  refine ⟨j, hj, ?_⟩; dsimp only [a]
  rw [mul_div_Fin_eq_mod2, Fin.val_add, Nat.mod_mod, Fin.val_natCast,
    Nat.add_mod_mod, ← mul_div_Fin_eq_mod2, hj0, Fin_add_comm, ← Fin.val_inj,
    Fin.val_natCast, Fin.val_add, Fin.val_natCast, Nat.mod_add_mod]





/-! ### Final solution -/

/-- Final solution -/
theorem final_solution {n m : ℕ} :
    (∃ f : Fin m.succ → Fin n.succ, good f) ↔ m.succ % n.succ ≤ m.succ / n.succ :=
  ⟨λ ⟨_, hf⟩ ↦ hf.mod_le_div, λ h ↦ ⟨_, mul_div_good_of_bound h⟩⟩
