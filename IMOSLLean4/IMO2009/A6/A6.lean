/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Order.Monotone.Basic
import IMOSLLean4.Extra.IntLinearSolver

/-!
# IMO 2009 A6 (P3)

Let $f : ℕ → ℕ$ be a strictly increasing function.
Suppose that there exists $A, B, C, D ∈ ℕ$ such that
  $f(f(n)) = An + B$ and $f(f(n) + 1) = Cn + D$ for any $n ∈ ℕ$.
Prove that there exists $M, N ∈ ℕ$ such that $f(n) = Mn + N$ for all $n ∈ ℕ$.
-/

namespace IMOSL
namespace IMO2009A6

theorem exists_map_minimal [hα : Nonempty α] (f : α → ℕ) : ∃ a₀ : α, ∀ a, f a₀ ≤ f a := by
  by_contra h; simp only [not_exists, not_forall, not_le] at h
  obtain ⟨a₀⟩ := hα
  have h0 : ∀ {m}, m ≤ f a₀ → ∃ a, f a < m := by
    refine Nat.decreasingInduction (λ k _ ⟨a, ha⟩ ↦ ?_) (h a₀)
    obtain ⟨b, hb⟩ := h a
    refine ⟨b, hb.trans_le (Nat.le_of_lt_succ ha)⟩
  obtain ⟨b, h1⟩ := h0 (f a₀).zero_le
  exact Nat.not_le_of_lt h1 (f b).zero_le

theorem unbounded_of_forall_map_not_maximal [hα : Nonempty α]
    {f : α → ℕ} (hf : ∀ a, ∃ b, f a < f b) : ∀ n, ∃ a, n ≤ f a :=
  Nat.rec (hα.elim λ a ↦ ⟨a, (f a).zero_le⟩)
    λ _ ⟨a, ha⟩ ↦ (hf a).imp λ _ ↦ ha.trans_lt

theorem exists_map_maximal_of_bdd [hα : Nonempty α]
    {f : α → ℕ} (hf : ∃ n, ∀ a, f a ≤ n) : ∃ a₀, ∀ a, f a ≤ f a₀ := by
  by_contra h; simp only [not_exists, not_forall, not_le] at h
  rcases hf with ⟨n, hn⟩
  obtain ⟨a₀, ha₀⟩ := unbounded_of_forall_map_not_maximal h n.succ
  exact Nat.not_le_of_lt ha₀ (hn a₀)

theorem le_of_linear_growth {A B C D : ℕ} (h : ∀ n, A * n + B ≤ C * n + D) : A ≤ C := by
  replace h : A * (D + 1) ≤ C * (D + 1) + D := Nat.le_of_add_right_le (h (D + 1))
  rw [← Nat.lt_add_one_iff, Nat.add_assoc, ← Nat.succ_mul] at h
  exact Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_right h)

theorem mul_sub_le_sub_map_of_diff {f : ℕ → ℕ} (hm : ∀ n, f n + m ≤ f (n + 1)) (n k) :
    m * (n - k) ≤ f n - f k := by
  obtain h | ⟨c, rfl⟩ : n ≤ k ∨ ∃ c, n = k + c :=
    (Nat.le_total n k).imp_right Nat.exists_eq_add_of_le
  ---- Case 1: `n ≤ k`
  · rw [Nat.sub_eq_zero_of_le h, Nat.mul_zero]
    exact Nat.zero_le _
  ---- Case 2: `n ≥ k`
  · rw [Nat.add_sub_cancel_left]; apply Nat.le_sub_of_add_le
    induction c with
      | zero => rw [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      | succ c c_ih =>
          rw [Nat.mul_succ, Nat.add_right_comm]
          exact (Nat.add_le_add_right c_ih m).trans (hm _)

theorem sub_le_sub_map_of_StrictMono {f : ℕ → ℕ} (hf : StrictMono f) (n k) :
    (n - k) ≤ f n - f k :=
  (n - k).one_mul ▸ mul_sub_le_sub_map_of_diff (λ n ↦ hf n.lt_succ_self) n k

theorem sub_map_le_mul_sub_of_Monotone {f : ℕ → ℕ}
    (hf : Monotone f) (hm : ∀ n, f (n + 1) ≤ f n + m) (n k) :
    f n - f k ≤ m * (n - k) := by
  obtain h | ⟨c, rfl⟩ : n ≤ k ∨ ∃ c, n = k + c :=
    (Nat.le_total n k).imp_right Nat.exists_eq_add_of_le
  ---- Case 1: `n ≤ k`
  · rw [Nat.sub_eq_zero_of_le h, Nat.mul_zero, Nat.le_zero, Nat.sub_eq_zero_iff_le]
    exact hf h
  ---- Case 2: `n ≥ k`
  · rw [Nat.add_sub_cancel_left]; apply Nat.sub_le_of_le_add
    induction c with
      | zero => rw [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
      | succ c c_ih =>
          rw [Nat.mul_succ, Nat.add_right_comm]
          exact (hm _).trans (Nat.add_le_add_right c_ih m)

/-- Final solution -/
theorem final_solution {f : ℕ → ℕ} (hf : StrictMono f)
    (h : ∃ A B, ∀ n, f (f n) = A * n + B) (h0 : ∃ C D, ∀ n, f (f n + 1) = C * n + D) :
    ∃ M N, ∀ n, f n = M * n + N := by
  have hf0 (n) : f n < f (n + 1) := hf n.lt_succ_self
  rcases h with ⟨A, B, h⟩
  rcases h0 with ⟨C, D, h0⟩
  ---- First, show that `A = C`
  obtain rfl : A = C := by
    apply Nat.le_antisymm
    -- `A ≤ C`
    · refine le_of_linear_growth (B := B) (D := D) λ n ↦ ?_
      rw [← h, ← h0]; exact (hf0 (f n)).le
    -- `C ≤ A`
    · refine le_of_linear_growth (B := D) (D := A + B) λ n ↦ ?_
      rw [← h0, ← Nat.add_assoc, ← Nat.mul_succ, ← h]
      exact hf.monotone (hf n.lt_succ_self)
  ---- Reduce to showing that all the differences are equal
  suffices ∃ M, ∀ n, f (n + 1) = M + f n
    from this.imp λ M hM ↦ ⟨f 0, Extra.LinearSolver.NatNat hM⟩
  ---- Pick a minimal difference and a maximal difference
  let d (n : ℕ) : ℕ := f (n + 1) - f n
  obtain ⟨xm, hxm⟩ : ∃ xm, ∀ n, d xm ≤ d n := exists_map_minimal d
  obtain ⟨xM, hxM⟩ : ∃ xM, ∀ n, d n ≤ d xM := by
    refine exists_map_maximal_of_bdd ⟨A, λ n ↦ ?_⟩
    apply (sub_le_sub_map_of_StrictMono hf _ _).trans
    rw [h, h, Nat.mul_succ, Nat.add_right_comm, Nat.add_sub_cancel_left]
  ---- Reduce the question to `d(xm) = d(xM)`
  suffices d xM ≤ d xm by
    refine ⟨d xm, λ n ↦ Nat.eq_add_of_sub_eq (hf0 n).le ?_⟩
    exact Nat.le_antisymm ((hxM n).trans this) (hxm n)
  ---- Strengthen the properties of `xm` and `xM`
  have hxm0 : ∀ n k, d xm * (n - k) ≤ f n - f k :=
    mul_sub_le_sub_map_of_diff λ n ↦ Nat.add_le_of_le_sub' (hf0 n).le (hxm n)
  have hxM0 : ∀ n k, f n - f k ≤ d xM * (n - k) := by
    refine sub_map_le_mul_sub_of_Monotone hf.monotone λ n ↦ ?_
    rw [Nat.add_comm (f n)]; exact Nat.le_add_of_sub_le (hxM n)
  ---- Get a bound of `A` in terms of `D - B`, `xm`, and `xM`
  obtain ⟨K, rfl⟩ : ∃ K, D = B + K := by
    have h1 : f (f 0) ≤ f (f 0 + 1) := (hf0 (f 0)).le
    rw [h, h0, Nat.mul_zero, Nat.zero_add, Nat.zero_add] at h1
    exact Nat.exists_eq_add_of_le h1
  have hA1 : A + d xM ≤ d xm * d xM + K := by
    rw [← Nat.add_le_add_iff_left (n := A * xm + B), Nat.add_add_add_comm, ← Nat.mul_succ,
      ← Nat.add_assoc, ← h, Nat.add_add_add_comm, Nat.add_right_comm, ← h0]
    apply (Nat.add_le_add_right (Nat.le_add_of_sub_le (hxM0 (f xm.succ) (f xm + 1))) _).trans
    rw [Nat.add_right_comm, ← Nat.mul_add_one, Nat.add_comm, Nat.mul_comm]
    refine Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _
    rw [← Nat.sub_sub, Nat.sub_add_cancel (Nat.sub_pos_of_lt (hf xm.lt_succ_self))]
  have hA2 : d xm * d xM + K ≤ A + d xm := by
    rw [← Nat.add_le_add_iff_left (n := A * xM + B), Nat.add_add_add_comm, Nat.add_right_comm,
      ← h0, Nat.add_add_add_comm, ← A.mul_succ, ← Nat.add_assoc, ← h]
    have h1 := hf.monotone (hf xM.lt_succ_self)
    apply Nat.add_le_of_le_sub' (Nat.le_add_right_of_le h1)
    rw [Nat.add_comm, Nat.add_sub_assoc h1, Nat.add_comm]
    apply (Nat.add_le_add_right (hxm0 _ _) _).trans_eq'
    rw [← Nat.mul_succ, Nat.sub_succ, Nat.succ_pred_eq_of_pos (Nat.sub_pos_of_lt (hf0 _))]
  exact Nat.le_of_add_le_add_left (hA1.trans hA2)
