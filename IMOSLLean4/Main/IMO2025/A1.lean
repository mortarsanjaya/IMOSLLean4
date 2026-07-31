/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Mathlib.Order.OrderIsoNat

/-!
# IMO 2025 A1

Initially, a pair of distinct nonzero integers is written on the board.
At any time, we can do the following operation: if the current pair on the board is $(a, b)$,
  replace it with a pair $(u, v)$ such that $u ≠ v$ are roots of $x^2 + ax + b$.
If such pairs do not exist, then the game ends.

Determine all initial pairs such that the game can be played forever.

### Answer

$(1, -2)$.

### Solution

We follow Solution 1 of the [official solution](https://www.imo-official.org/problems/2025/).
We represent the infinite game as an infinite sequence.
We say that a sequence $((a_i, b_i))_{i ≥ 0}$ is `good` if for every $i$,
  $a_{i + 1}$ and $b_{i + 1}$ are the distinct roots of $x^2 + a_i x + b_i$.
Then the question asks to find all pairs $(a, b)$ of distinct nonzero integers such that
  there exists a `good` sequence $((a_i, b_i))_{i ≥ 0}$ with $(a_0, b_0) = (a, b)$.

In fact, the same answer still holds without requiring that the entries of
  the initial pair are distinct or that the first entry is zero.
If the entries are allowed to be zero, then $(n, 0)$ also works for $n ≠ 0$.

### Notes

In the documentation of the lemmas about good sequences,
  we always denote the good sequences by $((a_i, b_i))_{i ≥ 0}$.
-/

@[expose] public section

namespace IMOSL
namespace IMO2025A1

/-- This is a predicate for pairs `(a, b)` and `(u, v)` saying that
  `u` and `v` are roots of the polynomial `x^2 + ax + b`. -/
def is_quad_root_of (p q : ℤ × ℤ) :=
  q.1 ^ 2 + p.1 * q.1 + p.2 = 0 ∧ q.2 ^ 2 + p.1 * q.2 + p.2 = 0

/-- A sequence `((a_i, b_i))_{i ≥ 0}` is called `good` if for every `i`,
  `a_{i + 1}` and `b_{i + 1}` are distinct roots of `x^2 + a_i x + b_i`. -/
def good (s : ℕ → ℤ × ℤ) :=
  ∀ i, (s (i + 1)).1 ≠ (s (i + 1)).2 ∧ is_quad_root_of (s i) (s (i + 1))

/-- The function `f(u, v) = (-(u + v), uv)`. -/
def f (p : ℤ × ℤ) := (-(p.1 + p.2), p.1 * p.2)

/-- The formula `a^2 + (-(a + b))a + ab = 0`. -/
theorem quadratic_formula (a b : ℤ) : a ^ 2 + -(a + b) * a + a * b = 0 := by
  rw [Int.pow_succ, Int.pow_one, ← Int.add_mul, Int.mul_comm,
    ← Int.mul_add, Int.add_right_comm, Int.add_right_neg, Int.mul_zero]

/-- The formula `u^2 - v^2 = (u - v)(u + v)`, implemented to avoid imports. -/
theorem Int_sq_sub_sq (u v : ℤ) : u ^ 2 - v ^ 2 = (u + v) * (u - v) := by
  rw [Int.mul_sub, Int.add_mul, Int.add_mul, ← Int.sub_sub, Int.mul_comm v,
    Int.add_sub_cancel, Int.pow_succ, Int.pow_one, Int.pow_succ, Int.pow_one]

/-- If `(a, b) = f(u, v)`, then `u` and `v` are roots of the polynomial `x^2 + ax + b`. -/
theorem is_quad_root_of_f (p) : is_quad_root_of (f p) p := by
  rcases p with ⟨u, v⟩
  refine ⟨quadratic_formula u v, ?_⟩
  rw [f, Int.add_comm u, Int.mul_comm u]
  exact quadratic_formula v u

/-- If `u ≠ v`, then `u` and `v` are roots of the polynomial `x^2 + ax + b`
  if and only if `(a, b) = f(u, v)`, i.e. `a = -(u + v)` and `b = uv`. -/
theorem is_quad_root_of_iff_eq_f {p q : ℤ × ℤ} (hp : q.1 ≠ q.2) :
    is_quad_root_of p q ↔ p = f q := by
  refine ⟨λ h ↦ ?_, λ h ↦ h ▸ is_quad_root_of_f q⟩
  rcases p with ⟨a, b⟩
  rcases q with ⟨u, v⟩
  rcases h with ⟨h, h0⟩
  ---- For the `→` direction, first subtract the two equations and get `a = -(u + v)`.
  replace h0 : a = -(u + v) := by
    rw [← h, eq_comm, Int.add_left_inj, ← Int.sub_eq_iff_eq_add, Int.add_sub_assoc,
      ← Int.mul_sub, ← Int.sub_eq_zero, Int.add_comm, Int.add_sub_assoc, Int_sq_sub_sq,
      ← Int.add_mul, Int.mul_eq_zero, Int.sub_eq_zero, or_iff_left hp, Int.add_comm] at h0
    exact (Int.neg_eq_of_add_eq_zero h0).symm
  ---- Afterwards it is easy to show that `b = uv`.
  rw [h0, ← quadratic_formula u v, Int.add_right_inj] at h
  exact Prod.ext h0 h

/-- If `f(u, v) = (a, b)`, then `a^2 - 4b ≥ 0`. -/
theorem discriminant_nonneg_of_f {p q} (h : f p = q) : q.1 ^ 2 - 4 * q.2 ≥ 0 := by
  calc q.1 ^ 2 - 2 * 2 * q.2
  _ = (-(p.1 + p.2)) ^ 2 - 2 * 2 * (p.1 * p.2) := by rw [← h, f]
  _ = (p.1 + p.2) ^ 2 - 2 * 2 * (p.1 * p.2) := by rw [Int.neg_pow, Int.pow_zero, Int.one_mul]
  _ = (p.1 - p.2) ^ 2 := by rw [sub_eq_iff_comm, Int_sq_sub_sq, add_add_sub_cancel,
    add_sub_sub_cancel, ← Int.two_mul, ← Int.two_mul, mul_mul_mul_comm]
  _ ≥ 0 := Int.sq_nonneg _


namespace good

/-- The constant `(1, -2)` sequence is good. -/
theorem of_const_one_neg_two : good (λ _ ↦ (1, -2)) :=
  λ _ ↦ ⟨(by decide : (1 : ℤ) ≠ -2), is_quad_root_of_f (1, -2)⟩


variable {s : ℕ → ℤ × ℤ} (hs : good s)
include hs

/-- We have the formula `(a_i, b_i) = f(a_{i + 1}, b_{i + 1})`. -/
theorem map_eq_f_map_succ (i) : s i = f (s (i + 1)) :=
  let ⟨h, h0⟩ := hs i; (is_quad_root_of_iff_eq_f h).mp h0

/-- If `b_0 ≠ 0`, then `(a_i, b_i) = (1, -2)` for all `i`. -/
theorem eq_const_one_neg_two_of_b0_ne_zero (hs0 : (s 0).2 ≠ 0) : s = λ _ ↦ (1, -2) := by
  have hs1 (i) : s i = f (s (i + 1)) := hs.map_eq_f_map_succ i
  have hs1' (i) : (s i).2.natAbs = (s (i + 1)).1.natAbs * (s (i + 1)).2.natAbs := by
    rw [hs1, f, Int.natAbs_mul]
  ---- First, each `b_i` are nonzero.
  replace hs0 : ∀ i, (s i).2 ≠ 0 :=
    Nat.rec hs0 λ i hi hi0 ↦ hi (hs1 i ▸ (Int.mul_eq_zero.mpr (Or.inr hi0)))
  have hs0' (i) : (s i).2.natAbs > 0 := Int.natAbs_pos.mpr (hs0 i)
  ---- Next, the sequence `(|b_i|)_{i ≥ 0}` is eventually constant, say starting at `N`.
  obtain ⟨N, hs2⟩ : ∃ N, ∀ i ≥ N, (s N).2.natAbs = (s i).2.natAbs := by
    refine WellFoundedLT.antitone_chain_condition <| antitone_nat_of_succ_le λ i ↦
      Nat.le_of_dvd (hs0' i) ⟨(s (i + 1)).1.natAbs, (hs1' i).trans (Nat.mul_comm _ _)⟩
  ---- Then we have `a_i = ±1` for all `i > N`.
  replace hs2 {i} (hi : i > N) : (s i).1 = 1 ∨ (s i).1 = -1 := by
    have h : (s (i - 1)).2.natAbs = (s i).2.natAbs :=
      (hs2 _ (Nat.le_sub_one_of_lt hi)).symm.trans (hs2 i hi.le)
    rw [hs1', Nat.sub_add_cancel (Nat.one_le_of_lt hi),
      Nat.mul_eq_right (hs0' i).ne.symm] at h
    exact Int.natAbs_eq_natAbs_iff.mp h
  ---- Change an auxiliary lemma to `a_i = -(a_{i + 1} + b_{i + 1})`.
  replace hs1' (i) : (s i).1 = -((s (i + 1)).1 + (s (i + 1)).2) := congrArg Prod.fst (hs1 i)
  ---- Now we show that `a_i = 1` for all `i ≥ N + 2`.
  replace hs2 {i} (hi : i ≥ N + 2) : (s i).1 = 1 := by
    -- Assume `a_i = -1`, and write `i = j + 1` where `j > N`.
    refine (hs2 (Nat.lt_of_succ_lt hi)).resolve_right λ hj ↦ ?_
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hi)
    rename j + 1 > N + 1 => hj0; replace hj0 : j > N := Nat.lt_of_succ_lt_succ hj0
    -- Now split into two cases: `a_j = 1` or `a_j = -1`.
    obtain hj1 | hj1 : (s j).1 = 1 ∨ (s j).1 = -1 := hs2 hj0
    -- The case `a_j = 1` yields `b_{j + 1} = 0`; contradiction.
    · rw [hs1', Int.neg_eq_comm, hj, left_eq_add] at hj1
      exact hs0 (j + 1) hj1
    -- The case `a_j = -1` yields `b_{j + 1} = 2`, but `f` does not attain `(-1, 2)`.
    · replace hj1 : f (s (j + 2)) = (-1, 2) := by
        rw [hs1', Int.neg_inj, hj, neg_add_eq_iff_eq_add] at hj1
        exact (hs1 _).symm.trans (Prod.ext hj hj1)
      exact (discriminant_nonneg_of_f hj1).not_gt (by decide)
  ---- Then `(a_i, b_i) = (1, -2)` for all `i ≥ N + 3`.
  replace hs2 {i} (hi : i ≥ N + 3) : s i = (1, -2) := by
    have hi0 : (s i).1 = 1 := hs2 (Nat.le_of_succ_le hi)
    have hi1 : (s (i - 1)).1 = -((s i).1 + (s i).2) := by
      rw [hs1', Nat.sub_add_cancel (Nat.one_le_of_lt hi)]
    rw [hs2 (Nat.le_sub_one_of_lt hi), hi0, Int.eq_neg_comm, ← eq_sub_iff_add_eq'] at hi1
    exact Prod.ext hi0 hi1
  ---- Finally, we apply decreasing induction to extend to the entire sequence.
  clear hs0 hs0' hs1'
  funext i; refine (Nat.le_total i (N + 3)).elim (λ hi ↦ ?_) hs2
  induction hi using Nat.decreasingInduction with
    | self => exact hs2 (Nat.le_refl _)
    | of_succ k _ hk => rw [hs1, hk]; rfl

end good


/-- Final solution -/
theorem final_solution (hp : p.2 ≠ 0) : (∃ s, good s ∧ s 0 = p) ↔ p = (1, -2) := by
  refine ⟨?_, λ hp0 ↦ ⟨λ _ ↦ (1, -2), good.of_const_one_neg_two, hp0.symm⟩⟩
  rintro ⟨s, hs, rfl⟩; exact congrFun (hs.eq_const_one_neg_two_of_b0_ne_zero hp) 0
