/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow

/-!
# IMO 2017 A4

Let $G$ be a totally ordered abelian group and let $D$ be a natural number.
A sequence $(a_n)_{n ≥ 0}$ of elements of $G$ satisfies the following properties:
* for any $i, j ∈ ℕ$ with $i + j ≥ D$, we have $a_{i + j + 1} ≤ -a_i - a_j$,
* for any $n ≥ D$, there exists $i, j ∈ ℕ$ such that
    $i + j = n$ and $a_{n + 1} = -a_i - a_j$.

Prove that $(a_n)_{n ≥ 0}$ is bounded.
Explicitly, prove that $|a_n| ≤ 2 \max\{B, C - B\}$, where
  $B = \max_{n ≤ D} a_n$ and $C = \max_{n ≤ D} (-a_n)$.
-/

namespace IMOSL
namespace IMO2017A4

open Finset

variable [AddCommGroup G] [LinearOrder G]

/-! ### Two definitions -/

abbrev good1 (D : ℕ) (a : ℕ → G) :=
  ∀ i j : ℕ, D ≤ i + j → a (i + j + 1) ≤ -(a i + a j)

abbrev good2 {G} [AddCommGroup G] (D : ℕ) (a : ℕ → G) :=
  ∀ n ≥ D, ∃ i j : ℕ, i + j = n ∧ a (n + 1) = -(a i + a j)





/-! ### Main properties of `good1` and `good2` -/

variable [IsOrderedAddMonoid G]

theorem abs_le_max_range_sup' (a : ℕ → G) (n : ℕ) :
    |a n| ≤ max ((range (n + 1)).sup' nonempty_range_add_one (-a))
      (2 • (range (n + 1)).sup' nonempty_range_add_one a) := by
  rw [le_max_iff]; refine (le_total (a n) 0).imp (λ h ↦ ?_) (λ h ↦ ?_)
  · exact (abs_of_nonpos h).trans_le (le_sup' (-a) (self_mem_range_succ _))
  · rw [abs_of_nonneg h, two_nsmul]
    have h0 : a n ≤ (range (n + 1)).sup' nonempty_range_add_one a :=
      le_sup' a (self_mem_range_succ _)
    exact le_add_of_le_of_nonneg h0 (h.trans h0)

theorem good1_bdd_above {a : ℕ → G} (h : good1 D a) (h0 : D ≤ n) :
    a (n + 1) ≤ (range (n + 1)).sup' nonempty_range_add_one (-a)
      - (range (n + 1)).sup' nonempty_range_add_one a := by
  obtain ⟨i, h2, h1⟩ :
      ∃ i ∈ range (n + 1), (range (n + 1)).sup' nonempty_range_add_one a = a i :=
    exists_mem_eq_sup' nonempty_range_add_one a
  obtain ⟨j, rfl⟩ : ∃ j, n = i + j := Nat.exists_eq_add_of_le (mem_range_succ_iff.mp h2)
  apply (h i j h0).trans
  rw [h1, neg_add_rev, ← sub_eq_add_neg, sub_le_sub_iff_right]
  exact le_sup' (-a) (mem_range_succ_iff.mpr (Nat.le_add_left j i))

theorem good1_range_sup' {a : ℕ → G} (h : good1 D a) (h0 : D ≤ n) :
    (range (n + 2)).sup' nonempty_range_add_one a ≤
      max ((range (n + 1)).sup' nonempty_range_add_one a)
        ((range (n + 1)).sup' nonempty_range_add_one (-a)
          - (range (n + 1)).sup' nonempty_range_add_one a) := by
  simp_rw [range_add_one (n := n + 1), sup'_insert nonempty_range_add_one, max_comm (a _)]
  refine max_le_max (le_refl _) (good1_bdd_above h h0)

theorem good2_bdd_below {a : ℕ → G} (h : good2 D a) (h0 : D ≤ n) :
    -a (n + 1) ≤ 2 • (range (n + 1)).sup' nonempty_range_add_one a := by
  rcases h n h0 with ⟨i, j, rfl, h0⟩
  rw [h0, neg_neg, two_nsmul]
  exact add_le_add (le_sup' a (mem_range_succ_iff.mpr (Nat.le_add_right i j)))
    (le_sup' a (mem_range_succ_iff.mpr (Nat.le_add_left j i)))

theorem good2_range_sup' {D : ℕ} {a : ℕ → G} (h : good2 D a) {n : ℕ} (h0 : D ≤ n) :
    (range (n + 2)).sup' nonempty_range_add_one (-a)
      ≤ max ((range (n + 1)).sup' nonempty_range_add_one (-a))
        (2 • (range (n + 1)).sup' nonempty_range_add_one a) := by
  simp_rw [range_add_one (n := n + 1), sup'_insert nonempty_range_add_one, max_comm ((-a) _)]
  exact max_le_max (le_refl _) (good2_bdd_below h h0)





/-! ### More general observations -/

section SeqMax

variable {b c : ℕ → G} (h : ∀ n, D ≤ n → b (n + 1) ≤ max (b n) (c n - b n))
  (h0 : ∀ n, D ≤ n → c (n + 1) ≤ max (c n) (2 • b n)) (h1 : Monotone b)
include h h0 h1

theorem c_bdd (h2 : D ≤ K) (h3 : c K ≤ 2 • b K) :
    b (K + 1) = b K ∧ c (K + 1) ≤ 2 • b (K + 1) := by
  suffices b K = b (K + 1) from ⟨this.symm, (h0 K h2).trans_eq (this ▸ max_eq_right h3)⟩
  rw [two_nsmul, ← sub_le_iff_le_add] at h3
  exact (h1 K.le_succ).antisymm ((h K h2).trans_eq (max_eq_left h3))

theorem c_succ_eq_D_of_b_bdd (h2 : Monotone c) (h3 : D ≤ K) :
    2 • b K < c K → c (K + 1) = c D := by
  have X {M : ℕ} : D ≤ M → 2 • b M < c M → c (M + 1) = c M := λ h3 h4 ↦
    ((h0 M h3).trans_eq (max_eq_left_of_lt h4)).antisymm (h2 M.le_succ)
  refine Nat.le_induction (X D.le_refl) (λ n h4 h5 h6 ↦ ?_) K h3
  rw [X (Nat.le_succ_of_le h4) h6]
  exact h5 (lt_of_not_ge λ h7 ↦ h6.not_ge (c_bdd h h0 h1 h4 h7).2)

theorem max_two_nsmul_b_and_c_bdd (h2 : Monotone c) (n : ℕ) :
    max (c n) (2 • b n) ≤ max (2 • b D) (2 • (c D - b D)) := by
  have h3 : max (c D) (2 • b D) ≤ max (2 • b D) (2 • (c D - b D)) := by
    refine max_le (le_max_of_two_nsmul_le_add ?_) (le_max_left _ _)
    rw [← nsmul_add, add_sub_cancel]
  refine (le_total n D).elim -- Focus on the case `D ≤ n`; induction
    (λ h4 ↦ h3.trans' (max_le_max (h2 h4) (nsmul_le_nsmul_right (h1 h4) 2)))
    (Nat.le_induction h3 (λ n h4 h5 ↦ ?_) n)
  rcases le_or_gt (c n) (2 • b n) with h6 | h6
  ---- Case 1: `c_n ≤ 2 b_n`
  · rcases c_bdd h h0 h1 h4 h6 with ⟨h7, h8⟩
    rwa [max_eq_right h8, h7, ← max_eq_right h6]
  ---- Case 2: `c_n > 2 b_n`
  · have h7 := c_succ_eq_D_of_b_bdd h h0 h1 h2 h4 h6
    refine max_le (h7 ▸ h3.trans' (le_max_left _ _))
      (le_max_of_le_right <| nsmul_le_nsmul_right ((h _ h4).trans ?_) 2)
    rw [two_nsmul, ← lt_sub_iff_add_lt] at h6
    rw [max_eq_right h6.le, ← h7]
    exact sub_le_sub (h2 n.le_succ) (h1 h4)

end SeqMax





/-! ### Summary -/

/-- For any function `f : ℕ → α`, the function `g(n) = max{f(0), …, f(n)}` is monotone. -/
theorem range_sup'_monotone [LinearOrder α] (f : ℕ → α) :
    Monotone (λ n ↦ (range (n + 1)).sup' nonempty_range_add_one f) :=
  λ _ _ hmn ↦ sup'_mono _ (range_subset_range.mpr (Nat.succ_le_succ hmn)) _

/-- Final solution -/
theorem final_solution {a : ℕ → G} (h : good1 D a) (h0 : good2 D a) (n : ℕ) :
    |a n| ≤ max (2 • (range (D + 1)).sup' nonempty_range_add_one a)
      (2 • ((range (D + 1)).sup' nonempty_range_add_one (-a)
        - (range (D + 1)).sup' nonempty_range_add_one a)) := by
  refine (abs_le_max_range_sup' a n).trans ?_
  exact max_two_nsmul_b_and_c_bdd (G := G)
    (b := λ n ↦ ((range (n + 1)).sup' nonempty_range_add_one a))
    (c := λ n ↦ ((range (n + 1)).sup' nonempty_range_add_one (-a)))
    (λ _ ↦ good1_range_sup' h) (λ _ ↦ good2_range_sup' h0)
    (range_sup'_monotone _) (range_sup'_monotone _) n
