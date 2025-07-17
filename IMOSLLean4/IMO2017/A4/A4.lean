/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.NatSequence.SeqMax
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

variable [AddCommGroup G] [LinearOrder G]

/-! ### Two definitions -/

abbrev good1 (D : ℕ) (a : ℕ → G) :=
  ∀ i j : ℕ, D ≤ i + j → a (i + j + 1) ≤ -(a i + a j)

abbrev good2 {G} [AddCommGroup G] (D : ℕ) (a : ℕ → G) :=
  ∀ n ≥ D, ∃ i j : ℕ, i + j = n ∧ a (n + 1) = -(a i + a j)





/-! ### Main properties of `good1` and `good2` -/

variable [IsOrderedAddMonoid G]

theorem abs_le_max_seqMax (a : ℕ → G) (n : ℕ) :
    |a n| ≤ max (Extra.seqMax (-a) n) (2 • Extra.seqMax a n) := by
  rw [le_max_iff]; refine (le_total (a n) 0).imp (λ h ↦ ?_) (λ h ↦ ?_)
  · exact (abs_of_nonpos h).trans_le (Extra.le_seqMax_self (-a) n)
  · rw [abs_of_nonneg h, two_nsmul]
    have h0 := Extra.le_seqMax_self a n
    exact le_add_of_le_of_nonneg h0 (h.trans h0)

theorem good1_bdd_above {a : ℕ → G} (h : good1 D a) (h0 : D ≤ n) :
    a (n + 1) ≤ Extra.seqMax (-a) n - Extra.seqMax a n := by
  rcases Extra.exists_map_eq_seqMax a n with ⟨i, h2, h1⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = i + j := Nat.exists_eq_add_of_le h2
  apply (h i j h0).trans
  rw [← h1, neg_add_rev, ← sub_eq_add_neg]
  exact sub_le_sub_right (Extra.le_seqMax_of_le (-a) (j.le_add_left i)) (a i)

theorem good1_seqMax {a : ℕ → G} (h : good1 D a) (h0 : D ≤ n) :
    Extra.seqMax a (n + 1) ≤
      max (Extra.seqMax a n) (Extra.seqMax (-a) n - Extra.seqMax a n) :=
  max_le_max (le_refl _) (good1_bdd_above h h0)

theorem good2_bdd_below {a : ℕ → G} (h : good2 D a) (h0 : D ≤ n) :
    -a (n + 1) ≤ 2 • Extra.seqMax a n := by
  rcases h n h0 with ⟨i, j, rfl, h0⟩
  rw [h0, neg_neg, two_nsmul]
  exact add_le_add (Extra.le_seqMax_of_le a (i.le_add_right j))
    (Extra.le_seqMax_of_le a (j.le_add_left i))

theorem good2_seqMax {D : ℕ} {a : ℕ → G} (h : good2 D a) {n : ℕ} (h0 : D ≤ n) :
    Extra.seqMax (-a) (n + 1) ≤ max (Extra.seqMax (-a) n) (2 • Extra.seqMax a n) :=
  max_le_max (le_refl _) (good2_bdd_below h h0)





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
  rw [X (Nat.le_step h4) h6]
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





/-! ### Final solution -/

/-- Final solution -/
theorem final_solution {a : ℕ → G} (h : good1 D a) (h0 : good2 D a) (n : ℕ) :
    |a n| ≤ max (2 • Extra.seqMax a D) (2 • (Extra.seqMax (-a) D - Extra.seqMax a D)) :=
  (abs_le_max_seqMax a n).trans <|
    max_two_nsmul_b_and_c_bdd (λ _ ↦ good1_seqMax h) (λ _ ↦ good2_seqMax h0)
      (λ _ _ ↦ Extra.seqMax_mono a) (λ _ _ ↦ Extra.seqMax_mono (-a)) n
