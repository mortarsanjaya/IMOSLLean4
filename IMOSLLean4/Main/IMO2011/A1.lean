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
Let $p_A$ be the number of pairs $(i, j)$ with $1 ≤ i < j ≤ 4$ such that
$$ a_i + a_j ∣ a_1 + a_2 + a_3 + a_4. $$
Determine all sets $A$ of size $4$ such that $p_A ≥ p_B$ for all sets $B$ of size $4$.

### Answer

$\{d, 5d, 7d, 11d\}$ and $\{d, 11d, 19d, 29d\}$ for some positive integer $d$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2011SL.pdf).
After getting $a_1 + a_4 = a_2 + a_3$, we write $a_1 + a_2 + a_3 + a_4$ as $2(a_2 + a_3)$.
We implement the set of pairs $(i, j)$ with the given property as
  `IMOSL.IMO2011A1.Card4NatSet.pSet`, so $p_A$ is the cardinality of this set.
-/

namespace IMOSL
namespace IMO2011A1

open Finset

/-- The data structure implementing a set of positive integers of cardinality `4`. -/
@[ext] structure Card4NatSet where
  toFun : Fin 4 → ℕ
  pos' : ∀ i, 0 < toFun i
  strictMono' : StrictMono toFun


namespace Card4NatSet

instance : FunLike Card4NatSet (Fin 4) ℕ where
  coe := toFun
  coe_injective' _ _ := Card4NatSet.ext

/-- Each `a_i` is positive. -/
theorem pos (A : Card4NatSet) (i) : A i > 0 :=
  A.pos' i

/-- We have `a_0 < a_1 < a_2 < a_3`. -/
theorem strictMono (A : Card4NatSet) : StrictMono A :=
  A.strictMono'

/-- The set of indices `(i, j)` such that `i < j` and `a_i + a_j ∣ a_0 + a_1 + a_2 + a_3`. -/
def pSet (A : Card4NatSet) : Finset (Fin 4 × Fin 4) :=
  {(i, j) : Fin 4 × Fin 4 | i < j ∧ A i + A j ∣ A 0 + A 1 + A 2 + A 3}

/-- Membership definition of `pSet`. -/
lemma mem_pSet_iff {A : Card4NatSet} :
    (i, j) ∈ A.pSet ↔ i < j ∧ A i + A j ∣ A 0 + A 1 + A 2 + A 3 :=
  mem_filter_univ _

/-- If `(i, j)` belongs to `pSet`, then `a_i + a_j ∣ a_0 + a_1 + a_2 + a_3`. -/
lemma mem_pSet_imp {A : Card4NatSet} (h : (i, j) ∈ A.pSet) :
    A i + A j ∣ A 0 + A 1 + A 2 + A 3 :=
  (mem_pSet_iff.mp h).2

/-- Scaling the elements a set of size `4` by a uniform multiplier. -/
def nsmul (A : Card4NatSet) (hn : 0 < n) : Card4NatSet where
  toFun := n • A
  pos' i := Nat.mul_pos hn (A.pos i)
  strictMono' _ _ h := Nat.mul_lt_mul_of_pos_left (A.strictMono h) hn

/-- The definition of scalar multiplication on `Card4NatSet`. -/
lemma nsmul_apply (A : Card4NatSet) (hn : 0 < n) (i) : A.nsmul hn i = n * A i := rfl

/-- The set `pSet` is stable under scalar multiplication. -/
lemma pSet_nsmul (A : Card4NatSet) (hn : 0 < n) : (A.nsmul hn).pSet = A.pSet := by
  refine Finset.ext λ (i, j) ↦ ?_
  simp only [mem_pSet_iff, nsmul_apply, ← Nat.mul_add]
  exact Iff.and Iff.rfl (Nat.mul_dvd_mul_iff_left hn)





/-! ### Start of the problem -/

/-- The indices in the `pSet` can only be one of `(0, 1), (0, 2), (0, 3), (1, 2)`. -/
lemma pSet_subset (A : Card4NatSet) : A.pSet ⊆ {(0, 1), (0, 2), (0, 3), (1, 2)} := by
  ---- For convenience, write `S = {(0, 1), (0, 2), (0, 3), (1, 2)}`, and let `p ∈ A.pSet`.
  set S : Finset (Fin 4 × Fin 4) := {(0, 1), (0, 2), (0, 3), (1, 2)}
  rintro p h
  ---- Then `p ∈ {(1, 3), (2, 3)} ∪ S` and `a_i + a_j ∣ a_0 + a_1 + a_2 + a_3`.
  replace h : (p = (1, 3) ∨ p = (2, 3) ∨ p ∈ S) ∧ A p.1 + A p.2 ∣ A 0 + A 1 + A 2 + A 3 := by
    have h0 : ({p | p.1 < p.2} : Finset _) = insert (1, 3) (insert (2, 3) S) := by decide
    rwa [← mem_insert, ← mem_insert, ← h0, mem_filter_univ, ← mem_pSet_iff]
  rcases h with ⟨rfl | rfl | h, h0⟩
  ---- The case `p = (1, 3)` yields `a_1 + a_3 ∣ a_0 + a_2`; contradiction.
  · replace h0 : A 1 + A 3 ∣ A 0 + A 2 := by
      rwa [Nat.add_assoc, Nat.add_add_add_comm, Nat.dvd_add_self_right] at h0
    have h1 : A 0 < A 1 := A.strictMono (by decide)
    have h2 : A 2 < A 3 := A.strictMono (by decide)
    exact absurd (Nat.le_of_dvd (Nat.add_pos_left (A.pos 0) _) h0)
      (Nat.not_le_of_gt (Nat.add_lt_add h1 h2))
  ---- The case `p = (2, 3)` yields `a_2 + a_3 ∣ a_0 + a_1`; contradiction.
  · replace h0 : A 2 + A 3 ∣ A 0 + A 1 := by
      rwa [Nat.add_assoc, Nat.dvd_add_self_right] at h0
    have h1 : A 0 < A 2 := A.strictMono (by decide)
    have h2 : A 1 < A 3 := A.strictMono (by decide)
    exact absurd (Nat.le_of_dvd (Nat.add_pos_left (A.pos 0) _) h0)
      (Nat.not_le_of_gt (Nat.add_lt_add h1 h2))
  ---- The case `p ∈ S` is the goal.
  · exact h

/-- The size of the `pSet` is at most four. -/
lemma card_pSet_le_four (A : Card4NatSet) : #A.pSet ≤ 4 :=
  card_le_card A.pSet_subset

/-- If `(0, 3)` and `(1, 2)` belongs to `pSet`, then `a_0 + a_3 = a_1 + a_2`. -/
lemma a0_add_a3_eq_a1_add_a2 {A : Card4NatSet} (hA : {(0, 3), (1, 2)} ⊆ A.pSet) :
    A 0 + A 3 = A 1 + A 2 := by
  have hA0 : A 0 + A 3 ∣ A 0 + A 1 + A 2 + A 3 := mem_pSet_imp (hA (mem_insert_self _ _))
  replace hA0 : A 0 + A 3 ∣ A 1 + A 2 := by
    rwa [Nat.add_assoc (A 0), Nat.add_right_comm, Nat.dvd_add_self_left] at hA0
  replace hA : A 1 + A 2 ∣ A 0 + A 1 + A 2 + A 3 :=
    mem_pSet_imp (hA (mem_insert_of_mem (mem_singleton_self _)))
  replace hA : A 1 + A 2 ∣ A 0 + A 3 := by
    rwa [Nat.add_assoc (A 0), Nat.add_right_comm, Nat.dvd_add_self_right] at hA
  exact Nat.dvd_antisymm hA0 hA

/-- If `a_0 + a_3 = a_1 + a_2` and `(0, 2) ∈ A.pSet`, then `3(a_0 + a_2) = 2(a_1 + a_2)`. -/
lemma three_mul_a0_add_a2_eq_two_mul_a1
    {A : Card4NatSet} (hA : A 0 + A 3 = A 1 + A 2) (hA0 : (0, 2) ∈ A.pSet) :
    3 * (A 0 + A 2) = 2 * (A 1 + A 2) := by
  ---- We have `a_0 + a_2 ∣ a_0 + a_1 + a_2 + a_3 = 2(a_1 + a_2)`, say `= n(a_0 + a_2)`.
  obtain ⟨n, hA1⟩ : A 0 + A 2 ∣ A 0 + A 1 + A 2 + A 3 := mem_pSet_imp hA0
  replace hA1 : n * (A 0 + A 2) = 2 * (A 1 + A 2) := by
    rw [Nat.mul_comm, ← hA1, Nat.add_assoc (A 0), Nat.add_right_comm, hA, Nat.two_mul]
  ---- Clearly it suffices to prove that `n = 3`.
  suffices n = 3 by rw [← hA1, this]
  ---- We show this by showing that `n > 2` and `n < 4`.
  refine Nat.eq_of_le_of_lt_succ (Nat.succ_le_of_lt ?_) ?_
  ---- Indeed, `n > 2` holds since `2(a_0 + a_2) < 2(a_1 + a_2) = n(a_0 + a_2)`.
  · refine Nat.lt_of_mul_lt_mul_right (a := A 0 + A 2) ?_
    calc 2 * (A 0 + A 2)
      _ < 2 * (A 1 + A 2) :=
        Nat.mul_lt_mul_of_pos_left (hk := Nat.two_pos)
          (Nat.add_lt_add_right (A.strictMono (by decide)) _)
      _ = n * (A 0 + A 2) := hA1.symm
  ---- Meanwhile, `n < 4` holds since `n(a_0 + a_2) = 2(a_1 + a_2) < 4a_2 ≤ 4(a_0 + a_2)`.
  · refine Nat.lt_of_mul_lt_mul_right (a := A 0 + A 2) ?_
    calc n * (A 0 + A 2)
      _ = 2 * (A 1 + A 2) := hA1
      _ < 2 * (A 2 + A 2) :=
          Nat.mul_lt_mul_of_pos_left (hk := Nat.two_pos)
            (Nat.add_lt_add_right (A.strictMono (by decide)) _)
      _ = 4 * A 2 := by rw [← Nat.two_mul, ← Nat.mul_assoc]
      _ ≤ 4 * (A 0 + A 2) := Nat.mul_le_mul_left _ (Nat.le_add_left _ _)

/-- If the size is exactly `4`, then `A` is a scalar multiple of
  either `{1, 5, 7, 11}` or `{1, 11, 19, 29}`. -/
lemma four_le_card_pSet_imp {A : Card4NatSet} (hA : 4 ≤ #A.pSet) :
    ⇑A = A 0 • ![1, 5, 7, 11] ∨ ⇑A = A 0 • ![1, 11, 19, 29] := by
  ---- The `pSet` is contained in (equal to) `{(0, 1), (0, 2), (0, 3), (1, 2)}`.
  replace hA : {(0, 1), (0, 2), (0, 3), (1, 2)} ⊆ A.pSet :=
    (eq_of_subset_of_card_le A.pSet_subset hA).symm.subset
  ---- Considering `(0, 3)` and `(1, 2)` gives `a_0 + a_3 = a_1 + a_2`.
  have hA0 : A 0 + A 3 = A 1 + A 2 := A.a0_add_a3_eq_a1_add_a2 (subset_trans (by decide) hA)
  ---- Considering `(0, 2)` gives `3(a_0 + a_2) = 2(a_1 + a_2) ↔ 3a_0 + a_2 = 2a_1`.
  have hA1 : 3 * (A 0 + A 2) = 2 * (A 1 + A 2) :=
    A.three_mul_a0_add_a2_eq_two_mul_a1 hA0 (hA (by decide))
  have hA2 : 3 * A 0 + A 2 = 2 * A 1 := by
    rw [← Nat.add_left_inj (n := 2 * A 2), ← Nat.mul_add, ← hA1, Nat.mul_add,
      Nat.add_assoc, Nat.add_right_inj, Nat.add_comm, ← Nat.succ_mul]
  ---- Considering `(0, 1)` now gives `m(a_0 + a_1) = 3(a_0 + a_2)` for some `m : ℕ`.
  replace hA : A 0 + A 1 ∣ A 0 + A 1 + A 2 + A 3 := mem_pSet_imp (hA (by decide))
  rcases hA with ⟨m, hA⟩
  replace hA : m * (A 0 + A 1) = 3 * (A 0 + A 2) := by
    rw [Nat.mul_comm, ← hA, Nat.add_assoc (A 0), Nat.add_right_comm, hA0, hA1, Nat.two_mul]
  ---- This equality also implies `6a_0 + m(a_0 + a_1) = 6a_1`.
  replace hA1 : 6 * A 0 + m * (A 0 + A 1) = 6 * A 1 := by
    rw [hA, Nat.mul_assoc 3 2, ← Nat.mul_add,
      ← Nat.add_assoc, ← Nat.succ_mul, hA2, ← Nat.mul_assoc]
  ---- We now show that `m ∈ {4, 5}`.
  obtain rfl | rfl : m = 4 ∨ m = 5 := by
    -- First we show that `m > 3`.
    have hm : m > 3 := by
      refine Nat.lt_of_mul_lt_mul_right (a := A 0 + A 1) ?_
      calc 3 * (A 0 + A 1)
        _ < 3 * (A 0 + A 2) :=
          Nat.mul_lt_mul_of_pos_left (hk := Nat.succ_pos 2)
          (Nat.add_lt_add_left (A.strictMono (by decide)) _)
        _ = m * (A 0 + A 1) := hA.symm
    -- Next we show that `m < 6`.
    have hm0 : m < 6 := by
      refine Nat.lt_of_mul_lt_mul_right (a := A 0 + A 1) ?_
      calc m * (A 0 + A 1)
        _ < 6 * A 0 + m * (A 0 + A 1) :=
          Nat.lt_add_of_pos_left (Nat.mul_pos (Nat.succ_pos 5) (A.pos 0))
        _ = 6 * A 1 := hA1
        _ ≤ 6 * (A 0 + A 1) := Nat.mul_le_mul_left 6 (Nat.le_add_left _ _)
    -- Now we finish.
    rwa [Nat.lt_succ_iff, Nat.le_succ_iff, Nat.le_succ_iff, or_iff_right hm.not_ge] at hm0
  ---- If `n = 4`, then `A_1 = 5A_0`, `A_2 = 7A_0`, and `A_3 = 11A_0`.
  · replace hA1 : A 1 = 5 * A 0 := by
      rwa [Nat.mul_add, ← Nat.add_assoc, ← Nat.add_mul, Nat.add_mul 2 4, Nat.add_left_inj,
        Nat.mul_assoc 2 5, Nat.mul_right_inj (Nat.succ_ne_zero 1), eq_comm] at hA1
    replace hA2 : A 2 = 7 * A 0 := by
      rwa [hA1, ← Nat.mul_assoc, Nat.add_mul 3 7, Nat.add_right_inj] at hA2
    replace hA0 : A 3 = 11 * A 0 := by
      rwa [hA1, hA2, ← Nat.add_mul, Nat.succ_mul, Nat.add_comm, Nat.add_left_inj] at hA0
    left; funext i; match i with
    | 0 => exact (Nat.mul_one _).symm
    | 1 => exact hA1.trans (Nat.mul_comm _ _)
    | 2 => exact hA2.trans (Nat.mul_comm _ _)
    | 3 => exact hA0.trans (Nat.mul_comm _ _)
  ---- If `n = 5`, then `A_1 = 11A_0`, `A_2 = 19A_0`, and `A_3 = 29A_0`.
  · replace hA1 : A 1 = 11 * A 0 := by
      rwa [Nat.mul_add, ← Nat.add_assoc, ← Nat.add_mul, Nat.succ_mul 5,
        Nat.add_comm, Nat.add_right_inj, eq_comm] at hA1
    replace hA2 : A 2 = 19 * A 0 := by
      rwa [hA1, ← Nat.mul_assoc, Nat.add_mul 3 19, Nat.add_right_inj] at hA2
    replace hA0 : A 3 = 29 * A 0 := by
      rwa [hA1, hA2, ← Nat.add_mul, Nat.succ_mul, Nat.add_comm, Nat.add_left_inj] at hA0
    right; funext i; match i with
    | 0 => exact (Nat.mul_one _).symm
    | 1 => exact hA1.trans (Nat.mul_comm _ _)
    | 2 => exact hA2.trans (Nat.mul_comm _ _)
    | 3 => exact hA0.trans (Nat.mul_comm _ _)

/-- The set `A = {1, 5, 7, 11}`, which has `p_A = 4`. -/
def MaxSet1 : Card4NatSet where
  toFun := ![1, 5, 7, 11]
  pos' := by decide
  strictMono' := by decide

/-- The set `A = {1, 11, 19, 29}`, which has `p_A = 4`. -/
def MaxSet2 : Card4NatSet where
  toFun := ![1, 11, 19, 29]
  pos' := by decide
  strictMono' := by decide

/-- We have `p_A = 4` if and only if `A` is a
  scalar multiple of `{1, 5, 7, 11}` or `{1, 11, 19, 29}`. -/
lemma four_le_card_pSet_iff {A : Card4NatSet} :
    4 ≤ #A.pSet ↔ ∃ (n : ℕ) (hn : n > 0), A = MaxSet1.nsmul hn ∨ A = MaxSet2.nsmul hn := by
  refine ⟨?_, ?_⟩
  ---- The `→` direction.
  · intro hA
    exact ⟨A 0, A.pos 0, (four_le_card_pSet_imp hA).imp Card4NatSet.ext Card4NatSet.ext⟩
  ---- The `←` direction.
  · rintro ⟨_, hn, rfl | rfl⟩
    all_goals rw [pSet_nsmul]; rfl

end Card4NatSet


open Card4NatSet in
/-- Final solution -/
theorem final_solution {A : Card4NatSet} :
    (∀ B : Card4NatSet, #B.pSet ≤ #A.pSet) ↔
      ∃ n > 0, ⇑A = n • ![1, 5, 7, 11] ∨ ⇑A = n • ![1, 11, 19, 29] :=
  calc (∀ B : Card4NatSet, #B.pSet ≤ #A.pSet)
  _ ↔ 4 ≤ #A.pSet := ⟨λ h ↦ h MaxSet1, λ h B ↦ B.card_pSet_le_four.trans h⟩
  _ ↔ ∃ (n : ℕ) (hn : n > 0), A = MaxSet1.nsmul hn ∨ A = MaxSet2.nsmul hn :=
    four_le_card_pSet_iff
  _ ↔ ∃ (n : ℕ) (_ : n > 0), ⇑A = n • ![1, 5, 7, 11] ∨ ⇑A = n • ![1, 11, 19, 29] := by
    simp only [Card4NatSet.ext_iff]; rfl
  _ ↔ ∃ n > 0, ⇑A = n • ![1, 5, 7, 11] ∨ ⇑A = n • ![1, 11, 19, 29] := bex_def
