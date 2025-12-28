/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# IMO 2011 A5

Prove that for every $n ≥ 0$, the set $\{2, 3, …, 3n + 1\}$ can be partitioned into $n$
  triples such that the numbers from each triple form the side lengths of an obtuse triangle.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2011SL.pdf).
Note that the official solution does more: it constructs a partition
  such that the shortest sides of the triples are $2, 3, …, n + 1$.
We do not bother with enforcing the set of side lengths to be
  exactly a partition of $\{2, 3, …, 3n + 1\}$.
We only force each of $2, …, 3n + 1$ to be a side length.
The partition property would follow by cardinality argument.
The final statement will force the set of all side lengths to be $\{2, 3, …, 3n + 1\}$.
-/

namespace IMOSL
namespace IMO2011A5

open Finset

/-! ### Obtuse triangles -/

/-- A data for the side lengths of an obtuse triangle. -/
structure ObtuseTriangle where
  a : ℕ
  b : ℕ
  c : ℕ
  a_le_b : a ≤ b
  c_lt_a_add_b : c < a + b
  spec : a ^ 2 + b ^ 2 < c ^ 2


namespace ObtuseTriangle

variable (T : ObtuseTriangle)

/-- We have `b < c`. -/
lemma b_lt_c : T.b < T.c :=
  (Nat.pow_lt_pow_iff_left (Nat.succ_ne_zero 1)).mp (Nat.lt_of_add_left_lt T.spec)

/-- We have `b ≤ c`. -/
lemma b_le_c : T.b ≤ T.c :=
  T.b_lt_c.le

/-- The (finite) set of side lengths of an obtuse triangle. -/
def sideLengths : Finset ℕ := {T.a, T.b, T.c}

/-- The members of `T.sideLengths` are the side lengths of `T`. -/
theorem mem_sideLengths_iff {T : ObtuseTriangle} {n : ℕ} :
    n ∈ T.sideLengths ↔ n = T.a ∨ n = T.b ∨ n = T.c := by
  rw [sideLengths, mem_insert, mem_insert, mem_singleton]

/-- The cardinality of the set of side lengths of an obtuse triangle is at most `3`. -/
theorem card_sideLengths_le_three : #T.sideLengths ≤ 3 :=
  card_le_three

/-- Extending two of the side lengths by the same amount. -/
def extend_two_sides (e : ℕ) : ObtuseTriangle where
  a := T.a
  b := T.b + e
  c := T.c + e
  a_le_b := Nat.le_add_right_of_le T.a_le_b
  c_lt_a_add_b := calc T.c + e
    _ < T.a + T.b + e := Nat.add_lt_add_right T.c_lt_a_add_b e
    _ = T.a + (T.b + e) := Nat.add_assoc T.a T.b e
  spec := calc T.a ^ 2 + (T.b + e) ^ 2
    _ = T.a ^ 2 + (T.b ^ 2 + 2 * T.b * e + e ^ 2) := by rw [add_sq]
    _ = T.a ^ 2 + T.b ^ 2 + (2 * T.b * e + e ^ 2) := by rw [Nat.add_assoc, Nat.add_assoc]
    _ < T.c ^ 2 + (2 * T.c * e + e ^ 2) :=
      Nat.add_lt_add_of_lt_of_le T.spec
        (Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ T.b_le_c)) _)
    _ = (T.c + e) ^ 2 := by rw [add_sq, Nat.add_assoc]

/-- The obtuse triangle of side length `i + 2, n + ⌊n/2⌋ + i + 2, 2n + i + 2`
  for `⌊n/2⌋ ≤ i < n`; note that this automatically implies `n > 0`. -/
def binary_maker (n i) (hi : n / 2 ≤ i) (hi0 : i < n) :
    ObtuseTriangle where
  a := i + 2
  b := n + n / 2 + (i + 2)
  c := n + n + (i + 2)
  a_le_b := Nat.le_add_left _ _
  c_lt_a_add_b :=
    have hi1 : n < n / 2 + (i + 2) := calc
      n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
      _ = n / 2 + (n / 2 + n % 2) := by rw [Nat.two_mul, Nat.add_assoc]
      _ < n / 2 + (i + 2) :=
        Nat.add_lt_add_left (Nat.add_lt_add_of_le_of_lt hi (Nat.mod_lt _ Nat.two_pos)) _
    calc n + n + (i + 2)
      _ < n + (n / 2 + (i + 2)) + (i + 2) :=
        Nat.add_lt_add_right (Nat.add_lt_add_left hi1 _) _
      _ = i + 2 + (n + n / 2 + (i + 2)) := by rw [Nat.add_comm, Nat.add_assoc n]
  spec :=
    let c := i + 2
    have hn : n > 0 := Nat.zero_lt_of_lt hi0
    have hi1 : c ≤ n + 1 := Nat.succ_lt_succ hi0
    calc c ^ 2 + (n + n / 2 + c) ^ 2
      _ = c * c + (n + n / 2 + c) ^ 2 := by rw [Nat.pow_two]
      _ ≤ c * (n + 1) + (n + n / 2 + c) ^ 2 :=
        Nat.add_le_add_right (Nat.mul_le_mul_left _ hi1) _
      _ = c * n + c + (n + n / 2 + c) ^ 2 := rfl
      _ ≤ c * n + (n + 1) + (n + n / 2 + c) ^ 2 :=
        Nat.add_le_add_right (Nat.add_le_add_left hi1 _) _
      _ = ((n + n / 2) ^ 2 + (n + 1)) + c ^ 2 + c * (3 * n) + c * (2 * (n / 2)) := by ring
      _ ≤ ((n + n / 2) ^ 2 + (n + 1)) + c ^ 2 + c * (3 * n) + c * n :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.mul_div_le n 2)) _
      _ = ((n + n / 2) ^ 2 + (n + 1)) + (c ^ 2 + c * (4 * n)) := by
        rw [Nat.add_assoc, Nat.add_assoc, ← Nat.mul_add, Nat.succ_mul 3 n]
      _ < ((n + n / 2) ^ 2 + (n + 1)) + (c ^ 2 + c * (4 * n)) + n :=
        Nat.lt_add_of_pos_right hn
      _ ≤ ((n + n / 2) ^ 2 + (n + 1)) + (c ^ 2 + c * (4 * n)) + n + 2 * (n / 2) :=
        Nat.le_add_right _ _
      _ = (n + (n / 2 + 1)) ^ 2 + (c ^ 2 + c * (4 * n)) := by ring
      _ ≤ (n + n) ^ 2 + (c ^ 2 + c * (4 * n)) :=
        have hn0 : n / 2 < n := Nat.div_lt_self hn Nat.one_lt_two
        Nat.add_le_add_right (Nat.pow_le_pow_left (Nat.add_le_add_left hn0 _) _) _
      _ = (n + n + c) ^ 2 := by ring

end ObtuseTriangle





/-! ### Good collection of obtuse triangles -/

/-- An `n`-*good* collection is a collection of `n` obtuse triangles `X_0, …, X_{n - 1}`
  such that (1). the triangle `X_i` has `i + 2` as one of their side lengths;
  (2). each of `2, 3, …, 3n + 1` is a side length of one of the triangles. -/
structure GoodCollection (n : ℕ) where
  T : Fin n → ObtuseTriangle
  T_side_a (i : Fin n) : (T i).a = i + 2
  spec : ∀ s, s < 2 * n → ∃ i : Fin n, s + (n + 2) ∈ (T i).sideLengths


namespace GoodCollection

/-- Copying an `n`-good collection. -/
def copy (X : GoodCollection m) (n) (h : m = n) : GoodCollection n :=
  h ▸ X

/-- The empty collection. -/
def zero : GoodCollection 0 where
  T i := Fin.elim0 i
  T_side_a i := Fin.elim0 i
  spec _ hs := absurd hs (Nat.not_lt_zero _)

open ObtuseTriangle in
/-- Extending a `⌊n/2⌋`-good collection `(U_i)` to an `n`-good collection `(T_i)`. -/
def binary_ext {n : ℕ} (X : GoodCollection (n / 2)) : GoodCollection n where
  T i := if hi : i < n / 2
            then (X.T ⟨i, hi⟩).extend_two_sides (n - n / 2)
            else binary_maker n i (Nat.ge_of_not_lt hi) i.2
  T_side_a i := by split_ifs with hi; exacts [X.T_side_a _, rfl]
  spec s hs := by
    ---- If `s < 2⌊n/2⌋`, then we can use the `⌊n/2⌋`-good collection `(U_i)`.
    obtain hs0 | hs0 : s < 2 * (n / 2) ∨ 2 * (n / 2) ≤ s := Nat.lt_or_ge _ _
    · have hn : n / 2 ≤ n := Nat.div_le_self n 2
      -- Pick the index `i` such that `U_i` has `s + ⌊n/2⌋ + 2` as a side length.
      obtain ⟨i, hi⟩ : ∃ i, s + (n / 2 + 2) ∈ (X.T i).sideLengths := X.spec s hs0
      refine ⟨⟨i, i.2.trans_le hn⟩, ?_⟩
      -- Then `s + n + 2` is a side of `T_i`.
      replace hi : s + (n / 2 + 2) = (X.T i).b ∨ s + (n / 2 + 2) = (X.T i).c := by
        refine (mem_sideLengths_iff.mp hi).resolve_left ?_
        rw [X.T_side_a, ← Nat.add_assoc, Nat.add_left_inj]
        exact Nat.ne_of_gt (Nat.lt_add_left s i.2)
      replace hi : s + (n + 2) = (X.T i).b + (n - n / 2)
          ∨ s + (n + 2) = (X.T i).c + (n - n / 2) := by
        have h : s + (n / 2 + 2) + (n - n / 2) = s + (n + 2) := by
          rw [Nat.add_assoc, Nat.add_right_comm, Nat.add_sub_cancel' hn]
        rwa [← h, Nat.add_left_inj, Nat.add_left_inj]
      rw [dif_pos i.2, mem_sideLengths_iff]
      right; exact hi
    ---- If `s ≥ 2⌊n/2⌋`, split into two cases: `s < n + ⌊n/2⌋` and `s ≥ n + ⌊n/2⌋`.
    obtain hs1 | hs1 : s < n + n / 2 ∨ n + n / 2 ≤ s := Nat.lt_or_ge _ _
    ---- Case 1: `2⌊n/2⌋ ≤ s < n + ⌊n/2⌋`.
    · replace hs : n / 2 ≤ s := (Nat.le_mul_of_pos_left _ Nat.two_pos).trans hs0
      replace hs0 : n / 2 ≤ s - n / 2 := Nat.le_sub_of_add_le (by rwa [← Nat.two_mul])
      replace hs1 : s - n / 2 < n := Nat.sub_lt_right_of_lt_add hs hs1
      -- Pick `i = s - ⌊n/2⌋`.
      refine ⟨⟨s - n / 2, hs1⟩, ?_⟩
      rw [dif_neg hs0.not_gt, mem_sideLengths_iff]
      -- Then choose side `b`.
      right; left; change s + (n + 2) = n + n / 2 + (s - n / 2 + 2)
      rw [Nat.add_assoc, ← Nat.add_assoc (n / 2),
        Nat.add_sub_cancel' hs, Nat.add_left_comm]
    ---- Case 2: `n + ⌊n/2⌋ ≤ s < 2n`.
    · replace hs0 : n ≤ s := Nat.le_of_add_right_le hs1
      replace hs1 : n / 2 ≤ s - n := Nat.le_sub_of_add_le' hs1
      replace hs : s - n < n := Nat.sub_lt_right_of_lt_add hs0 (by rwa [← Nat.two_mul])
      -- Pick `i = s - n`.
      refine ⟨⟨s - n, hs⟩, ?_⟩
      rw [dif_neg hs1.not_gt, mem_sideLengths_iff]
      -- Then choose side `c`.
      right; right; change s + (n + 2) = n + n + (s - n + 2)
      rw [Nat.add_assoc, ← Nat.add_assoc n (s - n),
        Nat.add_sub_cancel' hs0, Nat.add_left_comm]

/-- "Standard" construction of `n`-good collection for every `n`. -/
def std : (n : ℕ) → GoodCollection n :=
  Nat.strongRec λ n n_ih ↦ if h : n = 0 then zero.copy n h.symm else
    binary_ext (n_ih (n / 2) (Nat.div_lt_self (Nat.zero_lt_of_ne_zero h) Nat.one_lt_two))

/-- The set of side lengths occuring in an `n`-good collection is `{2, 3, …, 3n + 1}`. -/
theorem biUnion_sideLength_eq (X : GoodCollection n) :
    univ.biUnion (λ i ↦ (X.T i).sideLengths) = image (· + 2) (range (3 * n)) := by
  refine ((eq_iff_card_le_of_subset ?_).mp ?_).symm
  ---- First, show that this set contains `{2, 3, …, 3n + 1}`.
  · refine image_subset_iff.mpr λ s hs ↦ mem_biUnion.mpr ?_
    replace hs : s < 3 * n := mem_range.mp hs
    obtain hs0 | hs0 : s < n ∨ n ≤ s := Nat.lt_or_ge _ _
    -- Case 1: `s < n`; then `s + 2` is an `a`-side-length.
    · lift s to Fin n using hs0
      refine ⟨s, mem_univ _, ObtuseTriangle.mem_sideLengths_iff.mpr ?_⟩
      left; exact (X.T_side_a s).symm
    -- Case 2: `n < s ≤ 3n`; then `s + 2` is a side length by good collection specification.
    · replace hs : s - n < 2 * n := by rwa [Nat.sub_lt_iff_lt_add hs0, ← Nat.succ_mul]
      obtain ⟨i, hi⟩ : ∃ i, s - n + (n + 2) ∈ (X.T i).sideLengths := X.spec _ hs
      rw [← Nat.add_assoc, Nat.sub_add_cancel hs0] at hi
      exact ⟨i, mem_univ _, hi⟩
  ---- Second, show that the set has size `≤ #{2, 3, …, 3n + 1}`.
  · calc #(univ.biUnion (λ i ↦ (X.T i).sideLengths))
      _ ≤ #(univ : Finset (Fin n)) * 3 :=
        card_biUnion_le_card_mul _ _ 3 λ i _ ↦ (X.T i).card_sideLengths_le_three
      _ = n * 3 := by rw [card_univ, Fintype.card_fin]
      _ = #(image (· + 2) (range (3 * n))) := by
        rw [card_image_of_injective _ (add_left_injective _), card_range, Nat.mul_comm]

end GoodCollection





/-! ### Summary -/

/-- Final solution -/
theorem final_solution (n : ℕ) :
    ∃ T : Fin n → ObtuseTriangle,
      univ.biUnion (λ i ↦ (T i).sideLengths) = image (· + 2) (range (3 * n)) :=
  ⟨(GoodCollection.std n).T, GoodCollection.biUnion_sideLength_eq _⟩
