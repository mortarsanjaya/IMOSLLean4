/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Int.GCD
import Mathlib.Order.Bounds.Defs
import Mathlib.Algebra.Ring.Rat
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic

/-!
# IMO 2008 C3

For any $k ∈ ℕ$ and integer points $p, q ∈ ℤ^2$, we say that $p$ and $q$ are
  $k$-*friends* if there exists a point $r ∈ ℤ^2$ such that the area of the
  triangle with endpoints $p, q, r$ is equal to $k$.
A set $S ⊆ ℤ^2$ is a $k$-*clique* if every two distinct points in $S$ are $k$-friends.
For any positive integer $N$, find the smallest positive integer $k$
  such that there exists a $k$-clique with more than $N$ elements.

### Answer

$\text{lcm}(1, 2, …, ⌊√N⌋ + 1)/2$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2008SL.pdf).
We skip the characterization of the $k$-friends of $(0, 0)$.

### Implementation details

We implement the triangles as a function `Fin 3 → ℤ × ℤ`.
-/

namespace IMOSL
namespace IMO2008C3

open Finset

/-- The area of a triangle. -/
def triangleArea (Δ : Fin 3 → ℤ × ℤ) : Rat :=
  ((Δ 0).1 * (Δ 1).2 + (Δ 1).1 * (Δ 2).2 + (Δ 2).1 * (Δ 0).2
    - ((Δ 0).2 * (Δ 1).1 + (Δ 1).2 * (Δ 2).1 + (Δ 2).2 * (Δ 0).1)).natAbs / 2

/-- An alternative (assymetric) formula for the area of a triangle. -/
lemma triangleArea_alt (p q r : ℤ × ℤ) :
    triangleArea ![p, q, r] =
      ((p.1 - q.1) * (q.2 - r.2) + (p.2 - q.2) * (r.1 - q.1)).natAbs / 2 := by
  refine congrArg (λ n ↦ (Int.natAbs n : Rat) / 2) ?_
  calc p.1 * q.2 + q.1 * r.2 + r.1 * p.2 - (p.2 * q.1 + q.2 * r.1 + r.2 * p.1)
    _ = p.1 * q.2 + r.1 * p.2 - (p.2 * q.1 + q.2 * r.1) + (q.1 - p.1) * r.2 := by
      rw [Int.add_right_comm, add_sub_add_comm, Int.sub_mul, Int.mul_comm p.1 r.2]
    _ = p.1 * q.2 - p.2 * q.1 + (p.2 - q.2) * r.1 + (q.1 - p.1) * r.2 := by
      rw [add_sub_add_comm, Int.sub_mul p.2, Int.mul_comm r.1]
    _ = (p.1 - q.1) * q.2 - (p.2 - q.2) * q.1 + (p.2 - q.2) * r.1 + (q.1 - p.1) * r.2 := by
      rw [Int.sub_mul p.1, Int.sub_mul _ _ q.1, Int.mul_comm q.1, sub_sub_sub_cancel_right]
    _ = (p.1 - q.1) * q.2 + (p.2 - q.2) * (r.1 - q.1) + (q.1 - p.1) * r.2 := by
      rw [← add_sub_right_comm, Int.add_sub_assoc, ← Int.mul_sub]
    _ = (p.1 - q.1) * (q.2 - r.2) + (p.2 - q.2) * (r.1 - q.1) := by
      rw [Int.add_right_comm, ← Int.neg_sub p.1,
        Int.neg_mul, Int.add_neg_eq_sub, ← Int.mul_sub]

/-- Two points `p, q : ℤ × ℤ` are `k`-*friends* if there is a point `r`
  such that the triangle with vertices `p, q, r` has area `k`. -/
def friends (k : ℕ) (p q : ℤ × ℤ) := ∃ r, triangleArea ![p, q, r] = k

/-- The main criterion for two points to be `k`-friends. -/
theorem friends_iff {k : ℕ} {p q : ℤ × ℤ} :
    friends k p q ↔ Int.gcd (p.1 - q.1) (p.2 - q.2) ∣ 2 * k := calc
  _ ↔ ∃ r s, triangleArea ![p, q, (r, s)] = k := Prod.exists'
  _ ↔ ∃ r s, ((p.1 - q.1) * (q.2 - s) + (p.2 - q.2) * (r - q.1)).natAbs = 2 * k := by
    refine exists₂_congr λ r s ↦ ?_
    have h : (2 : Rat) ≠ 0 := by decide
    rw [triangleArea_alt, div_eq_iff h, mul_two, ← Nat.cast_add, Nat.cast_inj, Nat.two_mul]
  _ ↔ ∃ r s, ((p.1 - q.1) * s + (p.2 - q.2) * r).natAbs = 2 * k := by
    refine ⟨λ ⟨r, s, h⟩ ↦ ⟨r - q.1, q.2 - s, h⟩, λ ⟨r, s, h⟩ ↦ ⟨r + q.1, q.2 - s, ?_⟩⟩
    rw [sub_sub_cancel, Int.add_sub_cancel, h]
  _ ↔ ∃ s r, (2 * k : ℕ) = (p.1 - q.1) * s + (p.2 - q.2) * r := by
    refine ⟨λ ⟨r, s, h⟩ ↦ ?_, λ ⟨r, s, h⟩ ↦ ⟨s, r, congrArg Int.natAbs h.symm⟩⟩
    obtain h0 | h0 :
        (p.1 - q.1) * s + (p.2 - q.2) * r = (2 * k : ℕ)
          ∨ (p.1 - q.1) * s + (p.2 - q.2) * r = -(2 * k : ℕ) :=
      Int.natAbs_eq_iff.mp h
    · exact ⟨s, r, h0.symm⟩
    · refine ⟨-s, -r, ?_⟩
      rw [Int.mul_neg, Int.mul_neg, ← Int.neg_add, h0, Int.neg_neg]
  _ ↔ Int.gcd (p.1 - q.1) (p.2 - q.2) ∣ 2 * k :=
    Int.gcd_dvd_iff.symm

/-- A set `S` is a `k`-*clique* if every two distinct points in `S` are `k`-friends. -/
def clique (k : ℕ) (S : Set (ℤ × ℤ)) := ∀ p ∈ S, ∀ q ∈ S, p ≠ q → friends k p q

/-- If a subset `S ⊆ ℤ × ℤ` is good then there exist two distinct
  points `p, q ∈ S` such that `m ∣ gcd(p_1 - q_1, p_2 - q_2)`. -/
theorem exist_dvd_gcd_of_sq_lt_card (hm : m > 0) {S : Finset (ℤ × ℤ)} (hS : m ^ 2 < #S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ m ∣ Int.gcd (p.1 - q.1) (p.2 - q.2) := by
  haveI : NeZero m := NeZero.of_pos hm
  ---- First find `p ≠ q ∈ S` such that `p ≡ q (mod m)`.
  obtain ⟨p, hp, q, hq, hpq, h⟩ : ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧
      ((p.1, p.2) : ZMod m × ZMod m) = ((q.1, q.2) : ZMod m × ZMod m) := by
    have h : #(S.image λ x : ℤ × ℤ ↦ ((x.1, x.2) : ZMod m × ZMod m)) < #S := calc
      _ ≤ Fintype.card (ZMod m × ZMod m) := card_le_univ _
      _ = m ^ 2 := by rw [Fintype.card_prod, ZMod.card, Nat.pow_two]
      _ < #S := hS
    exact exists_ne_map_eq_of_card_image_lt h
  ---- Now we just check that this `p` and `q` works.
  refine ⟨p, hp, q, hq, hpq, ?_⟩
  rw [Int.dvd_gcd_iff, ← ZMod.intCast_eq_intCast_iff_dvd_sub, eq_comm,
    ← ZMod.intCast_eq_intCast_iff_dvd_sub, eq_comm (a := (q.2 : ZMod m))]
  exact Prod.mk_inj.mp h

/-- If `m > 0` and `m ∤ 2k`, then any `k`-clique has size at most `m^2`. -/
theorem clique_card_le_sq_of_not_dvd_two_mul
    (hm : m > 0) (h : ¬m ∣ 2 * k) {S : Finset (ℤ × ℤ)} (hS : clique k S) : #S ≤ m ^ 2 := by
  contrapose! h
  obtain ⟨p, hp, q, hq, hpq, h0⟩ :
      ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ m ∣ Int.gcd (p.1 - q.1) (p.2 - q.2) :=
    exist_dvd_gcd_of_sq_lt_card hm h
  exact h0.trans (friends_iff.mp (hS p hp q hq hpq))

/-- If `N : ℕ` satisfies `m ∣ 2k` for every `0 < m ≤ N`,
  then `{0, 1, …, N}^2` is a `k`-clique. -/
theorem range_sq_is_clique {N k : ℕ} (hN : ∀ m > 0, m ≤ N → m ∣ 2 * k) :
    clique k (Icc 0 (N : ℤ) ×ˢ Icc 0 (N : ℤ)) := by
  intro p hp q hq hpq
  sorry

/-- Final solution -/
theorem final_solution (hN : N > 0) :
    IsLeast {k : ℕ | ∃ S : Finset (ℤ × ℤ), clique k S ∧ #S > N}
      (Finset.fold Nat.lcm 1 Nat.succ (range (Nat.sqrt N + 1)) / 2) :=
  sorry
