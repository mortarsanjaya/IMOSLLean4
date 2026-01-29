/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Interval
import Mathlib.Data.ZMod.Basic

/-!
# IMO 2008 C3

For any $k ∈ ℕ$ and integer points $p, q ∈ ℤ^2$, we say that $p$ and $q$ are
  $k$-*friends* if there exists a point $r ∈ ℤ^2$ such that the area of the
  triangle with endpoints $p, q, r$ is equal to $k$.
A set $S ⊆ ℤ^2$ is a $k$-*clique* if every two distinct points in $S$ are $k$-friends.
For any positive integer $N ≥ 4$, find the smallest positive integer $k$
  such that there exists a $k$-clique with more than $N$ elements.

### Answer

$\text{lcm}(1, 2, …, ⌊√N⌋)/2$.

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
  mkRat ((Δ 0).1 * (Δ 1).2 + (Δ 1).1 * (Δ 2).2 + (Δ 2).1 * (Δ 0).2
    - ((Δ 0).2 * (Δ 1).1 + (Δ 1).2 * (Δ 2).1 + (Δ 2).2 * (Δ 0).1)).natAbs 2

/-- Two points `p, q : ℤ × ℤ` are `k`-*friends* if there is a point `r`
  such that the triangle with vertices `p, q, r` has area `k`. -/
def friends (k : ℕ) (p q : ℤ × ℤ) := ∃ r, triangleArea ![p, q, r] = k

/-- A set `S` is a `k`-*clique* if every two distinct points in `S` are `k`-friends. -/
def clique (k : ℕ) (S : Set (ℤ × ℤ)) := ∀ p ∈ S, ∀ q ∈ S, p ≠ q → friends k p q


/-- An alternative (assymetric) formula for the area of a triangle. -/
lemma triangleArea_alt (p q r) :
    triangleArea ![p, q, r] =
      mkRat ((p.1 - q.1) * (q.2 - r.2) + (p.2 - q.2) * (r.1 - q.1)).natAbs 2 := by
  refine congrArg (λ n ↦ mkRat (Int.natAbs n) 2) ?_
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

/-- The main criterion for two points to be `k`-friends. -/
theorem friends_iff {k : ℕ} {p q : ℤ × ℤ} :
    friends k p q ↔ Int.gcd (p.1 - q.1) (p.2 - q.2) ∣ 2 * k := calc
  _ ↔ ∃ r s, triangleArea ![p, q, (r, s)] = k := Prod.exists'
  _ ↔ ∃ r s, ((p.1 - q.1) * (q.2 - s) + (p.2 - q.2) * (r - q.1)).natAbs = 2 * k := by
    refine exists₂_congr λ r s ↦ ?_
    rw [triangleArea_alt, ← Rat.intCast_natCast, ← Rat.mkRat_one,
      Rat.mkRat_eq_iff (Nat.succ_ne_zero 1) Nat.one_ne_zero, Int.natCast_one,
      Int.mul_one, ← Int.natCast_mul, Int.natCast_inj, Nat.mul_comm k 2]
  _ ↔ ∃ r s, ((p.1 - q.1) * s + (p.2 - q.2) * r).natAbs = 2 * k := by
    refine ⟨λ ⟨r, s, h⟩ ↦ ⟨r - q.1, q.2 - s, h⟩, λ ⟨r, s, h⟩ ↦ ⟨r + q.1, q.2 - s, ?_⟩⟩
    rw [sub_sub_cancel, Int.add_sub_cancel, h]
  _ ↔ ∃ s r, (2 * k : ℕ) = (p.1 - q.1) * s + (p.2 - q.2) * r := by
    refine ⟨λ ⟨r, s, h⟩ ↦ ?_, λ ⟨r, s, h⟩ ↦ ⟨s, r, congrArg Int.natAbs h.symm⟩⟩
    obtain h0 | h0 :
        (p.1 - q.1) * s + (p.2 - q.2) * r = (2 * k : ℕ)
          ∨ (p.1 - q.1) * s + (p.2 - q.2) * r = -(2 * k : ℕ) := Int.natAbs_eq_iff.mp h
    · exact ⟨s, r, h0.symm⟩
    · refine ⟨-s, -r, ?_⟩
      rw [Int.mul_neg, Int.mul_neg, ← Int.neg_add, h0, Int.neg_neg]
  _ ↔ Int.gcd (p.1 - q.1) (p.2 - q.2) ∣ 2 * k := Int.gcd_dvd_iff.symm

/-- The point `(p_1, p_2)` is a `k`-friend of `(q_1, q_2)`
  if and only if `(p_2, p_1)` is a `k`-friend of `(q_2, q_1)`. -/
theorem friends_coord_comm : friends k (p₁, p₂) (q₁, q₂) ↔ friends k (p₂, p₁) (q₂, q₁) := by
  rw [friends_iff, friends_iff, Int.gcd_comm]

/-- If a subset `S ⊆ ℤ × ℤ` has cardinality greater than `m^2`, `m > 0`, then there exist
  two distinct points `p, q ∈ S` such that `m ∣ gcd(p_1 - q_1, p_2 - q_2)`. -/
theorem exist_dvd_gcd_of_sq_lt_card (hm : m > 0) {S : Finset (ℤ × ℤ)} (hS : m ^ 2 < #S) :
    ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧ m ∣ Int.gcd (p.1 - q.1) (p.2 - q.2) := by
  haveI : NeZero m := NeZero.of_pos hm
  ---- First find `p ≠ q ∈ S` such that `p ≡ q (mod m)`.
  obtain ⟨p, hp, q, hq, hpq, h⟩ : ∃ p ∈ S, ∃ q ∈ S, p ≠ q ∧
      ((p.1, p.2) : ZMod m × ZMod m) = ((q.1, q.2) : ZMod m × ZMod m) := by
    refine exists_ne_map_eq_of_card_image_lt ?_
    calc #(S.image λ x : ℤ × ℤ ↦ ((x.1, x.2) : ZMod m × ZMod m))
      _ ≤ Fintype.card (ZMod m × ZMod m) := card_le_univ _
      _ = m ^ 2 := by rw [Fintype.card_prod, ZMod.card, Nat.pow_two]
      _ < #S := hS
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
    clique k (Icc 0 (N : ℤ) ×ˢ Icc 0 (N : ℤ) : Finset _) := by
  ---- Fix some `p_1, q_1, p_2, q_2 ∈ {0, 1, …, N}^2` with `(p_1, p_2) ≠ (q_1, q_2)`.
  rintro ⟨p₁, p₂⟩ hp ⟨q₁, q₂⟩ hq hpq
  rw [mem_coe, mem_product] at hp hq
  replace hpq : p₁ ≠ q₁ ∨ p₂ ≠ q₂ := by rwa [Ne, Prod.ext_iff, not_and_or] at hpq
  ---- WLOG let `p_1 ≠ q_1`.
  wlog hpq₁ : p₁ ≠ q₁ generalizing p₁ p₂ q₁ q₂
  · exact friends_coord_comm.mp <|
      this p₂ p₁ hp.symm q₂ q₁ hq.symm hpq.symm (hpq.resolve_left hpq₁)
  ---- Then `0 < |p_1 - q_1| ≤ N` implies `gcd(p_1 - q_1, p_2 - q_2) ≤ N` and we are done.
  replace hpq₁ : p₁ - q₁ ≠ 0 := λ h ↦ hpq₁ (Int.eq_of_sub_eq_zero h)
  replace hp : 0 ≤ p₁ ∧ p₁ ≤ N := mem_Icc.mp hp.1
  replace hq : 0 ≤ q₁ ∧ q₁ ≤ N := mem_Icc.mp hq.1
  replace hpq : (p₁ - q₁).natAbs ≤ N := by
    rw [← Int.ofNat_le, Int.natCast_natAbs]
    exact abs_sub_le_of_nonneg_of_le hp.1 hp.2 hq.1 hq.2
  exact friends_iff.mpr <| hN _ (Int.gcd_pos_of_ne_zero_left _ hpq₁)
    ((Int.gcd_le_natAbs_left _ hpq₁).trans hpq)

/-- There exists a clique of size greater than `N`
  if and only if `m ∣ 2k` for every positive integer `m ≤ ⌊√N⌋`. -/
theorem exists_clique_card_lt_iff :
    (∃ S : Finset (ℤ × ℤ), clique k S ∧ #S > N) ↔ ∀ m > 0, m ≤ N.sqrt → m ∣ 2 * k := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  ---- The `→` direction uses `clique_card_le_sq_of_not_dvd_two_mul`.
  · rcases h with ⟨S, hS, hSN⟩
    intro m hm hm0; contrapose! hSN
    exact (clique_card_le_sq_of_not_dvd_two_mul hm hSN hS).trans (Nat.le_sqrt'.mp hm0)
  ---- The `←` direction uses `range_sq_is_clique`.
  · refine ⟨Icc 0 (N.sqrt : ℤ) ×ˢ Icc 0 (N.sqrt : ℤ), range_sq_is_clique h, ?_⟩
    rw [card_product, Int.card_Icc, Int.sub_zero, Int.toNat_natCast_add_one]
    exact Nat.lt_succ_sqrt N

/-- There exists a clique of size greater than `N`
  if and only if `lcm(1, 2, …, ⌊√N⌋)` divides `2k`. -/
theorem exists_clique_card_lt_iff2 :
    (∃ S : Finset (ℤ × ℤ), clique k S ∧ #S > N) ↔ (range N.sqrt).lcm Nat.succ ∣ 2 * k :=
  calc ∃ S : Finset (ℤ × ℤ), clique k S ∧ #S > N
  _ ↔ ∀ m > 0, m ≤ N.sqrt → m ∣ 2 * k := exists_clique_card_lt_iff
  _ ↔ ∀ m < N.sqrt, Nat.succ m ∣ 2 * k := by
    refine ⟨λ h m hm ↦ h _ m.succ_pos hm, λ h m hm hm0 ↦ ?_⟩
    cases m with | zero => exact absurd rfl hm.ne | succ l => exact h l hm0
  _ ↔ (range N.sqrt).lcm Nat.succ ∣ 2 * k := by simp_rw [Finset.lcm_dvd_iff, mem_range]

/-- If `k ≥ 2`, then `2 ∣ lcm(1, 2, …, k)`. -/
theorem two_dvd_lcm_range_succ (hk : k ≥ 2) : 2 ∣ (range k).lcm Nat.succ :=
  dvd_lcm (mem_range.mpr hk)

/-- For any `k`, we have `lcm(1, 2, …, k) > 0`. -/
theorem lcm_range_succ_pos (k) : 0 < (range k).lcm Nat.succ := by
  rw [Nat.pos_iff_ne_zero, lcm_ne_zero_iff]
  rintro x -; exact Nat.succ_ne_zero x

/-- Final solution -/
theorem final_solution (hN : N ≥ 4) :
    IsLeast {k : ℕ | k > 0 ∧ ∃ S : Finset (ℤ × ℤ), clique k S ∧ #S > N}
      ((range N.sqrt).lcm Nat.succ / 2) := by
  obtain ⟨K, hK⟩ : 2 ∣ (range N.sqrt).lcm Nat.succ :=
    two_dvd_lcm_range_succ (Nat.le_sqrt'.mpr hN)
  have hK0 : 0 < 2 * K := (lcm_range_succ_pos _).trans_eq hK
  replace hK0 : 0 < K := Nat.pos_of_mul_pos_left hK0
  replace hN : 2 > 0 := Nat.two_pos
  simp_rw [exists_clique_card_lt_iff2, hK,
    Nat.mul_dvd_mul_iff_left hN, Nat.mul_div_cancel_left K hN]
  exact ⟨⟨hK0, Nat.dvd_refl K⟩, λ k ⟨hk, hk0⟩ ↦ Nat.le_of_dvd hk hk0⟩
