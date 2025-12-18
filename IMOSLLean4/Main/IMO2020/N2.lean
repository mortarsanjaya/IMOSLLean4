/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# IMO 2020 N2

For any finite commutative ring $R$, let $G_R$ be the (simple) graph with vertex set $R$,
  where two distinct vertices $x, y ∈ R$ are connected by an edge if and only if
  either $y = x^2 + 1$ or $x = y^2 + 1$.
Prove that the graph $G_{𝔽_p}$ is disconnected for infinitely many primes $p$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2020SL.pdf).
With the same proof, we show more: $G_{𝔽_p}$ is disconnected if $p ≡ 1 (mod 3)$.
-/

namespace IMOSL
namespace IMO2020N2

open Finset

/-- The graph `G_R`, defined for all commutative rings `R`. -/
def RGraph (R) [CommRing R] : SimpleGraph R where
  Adj x y := x ≠ y ∧ (x = y ^ 2 + 1 ∨ y = x ^ 2 + 1)
  symm _ _ h := ⟨h.1.symm, h.2.symm⟩
  loopless _ h := h.1 rfl

/-- An unordered pair is an edge of `G_R` if and only if it has the form `(x^2 + 1, x)`. -/
theorem mem_edgeSet_RGraph_iff [CommRing R] :
    e ∈ (RGraph R).edgeSet ↔ ∃ x, x ^ 2 + 1 ≠ x ∧ e = s(x^2 + 1, x) := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  ---- The `→` direction.
  · induction e with | h x y => ?_
    change x ≠ y ∧ (x = y ^ 2 + 1 ∨ y = x ^ 2 + 1) at h
    rcases h with ⟨h, rfl | rfl⟩
    exacts [⟨y, h, rfl⟩, ⟨x, h.symm, Sym2.eq_swap⟩]
  ---- The `←` direction.
  · rcases h with ⟨x, hx, rfl⟩
    exact ⟨hx, Or.inl rfl⟩


section

variable [CommRing R] [Fintype R] [DecidableEq R]

/-- The number of edges of `G_R` is less than or equal to
  the number of `x ∈ R` with `x^2 + 1 ≠ x`. -/
theorem card_RGraph_le : Nat.card (RGraph R).edgeSet ≤ #{x : R | x ^ 2 + 1 ≠ x} := by
  ---- Consider `f : {x : x^2 + 1 ≠ x} ↦ E(G_R)` defined by `f(x) = (x^2 + 1, x)`.
  let f (x : ({x : R | x ^ 2 + 1 ≠ x} : Finset R)) : (RGraph R).edgeSet :=
    ⟨s(x ^ 2 + 1, x), mem_edgeSet_RGraph_iff.mpr ⟨x, (mem_filter.mp x.2).2, rfl⟩⟩
  ---- Then `f` is surjective.
  have hf : f.Surjective := by
    rintro ⟨e, he⟩
    obtain ⟨x, hx, rfl⟩ : ∃ x, x ^ 2 + 1 ≠ x ∧ e = s(x^2 + 1, x) :=
      mem_edgeSet_RGraph_iff.mp he
    exact ⟨⟨x, (mem_filter_univ _).mpr hx⟩, rfl⟩
  ---- Now do the calculations.
  calc Nat.card (RGraph R).edgeSet
    _ ≤ Nat.card ({x : R | x ^ 2 + 1 ≠ x} : Finset R) :=
      Nat.card_le_card_of_surjective f hf
    _ = #{x : R | x ^ 2 + 1 ≠ x} := Nat.card_eq_finsetCard _

/-- If `x^2 + 1 = x` for some `x ∈ R` with `2x ≠ 1`, then `G_R` is disconnected. -/
theorem RGraph_disconnected_of_cyclotomic3_has_root
    {x : R} (hx : x ^ 2 + 1 = x) (hx0 : 2 * x ≠ 1) : ¬(RGraph R).Connected := by
  ---- It suffices to show that `G_R` has less than `|R| - 1` edges.
  refine mt SimpleGraph.Connected.card_vert_le_card_edgeSet_add_one (Nat.not_le_of_gt ?_)
  ---- First note that `(1 - x)^2 + 1 = 1 - x`, and `2x ≠ 1` means `x ≠ 1 - x`.
  have hx1 : (1 - x) ^ 2 + 1 = 1 - x := by
    rw [sub_sq, one_pow, mul_one, add_assoc, hx, two_mul, ← sub_sub, sub_add_cancel]
  replace hx0 : x ≠ 1 - x := by rwa [Ne, eq_sub_iff_add_eq, ← two_mul]
  ---- Now do the calculations.
  calc Nat.card (RGraph R).edgeSet + 1
    _ < #{x : R | x ^ 2 + 1 ≠ x} + 2 :=
      Nat.add_lt_add_of_le_of_lt card_RGraph_le Nat.one_lt_two
    _ = #{x : R | x ^ 2 + 1 ≠ x} + #{x, 1 - x} := by rw [card_pair hx0]
    _ = #(({x : R | x ^ 2 + 1 ≠ x} : Finset R) ∪ {x, 1 - x}) := by
      refine (card_union_of_disjoint (disjoint_right.mpr λ t ht ↦ ?_)).symm
      rw [mem_filter, and_iff_right (mem_univ _), Decidable.not_not]
      rw [mem_insert, mem_singleton] at ht
      rcases ht with rfl | rfl <;> assumption
    _ ≤ #(univ : Finset R) := card_le_card (subset_univ _)
    _ = Nat.card R := by rw [card_univ, Fintype.card_eq_nat_card]

/-- There exists infinitely many primes `p` such that `x^2 + 1 = x` for some `x ∈ 𝔽_p`. -/
theorem exists_infinite_prime_cyclotomic3_has_root (N) :
    ∃ p > N, Nat.Prime p ∧ ∃ x : ZMod p, x ^ 2 + 1 = x := by
  /- We take `p` to be the minimal prime factor of `M^2 + 1 - M`, where `M = 2N!`.
    Note that we choose `M` in this way so that `M^2 + 1 - M > 1`. -/
  let M := 2 * N.factorial
  have hM : M + 1 < M ^ 2 + 1 := by
    rw [Nat.pow_two, Nat.add_lt_add_iff_right, Nat.lt_mul_self_iff]
    exact Nat.le_mul_of_pos_right 2 (Nat.factorial_pos _)
  have hM0 : M ≤ M ^ 2 + 1 := Nat.le_of_lt hM.le
  have hM1 : (M ^ 2 + 1 - M).minFac ∣ M ^ 2 + 1 - M := Nat.minFac_dvd _
  refine ⟨(M ^ 2 + 1 - M).minFac, ?_, ?_, ?_⟩
  ---- First show that `M^2 + 1 - M` has no prime factor less than or equal to `N`.
  · refine Nat.lt_of_not_ge λ h ↦ ?_
    replace h : (M ^ 2 + 1 - M).minFac ∣ M :=
      calc (M ^ 2 + 1 - M).minFac
        _ ∣ N.factorial := Nat.dvd_factorial (Nat.minFac_pos _) h
        _ ∣ 2 * N.factorial := Nat.dvd_mul_left N.factorial 2
    rw [Nat.pow_two] at hM hM0 hM1 h
    rw [Nat.dvd_sub_iff_left hM0 h, Nat.dvd_add_right (Nat.dvd_mul_right_of_dvd h M),
      Nat.dvd_one, Nat.minFac_eq_one_iff, Nat.sub_eq_iff_eq_add' hM0] at hM1
    exact hM.ne.symm hM1
  ---- Next show that `p` is indeed prime.
  · exact Nat.minFac_prime_iff.mpr (Nat.lt_sub_iff_add_lt'.mpr hM).ne.symm
  ---- Finally, show that `x = M (mod p)` works.
  · refine ⟨M, ?_⟩
    rwa [← Nat.cast_pow, ← Nat.cast_add_one, ← sub_eq_zero,
      ← Nat.cast_sub hM0, ZMod.natCast_eq_zero_iff]

/-- Final solution -/
theorem final_solution (N) : ∃ p > N, Nat.Prime p ∧ ¬(RGraph (ZMod p)).Connected := by
  ---- Choose a prime `p > max{N, 3}` such that `x^2 + 1 = x` for some `x ∈ 𝔽_p`.
  obtain ⟨p, hpN, hp, ⟨x, hx⟩⟩ : ∃ p > max N 3, Nat.Prime p ∧ ∃ x : ZMod p, x ^ 2 + 1 = x :=
    exists_infinite_prime_cyclotomic3_has_root _
  haveI h : NeZero p := NeZero.of_gt hpN
  refine ⟨p, (le_max_left _ _).trans_lt hpN, hp,
    RGraph_disconnected_of_cyclotomic3_has_root hx ?_⟩
  ---- The only work we need to do is to check that `2x ≠ 1`, which is due to `p > 3`.
  replace hpN : ¬p ∣ 3 :=
    Nat.not_dvd_of_pos_of_lt (Nat.succ_pos 2) ((Nat.le_max_right _ _).trans_lt hpN)
  replace hx : (2 * x) ^ 2 + 1 + 3 = 2 * (2 * x) := by
    rw [add_assoc, add_comm 1, three_add_one_eq_four, ← two_add_two_eq_four,
      ← two_mul, mul_pow, sq, ← mul_add_one, hx, mul_assoc]
  intro h; rw [h, one_pow, two_mul, add_eq_left] at hx
  exact hpN ((ZMod.natCast_eq_zero_iff _ _).mp hx)
