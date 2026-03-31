/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.PNat.Factors
import Mathlib.Data.Nat.ModEq

/-!
# IMO 2024 N3

Find all sequences $(a_n)_{n ≥ 0}$ of positive integers such that for any integers
  $m, k ≥ 0$, there exist positive integers $A$ and $G$ such that
\begin{align*}
  a_m + a_{m + 1} + … + a_{m + k - 1} &= kA, \\\\
  a_m a_{m + 1} … a_{m + k - 1} &= G^k.
\end{align*}

### Answer

Constant sequences.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2024SL.pdf).
Note that the existence of $A$ and $G$ are vacuous if $k = 0$.
We assume that an empty sum and product evaluates to $0$ and $1$, respectively.
-/

namespace IMOSL
namespace IMO2024N3

set_option backward.isDefEq.respectTransparency false

open Finset

/-! ### Extra lemmas -/

/-- TODO: Remove this once it gets into `mathlib`; it should have a chance. -/
theorem factorMultiset_inj {m n : ℕ+} : m.factorMultiset = n.factorMultiset ↔ m = n :=
  PNat.factorMultisetEquiv.apply_eq_iff_eq (x := m) (y := n)

/-- TODO: Remove this once it gets into `mathlib`; it should have a chance. -/
theorem factorMultiset_eq_iff_eq_prod {m : ℕ+} {S : PrimeMultiset} :
    m.factorMultiset = S ↔ m = S.prod :=
  PNat.factorMultisetEquiv.apply_eq_iff_eq_symm_apply (x := m) (y := S)

/-- TODO: Remove this once it gets into `mathlib`; it should have a chance. -/
theorem PrimeMultiset_prod_sum (S : ι → PrimeMultiset) (I : Finset ι) :
    (∑ i ∈ I, S i).prod = ∏ i ∈ I, (S i).prod := by
  change (PrimeMultiset.coePNatMonoidHom _).prod
    = ∏ i ∈ I, (PrimeMultiset.coePNatMonoidHom _).prod
  rw [map_sum, Multiset.prod_sum]

/-- Taking sums of `factorMultiset` is the same as taking `factorMultiset` of prods. -/
theorem sum_factorMultiset_eq_factorMultiset_prod (n : ι → ℕ+) (I : Finset ι) :
    ∑ i ∈ I, (n i).factorMultiset = (∏ i ∈ I, n i).factorMultiset := by
  rw [eq_comm, factorMultiset_eq_iff_eq_prod, PrimeMultiset_prod_sum]
  simp only [PNat.prod_factorMultiset]





/-! ### Start of the problem -/

/-- A sequence `(a_n)_{n ≥ 0}` of natural numbers is called *good* if
  for any `m, k ∈ ℕ`, we have `k ∣ a_m + a_{m + 1} + … + a_{m + k - 1}`. -/
def good (a : ℕ → ℕ) := ∀ m k, k ∣ ∑ i ∈ range k, a (m + i)

/-- A sequence is called *nice* if it satisfies the given condition. -/
structure nice (a : ℕ → ℕ+) : Prop where
  is_good : good λ n ↦ a n
  is_geo_good : ∀ m k, ∃ G, ∏ i ∈ range k, a (m + i) = G ^ k

/-- Constant sequences are good. -/
lemma good_of_const (C) : good (λ _ ↦ C) :=
  λ m k ↦ ⟨C, by rw [sum_const, card_range]; rfl⟩

/-- Constant sequences are nice. -/
lemma nice_of_const (C) : nice (λ _ ↦ C) where
  is_good := good_of_const C
  is_geo_good := λ m k ↦ ⟨C, by rw [prod_const, card_range]⟩

/-- If `(a_n)_{n ≥ 0}` is good, then `a_{m + k} ≡ a_m (mod k)` for any `k, m ≥ 0`. -/
lemma good.ModEq (ha : good a) (m k) : a (m + k) ≡ a m [MOD k] := calc
  _ ≡ a (m + k) + ∑ i ∈ range k, a (m + i) [MOD k] := (ha m k).zero_modEq_nat.add_left _
  _ ≡ a m + ∑ i ∈ range k, a (m + 1 + i) [MOD k] := by
    rw [Nat.add_comm, ← sum_range_succ, sum_range_succ', Nat.add_comm, Nat.add_zero]
    conv => left; right; right; ext; rw [← Nat.add_assoc, Nat.add_right_comm]
  _ ≡ _ [MOD k] := (ha (m + 1) k).modEq_zero_nat.add_left _

/-- If `(a_n)_{n ≥ 0}` is good and takes a value infinitely many times, it is constant. -/
lemma good.const_of_infinite_fiber (ha : good a) (hv : ∀ N, ∃ n ≥ N, a n = v) (k) :
    a k = v := by
  ---- Find a very big number `N > max{a_k, v}`.
  obtain ⟨N, hNk, hNv⟩ : ∃ N, a k < N ∧ v < N :=
    ⟨a k + v + 1, Nat.lt_succ_of_le (Nat.le_add_right _ _),
      Nat.lt_succ_of_le (Nat.le_add_left _ _)⟩
  ---- Now write `v = a_{n + k}` for some `n ≥ N`.
  obtain ⟨n, hn, rfl⟩ : ∃ n ≥ N, a (k + n) = v := by
    obtain ⟨n, hn, rfl⟩ : ∃ n ≥ k + N, a n = v := hv _
    obtain ⟨n', rfl⟩ : ∃ n', n = k + n' :=
      Nat.exists_eq_add_of_le (Nat.le_of_add_right_le hn)
    exact ⟨n', Nat.add_le_add_iff_left.mp hn, rfl⟩
  ---- Then `v = a_{n + k} ≡ a_k (mod n)`, but `a_k, a_{n + k} < N ≤ n`, so `v = a_k`.
  exact ((ha.ModEq k n).eq_of_lt_of_lt (hNv.trans_le hn) (hNk.trans_le hn)).symm

/-- If `(a_n)_{n ≥ 0}` is a good sequence of positive integers, then for any prime `p`
  and `k, m ≥ 0`, we have `ν_p(a_{m + kp^{ν_p(a_m) + 1}}) = ν_p(a_m)`. -/
lemma PNat_good_padic_eq_of_shift {a : ℕ → ℕ+} (ha : good λ n ↦ a n) (p k m) :
    (a (m + k * p ^ ((a m).factorMultiset.count p + 1))).factorMultiset.count p
      = (a m).factorMultiset.count p := by
  ---- Let `v = ν_p(a_m)`, and first write `a_{m + kp^{v + 1}} ≡ a_m (mod p^{v + 1})`.
  set v : ℕ := (a m).factorMultiset.count p
  have h : a (m + k * p ^ (v + 1)) ≡ a m [MOD p ^ (v + 1)] :=
    (ha.ModEq m (k * p ^ (v + 1))).of_mul_left _
  ---- Useful rewriting equality to have...
  have hp : ((p : ℕ+) : ℕ) = p.1 := rfl
  ---- Now break up `ν_p(a_{m + kp^{v + 1}}) = v` into two inequalities.
  apply Nat.le_antisymm
  ---- First show that `ν_p(a_{m + kp^{v + 1}}) ≤ v`.
  · -- Suppose that `v < ν_p(a_{m + kp^{v + 1}})`.
    refine Nat.le_of_not_lt λ h0 ↦ v.lt_irrefl ?_
    -- Then `p^{v + 1} ∣ a_{m + kp^{v + 1}}`, but `p^{v + 1} ∣ a_m`; contradiction.
    rw [← Nat.succ_le_iff, ← PNat.count_factorMultiset,
      PNat.dvd_iff, PNat.pow_coe, hp] at h0 ⊢
    exact (h.dvd_iff (Nat.dvd_refl _)).mp h0
  ---- Now show that `ν_p(a_{m + kp^{v + 1}}) ≤ v`.
  · -- Indeed this holds iff `p^v ∣ a_{m + kp^{v + 1}}` iff `p^v ∣ a_m`, which is true.
    have hv : v ≤ (a m).factorMultiset.count p := v.le_refl
    rw [← PNat.count_factorMultiset, PNat.dvd_iff, PNat.pow_coe, hp] at hv ⊢
    exact (h.dvd_iff ⟨p, rfl⟩).mpr hv

/-- If `(a_n)_{n ≥ 0}` is nice, then `(ν_p(a_n))_{n ≥ 0}` is good for any prime `p`. -/
lemma nice.padic_is_good (ha : nice a) (p : Nat.Primes) :
    good (λ n ↦ (a n).factorMultiset.count p) := by
  intro m k
  ---- Write `a_m … a_{m + k - 1} = G^k` for some `G ∈ ℕ⁺`.
  obtain ⟨G, hG⟩ : ∃ G, ∏ i ∈ range k, a (m + i) = G ^ k := ha.is_geo_good m k
  ---- Then `k ν_p(G) = ν_p(a_m) + … + ν_p(a_{m + k - 1})`.
  refine ⟨G.factorMultiset.count p, ?_⟩
  rw [← Multiset.count_nsmul, ← PNat.factorMultiset_pow, ← Multiset.count_sum']
  revert p; rw [← Multiset.ext, sum_factorMultiset_eq_factorMultiset_prod, hG]

/-- There are no nice sequences other than constant ones. -/
lemma nice.is_const (ha : nice a) : ∃ C, a = λ _ ↦ C := by
  /- By the results that we have proved above, the sequence
    `(ν_p(a_n))_{n ≥ 0}` is constant for each prime `p`. -/
  have h (p) : ∀ n, (a n).factorMultiset.count p = (a 0).factorMultiset.count p :=
    (ha.padic_is_good p).const_of_infinite_fiber
      λ N ↦ ⟨N * p ^ ((a 0).factorMultiset.count p + 1),
        Nat.le_mul_of_pos_right N (Nat.pow_pos p.2.pos),
        Nat.zero_add (N * _) ▸ PNat_good_padic_eq_of_shift ha.is_good p _ _⟩
  ---- Now conclude that the original sequence `(a_n)_{n ≥ 0}` is constant.
  refine ⟨a 0, funext λ n ↦ ?_⟩
  rw [← factorMultiset_inj, Multiset.ext]
  exact λ p ↦ h p n

/-- Final solution -/
theorem final_solution {a : ℕ → ℕ+} : nice a ↔ ∃ C, a = λ _ ↦ C :=
  ⟨nice.is_const, λ ⟨C, hC⟩ ↦ hC ▸ nice_of_const C⟩
