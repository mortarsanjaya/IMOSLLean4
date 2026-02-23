/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.ModEq

/-!
# IMO 2006 N7

Prove that for any positive integers $b$ and $n$,
  there exists a non-negative integer $m$ such that $n ∣ b^m + m$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2006SL.pdf).
Note that the original problem only considers $b = 2$,
  but the method given in the official solution works for any $b$.
Furthermore, the usage of $d = \gcd(a, k)$ in the official solution is unnecessary;
  one could apply the induction hypothesis on $k$ instead of $d$.
Our implementation will also avoid using $d = \gcd(a, k)$.
-/

namespace IMOSL
namespace IMO2006N7

open Finset in
/-- Given `b n : ℕ` with `n > 1`, there exists `M k : ℕ`
  with `0 < k < n` such that `b^{M + k} ≡ b^M (mod n)`. -/
theorem exists_ne_pow_modeq {n : ℕ} (hn : 1 < n) (b : ℕ) :
    ∃ M : ℕ, ∃ k > 0, k < n ∧ b ^ (M + k) ≡ b ^ M [MOD n] := by
  ---- If `n ∣ b^M` for some `M`, then we are done.
  obtain ⟨M, h⟩ | h : (∃ M, n ∣ b ^ M) ∨ (∀ M, ¬n ∣ b ^ M) :=
    Classical.exists_or_forall_not _
  · refine ⟨M, 1, Nat.one_pos, hn, ?_⟩
    rw [Nat.ModEq, Nat.pow_succ, ← Nat.mod_mul_mod,
      Nat.mod_eq_zero_of_dvd h, Nat.zero_mul, Nat.zero_mod]
  /- If `n ∤ b^M` for any `M`, then apply pigeonhole principle
    and find `x, y < n` distinct with `b^x ≡ b^y (mod n)`. -/
  obtain ⟨x, hx, y, hy, hxy, h0⟩ :
      ∃ x ∈ range n, ∃ y ∈ range n, x ≠ y ∧ b ^ x ≡ b ^ y [MOD n] := by
    replace hn : 0 < n := Nat.zero_lt_of_lt hn
    have h0 : #({x ∈ range n | x ≠ 0}) < #(range n) :=
      card_lt_card (filter_ssubset.mpr ⟨0, mem_range.mpr hn, λ h ↦ h rfl⟩)
    have h1 : Set.MapsTo (b ^ · % n) (range n) ↑({x ∈ range n | x ≠ 0}) := by
      rintro M -
      rw [mem_coe, mem_filter, mem_range]
      exact ⟨Nat.mod_lt _ hn, λ h1 ↦ h M (Nat.dvd_of_mod_eq_zero h1)⟩
    exact exists_ne_map_eq_of_card_lt_of_maps_to (t := (range n).filter (· ≠ 0)) h0 h1
  ---- WLOG `x < y`; then `M = x` and `k = y - x` works.
  wlog h1 : x < y
  · exact this hn b h y hy x hx hxy.symm h0.symm (hxy.lt_or_gt.resolve_left h1)
  refine ⟨x, y - x, Nat.sub_pos_of_lt h1, (y.sub_le x).trans_lt (mem_range.mp hy), ?_⟩
  rwa [Nat.add_sub_cancel' h1.le, Nat.ModEq.comm]

/-- If `a ≡ b (mod d)`, then there exists `t` such that `a + dt ≡ b (mod n)`. -/
theorem exists_mod_eq_mul_add_of_dvd {n a b d : ℕ} (hn : 0 < n) (h : a ≡ b [MOD d]) :
    ∃ t, a + d * t ≡ b [MOD n] := by
  obtain h0 | h0 : a ≤ b ∨ b ≤ a := Nat.le_total a b
  ---- If `a ≤ b`, then `t = (b - a)/d` works with literal equality.
  · refine ⟨(b - a) / d, ?_⟩
    rw [Nat.mul_div_cancel' ((Nat.modEq_iff_dvd' h0).mp h), Nat.add_sub_cancel' h0]
  ---- If `a ≥ b`, then `t = (n - 1)(a - b)/d` works.
  · refine ⟨(n - 1) * ((a - b) / d), Nat.ModEq.add_right_cancel' (a - b) ?_⟩
    replace h : d ∣ a - b := (Nat.modEq_iff_dvd' h0).mp h.symm
    calc a + d * ((n - 1) * ((a - b) / d)) + (a - b)
      _ = a + n * (a - b) := by rw [Nat.mul_left_comm, Nat.mul_div_cancel' h,
          Nat.add_assoc, ← Nat.add_one_mul, Nat.sub_add_cancel hn]
      _ ≡ a [MOD n] := Nat.add_modulus_mul_modEq_iff.mpr rfl
      _ = b + (a - b) := (Nat.add_sub_cancel' h0).symm

/-- The general claim -/
theorem general_claim {n : ℕ} (hn : 0 < n) (b N r) : ∃ m ≥ N, b ^ m + m ≡ r [MOD n] := by
  ---- Step 1: Induction on `n`; the base case `n = 1` is trivial.
  induction n using Nat.strong_induction_on generalizing N r with | h n n_ih => ?_
  obtain rfl | hn0 : 1 = n ∨ 1 < n := Nat.eq_or_lt_of_le hn
  · exact ⟨N, Nat.le_refl N, Nat.modEq_one⟩
  ---- Step 2: There exists a positive integer `k < n` such that `b^{M + k} ≡ b^M (mod n)`.
  obtain ⟨M, k, hk, hk0, h⟩ : ∃ M, ∃ k > 0, k < n ∧ b ^ (M + k) ≡ b ^ M [MOD n] :=
    exists_ne_pow_modeq hn0 b
  ---- Step 3: From IH, there exists `m' ≥ max{M, N}` such that `b^{m'} + m' ≡ r (mod k)`.
  specialize n_ih k hk0 hk (max M N) r
  rcases n_ih with ⟨m', hm', h0⟩
  replace hm' : M ≤ m' ∧ N ≤ m' := Nat.max_le.mp hm'
  ---- Step 4(a): Since `m' ≥ M`, we get `b^{m' + ks} ≡ b^{m'} (mod n)` for all `s`.
  replace h : b ^ (m' + k) ≡ b ^ m' [MOD n] := by
    rw [← Nat.add_sub_cancel' hm'.1, Nat.pow_add b M, Nat.add_right_comm, Nat.pow_add]
    exact h.mul_right _
  replace h (s) : b ^ (m' + k * s) ≡ b ^ m' [MOD n] := by
    induction s with | zero => rfl | succ s hs => ?_
    calc b ^ (m' + k * (s + 1))
      _ = b ^ (m' + k * s) * b ^ k := by rw [Nat.mul_succ, ← Nat.add_assoc, Nat.pow_add]
      _ ≡ b ^ m' * b ^ k [MOD n] := hs.mul_right _
      _ = b ^ (m' + k) := (Nat.pow_add _ _ _).symm
      _ ≡ b ^ m' [MOD n] := h
  ---- Step 4(b): There exists an index `s` such that `b^{m'} + (m' + ks) ≡ r (mod n)`.
  replace h0 : ∃ s, b ^ m' + m' + k * s ≡ r [MOD n] := exists_mod_eq_mul_add_of_dvd hn h0
  rcases h0 with ⟨s, hs⟩
  ---- Step 5: Then `m = m' + ks` works.
  refine ⟨m' + k * s, Nat.le_add_right_of_le hm'.2, ((h s).add_right _).trans ?_⟩
  rwa [← Nat.add_assoc]

/-- Final solution -/
theorem final_solution (hn : 0 < n) (b) : ∃ m, n ∣ b ^ m + m :=
  (general_claim hn b 0 0).imp λ _ h ↦ Nat.dvd_of_mod_eq_zero h.2
