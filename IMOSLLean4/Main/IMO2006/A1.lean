/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Order.OrderIsoNat

/-!
# IMO 2006 A1

A ring with floor is a totally ordered ring $R$ with a floor function $⌊⬝⌋ : R → ℤ$
  such that for any $x ∈ R$ and $n ∈ ℤ$, we have $⌊x⌋ ≤ n ↔ x ≤ n_R$.
(See `FloorRing` for the formal definition.)

Let $R$ be an archimedean ring with floor.
Define the function $f : R → R$ by
$$ f(x) = ⌊x⌋ (x - ⌊x⌋). $$
Prove that for any $r ∈ R$, there exists $N ∈ ℕ$ such that for all $k ≥ N$,
$$ f^{k + 2}(r) = f^k(r). $$

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2006SL.pdf)
  with some twists.
We prove more: the sequence $(f^k(r))_{k ≥ 0}$ either stabilizes to a constant
  sequence or $-s, s - 1, -s, s - 1, …$ for some $s ∈ R$ with $0 < s < 1$.

Instead of showing that $(⌊f^k(r)⌋)_{k ≥ 0}$ is non-increasing or non-decreasing,
  we show that $(|⌊f^k(r))⌋|)_{k ≥ 0}$ is non-increasing, thus eventually constant.
From this, we deduce that $(⌊f^k(r)⌋)_{k ≥ 0}$ is eventually constant,
  and we also deduce that this constant is non-positive.
After that, there is no need to divide into cases based on the sign of $r$.

Since there is no division, in the case $⌊f^k(r)⌋ → c ≤ -2$, we need to consider
  the sequence $b_k = (c - 1) f^k(r) - c^2$ as opposed to $b_k = f^k(r) - c^2/(c - 1)$.
We will use $b_k = (-c + 1) f^k(r) + c^2$ instead.
-/

namespace IMOSL
namespace IMO2006A1

variable [Ring R] [LinearOrder R] [FloorRing R] [IsStrictOrderedRing R]

/-- The function `f(r) = ⌊r⌋ (r - ⌊r⌋)`. -/
abbrev f (r : R) := ⌊r⌋ * Int.fract r

/-- For any `r ∈ R`, we have `|⌊f(r)⌋| ≤ |⌊r⌋|`. -/
theorem floor_f_abs_le_floor_abs (r : R) : |⌊f r⌋| ≤ |⌊r⌋| := by
  have hr0 : 0 ≤ Int.fract r := Int.fract_nonneg r
  have hr1 : Int.fract r ≤ 1 := (Int.fract_lt_one r).le
  obtain hr | hr : 0 ≤ r ∨ r ≤ 0 := le_total 0 r
  ---- Case 1: `r ≥ 0`.
  · have hr2 : 0 ≤ ⌊r⌋ := Int.floor_nonneg.mpr hr
    replace hr : (0 : R) ≤ ⌊r⌋ := Int.cast_nonneg hr2
    replace hr0 : 0 ≤ ⌊f r⌋ := Int.floor_nonneg.mpr (mul_nonneg hr hr0)
    rw [abs_of_nonneg hr2, abs_of_nonneg hr0, ← Int.cast_le (R := R)]
    exact (Int.floor_le (f r)).trans (mul_le_of_le_one_right hr hr1)
  ---- Case 2: `r ≤ 0`.
  · have hr2 : ⌊r⌋ ≤ 0 := Int.floor_nonpos hr
    replace hr : (⌊r⌋ : R) ≤ 0 := Int.cast_nonpos.mpr hr2
    replace hr0 : ⌊f r⌋ ≤ 0 := Int.floor_nonpos (mul_nonpos_of_nonpos_of_nonneg hr hr0)
    rw [abs_of_nonpos hr2, abs_of_nonpos hr0, neg_le_neg_iff, Int.le_floor]
    exact le_mul_of_le_one_right hr hr1

/-- For any `r ∈ R`, `(⌊f^k(r)⌋)_{k ≥ 0}` converges to `-C` for some `C : ℕ`. -/
theorem floor_f_iter_converges (r : R) : ∃ (C N : ℕ), ∀ n ≥ N, ⌊f^[n] r⌋ = -C := by
  ---- First, `(|⌊f^k(r)⌋|)_{k ≥ 0}` converges to some `C : ℕ`.
  obtain ⟨C, N, h⟩ : ∃ C N, ∀ n ≥ N, ⌊f^[n] r⌋.natAbs = C := by
    have h : Antitone (λ n ↦ ⌊f^[n] r⌋.natAbs) :=
      antitone_nat_of_succ_le λ n ↦ by
        simpa [f.iterate_succ_apply', ← Int.ofNat_le] using floor_f_abs_le_floor_abs _
    obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ⌊f^[N] r⌋.natAbs = ⌊f^[n] r⌋.natAbs :=
      WellFoundedGT.monotone_chain_condition (α := ℕᵒᵈ) ⟨_, h⟩
    exact ⟨⌊f^[N] r⌋.natAbs, N, λ n hn ↦ (hN n hn).symm⟩
  ---- We claim that this `C` works.
  refine ⟨C, N, λ n hn ↦ ?_⟩
  ---- We have `⌊f^n(r)⌋ ∈ {C, -C}`; it remains to consider the case `⌊f^n(r)⌋ = C > 0`.
  refine (Int.natAbs_eq_iff.mp (h n hn)).elim (λ h0 ↦ ?_) id
  obtain rfl | hC : C = 0 ∨ 0 < C := C.eq_zero_or_pos
  · exact h0
  ---- We claim and show that `|⌊f^{n + 1}(r)⌋| < C`, thus yielding a contradiction.
  refine absurd ?_ (h (n + 1) (Nat.le_succ_of_le hn)).not_lt
  replace hC : 0 < (C : R) := Nat.cast_pos.mpr hC
  rw [← Int.natAbs_natCast C, f.iterate_succ_apply', f, h0, Int.cast_natCast]
  exact Int.natAbs_lt_natAbs_of_nonneg_of_lt
    (Int.floor_nonneg.mpr (mul_nonneg hC.le (Int.fract_nonneg _)))
    (by simpa [Int.floor_lt] using mul_lt_of_lt_one_right hC (Int.fract_lt_one _))

/-- If `(⌊f^k(r)⌋)_{k ≥ 0} → -1`, then `(f^k(r))_{k ≥ 0}` alternates
  `-s, s - 1, -s, s - 1, …` for some `s ∈ R` with `0 < s < 1`. -/
theorem f_iter_alt_of_floor_f_iter_lim_one {r : R} (h : ∃ N, ∀ n ≥ N, ⌊f^[n] r⌋ = -1) :
    ∃ s, (0 < s ∧ s < 1) ∧ ∃ N, ∀ n ≥ N, f^[n] r = if n % 2 = 0 then -s else s - 1 := by
  ---- We take `s = -f^{2N}(r)`; the `2N` is chosen to be even and `≥ N`.
  rcases h with ⟨N, h⟩
  replace h {n} (hn : 2 * N ≤ n) : ⌊f^[n] r⌋ = -1 :=
    h n ((Nat.le_mul_of_pos_left N Nat.zero_lt_two).trans hn)
  refine ⟨-f^[2 * N] r, ?_, 2 * N, ?_⟩
  ---- First show that `0 < -f^{2N}(r) < 1`.
  · obtain ⟨h0, h1⟩ : -1 ≤ f^[2 * N] r ∧ f^[2 * N] r < 0 := by
      simpa [Int.floor_eq_iff] using h (Nat.le_refl _)
    -- We have `-1 ≤ f^{2N}(r) < 0`, so we just need to show that `f^{2N}(r) ≠ -1`.
    refine ⟨neg_pos.mpr h1, neg_lt.mpr (h0.lt_of_ne' λ h2 ↦ ?_)⟩
    replace h0 : ⌊f^[2 * N + 1] r⌋ = -1 := h (Nat.le_succ _)
    replace h : Int.fract (-1 : R) = 0 := Int.fract_neg_eq_zero.mpr Int.fract_one
    rw [f.iterate_succ_apply', h2, f, h, mul_zero, Int.floor_zero] at h0
    exact absurd h0 (Int.zero_ne_negSucc 0)
  ---- Now show using induction that `f^n(r)` takes the desired formula for `n ≥ 2N`.
  · intro n hn; induction n, hn using Nat.le_induction with
    | base => rw [if_pos (Nat.mul_mod_right _ _), neg_neg]
    | succ n hn hn0 => ?_
    -- Base case is obvious, so now we just do the induction step.
    simp_rw [Nat.succ_mod_two_eq_zero_iff, ← Nat.mod_two_ne_zero]
    rw [f.iterate_succ_apply', f, Int.fract, h hn, hn0, ite_not, neg_neg,
      Int.cast_neg, Int.cast_one, sub_neg_eq_add, ite_add, mul_ite,
      neg_one_mul, sub_add_cancel, neg_add', neg_mul_neg, one_mul]

omit [IsStrictOrderedRing R] in
/-- If `⌊r⌋ = -C`, then `(C + 1) f(r) + C^2 = -C ((C + 1)r + C^2)`. -/
theorem f_formula_of_floor_eq_neg {r : R} {C : ℕ} (h : ⌊r⌋ = -C) :
    (C + 1) * f r + C ^ 2 = (-C) * ((C + 1) * r + C ^ 2) := by
  rw [f, Int.fract, h, Int.cast_neg, sub_neg_eq_add, Int.cast_natCast]
  generalize (C : R) = s; clear C h
  rw [neg_mul, neg_mul, ← eq_sub_iff_add_eq, ← neg_add', mul_neg,
    neg_inj, ← mul_assoc, add_one_mul, mul_add, mul_add, add_assoc,
    ← mul_assoc, mul_add_one, add_right_inj, sq, add_mul, mul_assoc]


variable [Archimedean R]

/-- Suppose that `R` is archimedean and `C ≥ 2` is an positive integer.
  If `⌊f^k(r)⌋ = -C` for all `k`, then `(C + 1)r + C^2 = 0`.
  This is the only step that requires `R` to be archimedean. -/
theorem f_formula_of_archimedean_of_floor_eq_neg_nat
    {r : R} {C : ℕ} (hC : 2 ≤ C) (h : ∀ k, ⌊f^[k] r⌋ = -C) :
    (C + 1) * r + C ^ 2 = 0 := by
  ---- Let `s = (C + 1)r + C^2`, and suppose that `|s| > 0`.
  set s : R := (C + 1) * r + C ^ 2
  refine ((abs_nonneg _).eq_or_lt'.imp_left abs_eq_zero.mp).resolve_right λ h0 ↦ ?_
  ---- First show that `|(C + 1) f^k(r) + C^2| = C^k |s|` for all `k ≥ 0`
  have h1 (k : ℕ) : |(C + 1) * f^[k] r + C ^ 2| = C ^ k • |s| := by
    -- Base case is immediate, so just go to induction step and use the previous formula
    induction k with | zero => exact (one_nsmul _).symm | succ k hk => ?_
    rw [f.iterate_succ_apply', f_formula_of_floor_eq_neg (h k), abs_mul,
      hk, abs_neg, Nat.abs_cast, ← nsmul_eq_mul, ← mul_nsmul, ← Nat.pow_succ]
  ---- Find `k > 1` such that `C^k |s| > C + 1 + |s|`.
  obtain ⟨k, hk⟩ : ∃ k, (C : R) + 1 + |s| < C ^ k • |s| := by
    obtain ⟨k, hk⟩ : ∃ k, (C : R) + 1 + |s| < k • |s| := exists_lt_nsmul h0 _
    exact ⟨k, hk.trans (nsmul_lt_nsmul_left h0 (Nat.lt_pow_self hC))⟩
  ---- Deduce that `|(C + 1) (f^k(r) - r)| > C + 1`.
  replace hk : (C + 1 : R) < |(C + 1) * (f^[k] r - r)| := by
    rw [← h1, ← lt_sub_iff_add_lt] at hk
    refine hk.trans_le ((abs_sub_abs_le_abs_sub _ _).trans_eq ?_)
    rw [add_sub_add_right_eq_sub, ← mul_sub]
  ---- Then `|f^k(r) - r| > 1`, contradicting `⌊f^k(r)⌋ = ⌊r⌋`.
  replace h1 : 0 < (C : R) + 1 :=
    add_pos (two_pos.trans_le (Nat.ofNat_le_cast.mpr hC)) one_pos
  rw [abs_mul, abs_eq_self.mpr h1.le, lt_mul_iff_one_lt_right h1] at hk
  exact hk.not_gt (Int.abs_sub_lt_one_of_floor_eq_floor ((h k).trans (h 0).symm))

/-- Suppose that `R` is archimedean and `C ≥ 2` is an positive integer.
  If `⌊f^N(r)⌋ = -C` for all `n ≥ N`, then `(C + 1) f^N(r) + C^2 = 0`. -/
theorem f_formula2_of_archimedean_of_floor_eq_neg_nat
    {r : R} {C : ℕ} (hC : 2 ≤ C) (h : ∀ n ≥ N, ⌊f^[n] r⌋ = -C) :
    (C + 1) * f^[N] r + C ^ 2 = 0 :=
  f_formula_of_archimedean_of_floor_eq_neg_nat hC
    λ k ↦ f.iterate_add_apply k N r ▸ h _ (Nat.le_add_left N k)

/-- The sequence `(f^k(r))_{k ≥ 0}` eventually is either constant or alternating. -/
theorem f_iter_converges_or_alt (r : R) :
    (∃ r₀ N, ∀ n ≥ N, f^[n] r = r₀) ∨
      (∃ s : R, (0 < s ∧ s < 1) ∧
        ∃ N, ∀ n ≥ N, f^[n] r = if n % 2 = 0 then -s else s - 1) := by
  obtain ⟨C, h⟩ := floor_f_iter_converges r
  obtain rfl | rfl | hC : C = 0 ∨ C = 1 ∨ 2 ≤ C :=
    C.eq_zero_or_pos.imp_right eq_or_lt_of_le'
  ---- Case 1: `C = 0`
  · left; rcases h with ⟨N, h⟩
    refine ⟨0, N + 1, λ n hn ↦ ?_⟩
    rw [← Nat.succ_pred_eq_of_pos (Nat.zero_lt_of_lt hn), f.iterate_succ_apply',
      f, h _ (Nat.le_pred_of_lt hn), Nat.cast_zero, neg_zero, Int.cast_zero, zero_mul]
  ---- Case 2: `C = 1`
  · right; exact f_iter_alt_of_floor_f_iter_lim_one h
  ---- Case 3: `C ≥ 2`
  · left; rcases h with ⟨N, h⟩
    refine ⟨f^[N] r, N, λ n hn ↦ ?_⟩
    replace h : (C + 1) * f^[n] r + C ^ 2 = (C + 1) * f^[N] r + C ^ 2 :=
      (f_formula2_of_archimedean_of_floor_eq_neg_nat hC λ k hk ↦ h _ (hn.trans hk)).trans
        (f_formula2_of_archimedean_of_floor_eq_neg_nat hC h).symm
    replace hC : 0 < (C : R) + 1 :=
      add_pos (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hC)) one_pos
    exact mul_left_cancel₀ hC.ne.symm (add_right_cancel h)

/-- Final solution -/
theorem final_solution (r : R) : ∃ N, ∀ n ≥ N, f^[n + 2] r = f^[n] r := by
  obtain ⟨r₀, N, h⟩ | ⟨s, -, N, h⟩ := f_iter_converges_or_alt r
  ---- Case 1: `(f^k(r))_{k ≥ 0}` eventually converges
  · exact ⟨N, λ n hn ↦ (h _ (Nat.le_add_right_of_le hn)).trans (h n hn).symm⟩
  ---- Case 2: `(f^k(r))_{k ≥ 0}` eventually alternates
  · refine ⟨N, λ n hn ↦ ?_⟩
    rw [h _ (Nat.le_add_right_of_le hn), Nat.add_mod_right, h n hn]
