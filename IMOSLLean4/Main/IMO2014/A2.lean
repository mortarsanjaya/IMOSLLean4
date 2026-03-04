/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# IMO 2014 A2

Define the function $f : ℝ → ℝ$ by
$$ f(x) = \begin{cases} x + 1/2 & \text{if } x < 1/2, \\
  x^2 & \text{if } x ≥ 1/2. \end{cases} $$
Let $a$ and $b$ be real numbers with $0 < a < b < 1$.
Show that there exists a positive integer $n$ such that
$$ (f^n(a) - f^{n - 1}(a))(f^n(b) - f^{n - 1}(b)) < 0. $$

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2014SL.pdf).
We will not use the real numbers; instead they can be generalized to
  archimedean ordered commutative rings containing $1/2$.
-/

namespace IMOSL
namespace IMO2014A2

/-- The function `f : R → R` defined by
  `f(x) = x + 1/2` if `x < 1/2` and `f(x) = x^2` otherwise. -/
def f [Ring R] [Invertible (2 : R)] [LT R] [DecidableLT R] (x : R) : R :=
  if x < ⅟2 then x + ⅟2 else x ^ 2


variable [CommRing R] [Invertible (2 : R)] [LinearOrder R]

/-- If `x < 1/2` then `f(x) = x + 1/2`. -/
theorem f_of_lt_invOf_two {x : R} (hx : x < ⅟2) : f x = x + ⅟2 :=
  if_pos hx

/-- If `x ≥ 1/2` then `f(x) = x^2`. -/
theorem f_of_invOf_two_le {x : R} (hx : ⅟2 ≤ x) : f x = x ^ 2 :=
  if_neg hx.not_gt


variable [IsStrictOrderedRing R]

/-- If `x > 0`, then `f(x) > 0`. -/
theorem f_pos {x : R} (hx : x > 0) : f x > 0 := by
  unfold f; split_ifs
  exacts [add_pos hx (invOf_pos.mp two_pos), pow_pos hx 2]

/-- If `x > 0`, then `f^n(x) > 0` for all `n : ℕ`. -/
theorem f_iterate_pos {x : R} (hx : x > 0) (n : ℕ) : f^[n] x > 0 := by
  induction n generalizing x with | zero => exact hx | succ n n_ih => exact n_ih (f_pos hx)

/-- If `x < 1`, then `f(x) < 1`. -/
theorem f_lt_one {x : R} (hx0 : x < 1) : f x < 1 := by
  unfold f; split_ifs with hx1
  · rwa [← invOf_two_add_invOf_two, add_lt_add_iff_right]
  · replace hx1 : 0 ≤ x := (invOf_nonneg.mpr zero_le_two).trans (not_lt.mp hx1)
    exact pow_lt_one₀ hx1 hx0 (Nat.succ_ne_zero 1)

/-- If `x < 1`, then `f^n(x) < 1` for all `n : ℕ`. -/
theorem f_iterate_lt_one {x : R} (hx : x < 1) (n : ℕ) : f^[n] x < 1 := by
  induction n generalizing x with | zero => exact hx | succ n n_ih => exact n_ih (f_lt_one hx)

omit [IsStrictOrderedRing R] in
/-- If `a, b < 1/2`, then `f(b) - f(a) = b - a`. -/
theorem f_sub_f_of_lt_invOf_two {a b : R} (ha : a < ⅟2) (hb : b < ⅟2) :
    f b - f a = b - a := by
  rw [f_of_lt_invOf_two ha, f_of_lt_invOf_two hb, add_sub_add_right_eq_sub]

/-- If `b ≥ a ≥ 1/2`, then `f(b) - f(a) ≥ (b - a) + (b - a)^2`. -/
theorem f_sub_f_of_invOf_two_le {a b : R} (ha : ⅟2 ≤ a) (hab : a ≤ b) :
    (b - a) + (b - a) ^ 2 ≤ f b - f a := calc
  _ = (b - a) * (1 + (b - a)) := by rw [sq, mul_one_add]
  _ ≤ (b - a) * (a + a + (b - a)) :=
    have ha0 : 1 ≤ a + a := invOf_two_add_invOf_two.symm.trans_le (add_le_add ha ha)
    mul_le_mul_of_nonneg_left (add_le_add_left ha0 _) (sub_nonneg_of_le hab)
  _ = b ^ 2 - a ^ 2 := by rw [sq_sub_sq, add_add_sub_cancel, add_comm, mul_comm]
  _ = f b - f a := by rw [f_of_invOf_two_le ha, f_of_invOf_two_le (ha.trans hab)]

/-- Suppose that `0 < a ≤ b < 1`, and `(f(a) - a)(f(b) - b) ≥ 0`.
  Then one of the following holds: (1). `f(b) - f(a) ≥ (b - a) + (b - a)^2`; or
  (2). `f(b) - f(a) = b - a` and `f^2(b) - f^2(a) ≥ (b - a) + (b - a)^2`. -/
theorem main_lemma
    {a b : R} (ha : a > 0) (hab : a ≤ b) (hb : b < 1) (h : 0 ≤ (f a - a) * (f b - b)) :
    (b - a + (b - a) ^ 2 ≤ f b - f a) ∨
      (f b - f a = b - a ∧ b - a + (b - a) ^ 2 ≤ f (f b) - f (f a)) := by
  have hb0 : b > 0 := ha.trans_le hab
  ---- If `a ≥ 1/2`, then the first case holds.
  refine (le_or_gt ⅟2 a).imp (λ ha0 ↦ f_sub_f_of_invOf_two_le ha0 hab) (λ ha0 ↦ ?_)
  ---- If `a < 1/2 ≤ b`, then `(f(a) - a)(f(b) - b) < 0`; contradiction.
  obtain hb1 | hb1 : ⅟2 ≤ b ∨ b < ⅟2 := le_or_gt _ _
  · refine absurd (mul_neg_of_pos_of_neg ?_ ?_) h.not_gt
    -- The subgoal `f(a) - a > 0`.
    · rw [f_of_lt_invOf_two ha0, add_sub_cancel_left, invOf_pos]
      exact zero_lt_two
    -- The subgoal `f(b) - b < 0`.
    · rw [f_of_invOf_two_le hb1, sq, ← mul_sub_one]
      exact mul_neg_of_pos_of_neg hb0 (sub_neg.mpr hb)
  ---- If `a ≤ b < 1/2` then the second case holds.
  replace h : f b - f a = b - a := f_sub_f_of_lt_invOf_two ha0 hb1
  have h0 : ⅟2 ≤ f a := calc
    _ ≤ a + ⅟2 := le_add_of_nonneg_left ha.le
    _ = f a := (f_of_lt_invOf_two ha0).symm
  have h1 : f a ≤ f b := by rwa [← sub_nonneg, h, sub_nonneg]
  exact ⟨h, h ▸ f_sub_f_of_invOf_two_le h0 h1⟩


section

variable [Archimedean R] {a b : R} (ha : a > 0) (hab : a < b) (hb : b < 1)
include ha hab hb

/-- Suppose that `R` is archimedean. Then for any `a, b : R` with `0 < a < b < 1`,
  there exists `n : ℕ` such that `(f^{n + 1}(a) - f^n(a))(f^{n + 1}(b) - f^n(b)) < 0`. -/
theorem exists_diff_iterate_mul_diff_iterate_neg :
    ∃ n, (f^[n + 1] a - f^[n] a) * (f^[n + 1] b - f^[n] b) < 0 := by
  replace ha (n : ℕ) : f^[n] a > 0 := f_iterate_pos ha n
  replace hb (n : ℕ) : f^[n] b < 1 := f_iterate_lt_one hb n
  ---- Suppose for the sake of contradiction that such `n` does not exist.
  by_contra! h
  ---- Define the sequence `d : ℕ → R` by `d_n = f^n(b) - f^n(a)`.
  let d (n : ℕ) : R := f^[n] b - f^[n] a
  /- First, `d_n ≥ 0` implies either (1). `d_{n + 1} ≥ d_n + d_n^2`; or
    (2). `d_{n + 1} = d_n` and `d_{m + 2} ≥ d_n + d_n^2`. -/
  replace h (n) (hn : 0 ≤ d n) :
      d n + d n ^ 2 ≤ d (n + 1) ∨ (d (n + 1) = d n ∧ d n + d n ^ 2 ≤ d (n + 2)) := by
    have hn0 : 0 ≤ (f (f^[n] a) - f^[n] a) * (f (f^[n] b) - f^[n] b) := by
      simpa only [Function.iterate_succ_apply'] using h n
    simp_rw [d, Function.iterate_succ_apply']
    exact main_lemma (ha n) (sub_nonneg.mp hn) (hb n) hn0
  ---- Since `d_0 > 0`, we get `d_{n + 1} ≥ d_n` for all `n` by induction; `d` is monotone.
  have hd : d 0 > 0 := sub_pos.mpr hab
  have hd0 (n : ℕ) (hn : 0 ≤ d n) : d n ≤ d (n + 1) := by
    obtain hn0 | ⟨hn0, -⟩ : d n + d n ^ 2 ≤ d (n + 1) ∨ (d (n + 1) = d n ∧ _) := h n hn
    exacts [le_of_add_le_of_nonneg_left hn0 (sq_nonneg _), hn0.ge]
  replace hd0 : Monotone d := by
    refine monotone_nat_of_le_succ λ n ↦ hd0 n ?_
    induction n with | zero => exact hd.le | succ n n_ih => exact n_ih.trans (hd0 n n_ih)
  have hd1 (n : ℕ) : d n ≥ 0 := hd.le.trans (hd0 (Nat.zero_le n))
  ---- In particular, we have `d_{n + 2} ≥ d_n + d_n^2 ≥ d_n + d_0^2` for all `n`.
  replace h (n) : d n + d 0 ^ 2 ≤ d (n + 2) := calc
    _ ≤ d n + d n ^ 2 := add_le_add_right (pow_le_pow_left₀ hd.le (hd0 (Nat.zero_le n)) 2) _
    _ ≤ d (n + 2) := (h n (hd1 n)).elim (hd0 (Nat.le_succ _)).trans' And.right
  ---- By induction on `n`, we get `d_{2n} > n d_0^2` for all `n`.
  replace h (n) : n • d 0 ^ 2 < d (2 * n) := by
    induction n with
    | zero => rwa [zero_nsmul]
    | succ n n_ih =>
        calc (n + 1) • d 0 ^ 2
        _ = n • d 0 ^ 2 + d 0 ^ 2 := succ_nsmul _ _
        _ < d (2 * n) + d 0 ^ 2 := add_lt_add_left n_ih _
        _ ≤ d (2 * (n + 1)) := h _
  ---- But `d_0^2 > 0` and `R` is archimedean, so `Nd_0^2 ≥ 1` for some `N`.
  obtain ⟨N, hN⟩ : ∃ N, N • d 0 ^ 2 ≥ 1 := Archimedean.arch _ (pow_pos hd 2)
  ---- Then `d_{2N} ≥ 1`, contradicting `f^{2N}(a) > 0` and `f^{2N}(b) < 1`.
  refine hN.not_gt ?_
  calc N • d 0 ^ 2
    _ < f^[2 * N] b - f^[2 * N] a := h _
    _ < 1 - 0 := sub_lt_sub (hb _) (ha _)
    _ = 1 := sub_zero _

/-- Final solution -/
theorem final_solution : ∃ n > 0, (f^[n] a - f^[n - 1] a) * (f^[n] b - f^[n - 1] b) < 0 := by
  obtain ⟨n, hn⟩ : ∃ n, (f^[n + 1] a - f^[n] a) * (f^[n + 1] b - f^[n] b) < 0 :=
    exists_diff_iterate_mul_diff_iterate_neg ha hab hb
  exact ⟨n + 1, Nat.succ_pos n, hn⟩

end
