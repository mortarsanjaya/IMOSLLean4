/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Factors

/-!
# IMO 2013 N3

For each positive integer $n$, let $P(n)$ denote the largest prime divisor of $n$.
Prove that there exists infinitely many $n ∈ ℕ$ such that
$$ P(n^4 + n^2 + 1) = P((n + 1)^4 + (n + 1)^2 + 1). $$

### Solution

We generalize the problem even further.
Let $f : ℕ → S$ be a function to a totally ordered set $S$ such that for any $n$,
$$ f((n + 1)^2) = max\\{f(n), f(n + 1)\\}. $$
Then we prove that there exists infinitely many positive integers $n$ such that
$$ f(n^2) = f((n + 1)^2). $$
The original problem follows by taking $f(n) = P(n^2 + n + 1)$ due to the formula
$$ (n + 1)^4 + (n + 1)^2 + 1 = (n^2 + n + 1)((n + 1)^2 + (n + 1) + 1). $$

Replace $n$ in the equality to be proved with $n + 1$, and rewrite the equality as
$$ \max{f(n), f(n + 1)} = \max{f(n + 1), f(n + 2)}. $$
Suppose for the sake of contradiction that this equality only holds for finitely many $n$.
Then for every $n$ large enough, $f(n) ≤ f(n + 1)$ implies $f(n + 1) < f(n + 2)$.
If such $n$ exists, then then $f$ is eventually strictly increasing, contradicting the
  given functional equation as $n < n + 1 < (n + 1)^2$ for all $n ≥ 1$.
Otherwise, we have $f(n) > f(n + 1)$ for all $n$ large enough.
Then $f$ is eventually strictly increasing, again contradicting the
  given functional equation as $n < n + 1 < (n + 1)^2$ for all $n ≥ 1$.
-/

namespace IMOSL
namespace IMO2013N3

/-- The more general result. -/
theorem general_result [LinearOrder α]
    (f : ℕ → α) (hf : ∀ n, f ((n + 1) ^ 2) = max (f n) (f (n + 1))) (N) :
    ∃ n ≥ N, f (n ^ 2) = f ((n + 1) ^ 2) := by
  ---- Suppose that the statement is false.
  by_contra h
  ---- Then for every `n ≥ N`, if `f(n + 1) ≥ f(n)`, then `f(n + 2) > f(n + 1)`.
  replace h (n) (hn : N ≤ n) (hn0 : f n ≤ f (n + 1)) : f (n + 1) < f (n + 2) := by
    -- If not, then `f((n + 1)^2) = f((n + 2)^2)`.
    refine not_le.mp λ h0 ↦ h ⟨n + 1, Nat.le_succ_of_le hn, ?_⟩
    rw [hf, hf, max_eq_right hn0, max_eq_left h0]
  ---- We show that `f(n + 1) < f(n)` for all `n ≥ N`.
  replace h (n) (hn : N ≤ n) : f (n + 1) < f n := by
    -- Fix `n ≥ N`, and suppose for the sake of contradiction that `f(n + 1) ≥ f(n)`.
    refine not_le.mp λ hn0 ↦ ?_
    -- Since `f(n + 2) > f(n + 1)`, we have `f((n + 2)^2) = f(n + 2)`.
    replace hf : f ((n + 2) ^ 2) = f (n + 2) := by
      rw [hf, max_eq_right (h n hn hn0).le]
    -- On the other hand, by inducting twice, we get `f(m) > f(k)` for all `m > k > n`.
    replace h : ∀ k > n, f k < f (k + 1) :=
      Nat.le_induction (h n hn hn0) λ k hnk hk ↦ h k ((Nat.le_succ_of_le hn).trans hnk) hk.le
    replace h : ∀ k > n, ∀ m > k, f k < f m :=
      λ k hk ↦ Nat.le_induction (h k hk) λ m hm ↦ (h m (hk.trans hm)).trans'
    -- Then `n < n + 2 < (n + 2)^2` implies `f(n + 2) < f((n + 2)^2)`.
    replace hn : f (n + 2) < f ((n + 2) ^ 2) := by
      refine h _ (Nat.lt_add_of_pos_right Nat.two_pos) _ (?_ : n + 2 < (n + 2) ^ 2)
      calc n + 2
        _ = (n + 2) ^ 1 := (Nat.pow_one _).symm
        _ < (n + 2) ^ 2 := Nat.pow_lt_pow_right (Nat.one_lt_succ_succ n) Nat.one_lt_two
    -- But we also had `f((n + 2)^2) = f(n + 2)`; contradiction.
    exact hn.ne hf.symm
  ---- Thus by induction, we get `f(k) ≤ f(n)` whenever `k ≥ n ≥ N`.
  have h0 (n) (h0 : N ≤ n) : ∀ k, n ≤ k → f k ≤ f n :=
    Nat.le_induction (le_refl _) (λ k h1 ↦ (h k (h0.trans h1)).le.trans)
  ---- Then `f(N) > f(N + 1) ≥ f((N + 1)^2) = max{f(N + 1), f(N)}`; contradiction.
  replace h : f (N + 1) < f N :=
    h _ (Nat.le_refl N)
  replace h0 : f ((N + 1) ^ 2) ≤ f (N + 1) :=
    h0 _ (Nat.le_succ N) _ (Nat.le_self_pow (Nat.succ_ne_zero 1) _)
  replace hf : f N ≤ f ((N + 1) ^ 2) :=
    (le_max_left _ _).trans_eq (hf N).symm
  exact (hf.trans h0).not_gt h

/-- The maximum element of `l ++ l'` is the same as the maximum of the maximum element
  of `l` and the maximum element of `l'`, where the maximum of `[]` is set to be `0`. -/
theorem foldr_max_zero_append (l l' : List ℕ) :
    (l ++ l').foldr max 0 = max (l.foldr max 0) (l'.foldr max 0) := by
  induction l generalizing l' with
  | nil => exact (Nat.zero_max _).symm
  | cons a l ih => rw [List.cons_append, List.foldr_cons, List.foldr_cons, ih, max_assoc]

/-- The formula `(n + 1)^4 + (n + 1)^2 + 1 = (n^2 + n + 1)((n + 1)^2 + (n + 1) + 1)`. -/
theorem special_formula (n : ℕ) :
    ((n + 1) ^ 2) ^ 2 + (n + 1) ^ 2 + 1 = (n ^ 2 + n + 1) * ((n + 1) ^ 2 + (n + 1) + 1) :=
  let s : ℕ := n ^ 2 + n + 1
  have hn : (n + 1) ^ 2 = s + n := by
    rw [Nat.pow_two, Nat.mul_succ, Nat.succ_mul,
      Nat.add_comm n, ← Nat.add_assoc, ← Nat.pow_two]
  calc ((n + 1) ^ 2) ^ 2 + (n + 1) ^ 2 + 1
  _ = (s + (n + 1)) * (n + 1) ^ 2 + 1 := by
    rw [Nat.pow_two, ← Nat.add_one_mul, hn, Nat.add_assoc]
  _ = s * (n + 1) ^ 2 + ((n + 1) * (s + n) + 1) := by
    rw [Nat.add_mul, Nat.add_assoc, ← hn]
  _ = s * (n + 1) ^ 2 + (s * (n + 1) + s) := by
    rw [Nat.mul_add, Nat.mul_comm _ s, Nat.add_assoc, Nat.succ_mul n, ← Nat.pow_two]
  _ = s * ((n + 1) ^ 2 + (n + 1) + 1) := by
    rw [← Nat.mul_succ, ← Nat.mul_add, Nat.add_assoc]

/-- Final solution -/
theorem final_solution :
    ∀ N, ∃ n ≥ N, (n ^ 4 + n ^ 2 + 1).primeFactorsList.foldr max 0
      = ((n + 1) ^ 4 + (n + 1) ^ 2 + 1).primeFactorsList.foldr max 0 := by
  simp only [Nat.pow_mul _ 2 2]
  refine general_result (λ n ↦ (n ^ 2 + n + 1).primeFactorsList.foldr max 0) ?_
  have h0 (n) : n ^ 2 + n + 1 ≠ 0 := Nat.succ_ne_zero _
  intro n; simp only; rw [special_formula, ← foldr_max_zero_append]
  exact (Nat.perm_primeFactorsList_mul (h0 n) (h0 (n + 1))).foldr_eq _
