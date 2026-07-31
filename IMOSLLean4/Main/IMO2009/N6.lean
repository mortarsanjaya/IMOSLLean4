/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Mathlib.Algebra.Polynomial.Inductions
public import IMOSLLean4.Extra.ExplicitRings.F4

/-!
# IMO 2009 N6

An integer polynomial $P$ is called *good* if there exists a sequence $(a_n)_{n ≥ 0}$
  of integers such that $n a_n = a_{n - 1} + P(n)$ for all $n ≥ 1$.
Show that if $X^k$ is good, then $3 ∣ k + 1$.

### Solution

We follow Solution 1 and Solution 2 of the
  [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
We follow Solution 1 for part A and B, and we follow Solution 2 for part C.
However, we do a different construction for part A using induction on the degree of $P$.

A polynomial $Q$ is called the **companion** of $P$ if
$$ X Q(X) = P(X) + Q(X - 1) - (P(0) + Q(-1)). $$
It is easy to show every integer polynomial has at most one companion.
Our goal for part A is to construct the companion of any integer polynomial.
Here is the inductive construction.
1. First, if $P$ is constant, then set $Q(X) = 0$.
2. Next, write $P(X) = XR(X) + c$ for some $R ∈ ℤ[X]$ and integer constant $c$.
Let $S(X)$ be the companion of $R(X - 1)$, constructed inductively.
Then set $$Q(X) = (X + 1) S(X + 1) + (R(-1) + S(-1)). $$
It is easy to check that $Q$ is the companion of $P$.

For convenience, we say that $P(0) + Q(-1)$ is the *companion constant* of $P$,
  where $Q$ is the companion of $P$.
-/

@[expose] public section

namespace IMOSL
namespace IMO2009N6

open Polynomial

/-! ### Some routine polynomial lemma -/

/-- For any polynomial `P`, we have `deg(P(X - 1)) = deg(P)`. -/
theorem natDegree_comp_X_sub_one [Ring R] (P : R[X]) :
    (P.comp (X - 1)).natDegree = P.natDegree := by
  by_cases hP : P.leadingCoeff = 0
  · rw [leadingCoeff_eq_zero.mp hP, zero_comp]
  · haveI : Nontrivial R := ⟨⟨P.leadingCoeff, 0, hP⟩⟩
    replace hP : P.leadingCoeff * (X - C 1 : R[X]).leadingCoeff ^ P.natDegree ≠ 0 := by
      rwa [leadingCoeff_X_sub_C, one_pow, mul_one]
    rw [← C_1, natDegree_comp_eq_of_mul_ne_zero hP, natDegree_X_sub_C, Nat.mul_one]

/-- For any polynomial `P`, we have `deg(P(X + 1)) = deg(P)`. -/
theorem natDegree_comp_X_add_one [Semiring R] (P : R[X]) :
    (P.comp (X + 1)).natDegree = P.natDegree := by
  by_cases hP : P.leadingCoeff = 0
  · rw [leadingCoeff_eq_zero.mp hP, zero_comp]
  · haveI : Nontrivial R := ⟨⟨P.leadingCoeff, 0, hP⟩⟩
    replace hP : P.leadingCoeff * (X + C 1 : R[X]).leadingCoeff ^ P.natDegree ≠ 0 := by
      rwa [leadingCoeff_X_add_C, one_pow, mul_one]
    rw [← C_1, natDegree_comp_eq_of_mul_ne_zero hP, natDegree_X_add_C, Nat.mul_one]

/-- For any polynomial `P`, we have `P ∘ (X - 1) ∘ (X + 1) = P`. -/
theorem comp_X_sub_one_comp_X_add_one [CommRing R] (P : R[X]) :
    (P.comp (X - 1)).comp (X + 1) = P := by
  rw [comp_assoc, sub_comp, X_comp, one_comp, add_sub_cancel_right, comp_X]

/-- For any polynomial `P`, we have `P ∘ (X + 1) ∘ (X - 1) = P`. -/
theorem comp_X_add_one_comp_X_sub_one [CommRing R] (P : R[X]) :
    (P.comp (X + 1)).comp (X - 1) = P := by
  rw [comp_assoc, add_comp, X_comp, one_comp, sub_add_cancel, comp_X]

/-- Division algorithm variant: every polynomial over `R` can be written as
  `Q(X + 1) X + c` for some polynomial `Q ∈ R[X]` and `c ∈ R`. -/
theorem division_algo_comp_add_one [CommRing R] (P : R[X]) :
    ∃ (Q : R[X]) (c : R), P = Q.comp (X + 1) * X + C c := by
  refine ⟨P.divX.comp (X - 1), P.coeff 0, ?_⟩
  rw [comp_X_sub_one_comp_X_add_one, divX_mul_X_add]

/-- For any polynomial `P`, we have `(P(X) X).divX = P`. -/
theorem divX_mul_X [Semiring R] (P : R[X]) : (P * X).divX = P := by
  have h : (P * X).divX * X + C ((P * X).coeff 0) = P * X := (P * X).divX_mul_X_add
  rw [coeff_zero_eq_eval_zero, eval_mul_X, mul_zero, C_0, add_zero] at h
  exact isRegular_X.right h

/-- For any polynomial `P` and constant `c`, we have `(P(X) X + c).divX = P`. -/
theorem divX_mul_X_add_C [Semiring R] (P : R[X]) (c : R) : (P * X + C c).divX = P := by
  rw [divX_add, divX_mul_X, divX_C, add_zero]

/-- If `deg(P(X) X + c) = n + 1`, then `deg(P) = n`. -/
theorem deg_mul_X_add_C_eq_add_one_imp [Semiring R]
    {P : R[X]} (h : (P * X + C c).natDegree = n + 1) : P.natDegree = n := by
  obtain rfl | hP : P = 0 ∨ P ≠ 0 := eq_or_ne _ _
  · rw [zero_mul, zero_add, natDegree_C] at h
    exact absurd h.symm (Nat.succ_ne_zero n)
  · haveI : Nontrivial R := ⟨⟨P.leadingCoeff, 0, leadingCoeff_ne_zero.mpr hP⟩⟩
    rwa [natDegree_add_C, natDegree_mul_X hP, Nat.succ_inj] at h

/-- If `deg(P(X + 1) X + c) = n + 1`, then `deg(P) = n`. -/
theorem deg_comp_X_add_one_mul_X_add_C_eq_add_one_imp [Semiring R]
    {P : R[X]} (h : (P.comp (X + 1) * X + C c).natDegree = n + 1) : P.natDegree = n :=
  (natDegree_comp_X_add_one P).symm.trans (deg_mul_X_add_C_eq_add_one_imp h)

/-- The zeroth coefficient of `P(X) X + c` is `c`. -/
theorem coeff_mul_X_add_C_zero [Semiring R] (P : R[X]) (c : R) :
    (P * X + C c).coeff 0 = c := by
  rw [coeff_add, coeff_mul_X_zero, zero_add, coeff_C_zero]

/-- The polynomial `X + 1` evaluated at `-1` is equal to zero. -/
theorem eval_neg_one_X_add_one [Ring R] : (X + 1 : R[X]).eval (-1) = 0 := by
  rw [eval_add, eval_X, eval_one, neg_add_cancel]

/-- The polynomial `X - 1` evaluated at `r` is equal to `r - 1`. -/
theorem eval_X_sub_one [Ring R] (r : R) : (X - 1 : R[X]).eval r = r - 1 := by
  rw [eval_sub, eval_X, eval_one]

/-- The polynomial `X + 1` maps to `X + 1` under any ring homomorphism. -/
theorem map_X_add_one [Semiring R] [Semiring S] (φ : R →+* S) :
    (X + 1).map φ = X + 1 := by
  rw [Polynomial.map_add, map_X, Polynomial.map_one]





/-! ### Part A: Companion polynomial and companion constant -/

section

variable [Ring R]

/-- The explicit companion of a polynomial. -/
noncomputable def companion (P : R[X]) : R[X] :=
  if hP : P.natDegree = 0 then 0
  else  let T : R[X] := P.divX.comp (X - 1)
        (companion T).comp (X + 1) * (X + 1) + C (T.coeff 0 + (companion T).eval (-1))
termination_by P.natDegree
decreasing_by calc (P.divX.comp (X - 1)).natDegree
  _ = P.divX.natDegree := natDegree_comp_X_sub_one _
  _ = P.natDegree - 1 := natDegree_divX_eq_natDegree_tsub_one
  _ < P.natDegree := Nat.sub_one_lt hP

/-- The companion constant of `P` is `P(0) + Q(-1)`, where `Q` is the companion of `P`. -/
noncomputable def companionConstant (P : R[X]) : R :=
  P.coeff 0 + (companion P).eval (-1)

/-- The companion of a degree zero polynomial. -/
theorem companion_of_natDegree_eq_zero {P : R[X]} (hP : P.natDegree = 0) :
    companion P = 0 := by
  rw [companion, dif_pos hP]

/-- The companion of a constant polynomial. -/
theorem companion_const (c : R) : companion (C c) = 0 :=
  companion_of_natDegree_eq_zero (natDegree_C c)

/-- The companion of zero. -/
theorem companion_zero : companion (0 : R[X]) = 0 :=
  companion_of_natDegree_eq_zero rfl

/-- Companion in terms of division by `X`. -/
theorem companion_general_formula (P : R[X]) :
    companion P = (companion (P.divX.comp (X - 1))).comp (X + 1) * (X + 1)
      + C ((P.divX.comp (X - 1)).coeff 0 + (companion (P.divX.comp (X - 1))).eval (-1)) := by
  ---- The formula is exactly the one given here if `P` is non-constant.
  obtain hP | hP : P.natDegree ≠ 0 ∨ P.natDegree = 0 := ne_or_eq _ _
  · rw [companion, dif_neg hP]
  ---- If `P` is constant, then it is easy to compute both sides to be zero.
  obtain ⟨c, rfl⟩ : ∃ c, P = C c := ⟨P.coeff 0, eq_C_of_natDegree_eq_zero hP⟩
  rw [companion_const, divX_C, zero_comp, companion_zero, zero_comp,
    zero_mul, zero_add, coeff_zero, eval_zero, add_zero, C_0]

end


section

variable [CommRing R]

/-- Formula for the companion of `R(X + 1) X + c`. -/
theorem companion_X_mul_comp_add_one_add_const (Q : R[X]) (c : R) :
    companion (Q.comp (X + 1) * X + C c)
      = (companion Q).comp (X + 1) * (X + 1) + C (companionConstant Q) := by
  rw [companionConstant, companion_general_formula,
    divX_mul_X_add_C, comp_X_add_one_comp_X_sub_one]

/-- The formula characterizing the companion polynomial. -/
theorem companion_main_formula (P : R[X]) :
    companion P * X = P + (companion P).comp (X - 1) - C (companionConstant P) := by
  unfold companionConstant
  induction hP : P.natDegree generalizing P with
  | zero =>
      rw [companion_of_natDegree_eq_zero hP, zero_mul, zero_comp, add_zero,
        eval_zero, add_zero, ← eq_C_of_natDegree_eq_zero hP, sub_self]
  | succ n n_ih =>
      obtain ⟨Q, c, rfl⟩ : ∃ (Q : R[X]) (c : R), P = Q.comp (X + 1) * X + C c :=
        division_algo_comp_add_one P
      replace hP : Q.natDegree = n := deg_comp_X_add_one_mul_X_add_C_eq_add_one_imp hP
      replace n_ih :
          companion Q * X = Q + (companion Q).comp (X - 1) - C (companionConstant Q) :=
        n_ih Q hP
      replace hP : companion (Q.comp (X + 1) * X + C c) = Q.comp (X + 1) + companion Q := by
        rw [companion_X_mul_comp_add_one_add_const, ← mul_X_comp, n_ih, sub_comp,
          C_comp, sub_add_cancel, add_comp, comp_X_sub_one_comp_X_add_one]
      rw [hP, add_mul, add_assoc, add_sub_assoc, add_right_inj, coeff_mul_X_add_C_zero,
        C_add, add_sub_add_left_eq_sub, add_comp, comp_X_add_one_comp_X_sub_one, eval_add,
        eval_comp, eval_neg_one_X_add_one, n_ih, ← coeff_zero_eq_eval_zero]; rfl

/-- Another formula related to the companion polynomial. -/
theorem companion_second_formula (P : R[X]) :
    companion P * X - (companion P).comp (X - 1) + C (companionConstant P) = P := by
  rw [companion_main_formula, sub_right_comm, sub_add_cancel, add_sub_cancel_right]

end


section

variable [CommRing R] [CommRing S] (φ : R →+* S) (P : R[X])

/-- Mapping companion polynomial under ring homomorphism. -/
theorem map_companion : companion (P.map φ) = (companion P).map φ := by
  induction hP : P.natDegree generalizing P with
  | zero =>
      have hP0 : (P.map φ).natDegree = 0 :=
        Nat.eq_zero_of_le_zero (natDegree_map_le.trans_eq hP)
      rw [companion_of_natDegree_eq_zero hP, Polynomial.map_zero,
        companion_of_natDegree_eq_zero hP0]
  | succ n n_ih =>
      obtain ⟨Q, c, rfl⟩ : ∃ (Q : R[X]) (c : R), P = Q.comp (X + 1) * X + C c :=
        division_algo_comp_add_one P
      replace hP : Q.natDegree = n := deg_comp_X_add_one_mul_X_add_C_eq_add_one_imp hP
      replace n_ih : companion (Q.map φ) = (companion Q).map φ := n_ih Q hP
      replace hP : companionConstant (Q.map φ) = φ (companionConstant Q) := by
        unfold companionConstant
        rw [n_ih, coeff_map, φ.map_add, ← eval_map_apply, φ.map_neg, φ.map_one]
      calc companion ((Q.comp (X + 1) * X + C c).map φ)
        _ = companion ((Q.map φ).comp (X + 1) * X + C (φ c)) := by
          rw [Polynomial.map_add, map_C, Polynomial.map_mul, map_comp, map_X_add_one, map_X]
        _ = ((companion Q).map φ).comp (X + 1) * (X + 1) + C (φ (companionConstant Q)) := by
          rw [companion_X_mul_comp_add_one_add_const, n_ih, hP]
        _ = ((companion Q).comp (X + 1) * (X + 1) + C (companionConstant Q)).map φ := by
          rw [Polynomial.map_add, map_C, Polynomial.map_mul, map_comp, map_X_add_one]
        _ = (companion (Q.comp (X + 1) * X + C c)).map φ := by
          rw [companion_X_mul_comp_add_one_add_const]

/-- Mapping companion constant under ring homomorphism. -/
theorem map_companionConstant : companionConstant (P.map φ) = φ (companionConstant P) := by
  unfold companionConstant
  rw [map_companion, coeff_map, φ.map_add, ← eval_map_apply, φ.map_neg, φ.map_one]

end





/-! ### Part B: Good polynomials and relation with companion constant -/

/-- An integer polynomial `P` is called *good* if there exists a sequence `(a_n)_{n ≥ 0}`
  of integers such that `n a_n = a_{n - 1} + P(n)` for all `n ≥ 1`. -/
def good (P : ℤ[X]) :=
  ∃ a : ℕ → ℤ, ∀ n : ℕ, (n + 1 : ℕ) * a (n + 1) = a n + P.eval ((n + 1 : ℕ) : ℤ)


section

open Finset

/-- For any `n : ℕ`, we have `0! + 1! + … + (n - 1)! ≤ n!`. -/
theorem sum_factorial_range_le_factorial (n) :
    ∑ i ∈ range n, i.factorial ≤ n.factorial := by
  ---- Separate the case `n = 0`.
  cases n with | zero => exact Nat.zero_le 1 | succ n => ?_
  ---- Induction on the rest; the base case is trivial.
  induction n with | zero => exact Nat.le_refl 1 | succ n n_ih => ?_
  ---- The induction step.
  calc ∑ i ∈ range (n + 2), i.factorial
    _ = ∑ i ∈ range (n + 1), i.factorial + (n + 1).factorial := sum_range_succ _ _
    _ ≤ (n + 1).factorial + (n + 1).factorial := Nat.add_le_add_right n_ih _
    _ = 2 * (n + 1).factorial := (Nat.two_mul _).symm
    _ ≤ (n + 2) * (n + 1).factorial := Nat.mul_le_mul_right _ (Nat.le_add_left _ _)

/-- For any `n : ℕ`, we have `0! + 1! + … + n! ≤ 2n!`. -/
theorem sum_factorial_range_succ_le_two_mul_factorial (n) :
    ∑ i ∈ range (n + 1), i.factorial ≤ 2 * n.factorial :=
  calc ∑ i ∈ range (n + 1), i.factorial
  _ = ∑ i ∈ range n, i.factorial + n.factorial := sum_range_succ _ _
  _ ≤ n.factorial + n.factorial :=
    Nat.add_le_add_right (sum_factorial_range_le_factorial n) _
  _ = 2 * n.factorial := (Nat.two_mul _).symm

/-- If `n! ∣ x + (0! + 1! + … + (n - 1)!) y` for all `n`, then `y = 0`. -/
theorem right_eq_zero_of_factorial_dvd_add_sum_factorial_mul
    {x y : ℤ} (h : ∀ n : ℕ, (n.factorial : ℤ) ∣ x + (∑ i ∈ range n, i.factorial : ℕ) * y) :
    y = 0 := by
  ---- Indeed, we have `x + (0! + 1! + … + n!) y = 0` if `n ≥ N := |x| + 2|y|`.
  let N : ℕ := x.natAbs + 2 * y.natAbs
  replace h {n : ℕ} (hn : N ≤ n) : x + (∑ i ∈ range (n + 1), i.factorial : ℕ) * y = 0 := by
    -- ... which follows from `|x + (0! + 1! + … + n!) y| < (n + 1)!`.
    refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (h (n + 1)) ?_
    have hn0 : 0 < n.factorial := n.factorial_pos
    calc (x + (∑ i ∈ range (n + 1), i.factorial : ℕ) * y).natAbs
      _ ≤ x.natAbs + ((∑ i ∈ range (n + 1), i.factorial : ℕ) * y).natAbs :=
        Int.natAbs_add_le _ _
      _ = x.natAbs + (∑ i ∈ range (n + 1), i.factorial) * y.natAbs := by
        rw [Int.natAbs_mul, Int.natAbs_natCast]
      _ ≤ n.factorial * x.natAbs + 2 * n.factorial * y.natAbs :=
        Nat.add_le_add (Nat.le_mul_of_pos_left _ hn0)
          (Nat.mul_le_mul_right _ (sum_factorial_range_succ_le_two_mul_factorial n))
      _ = N * n.factorial := by rw [Nat.mul_right_comm, Nat.mul_comm, Nat.add_mul]
      _ < (n + 1) * n.factorial := Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_of_le hn) hn0
  ---- And thus taking `n = N` and `n = N + 1` gives `y = 0`.
  have h0 : x + (∑ i ∈ range (N + 1), i.factorial : ℕ) * y = 0 := h (Nat.le_refl N)
  replace h : x + (∑ i ∈ range (N + 2), i.factorial : ℕ) * y = 0 := h (Nat.le_succ N)
  rwa [sum_range_succ, Int.natCast_add, Int.add_mul, ← Int.add_assoc, h0, Int.zero_add,
    Int.mul_eq_zero, Int.natCast_eq_zero, or_iff_right (Nat.factorial_ne_zero _)] at h

/-- A polynomial `P` is good iff its companion constant `c` is zero. -/
theorem good_iff_companionConstant_eq_zero : good P ↔ companionConstant P = 0 := by
  /- First show that `Q` satisfies the recursion of `(a_n)_{n ≥ 0}`...
    minus a constant: `(n + 1) Q(n + 1) = Q(n) + P(n + 1) - c`. -/
  let Q : ℤ[X] := companion P
  set c : ℤ := companionConstant P
  have hP (n : ℕ) :
      (n + 1 : ℕ) * Q.eval ((n + 1 : ℕ) : ℤ)
        = Q.eval (n : ℤ) + P.eval ((n + 1 : ℕ) : ℤ) - c := by
    rw [Int.mul_comm, ← eval_mul_X, companion_main_formula, eval_sub, eval_C, eval_add,
      Int.add_comm, eval_comp, eval_X_sub_one, Nat.cast_succ, Int.add_sub_cancel]
  ---- Thus `←` is free if `c = 0`.
  refine Iff.symm ⟨λ hP0 ↦ ⟨λ n ↦ Q.eval (n : ℤ), λ n ↦ ?_⟩, λ hP0 ↦ ?_⟩
  · dsimp only; rw [hP, hP0, sub_zero]
  ---- For `→`, start with `(n + 1) b_{n + 1} = b_n + c` where `b_n = a_n - Q(n)`.
  rcases hP0 with ⟨a, ha⟩
  let b (n : ℕ) : ℤ := a n - Q.eval (n : ℤ)
  replace ha (n : ℕ) : (n + 1 : ℕ) * b (n + 1) = b n + c := by
    rw [Int.mul_sub, ha, hP, ← sub_add, add_sub_add_right_eq_sub]
  ---- By induction on `n`, we have `n! b_n = b_0 + (0! + 1! + … + (n - 1)!) c`.
  replace ha (n : ℕ) : n.factorial * b n = b 0 + (∑ i ∈ range n, i.factorial : ℕ) * c := by
    induction n with
    | zero =>
        change 1 * b 0 = b 0 + 0 * c
        rw [Int.one_mul, Int.zero_mul, Int.add_zero]
    | succ n n_ih =>
        rw [Nat.factorial_succ, Int.natCast_mul, Int.mul_right_comm, ha, Int.mul_comm,
          Int.mul_add, n_ih, sum_range_succ, Int.natCast_add, Int.add_mul, Int.add_assoc]
  ---- In particular, `n! ∣ b_0 + (0! + 1! + … + (n - 1)!) c` for all `n`, forcing `c = 0`.
  replace ha (n) : (n.factorial : ℤ) ∣ b 0 + (∑ i ∈ range n, i.factorial : ℕ) * c :=
    ⟨b n, (ha n).symm⟩
  exact right_eq_zero_of_factorial_dvd_add_sum_factorial_mul ha

end





/-! ### Part C: Evaluating companion constant over `𝔽₄` -/

section

open Extra

/-- Over `𝔽₄ = 𝔽₂[ω]`, the companion constant of `P` is `P(ω)ω + P(ω + 1)(ω + 1)`. -/
theorem companionConstant_𝔽₄_value (P : 𝔽₄[X]) :
    P.eval 𝔽₄.X * 𝔽₄.X + P.eval 𝔽₄.Y * 𝔽₄.Y = companionConstant P :=
  let c : 𝔽₄ := companionConstant P
  let Q : 𝔽₄[X] := companion P
  calc P.eval 𝔽₄.X * 𝔽₄.X + P.eval 𝔽₄.Y * 𝔽₄.Y
  _ = (Q * X - Q.comp (X - 1) + C c).eval 𝔽₄.X * 𝔽₄.X
      + (Q * X - Q.comp (X - 1) + C c).eval 𝔽₄.Y * 𝔽₄.Y := by
    rw [companion_second_formula]
  _ = (Q.eval 𝔽₄.X * 𝔽₄.X - Q.eval 𝔽₄.Y + c) * 𝔽₄.X
      + (Q.eval 𝔽₄.Y * 𝔽₄.Y - Q.eval 𝔽₄.X + c) * 𝔽₄.Y := by
    refine congrArg₂ (· + ·) ?_ ?_
    all_goals rw [eval_add, eval_C, eval_sub, eval_comp, eval_X_sub_one, eval_mul_X]; rfl
  _ = Q.eval 𝔽₄.X * (𝔽₄.X * 𝔽₄.X - 𝔽₄.Y)
      + Q.eval 𝔽₄.Y * (𝔽₄.Y * 𝔽₄.Y - 𝔽₄.X)
      + c * (𝔽₄.X + 𝔽₄.Y) := by ring
  _ = Q.eval 𝔽₄.X * 0 + Q.eval 𝔽₄.Y * 0 + c * 1 := rfl
  _ = c := by rw [← add_mul, mul_zero, zero_add, mul_one]

/-- Final solution -/
theorem final_solution (k : ℕ) (hk : good (X ^ k)) : 3 ∣ k + 1 := by
  replace hk : companionConstant (X ^ k : 𝔽₄[X]) = 0 := calc
    _ = companionConstant ((X ^ k : ℤ[X]).map (Int.castRingHom 𝔽₄)) := by
      rw [Polynomial.map_pow, map_X]
    _ = 0 := by rw [map_companionConstant, good_iff_companionConstant_eq_zero.mp hk]; rfl
  rwa [← companionConstant_𝔽₄_value, eval_pow, eval_pow, eval_X, eval_X,
    ← pow_succ, ← pow_succ, 𝔽₄.X_pow_add_Y_pow_eq_zero_iff] at hk

end
