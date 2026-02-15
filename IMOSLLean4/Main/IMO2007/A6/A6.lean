/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# IMO 2007 A6

Let $R$ be a totally ordered commutative ring.
Let $n ≥ 5$ be a positive integer, and let $a_1, a_2, …, a_n ∈ R$
  be elements such that $a_1^2 + a_2^2 + … + a_n^2 = 1$.
Prove that $25 \sum_{i = 1}^n a_i^2 a_{i + 1} < 12$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2007SL.pdf).
In particular, we prove an even more general inequality:
$$ \left(3 \sum_{i = 1}^n a_i^2 a_{i + 1}\right)^2 ≤ 2 \left(\sum_{i = 1}^n a_i^2\right)^3. $$
However, one hole in an attempt to do the estimation in general is that the inequality
$$ 4 \sum_{i = 1}^n x_i x_{i + 1} ≤ \left(\sum_{i = 1}^n x_i\right)^2 $$
  for $x_1, …, x_n ≥ 0$ is nontrivial for odd $n$.
(This estimate correspond to the second "trivial" estimate in the official solution,
  although they are not directly the same for $n = 100$.)
We prove the above inequality for all $n ≥ 4$ by induction on $n$.
The base case $n = 4$ follows by AM-GM inequality;
  the left hand side is $(x_1 + x_3)(x_2 + x_4)$.

For the induction step, let $n ≥ 4$ and consider $x_1, …, x_{n + 1} ∈ R$ non-negative.
Without loss of generality, assume that $x_{n + 1} ≤ x_i$ for all $i ≤ n$.
For convenience, write $x_{n + 1} = c$ and $x_i = y_i + c$, $y_i ≥ 0$ for each $i ≤ n$.
Then we have
\begin{align*}
    4 \sum_{i = 1}^{n + 1} x_i x_{i + 1}
    &= 4 \sum_{i = 1}^{n - 1} (y_i + c)(y_{i + 1} + c) + 4 (y_n + y_1 + 2c) c \\
    &= 4 \sum_{i = 1}^{n - 1} y_i y_{i + 1} + 8c \sum_{i = 1}^n y_i + 4 (n + 1) c^2 \\
    &≤ 4 \sum_{i = 1}^n y_i y_{i + 1} + 8c \sum_{i = 1}^n y_i + 4 (n + 1) c^2,
\end{align*}
  where we set $y_{n + 1} = y_1$ (not $y_{n + 1} = 0$).
On the other hand, we have
\begin{align*}
  \left(\sum_{i = 1}^{n + 1} x_i\right)^2
  &= \left(\sum_{i = 1}^n y_i + (n + 1) c\right)^2
  &= \left(\sum_{i = 1}^n y_i\right)^2 + 2 (n + 1) c \sum_{i = 1}^n y_i + (n + 1)^2 c^2.
\end{align*}
Matching terms one by one completes the induction step,
  where we use induction hypothesis on $y_1, y_2, …, y_n$ on the first term.

In the implementation, we assume the smallest value among the $x_i$'s is $x_0$ instead.
-/

namespace IMOSL
namespace IMO2007A6

open Finset

/-! ### Extra lemmas on sums over `Fin` -/

theorem Fin_exists_minimal [LinearOrder α] (a : Fin (n + 1) → α) : ∃ j, ∀ i, a j ≤ a i :=
  (exists_min_image univ a univ_nonempty).imp λ _ ⟨_, h⟩ i ↦ h i (mem_univ i)

/-- We have `∑_i a_{k + i} = ∑_i a_i`, where the summation runs over `Fin n`. -/
theorem Fin_sum_add_left [NeZero n] [AddCommMonoid M] (a : Fin n → M) (k) :
    ∑ i, a (k + i) = ∑ i, a i :=
  Fintype.sum_equiv (Equiv.addLeft k) _ _ (λ _ ↦ rfl)

/-- We have `∑_i a_{i + k} = ∑_i a_i`, where the summation runs over `Fin n`. -/
theorem Fin_sum_add_right [NeZero n] [AddCommMonoid M] (a : Fin n → M) (k) :
    ∑ i, a (i + k) = ∑ i, a i :=
  Fintype.sum_equiv (Equiv.addRight k) _ _ (λ _ ↦ rfl)

open Fin.NatCast in
/-- Taking `Fin.castLE` is the same as casting the value into the higher `Fin`. -/
theorem Fin_castLE_eq_natCast_val [NeZero m] (h : n ≤ m) (i : Fin n) :
    i.castLE h = i.val := by
  rw [Fin.ext_iff, Fin.val_castLE, Fin.val_natCast, Nat.mod_eq_of_lt (i.2.trans_le h)]





/-! ### The big claim on bounding a cyclic sum `∑ x_i x_{i + 1}` -/

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Nice temporary definition -/
abbrev niceTuple (a : Fin (n + 1) → R) :=
  2 ^ 2 * ∑ i, a i * a (i + 1) ≤ (∑ i, a i) ^ 2

theorem niceTuple.of_four [ExistsAddOfLE R] (a : Fin 4 → R) : niceTuple a := by
  have h : (2 : R) ^ 2 = 4 := by norm_num
  rw [niceTuple, Fin.sum_univ_four, Fin.sum_univ_four, h]
  change 4 * (a 0 * a 1 + a 1 * a 2 + a 2 * a 3 + a 3 * a 0) ≤ _
  rw [mul_comm (a 0), ← mul_add, add_assoc, mul_comm (a 2), ← mul_add, add_comm (a 2),
    ← add_mul, ← mul_assoc, add_assoc, add_add_add_comm, add_comm (a 0 + a 2)]
  exact four_mul_le_sq_add _ _

theorem cyclic_add_right_formula (a : Fin (n + 1) → R) (c : R) :
    ∑ i, (a i + c) * (a (i + 1) + c)
      = ∑ i, a i * a (i + 1) + (2 * ∑ i, a i) * c + (n + 1) • c ^ 2 := by
  simp only [mul_add, add_mul, sum_add_distrib]
  rw [← sq, Fin.sum_const, ← add_assoc, add_left_inj, add_assoc, add_right_inj,
    ← mul_sum, ← sum_mul, mul_comm, ← add_mul, Fin_sum_add_right, ← two_mul]

theorem sum_sq_add_right_formula (a : Fin (n + 1) → R) (c : R) :
    (∑ i, (a i + c)) ^ 2
      = (∑ i, a i) ^ 2 + (n + 1) • ((2 * ∑ i, a i) * c) + (n + 1) ^ 2 • c ^ 2 := by
  rw [sum_add_distrib, Fin.sum_const, add_sq, nsmul_eq_mul, mul_left_comm,
    ← nsmul_eq_mul, add_right_inj, nsmul_eq_mul, mul_pow, Nat.cast_pow]

omit [IsStrictOrderedRing R] in
theorem niceTuple.of_add₁ {n} {a : Fin (n + 1) → R} (ha : niceTuple a) (j) :
    niceTuple (λ i ↦ a (i + j)) := by
  rw [niceTuple, Fin_sum_add_right]; simp only [add_right_comm _ 1 j]
  rw [Fin_sum_add_right (λ i ↦ a i * a (i + 1))]; exact ha

omit [IsStrictOrderedRing R] in
theorem niceTuple.of_add₁_iff {n} {a : Fin (n + 1) → R} {j} :
    niceTuple (λ i ↦ a (i + j)) ↔ niceTuple a := by
  refine ⟨λ h ↦ ?_, λ h ↦ h.of_add₁ j⟩
  replace h := h.of_add₁ (-j)
  simp only [neg_add_cancel_right] at h; exact h

theorem niceTuple.of_add₂ [ExistsAddOfLE R] (hn : 4 ≤ n + 1) (hc : 0 ≤ c)
    {a : Fin (n + 1) → R} (ha : niceTuple a) (ha0 : ∀ i, 0 ≤ a i) :
    niceTuple (λ i ↦ a i + c) := by
  rw [niceTuple, cyclic_add_right_formula, sum_sq_add_right_formula, mul_add, mul_add]
  have h : (2 : R) ^ 2 ≤ (n + 1 : ℕ) :=
    (Nat.cast_le.mpr hn).trans_eq' (by rw [Nat.cast_mul 2 2, sq, Nat.cast_two])
  refine add_le_add (add_le_add ha ?_) ?_
  · rw [nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right h
      (mul_nonneg (mul_nonneg zero_le_two (sum_nonneg λ i _ ↦ ha0 i)) hc)
  · rw [sq (n + 1), mul_nsmul, nsmul_eq_mul _ (_ • _)]
    exact mul_le_mul_of_nonneg_right h (nsmul_nonneg (sq_nonneg c) _)

omit [LinearOrder R] [IsStrictOrderedRing R] in
theorem cyclic_cons_zero_formula (a : Fin (n + 1) → R) :
    let b := Fin.cons 0 a
    ∑ i, b i * b (i + 1) = ∑ i ∈ ({Fin.last n} : Finset _)ᶜ, a i * a (i + 1) := by
  refine (sum_of_injOn Fin.succ ?_ ?_ ?_ ?_).symm
  · exact Set.injOn_of_injective (Fin.succ_injective _)
  · rw [coe_univ]; exact Set.mapsTo_univ _ _
  · rintro i - h
    obtain (rfl | rfl) : i = 0 ∨ i = Fin.last (n + 1) := by
      apply i.eq_zero_or_eq_succ.imp_right; rintro ⟨j, rfl⟩
      rw [coe_compl, coe_singleton, Set.mem_image] at h; simp only [Fin.succ_inj] at h
      rw [exists_eq_right, Set.mem_compl_iff, not_not, Set.mem_singleton_iff] at h
      rw [h, Fin.succ_last]
    · rw [Fin.cons_zero, zero_mul]
    · rw [Fin.last_add_one, Fin.cons_zero, mul_zero]
  · intro i h; refine congrArg₂ _ rfl ?_
    rw [mem_compl, mem_singleton, ← Ne, ← Fin.exists_castSucc_eq] at h
    rcases h with ⟨j, rfl⟩
    rw [Fin.coeSucc_eq_succ, Fin.succ_castSucc, Fin.coeSucc_eq_succ]; rfl

theorem niceTuple.of_zero_cons [ExistsAddOfLE R]
    {a : Fin (n + 1) → R} (ha : niceTuple a) (ha0 : ∀ i, 0 ≤ a i) :
    niceTuple (Fin.cons 0 a) := by
  rw [niceTuple, cyclic_cons_zero_formula, Fin.sum_cons, zero_add]
  refine (mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)).trans ha
  exact sum_le_univ_sum_of_nonneg λ i ↦ mul_nonneg (ha0 i) (ha0 (i + 1))

omit [IsStrictOrderedRing R] in
theorem Fin_cons_nonneg {a : Fin (n + 1) → R} (ha : ∀ i, 0 ≤ a i) (i) :
    0 ≤ (Fin.cons 0 a : _ → R) i := by
  obtain (rfl | ⟨j, rfl⟩) := i.eq_zero_or_eq_succ
  exacts [le_refl 0, ha j]

theorem niceTuple.of_three_le [ExistsAddOfLE R] :
    ∀ (n : ℕ) (_ : 3 ≤ n) {a : Fin n.succ → R} (_ : ∀ i, 0 ≤ a i), niceTuple a := by
  refine Nat.le_induction (λ _ ↦ of_four _) (λ n hn n_ih a ha ↦ ?_)
  wlog h : ∀ i, a 0 ≤ a i
  · obtain ⟨j, hj⟩ : ∃ j, ∀ i, a j ≤ a i := Fin_exists_minimal a
    exact of_add₁_iff.mp <| this _ hn n_ih (a := λ i ↦ a (i + j))
      (λ i ↦ ha _) (λ i ↦ (hj _).trans_eq' (congrArg a j.zero_add.symm))
  specialize ha 0
  obtain ⟨b, hb, h0⟩ : ∃ b : Fin (n + 1) → R,
      (∀ i, 0 ≤ b i) ∧ ∀ i, a i = (Fin.cons 0 b : _ → R) i + a 0 := by
    obtain ⟨b, hb⟩ : ∃ b : Fin n.succ → R, ∀ i, a i.succ = a 0 + b i :=
      Classical.axiom_of_choice λ i ↦ exists_add_of_le (h _)
    refine ⟨b, λ i ↦ ?_, λ i ↦ ?_⟩
    · rw [← le_add_iff_nonneg_right (a 0), ← hb]; exact h _
    · obtain (rfl | ⟨j, rfl⟩) := i.eq_zero_or_eq_succ
      · exact (zero_add _).symm
      · rw [hb, add_comm, Fin.cons_succ]
  clear h; generalize a 0 = c at ha h0
  obtain rfl : a = ((Fin.cons 0 b : _ → R) · + c) := funext h0
  exact of_add₂ (Nat.le_succ_of_le (Nat.succ_le_succ hn))
    ha (of_zero_cons (n_ih hb) hb) (Fin_cons_nonneg hb)

/-- The main claim with `Fin (n + 1)` instead of `Fin n`. -/
theorem main_ineq' [ExistsAddOfLE R]
    (hn : 4 ≤ n + 1) {a : Fin (n + 1) → R} (ha : ∀ i, 0 ≤ a i) :
    4 * ∑ i, a i * a (i + 1) ≤ (∑ i, a i) ^ 2 := by
  rw [← two_add_two_eq_four, ← two_mul, ← sq]
  exact niceTuple.of_three_le n (Nat.succ_le_succ_iff.mp hn) ha

/-- The inequality `4 ∑_i x_i x_{i + 1} ≤ (∑_i x_i)^2`. -/
theorem main_ineq
    [ExistsAddOfLE R] [NeZero n] (hn : 4 ≤ n) {x : Fin n → R} (hx : ∀ i, 0 ≤ x i) :
    4 * ∑ i, x i * x (i + 1) ≤ (∑ i, x i) ^ 2 := by
  cases n with
  | zero => exact absurd (Nat.succ_pos 3) hn.not_gt
  | succ n => exact main_ineq' hn hx





/-! ### Start of the problem -/

open Fin.NatCast in
omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The identity
  `∑_i (x_i^2 + 2 x_i (x_{i + 1} + x_{i + 2})) = ∑_i x_{i + 2} ∑_{j < 5} x_{i + j}`. -/
theorem main_identity [NeZero n] (hn : 5 ≤ n) (x : Fin n → R) :
    ∑ i, (x i ^ 2 + 2 * x i * (x (i + 1) + x (i + 1 + 1)))
      = ∑ i, x (i + 2) * ∑ j : Fin 5, x (i + j.castLE hn) := by
  ---- Rearrange appropriately.
  calc ∑ i, (x i ^ 2 + 2 * x i * (x (i + 1) + x (i + 1 + 1)))
    _ = ∑ i, (x i ^ 2 + 2 * x i * (x (i + 1) + x (i + 2))) := by
      conv_lhs => right; ext i; rw [add_assoc, one_add_one_eq_two]
    _ = ∑ i, (x (i + 2) * x i + x (i + 1) * x i + x i * x i
        + x i * x (i + 1) + x i * x (i + 2)) :=
      Fintype.sum_congr _ _ λ _ ↦ by ring
    _ = ∑ i, x (i + 2) * x i + ∑ i, x (i + 1) * x i + ∑ i, x i * x i
        + ∑ i, x i * x (i + 1) + ∑ i, x i * x (i + 2) := by
      iterate 4 rw [sum_add_distrib]
    _ = ∑ i, x (i + 2) * x (i + 0) + ∑ i, x (i + 2) * x (i + 1) + ∑ i, x (i + 2) * x (i + 2)
        + ∑ i, x (i + 2) * x (i + 3) + ∑ i, x (i + 2) * x (i + 4) := ?_
    _ = ∑ i, x (i + 2) * x (i + Fin.castLE hn 0)
        + ∑ i, x (i + 2) * x (i + Fin.castLE hn 1)
        + ∑ i, x (i + 2) * x (i + Fin.castLE hn 2)
        + ∑ i, x (i + 2) * x (i + Fin.castLE hn 3)
        + ∑ i, x (i + 2) * x (i + Fin.castLE hn 4) := by
      simp only [Fin_castLE_eq_natCast_val]; rfl
    _ = ∑ i, x (i + 2) * ∑ j : Fin 5, x (i + j.castLE hn) := by
      simp_rw [Fin.sum_univ_five, mul_add, sum_add_distrib]
  ---- Now equate term-by-term.
  refine congrArg₂ _ (congrArg₂ _ (congrArg₂ _ (congrArg₂ _ ?_ ?_) ?_) ?_) ?_
  ---- Term `0`: `∑_i x_{i + 2} x_i = ∑_i x_{i + 2} x_{i + 0}`.
  · simp only [add_zero]
  ---- Term `1`: `∑_i x_{i + 1} x_i = ∑_i x_{i + 2} x_{i + 1}`.
  · calc ∑ i, x (i + 1) * x i
      _ = ∑ i, x (i + 1 + 1) * x (i + 1) := (Fin_sum_add_right _ 1).symm
      _ = ∑ i, x (i + 2) * x (i + 1) := by simp_rw [add_assoc, one_add_one_eq_two]
  ---- Term `2`: `∑_i x_i x_i = ∑_i x_{i + 2} x_{i + 2}`.
  · exact (Fin_sum_add_right _ 2).symm
  ---- Term `3`: `∑_i x_i x_{i + 1} = ∑_i x_{i + 2} x_{i + 3}`.
  · calc ∑ i, x i * x (i + 1)
      _ = ∑ i, x (i + 2) * x (i + 2 + 1) := (Fin_sum_add_right _ 2).symm
      _ = ∑ i, x (i + 2) * x (i + 3) := by simp_rw [add_assoc, two_add_one_eq_three]
  ---- Term `4`: `∑_i x_i x_{i + 2} = ∑_i x_{i + 2} x_{i + 4}`.
  · calc ∑ i, x i * x (i + 2)
      _ = ∑ i, x (i + 2) * x (i + 2 + 2) := (Fin_sum_add_right _ 2).symm
      _ = ∑ i, x (i + 2) * x (i + 4) := by simp_rw [add_assoc, two_add_two_eq_four]

/-- The general result `(3 ∑_i a_i^2 a_{i + 1})^2 ≤ 2 (∑_i a_i^2)^3`. -/
theorem general_result [ExistsAddOfLE R] [NeZero n] (hn : 5 ≤ n) (a : Fin n → R) :
    (3 * ∑ i, a i ^ 2 * a (i + 1)) ^ 2 ≤ 2 * (∑ i, a i ^ 2) ^ 3 := by
  /- Prove `(3 ∑_i a_i^2 a_{i + 1})^2 ≤ (∑_i a_i^2)(∑_i (a_i^2 + 2 a_{i + 1} a_{i + 2})^2)`.
    Thus we only need to prove `∑_i (a_i^2 + 2 a_{i + 1} a_{i + 2})^2 ≤ 2 (∑_i a_i^2)^2`. -/
  calc (3 * ∑ i, a i ^ 2 * a (i + 1)) ^ 2
    _ = (∑ i, a i ^ 2 * a (i + 1) + 2 * ∑ i, a i ^ 2 * a (i + 1)) ^ 2 := by
      rw [add_comm, ← add_one_mul, two_add_one_eq_three]
    _ = (∑ i, a i ^ 2 * a (i + 1) + 2 * ∑ i, a (i + 1) ^ 2 * a (i + 1 + 1)) ^ 2 :=
      congrArg ((∑ i, a i ^ 2 * a (i + 1) + 2 * ·) ^ 2) (Fin_sum_add_right _ 1).symm
    _ = (∑ i, (a i ^ 2 * a (i + 1) + 2 * (a (i + 1) ^ 2 * a (i + 1 + 1)))) ^ 2 := by
      rw [sum_add_distrib, mul_sum]
    _ = (∑ i, a (i + 1) * (a i ^ 2 + 2 * a (i + 1) * a (i + 1 + 1))) ^ 2 :=
      congrArg (· ^ 2) (Fintype.sum_congr _ _ λ i ↦ by ring)
    _ ≤ (∑ i, a (i + 1) ^ 2) * (∑ i, (a i ^ 2 + 2 * a (i + 1) * a (i + 1 + 1)) ^ 2) :=
      sum_mul_sq_le_sq_mul_sq _ _ _
    _ ≤ (∑ i, a (i + 1) ^ 2) * (2 * (∑ i, a i ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left ?_ (Fintype.sum_nonneg λ _ ↦ sq_nonneg _)
    _ = (∑ i, a i ^ 2) * (2 * (∑ i, a i ^ 2) ^ 2) :=
      congrArg (· * _) (Fin_sum_add_right (λ i ↦ a i ^ 2) 1)
    _ = 2 * (∑ i, a i ^ 2) ^ 3 := by rw [mul_left_comm, ← pow_succ']
  /- Now break up LHS into `∑_i (a_i^4 + 4 a_i^2 a_{i + 1} a_{i + 2})` and
    `4 ∑_{i + 1} a_i^2 a_{i + 1}^2 ≤ (∑_i a_i^2)^2`, so it remains to show that
    `∑_i (a_i^4 + 4 a_i^2 a_{i + 1} a_{i + 2}) ≤ (∑_i a_i^2)^2`. -/
  calc ∑ i, (a i ^ 2 + 2 * a (i + 1) * a (i + 1 + 1)) ^ 2
    _ = ∑ i, ((a i ^ 2) ^ 2 + 2 * a i ^ 2 * (2 * a (i + 1) * a (i + 1 + 1))
        + 4 * (a (i + 1) ^ 2 * a (i + 1 + 1) ^ 2)) :=
      Fintype.sum_congr _ _ λ _ ↦ by ring
    _ = ∑ i, ((a i ^ 2) ^ 2 + 2 * a i ^ 2 * (2 * a (i + 1) * a (i + 1 + 1)))
        + 4 * ∑ i, a (i + 1) ^ 2 * a (i + 1 + 1) ^ 2 := by
      rw [sum_add_distrib, mul_sum]
    _ = ∑ i, ((a i ^ 2) ^ 2 + 2 * a i ^ 2 * (2 * a (i + 1) * a (i + 1 + 1)))
        + 4 * ∑ i, a i ^ 2 * a (i + 1) ^ 2 :=
      congrArg (_ + ·) <| congrArg (4 * ·) <|
        Fin_sum_add_right (λ i ↦ a i ^ 2 * a (i + 1) ^ 2) 1
    _ ≤ (∑ i, a i ^ 2) ^ 2 + (∑ i, a i ^ 2) ^ 2 :=
      add_le_add ?_ (main_ineq (Nat.le_of_lt hn) (λ _ ↦ sq_nonneg _))
    _ = 2 * (∑ i, a i ^ 2) ^ 2 := (two_mul _).symm
  /- Finally, prove `∑_i (a_i^4 + 4 a_i^2 a_{i + 1} a_{i + 2}) ≤ (∑_i a_i^2)^2`. -/
  calc ∑ i, ((a i ^ 2) ^ 2 + 2 * a i ^ 2 * (2 * a (i + 1) * a (i + 1 + 1)))
    _ ≤ ∑ i, ((a i ^ 2) ^ 2 + 2 * a i ^ 2 * (a (i + 1) ^ 2 + a (i + 1 + 1) ^ 2)) :=
      sum_le_sum λ i _ ↦ add_le_add_right (a := (a i ^ 2) ^ 2) <|
        mul_le_mul_of_nonneg_left (two_mul_le_add_sq _ _)
          (mul_nonneg zero_le_two (sq_nonneg _))
    _ = ∑ i, a (i + 2) ^ 2 * ∑ j : Fin 5, a (i + j.castLE hn) ^ 2 :=
      main_identity hn _
    _ = ∑ i, a (i + 2) ^ 2 * ∑ j ∈ image (Fin.castLE hn) univ, a (i + j) ^ 2 :=
      Fintype.sum_congr _ _ λ i ↦ congrArg (_ * ·)
        (sum_image (f := λ j ↦ a (i + j) ^ 2)
          (Set.injOn_of_injective (Fin.castLE_injective hn))).symm
    _ ≤ ∑ i, a (i + 2) ^ 2 * ∑ j, a (i + j) ^ 2 :=
      sum_le_sum λ _ _ ↦ mul_le_mul_of_nonneg_left
        (sum_le_univ_sum_of_nonneg λ _ ↦ sq_nonneg _) (sq_nonneg _)
    _ = ∑ i, a (i + 2) ^ 2 * ∑ j, a j ^ 2 :=
      Fintype.sum_congr _ _ λ i ↦ congrArg (_ * ·) (Fin_sum_add_left (λ j ↦ a j ^ 2) i)
    _ = ∑ i, a i ^ 2 * ∑ j, a j ^ 2 :=
      Fin_sum_add_right (λ i ↦ a i ^ 2 * ∑ j, a j ^ 2) 2
    _ = (∑ i, a i ^ 2) ^ 2 := by rw [sq, sum_mul]

/-- Final solution -/
theorem final_solution [ExistsAddOfLE R] [NeZero n] (hn : 5 ≤ n)
    {a : Fin n → R} (ha : ∑ i, a i ^ 2 = 1) :
    25 * ∑ i, a i ^ 2 * a (i + 1) < 12 := by
  refine lt_of_pow_lt_pow_left₀ 2 (Nat.ofNat_nonneg 12) ?_
  calc (25 * ∑ i, a i ^ 2 * a (i + 1)) ^ 2
    _ = 25 ^ 2 * (∑ i, a i ^ 2 * a (i + 1)) ^ 2 := mul_pow _ _ _
    _ ≤ 70 * 3 ^ 2 * (∑ i, a i ^ 2 * a (i + 1)) ^ 2 := by
      have h : (25 ^ 2 : R) ≤ 70 * 3 ^ 2 := calc
        _ ≤ (25 ^ 2 : R) + 5 := le_add_of_nonneg_right (Nat.ofNat_nonneg 5)
        _ = 70 * 3 ^ 2 := by norm_num
      exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
    _ = 70 * (3 * ∑ i, a i ^ 2 * a (i + 1)) ^ 2 := by rw [mul_assoc, mul_pow]
    _ ≤ 70 * (2 * (∑ i, a i ^ 2) ^ 3) :=
      mul_le_mul_of_nonneg_left (general_result hn a) (Nat.ofNat_nonneg 70)
    _ = 70 * 2 := by rw [ha, one_pow, mul_one]
    _ < 70 * 2 + 4 := lt_add_of_pos_right _ four_pos
    _ = 12 ^ 2 := by norm_num
