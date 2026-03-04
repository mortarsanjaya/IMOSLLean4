/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.ALgebra.BigOperators.Group.Multiset.Basic
import Mathlib.Algebra.Order.Ring.Nat

/-!
# IMO 2014 C2

Let $m$ be a positive integer.
On the board, $2^m$ copies of $1$ is written.
At any time, we can perform the following operation: choose two numbers on the board,
  say $a$ and $b$, and replace them with two copies of $a + b$.
Prove that after $m 2^{m - 1}$ operations,
  the sum of the numbers on the board is at least $4^m$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2014SL.pdf).
The board is modelled as a multiset of non-negative integers.
We say that a pair $(M, N)$ of multisets *good* if
  we can obtain $N$ from $M$ by applying one operation.
-/

namespace IMOSL
namespace IMO2014C2

open Multiset

/-! ### Extra lemmas -/

/-- If `n ≤ |M|`, then there exists a sub-multiset of `M` of cardinality `n`. -/
theorem exists_le_card_eq_of_card_le {M : Multiset α} (hnM : n ≤ M.card) :
    ∃ S ≤ M, S.card = n := by
  ---- Induction on `M`; the base case `M = ∅` is trivial.
  induction M using Multiset.induction with
  | empty => exact ⟨0, zero_le _, (Nat.eq_zero_of_le_zero hnM).symm⟩
  | cons a M M_ih => ?_
  ---- If `|{a} + M| = n`, then pick `S = {a} + M`.
  obtain h | h : (a ::ₘ M).card = n ∨ n < (a ::ₘ M).card := hnM.eq_or_lt'
  · exact ⟨a ::ₘ M, le_refl _, h⟩
  ---- Otherwise, if `|{a} + M| > n`, then `|M| ≥ n`; apply induction hypothesis on `M`.
  rw [card_cons, Nat.lt_add_one_iff] at h
  obtain ⟨S, hSM, hSn⟩ : ∃ S ≤ M, S.card = n := M_ih h
  exact ⟨S, hSM.trans (M.le_cons_self a), hSn⟩

/-- AM-GM inequality on multisets whose size is a power of `2`.
  Using Cauchy induction (see `Nat.cauchy_induction_two_mul`), it is possible to
  lift the assumption on the size of the multiset, but we are not doing that. -/
theorem AM_GM_Multiset_Nat_card_eq_two_pow {M : Multiset ℕ} (h : M.card = 2 ^ n) :
    (2 ^ n) ^ (2 ^ n) * M.prod ≤ M.sum ^ (2 ^ n) := by
  ---- Induction on `n`; the base case `n = 0`, `|M| = 1`, is trivial.
  induction n generalizing M with | zero => ?_ | succ n n_ih => ?_
  · obtain ⟨k, rfl⟩ : ∃ k, M = {k} := card_eq_one.mp h
    rw [Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.pow_one, prod_singleton, sum_singleton]
  ---- For the induction step, first break `M` into two subsets of equal size, say `S + T`.
  replace h : M.card = 2 ^ n + 2 ^ n := by rw [h, Nat.pow_succ, Nat.mul_two]
  obtain ⟨S, hT, hS⟩ : ∃ S ≤ M, S.card = 2 ^ n :=
    exists_le_card_eq_of_card_le ((Nat.le_add_right _ _).trans_eq h.symm)
  obtain ⟨T, rfl⟩ : ∃ T, M = S + T := Multiset.le_iff_exists_add.mp hT
  replace hT : T.card = 2 ^ n := by rwa [card_add, hS, Nat.add_right_inj] at h
  clear h
  ---- Now do the calculations.
  calc (2 ^ (n + 1)) ^ 2 ^ (n + 1) * (S + T).prod
    _ = (4 * (2 ^ n * 2 ^ n)) ^ (2 ^ n) * (S + T).prod := by
      rw [Nat.pow_succ', Nat.pow_mul, Nat.mul_pow, ← Nat.pow_two]
    _ = 4 ^ (2 ^ n) * (((2 ^ n) ^ (2 ^ n) * S.prod) * ((2 ^ n) ^ (2 ^ n) * T.prod)) := by
      rw [Nat.mul_pow, Nat.mul_pow, Nat.mul_assoc, prod_add, mul_mul_mul_comm]
    _ ≤ 4 ^ (2 ^ n) * (S.sum ^ (2 ^ n) * T.sum ^ (2 ^ n)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul (n_ih hS) (n_ih hT))
    _ = (4 * S.sum * T.sum) ^ (2 ^ n) := by rw [Nat.mul_assoc, Nat.mul_pow, Nat.mul_pow]
    _ ≤ ((S.sum + T.sum) ^ 2) ^ (2 ^ n) := Nat.pow_le_pow_left (four_mul_le_sq_add _ _) _
    _ = (S + T).sum ^ 2 ^ (n + 1) := by rw [sum_add, Nat.pow_succ' (n := n), Nat.pow_mul]





/-! ### Start of the problem -/

/-- A pair `(M, N)` of multisets over `ℕ` is called `good` if there exists a multiset
  `T` and `a, b : ℕ` such that `M = {a, b} + T` and `N = {a + b, a + b} + T`. -/
def good (M N : Multiset ℕ) := ∃ T a b, M = {a, b} + T ∧ N = {a + b, a + b} + T


namespace good

/-- If `(M, N)` is good. then `|M| = |N|`. -/
theorem card_eq (h : good M N) : M.card = N.card := by
  rcases h with ⟨T, a, b, rfl, rfl⟩
  iterate 2 rw [card_add, card_pair]

/-- Let `M_0, …, M_n` be multisets such that `(M_i, M_{i + 1})` is good for each `i`.
  If `|M_0| = k`, then `|M_n| = k`. -/
theorem chain_card_eq (hMl : List.IsChain good (M :: l)) (hMk : M.card = k) :
    ((M :: l).getLast (l.cons_ne_nil M)).card = k := by
  induction l generalizing M with
  | nil => exact hMk
  | cons N l l_ih => exact l_ih hMl.of_cons (hMl.rel.card_eq.symm.trans hMk)

/-- If `(M, N)` is good, then `4 ∏_{x ∈ M} x ≤ ∏_{x ∈ N} x`. -/
theorem four_mul_prod_le (h : good M N) : 4 * M.prod ≤ N.prod := by
  rcases h with ⟨T, a, b, rfl, rfl⟩
  rw [prod_add, prod_pair, prod_add, prod_pair,
    ← Nat.mul_assoc, ← Nat.mul_assoc, ← Nat.pow_two]
  exact Nat.mul_le_mul_right _ (four_mul_le_pow_two_add a b)

/-- Let `M_0, …, M_n` be multisets such that `(M_i, M_{i + 1})` is good for each `i`.
  Then `4^n ∏_{x ∈ M_0} x ≤ ∏_{x ∈ M_n} x`. -/
theorem chain_four_pow_prod_le (hMl : List.IsChain good (M :: l)) :
    4 ^ l.length * M.prod ≤ ((M :: l).getLast (l.cons_ne_nil M)).prod := by
  ---- Induction on `l`, where the base case `l = []` is trivial.
  induction l generalizing M with
  | nil => exact Nat.le_of_eq (Nat.one_mul _)
  | cons N l l_ih => ?_
  ---- For the induction step, we just do calculations.
  calc 4 ^ (l.length + 1) * M.prod
    _ = 4 ^ l.length * (4 * M.prod) := Nat.mul_assoc _ _ _
    _ ≤ 4 ^ l.length * N.prod := Nat.mul_le_mul_left _ hMl.rel.four_mul_prod_le
    _ ≤ ((N :: l).getLast (List.cons_ne_nil _ _)).prod := l_ih hMl.of_cons
    _ = ((M :: N :: l).getLast (List.cons_ne_nil _ _)).prod :=
      congrArg prod (List.getLast_cons _).symm

end good


/-- Final solution -/
theorem final_solution {m l} (hm : m > 0) (hlm : l.length = m * 2 ^ (m - 1))
    (hlm0 : List.IsChain good (replicate (2 ^ m) 1 :: l)) :
    4 ^ m ≤ ((replicate (2 ^ m) 1 :: l).getLast (l.cons_ne_nil _)).sum := by
  ---- Let `M` be the multiset of `2^n` copies of `1` and `L` be the final multiset.
  set M : Multiset ℕ := replicate (2 ^ m) 1
  set L : Multiset ℕ := (M :: l).getLast (l.cons_ne_nil _)
  ---- Since `∏_{x ∈ M} x = 1`, we have `∏_{x ∈ L} x ≥ (2^m)^{2^m}`.
  have h : (2 ^ m) ^ (2 ^ m) ≤ L.prod := calc
    _ = 4 ^ l.length * M.prod := by
      rw [prod_replicate, Nat.one_pow, Nat.mul_one, hlm, ← Nat.pow_mul,
        ← Nat.pow_mul 2 2, Nat.mul_left_comm, ← Nat.pow_add_one', Nat.sub_add_cancel hm]
    _ ≤ L.prod := good.chain_four_pow_prod_le hlm0
  ---- Since `|L| = |M| = 2^m`, by AM-GM we get `4^m = 2^m 2^m ≤ ∑_{x ∈ L} x`.
  replace h : (4 ^ m) ^ (2 ^ m) ≤ L.sum ^ (2 ^ m) := calc
    _ = (2 ^ m) ^ (2 ^ m) * (2 ^ m) ^ (2 ^ m) := by rw [Nat.mul_pow 2 2, Nat.mul_pow]
    _ ≤ (2 ^ m) ^ (2 ^ m) * L.prod := Nat.mul_le_mul_left _ h
    _ ≤ L.sum ^ (2 ^ m) :=
      AM_GM_Multiset_Nat_card_eq_two_pow (good.chain_card_eq hlm0 (card_replicate _ _))
  exact (Nat.pow_le_pow_iff_left (Nat.two_pow_pos _).ne.symm).mp h
