/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Multiset.Basic

/-!
# IMO 2014 C4

Consider 4 types of skew-tetrominoes in $ℕ^2$, classified by its orientation.
Let $S ⊆ ℕ^2$ be a multiset, and suppose that it can be partitioned into skew-tetrominos.
Prove that the parity of the number of skew-tetrominoes used per
  each type in the partition does not depend on the partition.
-/

namespace IMOSL
namespace IMO2014C4

open Multiset

/-- Base skew-tetrominoes. -/
def BaseSkewT4 : Fin 4 → Multiset (ℕ × ℕ)
  | 1 => {(0, 0), (1, 0), (1, 1), (2, 1)}
  | 2 => {(1, 0), (1, 1), (0, 1), (0, 2)}
  | 3 => {(0, 1), (1, 1), (1, 0), (2, 0)}
  | 4 => {(0, 0), (0, 1), (1, 1), (1, 2)}

/-- Skew-tetrominoes, parametrized by coordinate and type. -/
def SkewT4 (q : Fin 4 × ℕ × ℕ) : Multiset (ℕ × ℕ) := (BaseSkewT4 q.1).map λ p ↦ q.2 + p





/-!
### Theory of weight on skew-tetrominoes

The theory is built with minimizing the number of results used in mind.
Certainly, more lemmas would be added if the theory is intended to be developed fully.
-/

/-- Weight of a multiset of lattice points, parametrized by two base weights -/
def weight (w : ℕ × ℕ) (S : Multiset (ℕ × ℕ)) : ℕ := (S.map λ p ↦ w.1 ^ p.1 * w.2 ^ p.2).sum

theorem weight_cons (w v S) : weight w (v ::ₘ S) = w.1 ^ v.1 * w.2 ^ v.2 + weight w S := by
  unfold weight; rw [map_cons, sum_cons]

theorem weight_add (w S T) : weight w (S + T) = weight w S + weight w T := by
  unfold weight; rw [Multiset.map_add, sum_add]

theorem weight_sum (w) (P : Multiset (Multiset (ℕ × ℕ))) :
    weight w P.sum = (P.map (weight w)).sum :=
  Multiset.induction_on P rfl λ p P h ↦ by rw [sum_cons, weight_add, h, map_cons, sum_cons]

/-- `(x, y)`-weight of a translated multiset -/
theorem weight_translate (w s S) :
    weight w (S.map λ p ↦ s + p) = w.1 ^ s.1 * w.2 ^ s.2 * weight w S := by
  refine Multiset.induction_on S rfl λ p S h ↦ ?_
  rw [map_cons, weight_cons, weight_cons, Nat.mul_add, ← h,
    Nat.mul_mul_mul_comm, ← Nat.pow_add, ← Nat.pow_add]; rfl

/-- Explicit weight-based skew-tetromino filter -/
def T4Filter : Fin 4 → ℕ × ℕ
  | 1 => (13, 3)
  | 2 => (3, 5)
  | 3 => (5, 3)
  | 4 => (3, 13)

/-- Filtered weight of base skew-tetromino mod `32` -/
theorem weight_T4Filter_BaseSkewT4_mod32 :
    ∀ i j, weight (T4Filter i) (BaseSkewT4 j) % 32 = 16 * if i = j then 1 else 0
  | 1, 1 => rfl
  | 1, 2 => rfl
  | 1, 3 => rfl
  | 1, 4 => rfl
  | 2, 1 => rfl
  | 2, 2 => rfl
  | 2, 3 => rfl
  | 2, 4 => rfl
  | 3, 1 => rfl
  | 3, 2 => rfl
  | 3, 3 => rfl
  | 3, 4 => rfl
  | 4, 1 => rfl
  | 4, 2 => rfl
  | 4, 3 => rfl
  | 4, 4 => rfl

theorem T4Filter_fst_mod2 : ∀ i, (T4Filter i).1 % 2 = 1
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl

theorem T4Filter_snd_mod2 : ∀ i, (T4Filter i).2 % 2 = 1
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl

/-- Filtered weight of skew-tetromino mod `32` -/
theorem weight_T4Filter_SkewT4_mod32 (i q) :
    weight (T4Filter i) (SkewT4 q) % 32 = 16 * if i = q.1 then 1 else 0 := by
  rw [SkewT4, weight_translate, ← Nat.mul_mod_mod, weight_T4Filter_BaseSkewT4_mod32]
  split_ifs
  · rw [Nat.mul_one, Nat.mul_mod_mul_right 16 _ 2, ← Nat.mod_mul_mod,
      Nat.pow_mod, T4Filter_fst_mod2, Nat.one_pow, ← Nat.mul_mod_mod,
      Nat.pow_mod, T4Filter_snd_mod2, Nat.one_pow]
  · rw [Nat.mul_zero, Nat.zero_mod]

theorem weight_T4Filter_sum_SkewT4_mod32 (i : Fin 4) (P : Multiset (Fin 4 × ℕ × ℕ)) :
    weight (T4Filter i) (P.map SkewT4).sum % 32 = 16 * ((P.map Prod.fst).count i % 2) := by
  rw [weight_sum, map_map, sum_nat_mod, map_map]
  simp only [Function.comp_apply, weight_T4Filter_SkewT4_mod32]
  refine Multiset.induction_on P rfl λ p P h ↦ ?_
  rw [map_cons, sum_cons, ← Nat.add_mod_mod, h, ← Nat.mul_add, add_comm,
    Nat.mul_mod_mul_left 16 _ 2, Nat.mod_add_mod, map_cons, count_cons]





/-! ### Final solution -/

/-- Final solution -/
theorem final_solution (h : (map SkewT4 P).sum = (map SkewT4 Q).sum) (i : Fin 4) :
    (P.map Prod.fst).count i % 2 = (Q.map Prod.fst).count i % 2 := by
  rw [← Nat.mul_right_inj (Nat.succ_ne_zero 15), ← weight_T4Filter_sum_SkewT4_mod32,
    ← weight_T4Filter_sum_SkewT4_mod32, h]
