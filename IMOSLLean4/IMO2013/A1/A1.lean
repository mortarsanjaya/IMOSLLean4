/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Matrix.Notation
import Mathlib.Algebra.BigOperators.Fin

/-!
# IMO 2013 A1

Let $R$ be a commutative ring.
Given $a_1, …, a_n ∈ R$, we define $f(a_1, a_2, …, a_n)$ as follows:

Let $u_0 = u_1 = 1$, and define $u_{k + 2} = u_{k + 1} + a_k u_k$ for each $0 ≤ k < n$.
Then set $$f(a_1, a_2, …, a_n) = u_{n + 1}. $$

Prove that, for any $a_1, a_2, a_3, …, a_n ∈ R$, we have
$$ f(a_1, a_2, …, a_n) = f(a_n, a_{n - 1}, …, a_1). $$
-/

namespace IMOSL
namespace IMO2013A1

open List Matrix
open scoped Matrix

/-! ### Extra stuffs -/

/-- `![1, 0]` -/
abbrev oneZeroVec (R) [Zero R] [One R] : Fin 2 → R := ![1, 0]



section NoncommRing

variable [Ring R]

theorem matrix_fin2_mulVec (M : Matrix (Fin 2) (Fin 2) R) (v : Fin 2 → R) (b : Fin 2) :
    M.mulVec v b = M b 0 * v 0 + M b 1 * v 1 :=
  vec2_dotProduct (M b) v

theorem matrix_fin2_vecMul (v : Fin 2 → R) (M : Matrix (Fin 2) (Fin 2) R) (b : Fin 2) :
    vecMul v M b = v 0 * M 0 b + v 1 * M 1 b :=
  vec2_dotProduct v _





/-! ### Main Definition -/

def f_aux : List R → R × R
  | [] => (1, 1)
  | r :: l => let (a, b) := f_aux l; (a + r * b, a)

theorem f_aux_nil : f_aux ([] : List R) = (1, 1) := rfl

theorem f_aux_cons (r : R) (l : List R) :
    f_aux (r :: l) = ((f_aux l).1 + r * (f_aux l).2, (f_aux l).1) := rfl

/-- The main function -/
def f (l : List R) : R := (f_aux l).1



/-! ### Alternative calculation 1 -/

/-- The matrix `M_r` as in the LaTeX document -/
def M (r : R) : Matrix (Fin 2) (Fin 2) R := !![1 + r, -r; r, -r]

def f_aux_alt1 (l : List R) : Fin 2 → R := foldr (λ r ↦ (M r).mulVec) (oneZeroVec R) l

theorem f_aux_alt1_nil : f_aux_alt1 nil = oneZeroVec R := rfl

theorem f_aux_alt1_cons (r : R) (l : List R) :
    f_aux_alt1 (r :: l) = (M r).mulVec (f_aux_alt1 l) := rfl

theorem f_aux_alt1_prod_description :
    ∀ l : List R, f_aux_alt1 l = (l.map M).prod.mulVec (oneZeroVec R) := by
  refine List.rec (one_mulVec (oneZeroVec R)).symm λ r l h ↦ ?_
  rw [map_cons, prod_cons, f_aux_alt1_cons, h, mulVec_mulVec]

theorem f_aux_matrix_description1 :
    ∀ l : List R, f_aux l = (f_aux_alt1 l 0, f_aux_alt1 l 0 - f_aux_alt1 l 1) := by
  refine List.rec (Prod.ext rfl (sub_zero 1).symm) λ r l h ↦ ?_
  rw [f_aux_cons, f_aux_alt1_cons, h, Prod.mk_inj,
    matrix_fin2_mulVec, matrix_fin2_mulVec, M]
  simp only [of_apply, cons_val_one, cons_val_zero]
  refine ⟨?_, ?_⟩
  · rw [one_add_mul, neg_mul, add_assoc, ← sub_eq_add_neg, mul_sub]
  · rw [add_sub_add_right_eq_sub, one_add_mul, add_sub_cancel_right]

theorem f_description1 (l : List R) : f l = f_aux_alt1 l 0 :=
  congrArg Prod.fst (f_aux_matrix_description1 l)



/-! ### Alternative calculation 2 -/

def f_aux_alt2 (l : List R) : Fin 2 → R :=
  foldr (λ r v ↦ vecMul v (M r)) (oneZeroVec R) l

theorem f_aux_alt2_nil : f_aux_alt2 nil = oneZeroVec R := rfl

theorem f_aux_alt2_cons (r : R) (l : List R) :
    f_aux_alt2 (r :: l) = vecMul (f_aux_alt2 l) (M r) := rfl

theorem f_aux_alt2_prod_description :
    ∀ l : List R, f_aux_alt2 l = vecMul (oneZeroVec R) (l.reverse.map M).prod := by
  refine List.rec (vecMul_one (oneZeroVec R)).symm λ r l h ↦ ?_
  rw [f_aux_alt2_cons, reverse_cons, map_append, map_singleton,
    prod_append, prod_singleton, h, vecMul_vecMul]

end NoncommRing


section CommRing

variable [CommRing R]

theorem f_aux_matrix_description2 :
    ∀ l : List R, f_aux l = (f_aux_alt2 l 0, f_aux_alt2 l 0 + f_aux_alt2 l 1) := by
  refine List.rec (Prod.ext rfl (add_zero 1).symm) λ r l h ↦ ?_
  rw [f_aux_cons, f_aux_alt2_cons, h, Prod.mk_inj,
    matrix_fin2_vecMul, matrix_fin2_vecMul, M]
  simp only [of_apply, cons_val_one, cons_val_zero]
  refine ⟨?_, ?_⟩
  · rw [mul_comm, add_mul, mul_one_add, add_assoc]
  · rw [← add_mul, mul_one_add, add_assoc (f_aux_alt2 l 0),
      ← add_mul, mul_neg, add_neg_cancel_right]

theorem f_description2 (l : List R) : f l = f_aux_alt2 l 0 :=
  congrArg Prod.fst (f_aux_matrix_description2 l)





/-! ### Final solution -/

/-- Final solution -/
theorem final_solution (l : List R) : f l.reverse = f l := by
  rw [f_description2, f_aux_alt2_prod_description, reverse_reverse, matrix_fin2_vecMul,
    f_description1, f_aux_alt1_prod_description, oneZeroVec, matrix_fin2_mulVec]
  simp
