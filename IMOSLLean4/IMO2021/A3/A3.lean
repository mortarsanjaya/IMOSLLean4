/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Size
import Mathlib.Order.Bounds.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# IMO 2021 A3

Find the smallest possible value of
$$ \sum_{j = 1}^n \left\lfloor \frac{a_j}{j} \right\rfloor $$
  across all permutations $(a_1, a_2, \ldots, a_n)$ of $(1, 2, \ldots, n)$.

### TODO

Remove occurrence of `Nat.size` and use `Nat.log2` instead.
Also, remove occurrence of `List.iota` and work around the problems.
-/

namespace IMOSL
namespace IMO2021A3

open List

def targetSum : List ℕ → ℕ
  | [] => 0
  | a :: l => a / (a :: l).length + targetSum l



/-! ### Lower bound -/

theorem succ_le_mul_two_pow_div (a) (h : 0 < b) : a + 1 ≤ 2 ^ (a / b) * b :=
  Nat.lt_mul_of_div_lt (a / b).lt_two_pow_self h

theorem prod_map_succ_iota : ∀ n : ℕ, ((iota n).map Nat.succ).prod = (n + 1).factorial
  | 0 => rfl
  | n + 1 => prod_cons.trans <| congr_arg₂ _ rfl (prod_map_succ_iota n)

theorem targetSum_general_lower_bound :
    ∀ l : List ℕ, (l.map Nat.succ).prod ≤ 2 ^ targetSum l * l.length.factorial
  | [] => Nat.le_refl 1
  | a :: l => by
      rw [map_cons, prod_cons, targetSum, pow_add,
        length_cons, Nat.factorial_succ, mul_mul_mul_comm]
      exact Nat.mul_le_mul (succ_le_mul_two_pow_div a l.length.succ_pos)
        (targetSum_general_lower_bound l)

theorem targetSum_perm_iota_n_lower_bound (h : l ~ iota n) : n.size ≤ targetSum l := by
  have h0 := targetSum_general_lower_bound l
  rw [(h.map Nat.succ).prod_eq, h.length_eq, prod_map_succ_iota, length_iota] at h0
  exact Nat.size_le.mpr (Nat.le_of_mul_le_mul_right h0 n.factorial_pos)



/-! ### Construction -/

/-- The main construction -/
def lowerBoundMk : ℕ → List ℕ :=
  Nat.binaryRec [] λ b n l ↦ match b, n with
    | false, 0 => l
    | false, k + 1 => (iota k).map (k + 1).add ++ (2 * k + 2) :: l
    | true, n => (iota n).map n.add ++ (2 * n + 1) :: l

lemma lowerBoundMk_zero : lowerBoundMk 0 = [] :=
  Nat.binaryRec_zero _ _

lemma lowerBoundMk_bit0_succ (k : ℕ) :
    lowerBoundMk ((k + 1).bit false)
      = (iota k).map (k + 1).add ++ (2 * k + 2) :: lowerBoundMk (k + 1) :=
  Nat.binaryRec_eq _ _ (by simp)

lemma lowerBoundMk_bit1 (n : ℕ) :
    lowerBoundMk (n.bit true) = (iota n).map n.add ++ (2 * n + 1) :: lowerBoundMk n :=
  Nat.binaryRec_eq _ _ (by simp)

theorem iota_map_add_append_iota_eq_iota (n : ℕ) :
    ∀ k, (iota k).map n.add ++ iota n = iota (n + k)
  | 0 => rfl
  | k+1 => by rw [iota_succ, map_cons, cons_append]
              exact congr_arg₂ _ rfl (iota_map_add_append_iota_eq_iota n k)

theorem lowerBoundMk_perm_iota : ∀ n : ℕ, lowerBoundMk n ~ iota n :=
  Nat.binaryRec (Perm.of_eq lowerBoundMk_zero) λ b n ↦ match b, n with
    | false, 0 => id
    | false, k + 1 => λ h ↦ by
        rw [lowerBoundMk_bit0_succ, Nat.bit_false]
        refine perm_middle.trans (((h.append_left _).trans ?_).cons _)
        rw [iota_map_add_append_iota_eq_iota, add_right_comm, ← two_mul]
        exact Perm.refl _
    | true, n => λ h ↦ by
        rw [lowerBoundMk_bit1, Nat.bit_true]
        refine perm_middle.trans (((h.append_left _).trans ?_).cons _)
        rw [iota_map_add_append_iota_eq_iota, ← two_mul]

lemma lowerBoundMk_length (n : ℕ) : (lowerBoundMk n).length = n :=
  (lowerBoundMk_perm_iota n).length_eq.trans (length_iota n)

lemma targetSum_map_add_iota_length_succ (h : l.length = Nat.succ n) :
    ∀ k, targetSum ((iota k).map n.add ++ l) = targetSum l
  | 0 => rfl
  | k + 1 => by
      rw [iota_succ, map_cons, cons_append, targetSum, length_cons,
        targetSum_map_add_iota_length_succ h k, Nat.add_eq_right]
      refine Nat.div_eq_of_lt ?_
      rw [length_append, length_map, length_iota, h]
      exact (congr_arg (· + 2) (n.add_comm k)).le

theorem lowerBoundMk_targetSum : ∀ n : ℕ, targetSum (lowerBoundMk n) = n.size :=
  have X := Nat.succ_pos 1
  have X0 m : m ≤ 2 * m := Nat.le_mul_of_pos_left m X
  Nat.binaryRec (by rw [lowerBoundMk_zero, targetSum, Nat.size_zero]) λ b n ↦ match b, n with
    | false, 0 => id
    | false, k + 1 => λ h ↦ by
        have h0 : ((2 * k + 2) :: lowerBoundMk (k + 1)).length = (k + 1).succ :=
          congr_arg Nat.succ (lowerBoundMk_length (k + 1))
        have X1 : 2 * k.succ ≠ 0 := Nat.mul_ne_zero (Nat.succ_ne_zero 1) k.succ_ne_zero
        rw [lowerBoundMk_bit0_succ, Nat.size_bit (by exact X1),
          (k + 1).size.succ_eq_add_one, targetSum_map_add_iota_length_succ h0,
          targetSum, h0, h, add_comm, Nat.add_right_inj]
        exact Nat.div_eq_of_lt_le
          ((one_mul _).trans_le <| Nat.add_le_add_right (X0 _) 2)
          (Nat.mul_lt_mul_of_pos_left (k + 1).lt_succ_self X)
    | true, n => λ h ↦ by
        have h0 : ((2 * n + 1) :: lowerBoundMk n).length = n.succ :=
          congr_arg Nat.succ (lowerBoundMk_length n)
        rw [lowerBoundMk_bit1, Nat.size_bit (by exact (2 * n).succ_ne_zero),
          targetSum_map_add_iota_length_succ h0, targetSum, h0, h,
          n.size.succ_eq_add_one, add_comm, Nat.add_right_inj]
        exact Nat.div_eq_of_lt_le
          ((one_mul _).trans_le <| Nat.succ_le_succ (X0 _)) (Nat.le_refl _)





/-! ## Final solution -/

/-- Final solution. Note: the answer `Nat.size n` is equal to $⌈\log_2 (n + 1)⌉$. -/
theorem final_solution :
    IsLeast (targetSum '' {l : List ℕ | l ~ iota n}) n.size :=
  ⟨⟨lowerBoundMk n, lowerBoundMk_perm_iota n, lowerBoundMk_targetSum n⟩,
  λ _ h ↦ h.elim λ _ h ↦ (targetSum_perm_iota_n_lower_bound h.1).trans_eq h.2⟩
