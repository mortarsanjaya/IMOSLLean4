/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# IMO 2009 C5

Let $r$ be a positive real number.
Five nonnegative real numbers are written on the board,
  say $x_0, x_1, x_2, x_3, x_4$, in a cyclic order.
The initial state of the board is $x_0 = x_1 = x_2 = x_3 = x_4 = 0$.

Two players, A and B, take turns rewriting the board, with player A going first.
* During A's turn, he replaces the real numbers $x_0, x_1, x_2, x_3, x_4$ on the board
  with $x_0 + y_0, …, x_4 + y_4$, where $y_0, …, y_4 ≥ 0$ and $y_0 + … + y_4 = r$.
* During B's turn, he chooses an index $i$ and resets $x_i$ and $x_{i + 1}$ to $0$,
  where we define $x_5 = x_0$ for convenience.

Player B loses whenever one of the real numbers on the board is greater than $2r$.
Can player B avoid losing?

### Answer

Yes.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
The invariant condition is as follows: there exists an index $i$ such that
  $x_{i + 2} + x_{i + 4} ≤ r$, $x_{i + 3} ≤ r$, and $x_i = x_{i + 1} = 0$
  (before A's turn) or $x_i, x_{i + 1} ≤ 2r$ (before B's turn).
The predicate `IMOSL.IMO2009C5.GameState.good` implements this invariant.
-/

namespace IMOSL
namespace IMO2009C5

variable [AddCommMonoid G]

/-- The state of a game. -/
structure GameState [Preorder G] (r : G) (hr : r ≥ 0) where
  board : Fin 5 → G
  board_nonneg i : board i ≥ 0


namespace GameState

/-- The initial state of the board. -/
def init [Preorder G] (r : G) (hr : r ≥ 0) : GameState r hr where
  board _ := 0
  board_nonneg _ := le_refl 0



/-! ### Possible moves of the player A -/

/-- The possible moves of player A. -/
structure AMove [Preorder G] [AddLeftMono G] (r : G) (hr : r ≥ 0) where
  y : Fin 5 → G
  y_nonneg i : y i ≥ 0
  y_sum : ∑ i, y i = r

/-- Applying A's move. -/
def applyAMove [Preorder G] [AddLeftMono G] {r : G} {hr : r ≥ 0}
    (X : GameState r hr) (A : AMove r hr) : GameState r hr where
  board i := X.board i + A.y i
  board_nonneg i := add_nonneg (X.board_nonneg i) (A.y_nonneg i)

/-- Player A's move adds to each number by at most `r`. -/
theorem AMove.y_le_r [PartialOrder G] [AddLeftMono G] {r : G} {hr : r ≥ 0}
    (A : AMove r hr) (i) : A.y i ≤ r :=
  calc A.y i
  _ ≤ ∑ j, A.y j := Finset.single_le_sum (λ i _ ↦ A.y_nonneg i) (Finset.mem_univ _)
  _ = r := A.y_sum




/-! ### Possible moves of the player B -/

section

variable [Preorder G]

/-- The possible moves of player B. -/
structure BMove (r : G) (hr : r ≥ 0) where
  index : Fin 5


section

variable {r : G} {hr : r ≥ 0} (X : GameState r hr) (B : BMove r hr)

/-- Applying B's move. -/
def applyBMove : GameState r hr where
  board i := if i = B.index ∨ i = B.index + 1 then 0 else X.board i
  board_nonneg i := by split_ifs; exacts [le_refl 0, X.board_nonneg i]

/-- The number `x_i` after B's move indexed `i`. -/
theorem applyBMove_board_index : (X.applyBMove B).board B.index = 0 :=
  if_pos (Or.inl rfl)

/-- The number `x_{i + 1}` after B's move indexed `i`. -/
theorem applyBMove_board_index_add_one : (X.applyBMove B).board (B.index + 1) = 0 :=
  if_pos (Or.inr rfl)

/-- The number `x_{i + 2}` after B's move indexed `i`. -/
theorem applyBMove_board_index_add_two :
    (X.applyBMove B).board (B.index + 2) = X.board (B.index + 2) := by
  refine if_neg ?_
  rw [add_eq_left, add_right_inj]
  decide

/-- The number `x_{i + 3}` after B's move indexed `i`. -/
theorem applyBMove_board_index_add_three :
    (X.applyBMove B).board (B.index + 3) = X.board (B.index + 3) := by
  refine if_neg ?_
  rw [add_eq_left, add_right_inj]
  decide

/-- The number `x_{i + 4}` after B's move indexed `i`. -/
theorem applyBMove_board_index_add_four :
    (X.applyBMove B).board (B.index + 4) = X.board (B.index + 4) := by
  refine if_neg ?_
  rw [add_eq_left, add_right_inj]
  decide

end



/-! ### Lost state and losing state -/

/-- A state is "lost" if at least one number on the board is greater than `2r`. -/
def isLost {r : G} {hr : r ≥ 0} (X : GameState r hr) := ∃ i, 2 • r < X.board i

/-- A state is "losing" if B cannot avoid going into a lost state.
  The boolean input is `true` if A has the next turn and `false` otherwise. -/
inductive isLosing [AddLeftMono G] {r : G} {hr : r ≥ 0} :
    (X : GameState r hr) → (isPlayerATurn : Bool) → Prop
  | ofLost (X : GameState r hr) (hX : isLost X) (b : Bool) : isLosing X b
  | ofAMove (X : GameState r hr) (A : AMove r hr) (hXA : isLosing (X.applyAMove A) false) :
      isLosing X true
  | ofBMove (X : GameState r hr) (hX : ∀ B, isLosing (X.applyBMove B) true) :
      isLosing X false



/-! ### Good state -/

/-- A good state is a state satisfying the main invariant. -/
def good {r : G} {hr : r ≥ 0} (X : GameState r hr) (b : Bool) : Prop :=
  ∃ i, (X.board (i + 2) + X.board (i + 4) ≤ r) ∧ X.board (i + 3) ≤ r
    ∧ bif b then X.board i = 0 ∧ X.board (i + 1) = 0
      else X.board i ≤ 2 • r ∧ X.board (i + 1) ≤ 2 • r

/-- The initial state is good. -/
theorem init_is_good [AddLeftMono G] {r : G} {hr : r ≥ 0} (isPlayerATurn) :
    good (GameState.init r hr) isPlayerATurn := by
  refine ⟨0, (zero_add 0).trans_le hr, hr, ?_⟩
  cases isPlayerATurn with | true => exact ⟨rfl, rfl⟩ | false => ?_
  have hr2 : 2 • r ≥ 0 := nsmul_nonneg hr 2
  exact ⟨hr2, hr2⟩

/-- A good state is not lost. -/
theorem good.not_isLost [AddLeftMono G] {r : G} {hr : r ≥ 0}
    {X : GameState r hr} (hX : good X isPlayerATurn) : ¬isLost X := by
  rcases hX with ⟨i, h24, h3, h01⟩
  ---- First of all, we must have `x_i ≤ 2r` and `x_{i + 1} ≤ 2r`.
  replace h01 : X.board i ≤ 2 • r ∧ X.board (i + 1) ≤ 2 • r := by
    cases isPlayerATurn with | false => exact h01 | true => ?_
    have hr2 : 2 • r ≥ 0 := nsmul_nonneg hr 2
    exact ⟨h01.1.trans_le hr2, h01.2.trans_le hr2⟩
  have h0 : X.board (i + 0) ≤ 2 • r := (add_zero i).symm ▸ h01.1
  ---- Suppose that `x_j = x_{i + (j - i)} > 2r` for some `j`.
  rintro ⟨j, h⟩; revert h
  suffices X.board (i + (j - i)) ≤ 2 • r from (add_sub_cancel i j ▸ this).not_gt
  ---- Then bashing out all the possible values of `j - i` yield a contradiction.
  have hr2 : r ≤ 2 • r := calc
    _ ≤ r + r := le_add_of_nonneg_right hr
    _ = 2 • r := (two_nsmul r).symm
  replace h24 : X.board (i + 2) + X.board (i + 4) ≤ 2 • r := h24.trans hr2
  match j - i with
    | 0 => exact h0
    | 1 => exact h01.2
    | 2 => exact (le_add_of_nonneg_right (X.board_nonneg _)).trans h24
    | 3 => exact h3.trans hr2
    | 4 => exact (le_add_of_nonneg_left (X.board_nonneg _)).trans h24

/-- If a state is good before B's turn, then some move of B preserve goodness. -/
theorem good.exists_BMove {r : G} {hr : r ≥ 0} {X : GameState r hr} (hX : good X false) :
    ∃ B, good (X.applyBMove B) true := by
  rcases hX with ⟨B_index, h24, h3, h01⟩
  refine ⟨⟨B_index⟩, B_index, ?_, ?_, ?_⟩
  · rwa [applyBMove_board_index_add_two, applyBMove_board_index_add_four]
  · rwa [applyBMove_board_index_add_three]
  · rw [cond_true, applyBMove_board_index, applyBMove_board_index_add_one, and_self]

end


section

variable [LinearOrder G] [IsOrderedAddMonoid G] [AddLeftStrictMono G] {r : G} {hr : r ≥ 0}

/-- If a state is good before A's turn, then any move of A preserve goodness. -/
theorem good.forall_AMove {X : GameState r hr} (hX : good X true) (A : AMove r hr) :
    good (X.applyAMove A) false := by
  set Z : GameState r hr := X.applyAMove A
  /- Choose an index`i` with `x_{i + 2} + x_{i + 4} ≤ r`,
    `x_{i + 3} ≤ r`, and `x_i = x_{i + 1} = 0`. -/
  rcases hX with ⟨i, hi24, hi3, hi0, hi1⟩
  ---- Note that `z_{i + 3} ≤ 2r`, where `z_j = x_j + y_j` for each `j`.
  replace hi3 : Z.board (i + 3) ≤ 2 • r :=
    calc X.board (i + 3) + A.y (i + 3)
    _ ≤ r + r := add_le_add hi3 (A.y_le_r _)
    _ = 2 • r := (two_nsmul r).symm
  ---- Next, we have either `z_{i + 4} + z_{i + 1} ≤ r` or `z_i + z_{i + 2} ≤ r`.
  have h : (Z.board (i + 4) + Z.board (i + 1)) + (Z.board i + Z.board (i + 2)) ≤ 2 • r := by
    -- Note that `(y_{i + 4} + y_{i + 1}) + (y_i + y_{i + 2}) + y_{i + 3} = r`.
    have h : (A.y (i + 4) + A.y (i + 1)) + (A.y i + A.y (i + 2)) + A.y (i + 3) = r := calc
      _ = A.y (i + 0) + A.y (i + 1) + A.y (i + 2) + A.y (i + 3) + A.y (i + 4) := by
        rw [add_zero, add_add_add_comm, add_assoc _ (A.y i), add_rotate, ← add_assoc]
      _ = ∑ j, A.y (i + j) := (Fin.sum_univ_five (λ j ↦ A.y (i + j))).symm
      _ = ∑ j, A.y j := Fintype.sum_equiv (Equiv.addLeft i) _ _ λ _ ↦ rfl
      _ = r := A.y_sum
    -- Just remove the `y_{i + 3}` and we are done.
    calc ((X.board (i + 4) + A.y (i + 4)) + (X.board (i + 1) + A.y (i + 1)))
        + ((X.board i + A.y i) + (X.board (i + 2) + A.y (i + 2)))
    _ = ((X.board (i + 4) + X.board (i + 1)) + (A.y (i + 4) + A.y (i + 1)))
        + ((X.board i + X.board (i + 2)) + (A.y i + A.y (i + 2))) := by
      apply congrArg₂ (· + ·) <;> exact add_add_add_comm _ _ _ _
    _ = ((X.board (i + 4) + X.board (i + 1))) + (X.board i + X.board (i + 2))
        + ((A.y (i + 4) + A.y (i + 1)) + (A.y i + A.y (i + 2))) :=
      add_add_add_comm _ _ _ _
    _ = (X.board (i + 2) + X.board (i + 4))
        + ((A.y (i + 4) + A.y (i + 1)) + (A.y i + A.y (i + 2))) := by
      rw [hi0, hi1, add_zero, zero_add, add_comm (X.board (i + 4))]
    _ ≤ r + (((A.y (i + 4) + A.y (i + 1)) + (A.y i + A.y (i + 2))) + A.y (i + 3)) :=
      add_le_add hi24 (le_add_of_nonneg_right (A.y_nonneg _))
    _ = 2 • r := by rw [h, two_nsmul]
  ---- Thus either `z_{i + 4} + z_{i + 1} ≤ r` or `z_i + z_{i + 2} ≤ r`.
  replace h : Z.board (i + 4) + Z.board (i + 1) ≤ r ∨ Z.board i + Z.board (i + 2) ≤ r := by
    contrapose! h; exact two_nsmul r ▸ add_lt_add h.1 h.2
  rcases h with hi41 | hi02
  ---- If `z_{i + 4} + z_{i + 1} ≤ r` then index `i + 2` works.
  · refine ⟨i + 2, ?_, ?_, ?_, ?_⟩
    -- Check `z_{i + 4} + z_{i + 1} ≤ r`.
    · rwa [add_assoc, add_assoc]
    -- Check `z_i ≤ r`.
    · calc Z.board (i + 2 + 3)
        _ = X.board i + A.y i := congrArg Z.board ((add_assoc i 2 3).trans (add_zero i))
        _ = A.y i := by rw [hi0, zero_add]
        _ ≤ r := A.y_le_r _
    -- Check `z_{i + 2} ≤ 2r`.
    · replace hi24 : X.board (i + 2) ≤ r :=
        le_of_add_le_of_nonneg_left hi24 (X.board_nonneg _)
      calc X.board (i + 2) + A.y (i + 2)
        _ ≤ r + r := add_le_add hi24 (A.y_le_r _)
        _ = 2 • r := (two_nsmul r).symm
    -- Check `z_{i + 3} ≤ 2r`.
    · rwa [add_assoc]
  ---- If `z_i + z_{i + 2} ≤ r` then index `i + 3` works.
  · refine ⟨i + 3, ?_, ?_, ?_, ?_⟩
    -- Check `z_i + z_{i + 2} ≤ r`.
    · calc Z.board (i + 3 + 2) + Z.board (i + 3 + 4)
        _ = Z.board (i + 0) + Z.board (i + 2) := by rw [add_assoc, add_assoc]; rfl
        _ = Z.board i + Z.board (i + 2) := by rw [add_zero]
        _ ≤ r := hi02
    -- Check `z_{i + 1} ≤ r`.
    · calc Z.board (i + 3 + 3)
        _ = X.board (i + 1) + A.y (i + 1) := congrArg Z.board (add_assoc i 3 3)
        _ = A.y (i + 1) := by rw [hi1, zero_add]
        _ ≤ r := A.y_le_r _
    -- Check `z_{i + 3} ≤ 2r`.
    · exact hi3
    -- Check `z_{i + 4} ≤ 2r`.
    · replace hi24 : X.board (i + 4) ≤ r :=
        le_of_add_le_of_nonneg_right hi24 (X.board_nonneg _)
      calc Z.board (i + 3 + 1)
        _ = X.board (i + 4) + A.y (i + 4) := congrArg Z.board (add_assoc i 3 1)
        _ ≤ r + r := add_le_add hi24 (A.y_le_r _)
        _ = 2 • r := (two_nsmul r).symm

/-- A losing state is not good. -/
theorem isLosing.not_good {X : GameState r hr} (hXb : isLosing X isPlayerATurn) :
    ¬good X isPlayerATurn := by
  intro hX0; induction hXb with
  | ofLost X hX isPlayerATurn => exact hX0.not_isLost hX
  | ofBMove X hX X_ih => exact hX0.exists_BMove.elim X_ih
  | ofAMove X A hXA X_ih => exact X_ih (hX0.forall_AMove A)

/-- The initial state is not losing. -/
theorem not_isLosing_init (isPlayerATurn) : ¬(GameState.init r hr).isLosing isPlayerATurn :=
  λ h ↦ h.not_good (init_is_good isPlayerATurn)

end

end GameState


/-- Final solution -/
theorem final_solution [LinearOrder G] [IsOrderedAddMonoid G] [AddLeftStrictMono G]
    {r : G} {hr : r ≥ 0} : ¬(GameState.init r hr).isLosing true :=
  GameState.not_isLosing_init true
