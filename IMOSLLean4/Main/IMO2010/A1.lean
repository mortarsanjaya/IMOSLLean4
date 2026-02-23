/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Module.Torsion.Free

/-!
# IMO 2010 A1 (P1)

A ring with floor is a totally ordered ring $R$ with a floor function $⌊⬝⌋ : R → ℤ$
  such that for any $x ∈ R$ and $n ∈ ℤ$, we have $⌊x⌋ ≤ n$ if and only if $x ≤ n_R$.
(See `FloorRing` for the formal definition.)

Let $R$ and $S$ be totally ordered rings with floor.
Suppose that there exists $α ∈ R$ such that $0 < α < 1$.
Find all functions $f : R → S$ such that for any $x, y ∈ R$,
$$ f(⌊x⌋ y) = ⌊f(y)⌋ f(x). $$

### Answer

$f ≡ 0$ and $f ≡ C$ for some constant $C ∈ S$ with $⌊C⌋ = 1$.

### Solution

Plugging $(x, y) = (0, 0)$ yields either $f(0) = 0$ or $⌊f(0)⌋ = 1$.
In the case $⌊f(0)⌋ = 1$, plugging $y = 0$ yields that $f ≡ C$ for some constant $C$.
Note that $C = f(0)$, so $⌊C⌋ = ⌊f(0)⌋ = 1$.

Now assume that $f(0) = 0$.
Fix some $α ∈ R$ such that $0 < α < 1$.
Plugging $x = y = α$ yields $⌊f(α)⌋ f(α) = f(0) = 0$ and so $⌊f(α)⌋ = 0$.
Plugging $(x, y) = (-1, α)$ then yields $f(-α) = 0$.
Finally, since $⌊-α⌋ = -1$, plugging $x = -α$ gives $f ≡ 0$.

### Extra

It can be shown that there exists $α ∈ R$ such that $0 < α < 1$
  as long as $R$ is not isomorphic to either $ℤ$ or the trivial ring.
-/

namespace IMOSL
namespace IMO2010A1

variable  [Ring R] [LinearOrder R] [FloorRing R] [Ring S] [LinearOrder S] [FloorRing S]

/-- A function `f : R → S` is called *good* if
  `f(⌊x⌋ y) = ⌊f(y)⌋ f(x)` for all `x, y : R`. -/
def good (f : R → S) := ∀ x y : R, f (⌊x⌋ • y) = ⌊f y⌋ • f x

/-- The zero function is good. -/
theorem zero_is_good : good (0 : R → S) :=
  λ _ _ ↦ (zsmul_zero _).symm

/-- The constant function `f ≡ C` is good if `⌊C⌋ = 1`. -/
theorem const_is_good_of_floor_eq_one {C : S} (hC : ⌊C⌋ = 1) : good (λ _ : R ↦ C) :=
  λ _ _ ↦ ((congrArg (· • C) hC).trans (one_zsmul C)).symm


namespace good

/-- We have either `⌊f(0)⌋ = 1` or `f(0) = 0`. -/
theorem floor_eq_one_or_eq_zero [IsOrderedAddMonoid S] {f : R → S} (hf : good f) :
    ⌊f 0⌋ = 1 ∨ f 0 = 0 := by
  have h : f (⌊(0 : R)⌋ • 0) = ⌊f 0⌋ • f 0 := hf 0 0
  rwa [zsmul_zero, eq_comm, ← add_neg_eq_zero,
    ← sub_one_zsmul, smul_eq_zero, sub_eq_zero] at h

/-- If `⌊f(0)⌋ = 1`, then `f` is constant. -/
theorem eq_const_of_floor_map_zero_eq_one {f : R → S} (hf : good f) (hf0 : ⌊f 0⌋ = 1) :
    ∃ C, ⌊C⌋ = 1 ∧ f = λ _ ↦ C := by
  refine ⟨f 0, hf0, funext λ x ↦ ?_⟩
  have h : f (⌊x⌋ • 0) = ⌊f 0⌋ • f x := hf x 0
  rwa [zsmul_zero, hf0, one_zsmul, eq_comm] at h

/-- Suppose there exists `α : R` such that `0 < α < 1`. Then `f(0) = 0` implies `f ≡ 0`. -/
theorem eq_zero_of_map_zero_eq_zero
    [IsStrictOrderedRing R] (hR : ∃ α : R, 0 < α ∧ α < 1) [IsStrictOrderedRing S]
    {f : R → S} (hf : good f) (hf0 : f 0 = 0) : f = 0 := by
  ---- What we need from `0 < α < 1` is `⌊α⌋ = 0` and `⌊-α⌋ = -1`.
  rcases hR with ⟨α, hα0, hα1⟩
  have hα : ⌊α⌋ = 0 := by
    refine Int.le_antisymm ?_ (Int.floor_nonneg.mpr hα0.le)
    rwa [← Int.lt_add_one_iff, Int.floor_lt, Int.zero_add, Int.cast_one]
  replace hα0 : ⌊-α⌋ = -1 := by
    refine Int.le_antisymm ?_ ?_
    · rwa [← Int.lt_add_one_iff, neg_add_cancel, Int.floor_lt, Int.cast_zero, neg_lt_zero]
    · rw [Int.le_floor, Int.cast_neg, Int.cast_one, neg_le_neg_iff]; exact hα1.le
  clear hα1
  ---- First plug `x = y = α` and get `⌊f(α)⌋ = 0`.
  replace h : ⌊f α⌋ = 0 := by
    have h : f (⌊α⌋ • α) = ⌊f α⌋ • f α := hf α α
    rw [hα, zero_zsmul, hf0, eq_comm, smul_eq_zero] at h
    exact h.elim id λ h0 ↦ (congrArg Int.floor h0).trans Int.floor_zero
  ---- Now plug `(x, y) = (-1, α)` and get `f(-α) = 0`.
  replace h : f (-α) = 0 := by
    have h0 : f (⌊(-1 : R)⌋ • α) = ⌊f α⌋ • f (-1) := hf (-1) α
    rwa [h, zero_zsmul, Int.floor_neg, Int.ceil_one, neg_one_zsmul] at h0
  ---- Finally, plug `x = -α` and replace `y` with `-y`.
  refine funext λ y ↦ ?_
  have h0 : f (⌊-α⌋ • -y) = ⌊f (-y)⌋ • f (-α) := hf (-α) (-y)
  rwa [h, zsmul_zero, hα0, neg_one_zsmul, neg_neg] at h0

end good


/-- Final solution -/
theorem final_solution [IsStrictOrderedRing R] (hR : ∃ α : R, 0 < α ∧ α < 1)
    [IsStrictOrderedRing S] {f : R → S} :
    good f ↔ (∃ C : S, ⌊C⌋ = 1 ∧ f = λ _ ↦ C) ∨ f = 0 := by
  refine ⟨λ hf ↦ ?_, λ hf ↦ ?_⟩
  · exact hf.floor_eq_one_or_eq_zero.imp
      hf.eq_const_of_floor_map_zero_eq_one (hf.eq_zero_of_map_zero_eq_zero hR)
  · rcases hf with ⟨C, hC, rfl⟩ | rfl
    exacts [const_is_good_of_floor_eq_one hC, zero_is_good]
