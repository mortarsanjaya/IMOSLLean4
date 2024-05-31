/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Hom.Instances

/-!
# Square-like functions

Let `G` and `H` be abelian groups, and suppose that `H` is `2`-torsion free.
Let `f : G → H` be a function such that `f(x + y) + f(x - y) = 2(f(x) + f(y))`.
We show that there exists a ℤ-bilinear map `φ : G × G → H` such that
  `φ` is symmetric and `2 f(x) = φ(x, x)` for all `x : G`.
-/

namespace IMOSL
namespace Extra
namespace SquareLike

section

variable [AddCommGroup G] [AddCancelCommMonoid H] (hH : ∀ x y : H, 2 • x = 2 • y → x = y)
  {f : G → H} (h : ∀ x y, f (x + y) + f (x - y) = 2 • (f x + f y))

lemma map_zero : f 0 = 0 := by
  specialize h 0 0
  rw [add_zero, sub_zero, two_nsmul, self_eq_add_right, ← two_nsmul] at h
  exact hH _ _ (h.trans (nsmul_zero 2).symm)

lemma map_even (x) : f (-x) = f x := by
  have h0 := h 0 x
  rwa [zero_add, zero_sub, map_zero hH h, zero_add, two_nsmul, add_right_inj] at h0

private lemma map_triple (x y z) :
    f (x + y + z) + f x + (f y + f z) = f (x + y) + f (x + z) + f (y + z) :=
  hH _ _ <| by rw [nsmul_add, ← h, ← h, add_add_add_comm, add_assoc x, add_sub_cancel_left,
    add_comm (f (y + z)), add_add_add_comm, ← two_nsmul, nsmul_add, add_left_inj, ← h,
    add_sub_add_left_eq_sub, add_left_inj, add_right_comm, add_add_add_comm]

end


variable [AddCommGroup G] [AddCommGroup H] (hH : ∀ x y : H, 2 • x = 2 • y → x = y)
  {f : G → H} (h : ∀ x y, f (x + y) + f (x - y) = 2 • (f x + f y))

def BilinMap_at (x : G) : G →+ H :=
  { toFun := λ y ↦ f (x + y) - (f x + f y)
    map_zero' := sub_eq_zero_of_eq <| by rw [add_zero, map_zero hH h, add_zero]
    map_add' := λ y z ↦ by
      change f (x + (y + z)) - (f x + f (y + z))
        = f (x + y) - (f x + f y) + (f (x + z) - (f x + f z))
      rw [sub_add_sub_comm, add_add_add_comm, sub_eq_sub_iff_add_eq_add,
        add_right_comm, ← add_assoc x, ← add_assoc, ← add_assoc,
        map_triple hH h, add_right_comm, add_assoc] }

lemma BilinMap_at_symm (x y : G) : BilinMap_at hH h x y = BilinMap_at hH h y x :=
  congrArg₂ (f · - ·) (add_comm x y) (add_comm (f x) (f y))

def BilinMap : G →+ G →+ H :=
  { toFun := BilinMap_at hH h
    map_zero' := AddMonoidHom.ext λ x ↦
      (BilinMap_at_symm hH h 0 x).trans (BilinMap_at hH h x).map_zero
    map_add' := λ x y ↦ AddMonoidHom.ext λ z ↦ by
      change BilinMap_at hH h (x + y) z = BilinMap_at hH h x z + BilinMap_at hH h y z
      rw [BilinMap_at_symm hH h, map_add]
      apply congrArg₂ <;> exact BilinMap_at_symm hH h _ _ }

lemma BilinMap_symm (x y : G) : BilinMap hH h x y = BilinMap hH h y x :=
  BilinMap_at_symm hH h x y

lemma BilinMap_def (x y : G) : BilinMap hH h x y = f (x + y) - (f x + f y) := rfl

lemma BilinMap_eq_two_nsmul (x : G) : BilinMap hH h x x = 2 • f x := by
  rw [two_nsmul, ← neg_inj, ← map_neg, BilinMap_def,
    add_neg_self, map_zero hH h, map_even hH h, zero_sub]

lemma two_nsmul_BilinMap_eq (x y : G) :
    2 • BilinMap hH h x y = f (x + y) - f (x - y) := by
  rw [BilinMap_def, nsmul_sub, ← h, two_nsmul, add_sub_add_left_eq_sub]
