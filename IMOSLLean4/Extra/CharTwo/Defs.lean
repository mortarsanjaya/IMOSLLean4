/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Defs

/-!
# Characteristic two monoids

We say that a monoid `M` has *characteristic two* if `x + x = 0` for any `x : M`.
Such monoids are secretly abelian groups, and subtraction is the same as addition.
-/

namespace IMOSL
namespace Extra

class CharTwo (M) [AddMonoid M] : Prop where
  add_self_eq_zero : ∀ x : M, x + x = 0


namespace CharTwo

section

variable [AddMonoid M] [CharTwo M]

theorem add_add_cancel_left (x y : M) : x + (x + y) = y := by
  rw [← add_assoc, add_self_eq_zero, zero_add]

theorem add_add_cancel_right (x y : M) : x + y + y = x := by
  rw [add_assoc, add_self_eq_zero, add_zero]

theorem add_add_add_cancel_middle (x y z : M) : (x + y) + (y + z) = x + z := by
  rw [← add_assoc, add_add_cancel_right]

theorem add_comm (x y : M) : x + y = y + x := by
  rw [← add_add_cancel_right (x + y) (y + x),
    add_add_add_cancel_middle, add_self_eq_zero, zero_add]

theorem add_add_cancel_middle₁ (x y : M) : x + (y + x) = y := by
  rw [add_comm, add_add_cancel_right]

theorem add_add_cancel_middle₂ (x y : M) : x + y + x = y := by
  rw [add_comm, add_add_cancel_left]

theorem add_right_inj {x y z : M} : x + y = x + z ↔ y = z :=
  ⟨λ h ↦ by rw [← add_add_cancel_left x y, h, add_add_cancel_left], congr_arg₂ _ rfl⟩

theorem add_left_inj {x y z : M} : x + z = y + z ↔ x = y := by
  rw [add_comm, add_comm y, add_right_inj]

theorem add_eq_iff_eq_add {x y z : M} : x + y = z ↔ x = z + y := by
  rw [← add_left_inj (z := y), add_add_cancel_right]

theorem add_eq_iff_eq_add' {x y z : M} : x + y = z ↔ x = y + z := by
  rw [add_eq_iff_eq_add, add_comm]

theorem add_eq_iff_eq_add'' {x y z : M} : x + y = z ↔ y = x + z := by
  rw [add_comm, add_eq_iff_eq_add']

theorem add_eq_iff_eq_add''' {x y z : M} : x + y = z ↔ y = z + x := by
  rw [add_eq_iff_eq_add'', add_comm]

theorem add_eq_zero_iff_eq {x y : M} : x + y = 0 ↔ x = y := by
  rw [add_eq_iff_eq_add, zero_add]

theorem add_add_add_cancel_left (x y z : M) : (x + y) + (x + z) = y + z := by
  rw [← add_assoc, add_add_cancel_middle₂]

theorem add_add_add_cancel_right (x y z : M) : (x + z) + (y + z) = x + y := by
  rw [add_assoc, add_add_cancel_middle₁]

end





/-! ### `CharTwo` on groups -/

section

variable [AddGroup G] [CharTwo G]

theorem neg_eq_self (x : G) : -x = x :=
  neg_eq_of_add_eq_zero_left (add_self_eq_zero x)

theorem neg_eq_self' : (λ x : G ↦ -x) = id :=
  funext neg_eq_self

theorem sub_eq_add (x y : G) : x - y = x + y := by
  rw [sub_eq_add_neg, neg_eq_self]

theorem sub_eq_add' : (λ x y : G ↦ x - y) = (· + ·) :=
  funext₂ sub_eq_add

end
