/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.ExcellentFun.AddHomSurj.Defs
import Mathlib.Algebra.Group.Equiv.Basic

/-!
# Equivalence between excellent functions and group homomorphisms

We provide equivalence between `ExcellentFun R G` and `R →+ G`.
Certainly, this assumes `IsOfAddMonoidHomSurjective R G`.
-/

namespace IMOSL
namespace IMO2017A6
namespace ExcellentFun

variable [NonAssocRing R]

/-- Choice-independent bijection between excellent functions and group homomorphisms. -/
def equiv_AddMonoidHom [AddZeroClass G] [IsOfAddMonoidHomSurjective R G] :
    ExcellentFun R G ≃ (R →+ G) where
  toFun := toAddMonoidHom
  invFun := ofAddMonoidHom
  left_inv := ofAddMonoidHom_toAddMonoidHom
  right_inv := toAddMonoidHom_ofAddMonoidHom

/-- Choice-independent homomorphism between excellent functions and group homomorphisms. -/
def AddEquiv_AddMonoidHom [AddCommMonoid G] [IsOfAddMonoidHomSurjective R G] :
    ExcellentFun R G ≃+ (R →+ G) :=
  { equiv_AddMonoidHom with map_add' := λ _ _ ↦ rfl }
