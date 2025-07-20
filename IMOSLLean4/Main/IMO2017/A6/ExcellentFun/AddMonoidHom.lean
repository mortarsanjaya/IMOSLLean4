/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2017.A6.ExcellentFun.Defs
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Group homomorphism as excellent function

Every (additive) group homomorphism from $R$ to $G$ is an excellent function.
Thus, we have a map from $\text{Hom}(R, G)$ to the set of exellent functions.
We are mainly interested in classifying pairs $(R, G)$ such that the converse holds:
  the only excellent functions from $R$ to $G$ are group homomorphisms.

The function `ofAddMonoidHom` provides an inclusion from $\text{Hom}(R, G)$
  to the set of exellent functions from $R$ and $G$.
The typeclass `IsOfAddMonoidHomSurjective R G` indicates that this map is surjective.
When this holds, `toAddMonoidHom` gives an explicit inverse of `ofAddMonoidHom`.
-/

namespace IMOSL
namespace IMO2017A6
namespace ExcellentFun

variable [NonAssocRing R] [AddZeroClass G]

def ofAddMonoidHom (φ : R →+ G) : ExcellentFun R G where
  toFun := φ
  excellent_def' x y := by
    simp only [sub_eq_add_neg]
    rw [← φ.map_add, add_comm, add_assoc, neg_add_cancel_left]

theorem ofAddMonoidHom_injective : (ofAddMonoidHom (R := R) (G := G)).Injective :=
  λ _ _ h ↦ AddMonoidHom.ext λ _ ↦ ExcellentFun.ext_iff.mp h _

/-- Typeclass stating that all excellent functions `R → G` are group homs. -/
class IsOfAddMonoidHomSurjective (R G) [NonAssocRing R] [AddZeroClass G] : Prop where
  ofAddMonoidHom_surjective : (ofAddMonoidHom (R := R) (G := G)).Surjective

theorem IsOfAddMonoidHomSurjective.mk' [IsCancelAdd G]
    (h : ∀ (f : ExcellentFun R G) (x y : R), f (x + y) = f x + f y) :
    IsOfAddMonoidHomSurjective R G where
  ofAddMonoidHom_surjective f := ⟨⟨⟨f, excellent_map_zero f⟩, h f⟩, rfl⟩


section

variable [IsOfAddMonoidHomSurjective R G]

theorem ofAddMonoidHom_surjective : (ofAddMonoidHom (R := R) (G := G)).Surjective :=
  IsOfAddMonoidHomSurjective.ofAddMonoidHom_surjective

/-- Choice-independent inverse of `ofAddMonoidHom` -/
def toAddMonoidHom (f : ExcellentFun R G) : R →+ G where
  toFun := f.toFun
  map_zero' := by obtain ⟨φ, rfl⟩ := ofAddMonoidHom_surjective f; exact φ.map_zero
  map_add' := by obtain ⟨φ, rfl⟩ := ofAddMonoidHom_surjective f; exact φ.map_add

theorem toAddMonoidHom_ofAddMonoidHom (φ : R →+ G) :
    toAddMonoidHom (ofAddMonoidHom φ) = φ := rfl

theorem ofAddMonoidHom_toAddMonoidHom (f : ExcellentFun R G) :
    ofAddMonoidHom (toAddMonoidHom f) = f := rfl

end
