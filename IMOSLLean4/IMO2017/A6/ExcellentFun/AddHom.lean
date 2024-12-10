/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.ExcellentFun.Defs
import Mathlib.Algebra.Group.Hom.Instances

/-!
# Group homomorphism as excellent function

Every (additive) group homomorphism from $R$ to $G$ is an excellent function.
Thus, we have a map from $\text{Hom}(R, G)$ to the set of group homomorphisms.
-/

namespace IMOSL
namespace IMO2017A6
namespace ExcellentFun

variable [NonAssocRing R]

/-! ### Excellent functions from additive map -/

def ofAddHom [Add G] (φ : AddHom R G) : ExcellentFun R G where
  toFun := φ
  excellent_def' x y := by rw [← φ.map_add, sub_add_sub_cancel']

theorem ofAddHom_injective [Add G] : (ofAddHom (R := R) (G := G)).Injective :=
  λ _ _ h ↦ AddHom.ext λ _ ↦ ExcellentFun.ext_iff.mp h _

def HomOfAddHom [AddCommSemigroup G] : AddHom (AddHom R G) (ExcellentFun R G) where
  toFun := ofAddHom
  map_add' _ _ := rfl

theorem HomOfAddHom_injective [AddCommSemigroup G] :
    Function.Injective (HomOfAddHom (R := R) (G := G)) :=
  ofAddHom_injective





/-! ### Excellent functions from group homomorphisms -/

def ofAddMonoidHom [AddZeroClass G] (φ : R →+ G) : ExcellentFun R G :=
  ExcellentFun.ofAddHom φ

theorem ofAddMonoidHom_injective [AddZeroClass G] :
    (ofAddMonoidHom (R := R) (G := G)).Injective :=
  λ _ _ h ↦ AddMonoidHom.ext λ _ ↦ ExcellentFun.ext_iff.mp h _

def HomOfAddMonoidHom [AddCommMonoid G] : (R →+ G) →+ ExcellentFun R G where
  toFun := ofAddMonoidHom
  map_add' _ _ := rfl
  map_zero' := rfl

theorem HomOfAddMonoidHom_injective [AddCommMonoid G] :
    Function.Injective (HomOfAddMonoidHom (R := R) (G := G)) :=
  ofAddMonoidHom_injective
