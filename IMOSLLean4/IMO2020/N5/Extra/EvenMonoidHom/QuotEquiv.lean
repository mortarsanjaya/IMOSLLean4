/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.Extra.EvenMonoidHom.Basic
import Mathlib.GroupTheory.QuotientGroup

/-!
# Isomorphism between `EvenMonoidHom M N` and `M/{±1} →* N`

This file provides an isomorphism between `EvenMonoidHom M N` and `M/{±1} →* N`.
It is made as explicit as possible.
-/

namespace IMOSL
namespace IMO2020N5
namespace EvenMonoidHom

variable (M N : Type*) [CommGroup M] [HasDistribNeg M] [CommMonoid N]

/-- The function from `EvenMonoidHom M N` to `M/{±1} →* N` -/
def toQuotHom' (f : EvenMonoidHom M N) : M ⧸ Subgroup.zpowers (-1) →* N :=
  QuotientGroup.lift _ f.toMonoidHom (Subgroup.zpowers_le_of_mem f.map_neg_one)

lemma toQuotHom'_one : toQuotHom' M N 1 = 1 :=
  MonoidHom.ext λ x ↦ x.induction_on λ _ ↦ rfl

lemma toQuotHom'_mul (f g : EvenMonoidHom M N) :
    toQuotHom' M N (f * g) = toQuotHom' M N f * toQuotHom' M N g :=
  MonoidHom.ext λ x ↦ x.induction_on λ _ ↦ rfl

/-- `toQuotHom'` as a homomorphism -/
def toQuotHom : EvenMonoidHom M N →* (M ⧸ Subgroup.zpowers (-1) →* N) :=
  { toFun := toQuotHom' M N
    map_one' := toQuotHom'_one M N
    map_mul' := toQuotHom'_mul M N }



/-- The function from `(M/{±1} →* N)` to `EvenMonoidHom M N` -/
def ofQuotHom' (φ : M ⧸ Subgroup.zpowers (-1) →* N) : EvenMonoidHom M N :=
  { toMonoidHom := φ.comp (QuotientGroup.mk' (Subgroup.zpowers (-1 : M)))
    map_neg_one' := φ.map_one ▸ congr_arg φ.toFun
      ((QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_zpowers _)) }

lemma ofQuotHom'_one : ofQuotHom' M N 1 = 1 := rfl

lemma ofQuotHom'_mul (f g : M ⧸ Subgroup.zpowers (-1) →* N) :
    ofQuotHom' M N (f * g) = ofQuotHom' M N f * ofQuotHom' M N g := rfl

/-- `ofQuotHom` as a homomorphism -/
def ofQuotHom : (M ⧸ Subgroup.zpowers (-1) →* N) →* EvenMonoidHom M N :=
  { toFun := ofQuotHom' M N
    map_one' := ofQuotHom'_one M N
    map_mul' := ofQuotHom'_mul M N }



lemma ofQuotHom'_toQuotHom' (f : EvenMonoidHom M N) :
    ofQuotHom' M N (toQuotHom' M N f) = f := rfl

lemma toQuotHom'_ofQuotHom' (φ : M ⧸ Subgroup.zpowers (-1) →* N) :
    toQuotHom' M N (ofQuotHom' M N φ) = φ := by
  ext x; rfl

def equivQuotHom : EvenMonoidHom M N ≃* (M ⧸ Subgroup.zpowers (-1) →* N) :=
  { toFun := toQuotHom' M N
    invFun := ofQuotHom' M N
    left_inv := ofQuotHom'_toQuotHom' M N
    right_inv := toQuotHom'_ofQuotHom' M N
    map_mul' := toQuotHom'_mul M N }
