/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.F2Map
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.F2eMap
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.F3Map1
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.F3Map2
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.F4Map
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.Z4Map
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.SqSubOneMap
public import IMOSLLean4.Generalization.IMO2012A5.A5Answers.SubOneMap
public import IMOSLLean4.Generalization.IMO2012A5.A5General.A5Hom
public import IMOSLLean4.Generalization.IMO2012A5.Extra.BundledRingFun

/-!
# IMO 2012 A5 (Description of answers)

We describe all non-trivial good maps and prove that they are non-trivial good.
The proof that they are the only ones is the main content of the problem.

* `isPolyGoodMap f` says that `f` is one of the two polynomial solutions:
  `x : R ↦ x - 1` and `x : R ↦ x^2 - 1 : R_2`.
* `isFinGoodMap f` says that `f` is one of the six special solutions:
  `𝔽₂Map`, `𝔽₃Map1`, `𝔽₃Map2`, `ℤ₄Map`, `𝔽₂εMap`, and `𝔽₄Map`.
* `isNontrivialAnswer f` says that `f` is either `isPolyGoodMap` or `isFinGoodMap`.
* `isNontrivialAnswer.NontrivialGood` is a proof the above functions are non-trivial good.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

open BundledRingFun

inductive isPolyGoodMap : BundledRingFun → Prop
  | SubOne (R) [Ring R] : isPolyGoodMap (ofFun λ (x : R) ↦ x - 1)
  | SqSubOne (R) [CommRing R] : isPolyGoodMap (ofFun (RestrictedSq (R := R) - 1))

inductive isFinGoodMap : BundledRingFun → Prop
  | 𝔽₂Map  : isFinGoodMap (ofFun 𝔽₂Map)
  | 𝔽₃Map1 : isFinGoodMap (ofFun 𝔽₃Map1)
  | 𝔽₃Map2 : isFinGoodMap (ofFun 𝔽₃Map2)
  | ℤ₄Map  : isFinGoodMap (ofFun ℤ₄Map)
  | 𝔽₂εMap : isFinGoodMap (ofFun 𝔽₂εMap)
  | 𝔽₄Map  : isFinGoodMap (ofFun 𝔽₄Map)

/-- Claimed set of non-trivial good functions -/
def isNontrivialAnswer.{u} (X : BundledRingFun.{u}) : Prop :=
  (∃ A : BundledRingFun.{u}, isPolyGoodMap A ∧ Nonempty (A.Hom X)) ∨
    (∃ A : BundledRingFun, isFinGoodMap A ∧ Nonempty (A.Hom X))

theorem isPolyGoodMap.NontrivialGood (hX : isPolyGoodMap X) : NontrivialGood X.f :=
  hX.rec (λ R ↦ sub_one_is_NontrivialGood (R := R))
    (λ R ↦ RestrictedSq_sub_one_is_NontrivialGood (R := R))

theorem isFinGoodMap.NontrivialGood (hX : isFinGoodMap X) : NontrivialGood X.f :=
  hX.rec 𝔽₂Map_is_NontrivialGood 𝔽₃Map1_is_NontrivialGood 𝔽₃Map2_is_NontrivialGood
    ℤ₄Map_is_NontrivialGood 𝔽₂εMap_is_NontrivialGood 𝔽₄Map_is_NontrivialGood

theorem BundledRingFun.Hom.NontrivialGood_trans {A X : BundledRingFun}
    (hA : NontrivialGood A.f) (F : A.Hom X) : NontrivialGood X.f :=
  have h : X.f = F.targetHom ∘ A.f ∘ F.sourceHom := funext F.spec
  h ▸ (hA.hom_comp _).comp_hom _

theorem isNontrivialAnswer.NontrivialGood (hX : isNontrivialAnswer X) : NontrivialGood X.f :=
  hX.elim (λ ⟨_, h, h0⟩ ↦ h0.elim λ φ ↦ φ.NontrivialGood_trans h.NontrivialGood)
    (λ ⟨_, h, h0⟩ ↦ h0.elim λ φ ↦ φ.NontrivialGood_trans h.NontrivialGood)
