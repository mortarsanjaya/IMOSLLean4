/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Core.Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Irreducible.Hom

/-!
# Dense cores of self-maps

A dense core of a self-map `X` is a core `Y` such that every point in `X`
  is point-equivalent to a point in the image of `Y` in `X`.
Every core of an irreducible self-map is dense.
Furthermore, dense cores also behave well with respect to direct sums.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

structure DenseCore (X Y : SelfMap) extends Core X Y :=
  dense : ∀ x : X.α, ∃ y : Y.α, ptEquiv X x (ι y)



namespace DenseCore

def refl (X : SelfMap) : DenseCore X X :=
  ⟨Core.refl X, λ x ↦ ⟨x, ptEquiv.refl X x⟩⟩

def trans (C₁ : DenseCore X Y) (C₂ : DenseCore Y Z) : DenseCore X Z where
  toCore := C₁.toCore.trans C₂.toCore
  dense := λ x ↦ (C₁.dense x).elim λ y h ↦
    (C₂.dense y).elim λ z h0 ↦ ⟨z, h.trans (h0.ofHom C₁.ι)⟩

def ofIrreducibleCore (C : Core X Y) (h : Irreducible X) : DenseCore X Y :=
  ⟨C, λ x ↦ ⟨C.φ x, h.ptEquiv _ _⟩⟩

def sum_map (C₁ : DenseCore X₁ Y₁) (C₂ : DenseCore X₂ Y₂) :
    DenseCore (sum X₁ X₂) (sum Y₁ Y₂) where
  toCore := C₁.toCore.sum_map C₂.toCore
  dense := λ x ↦ match x with
    | Sum.inl a => (C₁.dense a).elim λ y h ↦ ⟨Sum.inl y, h.sum_inl _⟩
    | Sum.inr a => (C₂.dense a).elim λ y h ↦ ⟨Sum.inr y, h.sum_inr _⟩

def sigma_map_id (C : (i : I) → DenseCore (X i) (Y i)) :
    DenseCore (sigma X) (sigma Y) where
  toCore := Core.sigma_map_id λ i ↦ (C i).toCore
  dense := λ ⟨i, x⟩ ↦ ((C i).dense x).elim λ y h ↦ ⟨⟨i, y⟩, h.sigma_incl⟩

end DenseCore



/-! ### Composition with "normal" core -/

namespace Core

def transDenseCore (C : Core X Y) (D : DenseCore Y Z) : Core X Z :=
  C.trans D.toCore

def denseCoreTrans (D : DenseCore X Y) (C : Core Y Z) : Core X Z :=
  D.toCore.trans C

end Core
