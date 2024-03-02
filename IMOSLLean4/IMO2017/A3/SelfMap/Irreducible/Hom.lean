/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Irreducible.Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Hom

/-!
# Point-equivalence and homomorphisms

We prove that homomorphisms preserve point-equivalence.
We also prove some more related properties.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace ptEquiv

lemma ofHom (e : Hom X Y) : ptEquiv X a b → ptEquiv Y (e a) (e b) :=
  Exists.imp λ k ↦ Exists.imp λ m h ↦
    (e.semiconj_iterate_apply k a).symm.trans <|
      h ▸ e.semiconj_iterate_apply m b

lemma sum_inl {X} (Y) {a b : X.α} :
    ptEquiv X a b → ptEquiv (sum X Y) (Sum.inl a) (Sum.inl b) :=
  ofHom (Hom.sum_inl X Y)

lemma sum_inr (X) {Y} {a b : Y.α} :
    ptEquiv Y a b → ptEquiv (sum X Y) (Sum.inr a) (Sum.inr b) :=
  ofHom (Hom.sum_inr X Y)

lemma sigma_incl (X : I → SelfMap) {a b : (X i).α} :
    ptEquiv (X i) a b → ptEquiv (sigma X) ⟨i, a⟩ ⟨i, b⟩ :=
  ofHom (Hom.sigma_incl X i)
