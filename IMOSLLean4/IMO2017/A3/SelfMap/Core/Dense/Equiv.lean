/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Core.Dense.Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Core.Equiv

/-!
# Isomorphism of self-maps as dense cores

We provide some relation between isomorphism
  and dense core instances of self-maps.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace DenseCore

def ofEquiv (e : Equiv X Y) : DenseCore X Y :=
  ⟨Core.ofEquiv e, λ x ↦ ⟨e.toHom x, 0, 0, (e.toEquiv.symm_apply_apply x).symm⟩⟩

def toEquiv (C : DenseCore X Y) (h : C.φ.toFun.RightInverse C.ι) : Equiv X Y :=
  C.toCore.toEquiv h

def equivTrans (e : Equiv X Y) (C : DenseCore Y Z) : DenseCore X Z :=
  (ofEquiv e).trans C

def transEquiv (C : DenseCore X Y) (e : Equiv Y Z) : DenseCore X Z :=
  C.trans (ofEquiv e)
