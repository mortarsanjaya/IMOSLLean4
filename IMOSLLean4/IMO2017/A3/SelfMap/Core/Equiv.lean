/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Core.Defs
import IMOSLLean4.IMO2017.A3.SelfMap.Equiv.Defs

/-!
# Isomorphism of self-maps as cores

We provide some relation between isomorphism and core instances of self-maps.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace Core

def ofEquiv (e : Equiv X Y) : Core X Y :=
  ⟨e.toHom, e.symm.toHom, e.right_inv⟩

def toEquiv (C : Core X Y) (h : C.φ.toFun.RightInverse C.ι) : Equiv X Y :=
  ⟨⟨C.φ, C.ι, h, C.is_inv⟩, C.φ.Semiconj⟩

def equivTrans (e : Equiv X Y) (C : Core Y Z) : Core X Z :=
  (ofEquiv e).trans C

def transEquiv (C : Core X Y) (e : Equiv Y Z) : Core X Z :=
  C.trans (ofEquiv e)
