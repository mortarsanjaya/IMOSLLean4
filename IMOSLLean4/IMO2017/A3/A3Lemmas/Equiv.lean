/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.A3Lemmas.Core
import IMOSLLean4.IMO2017.A3.SelfMap.Core.Equiv

/-!
# IMO 2017 A3 (Good self-maps and isomorphism)

We prove that the `good` predicate respects isomorphism of self-maps.
-/

namespace IMOSL
namespace IMO2017A3

variable {X Y : SelfMap} (e : X.Equiv Y)

lemma good_of_equiv (h : good X) : good Y :=
  good_of_core (SelfMap.Core.ofEquiv e) h

lemma good_iff_equiv : good X ↔ good Y :=
  ⟨good_of_equiv e, good_of_equiv e.symm⟩
