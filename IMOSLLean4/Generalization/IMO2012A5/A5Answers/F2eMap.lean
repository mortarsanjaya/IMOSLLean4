/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import IMOSLLean4.Generalization.IMO2012A5.A5Defs
public import IMOSLLean4.Generalization.IMO2012A5.Extra.ExplicitRings.F2e

/-!
# IMO 2012 A5 (`𝔽₂εMap`)

We define `𝔽₂εMap : 𝔽₂ε → ℤ` and prove that it is a good map.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

open 𝔽₂ε

def 𝔽₂εMap : 𝔽₂ε → ℤ
  | O => -1
  | I => 0
  | X => 1
  | Y => 0

/-- The map `𝔽₂εMap` is good. -/
theorem 𝔽₂εMap_is_good : good 𝔽₂εMap
  | O, O => rfl
  | O, I => rfl
  | O, X => rfl
  | O, Y => rfl
  | I, O => rfl
  | I, I => rfl
  | I, X => rfl
  | I, Y => rfl
  | X, O => rfl
  | X, I => rfl
  | X, X => rfl
  | X, Y => rfl
  | Y, O => rfl
  | Y, I => rfl
  | Y, X => rfl
  | Y, Y => rfl

/-- The map `𝔽₂εMap` is non-trivial good. -/
theorem 𝔽₂εMap_is_NontrivialGood : NontrivialGood 𝔽₂εMap :=
  ⟨𝔽₂εMap_is_good, rfl⟩
