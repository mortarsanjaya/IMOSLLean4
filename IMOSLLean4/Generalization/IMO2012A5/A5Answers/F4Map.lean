/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import IMOSLLean4.Generalization.IMO2012A5.A5Defs
public import IMOSLLean4.Generalization.IMO2012A5.Extra.ExplicitRings.F4
public import IMOSLLean4.Generalization.IMO2012A5.Extra.ExplicitRings.Zphi

/-!
# IMO 2012 A5 (`𝔽₄Map`)

We define `𝔽₄Map : 𝔽₄ → ℤφ` and prove that it is a (non-trivial) good map.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

open 𝔽₄

def 𝔽₄Map : 𝔽₄ → ℤφ
  | O => -1
  | I => 0
  | X => ℤφ.φ
  | Y => 1 - ℤφ.φ

/-- The map `𝔽₄Map` is good. -/
theorem 𝔽₄Map_is_good : good 𝔽₄Map
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

/-- The map `𝔽₄Map` is non-trivial good. -/
theorem 𝔽₄Map_is_NontrivialGood : NontrivialGood 𝔽₄Map :=
  ⟨𝔽₄Map_is_good, rfl⟩
