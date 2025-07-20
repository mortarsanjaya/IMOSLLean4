/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2012.A5.A5Defs
import IMOSLLean4.Main.IMO2012.A5.Extra.ExplicitRings.F2

/-!
# IMO 2012 A5 (`𝔽₂Map`)

We define `𝔽₂Map : 𝔽₂ → ℤ` and prove that it is a good map.
-/

namespace IMOSL
namespace IMO2012A5

open 𝔽₂

def 𝔽₂Map : 𝔽₂ → ℤ
  | O => -1
  | I => 0

/-- The map `𝔽₂Map` is good. -/
theorem 𝔽₂Map_is_good : good 𝔽₂Map
  | O, O => rfl
  | O, I => rfl
  | I, O => rfl
  | I, I => rfl

/-- The map `𝔽₂Map` is non-trivial good. -/
theorem 𝔽₂Map_is_NontrivialGood : NontrivialGood 𝔽₂Map :=
  ⟨𝔽₂Map_is_good, rfl⟩
