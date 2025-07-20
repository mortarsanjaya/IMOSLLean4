/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2012.A5.A5Defs
import IMOSLLean4.Main.IMO2012.A5.Extra.ExplicitRings.F3

/-!
# IMO 2012 A5 (`𝔽₃Map2`)

We define `𝔽₃Map2 : 𝔽₃ → ℤ` and prove that it is a good map.
-/

namespace IMOSL
namespace IMO2012A5

open 𝔽₃

def 𝔽₃Map2 : 𝔽₃ → ℤ
  | 𝔽₃0 => -1
  | 𝔽₃1 => 0
  | 𝔽₃2 => 0

/-- The map `𝔽₃Map2` is good. -/
theorem 𝔽₃Map2_is_good : good 𝔽₃Map2
  | 𝔽₃0, 𝔽₃0 => rfl
  | 𝔽₃0, 𝔽₃1 => rfl
  | 𝔽₃0, 𝔽₃2 => rfl
  | 𝔽₃1, 𝔽₃0 => rfl
  | 𝔽₃1, 𝔽₃1 => rfl
  | 𝔽₃1, 𝔽₃2 => rfl
  | 𝔽₃2, 𝔽₃0 => rfl
  | 𝔽₃2, 𝔽₃1 => rfl
  | 𝔽₃2, 𝔽₃2 => rfl

/-- The map `𝔽₃Map2` is non-trivial good. -/
theorem 𝔽₃Map2_is_NontrivialGood : NontrivialGood 𝔽₃Map2 :=
  ⟨𝔽₃Map2_is_good, rfl⟩
