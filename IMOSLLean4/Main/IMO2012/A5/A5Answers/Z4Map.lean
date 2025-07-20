/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2012.A5.A5Defs
import IMOSLLean4.Main.IMO2012.A5.Extra.ExplicitRings.Z4

/-!
# IMO 2012 A5 (`ℤ₄Map`)

We define `ℤ₄Map : ℤ₄ → ℤ` and prove that it is a good map.
-/

namespace IMOSL
namespace IMO2012A5

open ℤ₄

def ℤ₄Map : ℤ₄ → ℤ
  | ℤ₄0 => -1
  | ℤ₄1 => 0
  | ℤ₄2 => 1
  | ℤ₄3 => 0

/-- The map `ℤ₄Map` is good. -/
theorem ℤ₄Map_is_good : good ℤ₄Map
  | ℤ₄0, ℤ₄0 => rfl
  | ℤ₄0, ℤ₄1 => rfl
  | ℤ₄0, ℤ₄2 => rfl
  | ℤ₄0, ℤ₄3 => rfl
  | ℤ₄1, ℤ₄0 => rfl
  | ℤ₄1, ℤ₄1 => rfl
  | ℤ₄1, ℤ₄2 => rfl
  | ℤ₄1, ℤ₄3 => rfl
  | ℤ₄2, ℤ₄0 => rfl
  | ℤ₄2, ℤ₄1 => rfl
  | ℤ₄2, ℤ₄2 => rfl
  | ℤ₄2, ℤ₄3 => rfl
  | ℤ₄3, ℤ₄0 => rfl
  | ℤ₄3, ℤ₄1 => rfl
  | ℤ₄3, ℤ₄2 => rfl
  | ℤ₄3, ℤ₄3 => rfl

/-- The map `ℤ₄Map` is non-trivial good. -/
theorem ℤ₄Map_is_NontrivialGood : NontrivialGood ℤ₄Map :=
  ⟨ℤ₄Map_is_good, rfl⟩
