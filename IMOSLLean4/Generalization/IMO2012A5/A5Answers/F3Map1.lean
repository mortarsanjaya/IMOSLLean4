/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import IMOSLLean4.Generalization.IMO2012A5.A5Defs
public import IMOSLLean4.Generalization.IMO2012A5.Extra.ExplicitRings.F3

/-!
# IMO 2012 A5 (`𝔽₃Map1`)

We define `𝔽₃Map1 : 𝔽₃ → ℤ` and prove that it is a good map.
-/

@[expose] public section

namespace IMOSL
namespace IMO2012A5
namespace Generalization

def 𝔽₃Map1 : 𝔽₃ → ℤ
  | 𝔽₃.𝔽₃0 => -1
  | 𝔽₃.𝔽₃1 => 0
  | 𝔽₃.𝔽₃2 => 1

/-- The map `𝔽₃Map1` is good. -/
theorem 𝔽₃Map1_is_good : good 𝔽₃Map1
  | 𝔽₃.𝔽₃0, 𝔽₃.𝔽₃0 => rfl
  | 𝔽₃.𝔽₃0, 𝔽₃.𝔽₃1 => rfl
  | 𝔽₃.𝔽₃0, 𝔽₃.𝔽₃2 => rfl
  | 𝔽₃.𝔽₃1, 𝔽₃.𝔽₃0 => rfl
  | 𝔽₃.𝔽₃1, 𝔽₃.𝔽₃1 => rfl
  | 𝔽₃.𝔽₃1, 𝔽₃.𝔽₃2 => rfl
  | 𝔽₃.𝔽₃2, 𝔽₃.𝔽₃0 => rfl
  | 𝔽₃.𝔽₃2, 𝔽₃.𝔽₃1 => rfl
  | 𝔽₃.𝔽₃2, 𝔽₃.𝔽₃2 => rfl

/-- The map `𝔽₃Map1` is non-trivial good. -/
theorem 𝔽₃Map1_is_NontrivialGood : NontrivialGood 𝔽₃Map1 :=
  ⟨𝔽₃Map1_is_good, rfl⟩
