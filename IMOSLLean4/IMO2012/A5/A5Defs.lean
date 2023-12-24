/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.ExplicitRings.F2
import IMOSLLean4.IMO2012.A5.ExplicitRings.F2e
import IMOSLLean4.IMO2012.A5.ExplicitRings.F3
import IMOSLLean4.IMO2012.A5.ExplicitRings.F4
import IMOSLLean4.IMO2012.A5.ExplicitRings.Z4

/-!
# IMO 2012 A5 (Definitions)

Let $R$ be a commutative ring and $S$ be a field.
Find all functions $f : R \to S$ such that, for any $x, y \in R$,
$$ f(xy + 1) - f(x + y) = f(x) f(y). $$

This file define the functional equation and its (claimed) set of answers.
-/

namespace IMOSL
namespace IMO2012A5

/-- The problem. -/
def good [Ring R] [Ring S] (f : R → S) :=
  ∀ x y : R, f (x * y + 1) - f (x + y) = f x * f y



/-! ## Answer description -/

section ExtraMaps

variable (R : Type _) [Ring R]

def 𝔽₂Map : 𝔽₂ → R
  | 𝔽₂.O => -1
  | 𝔽₂.I => 0

def 𝔽₂εMap : 𝔽₂ε → R
  | 𝔽₂ε.O => -1
  | 𝔽₂ε.I => 0
  | 𝔽₂ε.X => 1
  | 𝔽₂ε.Y => 0

def 𝔽₃Map1 : 𝔽₃ → R
  | 𝔽₃.𝔽₃0 => -1
  | 𝔽₃.𝔽₃1 => 0
  | 𝔽₃.𝔽₃2 => 1

def 𝔽₃Map2 : 𝔽₃ → R
  | 𝔽₃.𝔽₃0 => -1
  | 𝔽₃.𝔽₃1 => 0
  | 𝔽₃.𝔽₃2 => 0

def 𝔽₄Map (c : R) : 𝔽₄ → R
  | 𝔽₄.O => -1
  | 𝔽₄.I => 0
  | 𝔽₄.X => c
  | 𝔽₄.Y => 1 - c

def ℤ₄Map : ℤ₄ → R
  | 0 => -1
  | 1 => 0
  | 2 => 1
  | 3 => 0

end ExtraMaps



/-- The answer set. -/
inductive IsAnswer [Ring R] [Ring S] : (R → S) → Prop
  | of_zero :
      IsAnswer (0 : R → S)
  | hom_sub_one (φ : R →+* S) :
      IsAnswer (φ.toFun · - 1)
  | hom_sq_sub_one (φ : R →+* S) :
      IsAnswer (φ.toFun · ^ 2 - 1)
  | 𝔽₂_map_comp (φ : R →+* 𝔽₂) (_ : φ.toFun.Surjective) :
      IsAnswer (𝔽₂Map S ∘ φ.toFun)
  | 𝔽₃_map1_comp (φ : R →+* 𝔽₃) (_ : φ.toFun.Surjective) :
      IsAnswer (𝔽₃Map1 S ∘ φ.toFun)
  | 𝔽₃_map2_comp (φ : R →+* 𝔽₃) (_ : φ.toFun.Surjective) :
      IsAnswer (𝔽₃Map2 S ∘ φ.toFun)
  | ℤ₄_map_comp (φ : R →+* ℤ₄) (_ : φ.toFun.Surjective) :
      IsAnswer (ℤ₄Map S ∘ φ.toFun)
  | 𝔽₂ε_map_comp (φ : R →+* 𝔽₂ε) (_ : φ.toFun.Surjective) :
      IsAnswer (𝔽₂εMap S ∘ φ.toFun)
  | 𝔽₄_map_comp (φ : R →+* 𝔽₄) (_ : φ.toFun.Surjective)
        (c : S) (_ : c * (1 - c) = -1) :
      IsAnswer (𝔽₄Map S c ∘ φ.toFun)
