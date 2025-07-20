/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2012.A5.A5Cases.Case1
import IMOSLLean4.Main.IMO2012.A5.A5Cases.Case2
import IMOSLLean4.Main.IMO2012.A5.A5Cases.Case3
import IMOSLLean4.Main.IMO2012.A5.A5Answers.Common
import IMOSLLean4.Main.IMO2012.A5.A5Answers.ZeroMap
import IMOSLLean4.Main.IMO2012.A5.A5General.A5Periodic

/-!
# IMO 2012 A5

Let $R$ be a ring and $S$ be a domain.
Find all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(xy + 1) = f(x) f(y) + f(x + y). $$

### Implementation details

The solution is broken up into several files.
We highlight some of the most important ones.
* The file `IMOSLLean4/IMO2012/A5/A5Defs.lean` defines the functional equation.
* The file `IMOSLLean4/IMO2012/A5/A5Answers/Common.lean` defines the predicate
    `isNontrivialAnswer`, which describes all guesses for the solution up to homomorphism.
  It also proves that all the guess functions work.
* The file `IMOSLLean4/IMO2012/A5/A5General/A5Periodic.lean`
    defines the quotient of $R$ by $f$-periods.
  It also proves that the set $I$ of $f$-periods form an ideal, and
    the induced quotient function $\tilde{f} : R/I → S$ is good.

Three files prove that no other functions are good:
* `IMOSLLean4/IMO2012/A5/A5Cases/Case1.lean` for case `f(-1) ≠ 0`.
* `IMOSLLean4/IMO2012/A5/A5Cases/Case2.lean` for case `f(-1) = 0`, `char(R) ≠ 2`.
* `IMOSLLean4/IMO2012/A5/A5Cases/Case3.lean` for case `char(R) = 2`.
-/

namespace IMOSL
namespace IMO2012A5

open BundledRingFun

variable [Ring R] [Ring S] [NoZeroDivisors S] {f : R → S}

theorem ReducedGood.isNontrivialAnswer (hf : ReducedGood f) : isNontrivialAnswer (ofFun f) :=
  (em' <| f (-1) = 0).elim
    ---- Case 1: `f(-1) ≠ 0`
    (λ h ↦ (Case1.solution hf h).imp
      (λ ⟨φ, h0⟩ ↦ ⟨_, isPolyGoodMap.SubOne R, RingHom.id R, φ, h0⟩)
      (λ ⟨φ, h0⟩ ↦ ⟨_, isFinGoodMap.𝔽₃Map1, φ, Int.castRingHom S, h0⟩))
  λ h ↦ (em' <| f 2 = -1).elim
    ---- Case 2: `f(-1) = 0`, `f(2) ≠ -1`
    (λ h0 ↦ (Case2.solution hf h h0).imp
      (λ ⟨R', _, φ, ι, h1⟩ ↦ ⟨_, isPolyGoodMap.SqSubOne R', φ, ι, h1⟩)
    λ h1 ↦ h1.elim
      (λ ⟨φ, h1⟩ ↦ ⟨_, isFinGoodMap.ℤ₄Map, φ, Int.castRingHom S, h1⟩)
      (λ ⟨φ, h1⟩ ↦ ⟨_, isFinGoodMap.𝔽₃Map2, φ, Int.castRingHom S, h1⟩))
    ---- Case 3: `f(2) = -1`
    (λ h0 ↦ have : Extra.CharTwo R :=
      Extra.CharTwo.Semiring_of_two_eq_zero (Case2.CharTwo'_of_map_two hf h h0)
    (Case3.solution hf).imp
      (λ ⟨φ, h0⟩ ↦ ⟨_, isPolyGoodMap.SubOne R, RingHom.id R, φ, h0⟩)
    λ h1 ↦ h1.elim
      (λ ⟨φ, h1⟩ ↦ ⟨_, isFinGoodMap.𝔽₂εMap, φ, Int.castRingHom S, h1⟩)
    λ h1 ↦ h1.elim
      (λ ⟨φ, ι, h1⟩ ↦ ⟨_, isFinGoodMap.𝔽₄Map, φ, ι, h1⟩)
      (λ ⟨φ, h1⟩ ↦ ⟨_, isFinGoodMap.𝔽₂Map, φ, Int.castRingHom S, h1⟩))

theorem isNontrivialAnswer.trans_Hom {X Y : BundledRingFun.{u, v}}
    (hA : isNontrivialAnswer X) (F : X.Hom Y) : isNontrivialAnswer Y :=
  hA.imp (λ ⟨A, h, ⟨G⟩⟩ ↦ ⟨A, h, ⟨F.trans G⟩⟩) (λ ⟨A, h, ⟨G⟩⟩ ↦ ⟨A, h, ⟨F.trans G⟩⟩)

theorem NontrivialGood.isNontrivialAnswer (hf : NontrivialGood f) :
    isNontrivialAnswer (ofFun f) :=
  (PeriodEquiv.toQuotientMap_ReducedGood hf).isNontrivialAnswer.trans_Hom
    (Hom.ofRingHom_right (ofFun (PeriodEquiv.toQuotientMap hf))
      (PeriodEquiv.toRingCon hf).mk')





/-! ### Summary -/

/-- Final solution for `NontrivialGood` -/
theorem NontrivialGood_iff_isNontrivialAnswer :
    NontrivialGood f ↔ isNontrivialAnswer (ofFun f) :=
  ⟨NontrivialGood.isNontrivialAnswer, isNontrivialAnswer.NontrivialGood⟩

/-- Final solution -/
theorem final_solution : good f ↔ isNontrivialAnswer (ofFun f) ∨ f = 0 :=
  good_iff_Nontrivial_or_eq_zero.trans <|
    or_congr_left NontrivialGood_iff_isNontrivialAnswer
