/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2017.A6.A6RingCon.Defs
import Mathlib.RingTheory.Congruence.Basic

/-!
# IMO 2017 A6 (P2, Basic lemmas about ring congruence on good functions)

Let $f : R → G$ be an $ι$-good function.
We show that the period ideal $I_f$ is $R$ iff $f = 0$ and is $0$ iff $f$ is non-periodic.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### When is the induced ring congruence equal to ⊤? -/

namespace GoodFun

variable [AddCommMonoid R] [Semigroup R] [AddZeroClass G] [IsCancelAdd G] {ι : G → R}

theorem inducedRingCon_zero : (0 : GoodFun ι).inducedRingCon = ⊤ :=
  RingCon.ext λ _ _ ↦ iff_true_intro λ _ ↦ rfl

theorem eq_zero_of_inducedRingCon {f : GoodFun ι} (h : f.inducedRingCon = ⊤) : f = 0 := by
  replace h (x) : f x = f 0 := f.inducedRingConEquiv_map_eq (h ▸ trivial)
  have h0 : f 0 = 0 := add_right_cancel (by simpa [h] using good_def ι f 0 0)
  exact GoodFun.ext λ x ↦ (h x).trans h0

theorem eq_zero_iff_inducedRingCon {f : GoodFun ι} : f = 0 ↔ f.inducedRingCon = ⊤ :=
  ⟨λ h ↦ h ▸ inducedRingCon_zero, f.eq_zero_of_inducedRingCon⟩

end GoodFun





/-! ### When is the induced ring congruence equal to ⊥? -/

section

variable [AddCommMonoid R] [Semigroup R] [Add G] [IsCancelAdd G] {ι : G → R}

theorem NonperiodicGoodFun.inducedRingCon_eq (f : NonperiodicGoodFun ι) :
    f.inducedRingCon = ⊥ :=
  RingCon.ext λ _ _ ↦ ⟨period_imp_eq ι (f := f), λ h x ↦ congrArg (λ a ↦ f (x + a)) h⟩

theorem GoodFun.nonperiodic_of_inducedRingCon {f : GoodFun ι} (h : f.inducedRingCon = ⊥) :
    IsNonperiodicGoodFun ι f :=
  ⟨f.IsGoodFun, (congrFun₂ (congrArg DFunLike.coe h) _ _).to_iff.mp⟩

theorem GoodFun.IsNonperiodicGoodFun_if_inducedRingCon {f : GoodFun ι} :
    IsNonperiodicGoodFun ι f ↔ f.inducedRingCon = ⊥ :=
  ⟨λ h ↦ h.toNonperiodicGoodFun.inducedRingCon_eq, f.nonperiodic_of_inducedRingCon⟩

end
