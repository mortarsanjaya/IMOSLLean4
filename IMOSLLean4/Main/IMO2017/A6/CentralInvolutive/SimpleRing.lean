/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2017.A6.CentralInvolutive.Defs
import Mathlib.RingTheory.SimpleRing.Field

/-!
# Central involutive elements of a simple ring

Let $R$ be a simple ring.
Then the only central involutive elements of $R$ are $±1$.
-/

namespace IMOSL
namespace IMO2017A6
namespace CentralInvolutive

variable [Ring R] [IsSimpleRing R]

instance : NoZeroDivisors (Subring.center R) := by
  refine ⟨λ h ↦ (ne_or_eq _ 0).imp_left λ h0 ↦ ?_⟩
  obtain ⟨c, h1⟩ := (IsSimpleRing.isField_center R).mul_inv_cancel h0
  simpa [mul_assoc, h1] using congrArg (· * c) h

theorem eq_one_or_neg_one_of_IsSimpleRing (a : CentralInvolutive R) : a = 1 ∨ a = -1 := by
  let b : Subring.center R := ⟨a.val, Subring.mem_center_iff.mpr a.val_mul_comm⟩
  have hb : b = 1 ∨ b = -1 := mul_self_eq_one_iff.mp (Subtype.ext a.val_mul_self_eq_one)
  apply hb.imp <;> exact λ h ↦ CentralInvolutive.ext (congrArg Subtype.val h)
