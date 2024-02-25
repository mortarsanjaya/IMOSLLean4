/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Basic
import Mathlib.Dynamics.PeriodicPts

/-!
# `FinMap`

For any `n : ℕ`, we denote by `FinMap n` the
  self-map on `Fin (n + 1)` defined by `x ↦ x + 1`.
We prove some properties of `FinMap n`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

open Function

/-- The map `x ↦ x + 1` on `Fin n.succ`. -/
abbrev FinMap (n : ℕ) (k : Fin n.succ) : Fin n.succ := k + 1

lemma FinMap_iterate_Nat (m : Fin n.succ) :
    ∀ k, (FinMap n)^[k] m = m + (k : Fin n.succ)
  | 0 => by rw [Nat.cast_zero, add_zero]; rfl
  | k + 1 => by rw [iterate_succ_apply', FinMap_iterate_Nat m,
                  Nat.cast_succ, ← add_assoc]

lemma FinMap_iterate_eq_self_iff (m : Fin n.succ) :
    (FinMap n)^[k] m = m ↔ n.succ ∣ k := by
  rw [FinMap_iterate_Nat, add_right_eq_self, Fin.nat_cast_eq_zero]

/-- Homomorphism from `FinMap` defined by a periodic point -/
def FinMapHom (hx : minimalPeriod f x = Nat.succ n) : Hom (FinMap n) f where
  toFun := λ k ↦ f^[k] x
  Semiconj := λ k ↦ by
    change f^[(k + 1 % _) % _] x = f (f^[k] x)
    rw [Nat.add_mod_mod, ← f.iterate_succ_apply',
      eq_comm, ← iterate_mod_minimalPeriod_eq, hx]
