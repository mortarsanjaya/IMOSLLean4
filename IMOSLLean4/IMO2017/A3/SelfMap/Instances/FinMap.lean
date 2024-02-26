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
We also define the coproduct of multiple `FinMap`s.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

open Function

/-- The map `x ↦ x + 1` on `Fin n.succ`. -/
abbrev FinMap (n : ℕ) (k : Fin n.succ) : Fin n.succ := k + 1

def FinMap_asEquiv (n : ℕ) : Equiv.Perm (Fin n.succ) where
  toFun := FinMap n
  invFun := λ k ↦ k - 1
  left_inv := λ k ↦ add_sub_cancel k 1
  right_inv := λ k ↦ sub_add_cancel k 1

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



/-- `Σ_{i ∈ I} FinMap β(i)`, where `β : I → ℕ` is an arbitrary function. -/
def FinMapSigma (β : I → ℕ) :
    (i : I) × Fin (β i).succ → (i : I) × Fin (β i).succ :=
  Sigma.map id λ i ↦ FinMap (β i)

lemma FinMapSigma_apply (β : I → ℕ) (p) :
    FinMapSigma β p = ⟨p.1, p.2 + 1⟩ := rfl

lemma FinMapSigma_apply' (β : I → ℕ) (x : Fin (β i).succ) :
    FinMapSigma β ⟨i, x⟩ = ⟨i, x + 1⟩ := rfl



/-- `Σ_{n ∈ S} FinMap n` for a subset `S ⊆ ℕ`. -/
def FinMapSetSigma (S : Set ℕ) := FinMapSigma λ n : S ↦ n.1

lemma FinMapSetSigma_apply (S : Set ℕ) (p) :
    FinMapSetSigma S p = ⟨p.1, p.2 + 1⟩ := rfl

lemma FinMapSetSigma_apply' (S : Set ℕ) {n : S} (x : Fin n.1.succ) :
    FinMapSetSigma S ⟨n, x⟩ = ⟨n, x + 1⟩ := rfl
