/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Basic
import Mathlib.Logic.Equiv.Defs

/-!
### Homomorphisms from `Nat.succ`

Given `x : α`, there is a (unique) homomorphism from `Nat.succ` to `f`,
  defined by  mapping each `k : ℕ` to `f^[k] x`.
We denote this homomorphism by `NatSuccHomOf f x`.

Categorically, the category of self-maps is representable by `Nat.succ`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace NatSuccHom

def mk (f : α → α) (x : α) : Hom Nat.succ f :=
  ⟨λ k ↦ f^[k] x, λ k ↦ f.iterate_succ_apply' k x⟩

lemma mk_apply (f : α → α) (x : α) (k : ℕ) : mk f x k = f^[k] x := rfl

lemma apply_eq_iterate (e : Hom Nat.succ f) : ∀ k, e k = f^[k] (e 0)
  | 0 => rfl
  | k + 1 => by rw [e.Semiconj, f.iterate_succ_apply', apply_eq_iterate e k]

lemma mk_map_zero_eq (e : Hom Nat.succ f) : mk f (e 0) = e :=
  (Hom.ext (apply_eq_iterate e)).symm


def type_equiv (f : α → α) : α ≃ Hom Nat.succ f where
  toFun := mk f
  invFun := λ e ↦ e 0
  left_inv := λ _ ↦ rfl
  right_inv := mk_map_zero_eq

lemma mk_injective (f : α → α) : (mk f).Injective :=
  (type_equiv f).injective

lemma mk_surjective (f : α → α) : (mk f).Surjective :=
  (type_equiv f).surjective

lemma mk_bijective (f : α → α) : (mk f).Bijective :=
  (type_equiv f).bijective
