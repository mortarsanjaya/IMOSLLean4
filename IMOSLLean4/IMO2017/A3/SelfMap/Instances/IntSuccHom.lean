/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Int.Order.Basic

/-!
# Homomorphism from `Int.succ`

Given a permutation `f : α ≃ α` and `x : α`, there is a (unique) homomorphism
  from `Int.succ` to `f`, defined by mapping `k` to `f^k(x)`.
We denote this homomorphism by `IntSuccHomOf f x`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap
namespace IntSuccHom

def mk (f : Equiv.Perm α) (x : α) : Hom Int.succ f :=
  ⟨λ k ↦ (f ^ k) x, λ k ↦ by
    change (f ^ (k + 1)) x = (f * f ^ k) x
    rw [add_comm, zpow_one_add]⟩

lemma mk_apply (f : Equiv.Perm α) (x : α) (k : ℤ) : mk f x k = (f ^ k) x := rfl

lemma apply_eq_iterate {f : Equiv.Perm α} (e : Hom Int.succ f) (k : ℤ) :
    e k = (f ^ k) (e 0) :=
  k.inductionOn' 0 rfl
    (λ k _ h ↦ by rw [add_comm, zpow_one_add, f.mul_apply,
      ← h, ← e.Semiconj, Int.succ, add_comm])
    (λ k _ h ↦ f.injective <| by rw [← f.mul_apply, ← zpow_one_add,
       ← e.Semiconj, Int.succ, add_comm, add_sub_cancel'_right, ← h])

lemma mk_map_zero_eq {f : Equiv.Perm α} (e : Hom Int.succ f) : mk f (e 0) = e :=
  (Hom.ext (apply_eq_iterate e)).symm


def type_equiv (f : Equiv.Perm α) : α ≃ Hom Int.succ f where
  toFun := mk f
  invFun := λ e ↦ e 0
  left_inv := λ _ ↦ rfl
  right_inv := mk_map_zero_eq

lemma mk_injective (f : Equiv.Perm α) : (mk f).Injective :=
  (type_equiv f).injective

lemma mk_surjective (f : Equiv.Perm α) : (mk f).Surjective :=
  (type_equiv f).surjective

lemma mk_bijective (f : Equiv.Perm α) : (mk f).Bijective :=
  (type_equiv f).bijective
