/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Data.FunLike.Basic

/-!
# Multiplicative map over ℕ

Let `M` be a multiplicative monoid.
A multiplicative map is a function `f : ℕ → M` such that
* `f(0) = f(1) = 1`; and
* `f(mn) = f(m) f(n)` for any `m, n ≠ 0`
We also prove some basic results regarding multiplicative maps.
-/

namespace IMOSL
namespace IMO2020N5
namespace Nat

structure MulMap (M) [MulOneClass M] where
  toFun : ℕ → M
  map_zero' : toFun 0 = 1
  map_one' : toFun 1 = 1
  map_mul' (hm : 0 < m) (hn : 0 < n) : toFun (m * n) = toFun m * toFun n


namespace MulMap

variable [MulOneClass M] (f : MulMap M)

instance {M : outParam Type*} [MulOneClass M] : FunLike (MulMap M) ℕ M where
  coe := toFun
  coe_injective' := λ _ _ _ ↦ by rwa [mk.injEq]

@[ext] theorem ext {f g : MulMap M} (h : ∀ n, 0 < n → f n = g n) : f = g :=
  DFunLike.ext _ _ λ n ↦ n.eq_zero_or_pos.elim
    (λ h ↦ h ▸ f.map_zero'.trans g.map_zero'.symm) (h n)

@[simp] theorem toFun_eq_coe : f.toFun = f := rfl

@[simp] theorem map_zero : f 0 = 1 :=
  f.map_zero'

@[simp] theorem map_one : f 1 = 1 :=
  f.map_one'

@[simp] theorem map_mul (hm : 0 < m) (hn : 0 < n) : f (m * n) = f m * f n :=
  f.map_mul' hm hn

@[simp] theorem map_pow {M} [Monoid M] (f : MulMap M) (hm : 0 < m) :
    ∀ n, f (m ^ n) = f m ^ n
  | 0 => by rw [m.pow_zero, f.map_one, pow_zero]
  | n + 1 => by rw [m.pow_succ, f.map_mul (Nat.pow_pos hm) hm, f.map_pow hm, pow_succ]

theorem map_comm (m n) : f m * f n = f n * f m := by
  obtain rfl | hm : m = 0 ∨ 0 < m := m.eq_zero_or_pos
  · rw [f.map_zero, one_mul, mul_one]
  obtain rfl | hn : n = 0 ∨ 0 < n := n.eq_zero_or_pos
  · rw [f.map_zero, one_mul, mul_one]
  · rw [← f.map_mul hm hn, ← f.map_mul hn hm, m.mul_comm]

theorem map_assoc (k m n) : f k * f m * f n = f k * (f m * f n) := by
  obtain rfl | hk : k = 0 ∨ 0 < k := k.eq_zero_or_pos
  · rw [f.map_zero, one_mul, one_mul]
  obtain rfl | hm : m = 0 ∨ 0 < m := m.eq_zero_or_pos
  · rw [f.map_zero, one_mul, mul_one]
  obtain rfl | hn : n = 0 ∨ 0 < n := n.eq_zero_or_pos
  · rw [f.map_zero, mul_one, mul_one]
  · rw [← f.map_mul hk hm, ← f.map_mul (Nat.mul_pos hk hm) hn,
      k.mul_assoc, f.map_mul hk (Nat.mul_pos hm hn), f.map_mul hm hn]


instance : One (MulMap M) := ⟨⟨λ _ ↦ 1, rfl, rfl, λ _ _ ↦ (one_mul 1).symm⟩⟩

instance {M} [CommMonoid M] : Mul (MulMap M) := ⟨λ f g ↦
  { toFun := λ n ↦ f n * g n
    map_zero' := (congrArg₂ _ f.map_zero' g.map_zero').trans (mul_one 1)
    map_one' := (congrArg₂ _ f.map_one' g.map_one').trans (mul_one 1)
    map_mul' := λ hm hn ↦ by
      show f (_ * _) * g (_ * _) = (f _ * g _) * (f _ * g _)
      rw [f.map_mul hm hn, g.map_mul hm hn, ← mul_assoc, mul_assoc (f _),
        mul_comm (f _) (g _), ← mul_assoc, mul_assoc] }⟩

instance {M} [CommMonoid M] : CommMonoid (MulMap M) :=
  { mul_comm := λ f g ↦ ext λ _ _ ↦ mul_comm _ _
    mul_assoc := λ f g h ↦ ext λ _ _ ↦ mul_assoc _ _ _
    mul_one := λ f ↦ ext λ _ _ ↦ mul_one _
    one_mul := λ f ↦ ext λ _ _ ↦ one_mul _ }
