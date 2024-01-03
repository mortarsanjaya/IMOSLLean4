/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.Extra.MulMap.Basic
import Mathlib.Data.PNat.Basic

/-!
# Equivalence between `MulMap M` and `ℕ+ →* M`

We provide the natural equivalence between `MulMap M` and `ℕ+ →* M`.
The map from `MulMap M` to `ℕ+ →* M` is given by ignoring `0`.
The map from `ℕ+ →* M` to `MulMap M` is given by imposing `f(0) = 1`.

When `M` is a commutative monoid, this equivalence is an isomorphism.
We try to minimize imports, so we are not going to prove this fact.
-/

namespace IMOSL
namespace IMO2020N5
namespace MulMap

variable {M : Type*} [MulOneClass M]

/-- The function from `MulMap M` to `ℕ+ →* M` -/
def toPNatHom (f : MulMap M) : ℕ+ →* M :=
  { toFun := λ n ↦ f n
    map_one' := f.map_one'
    map_mul' := λ x y ↦ f.map_mul' x.2 y.2 }

/-- The function from `ℕ+ →* M` to `MulMap M` -/
def ofPNatHom (φ : ℕ+ →* M) : MulMap M :=
  { toFun := λ n ↦ dite (0 < n) (λ h ↦ φ ⟨n, h⟩) (λ _ ↦ 1)
    map_zero' := rfl
    map_one' := (dif_pos Nat.one_pos).trans φ.map_one
    map_mul' := λ hx hy ↦ by
      change dite _ _ _ = dite _ _ _ * dite _ _ _
      rw [dif_pos (Nat.mul_pos hx hy), dif_pos hx, dif_pos hy, ← φ.map_mul]
      rfl }

lemma toPNatHom_spec (f : MulMap M) (n : ℕ+) : toPNatHom f n = f n := rfl

lemma ofPNatHom_spec (φ : ℕ+ →* M) (n : ℕ+) : ofPNatHom φ n = φ n :=
  dif_pos n.pos

lemma ofPNatHom_toPNatHom (f : MulMap M) : ofPNatHom (toPNatHom f) = f :=
  ext λ n ↦ n.eq_zero_or_pos.symm.elim (λ h ↦ dif_pos h)
    (λ h ↦ (dif_neg h.not_gt).trans <| h.symm ▸ f.map_zero.symm)

lemma toPNatHom_ofPNatHom (φ : ℕ+ →* M) : toPNatHom (ofPNatHom φ) = φ :=
  MonoidHom.ext (ofPNatHom_spec φ)
