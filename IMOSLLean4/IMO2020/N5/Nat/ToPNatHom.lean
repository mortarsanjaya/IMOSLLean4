/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.Nat.MulMap
import Mathlib.Data.PNat.Basic

/-!
# Correspondence between `MulMap M` and `ℕ+ →* M`

We provide a canonical correspondence between `MulMap M` and `ℕ+ →* M`.
-/

namespace IMOSL
namespace IMO2020N5
namespace Nat
namespace MulMap

variable [MulOneClass M]

def toPNatHom (f : MulMap M) : ℕ+ →* M :=
  { toFun := λ n ↦ f n.1
    map_one' := f.map_one'
    map_mul' := λ m n ↦ f.map_mul' m.2 n.2 }

def ofPNatHom (φ : ℕ+ →* M) : MulMap M :=
  { toFun := λ n ↦ dite (0 < n) (φ ⟨n, ·⟩) (λ _ ↦ 1)
    map_zero' := rfl
    map_one' := φ.map_one
    map_mul' := λ hm hn ↦ by
      simp only [dif_pos, hm, hn, mul_pos hm hn]
      exact φ.map_mul ⟨_, hm⟩ ⟨_, hn⟩ }

lemma toPNatHom_apply (f : MulMap M) (n : ℕ+) : f.toPNatHom n = f n.1 := rfl

lemma ofPNatHom_apply (φ : ℕ+ →* M) (n : ℕ) :
    ofPNatHom φ n = dite (0 < n) (φ ⟨n, ·⟩) (λ _ ↦ 1) := rfl

lemma ofPNatHom_apply_PNat (φ : ℕ+ →* M) (n : ℕ+) : ofPNatHom φ n = φ n :=
  dif_pos n.2

lemma toPNatHom_ofPNatHom (φ : ℕ+ →* M) : (ofPNatHom φ).toPNatHom = φ :=
  MonoidHom.ext λ n ↦ dif_pos n.2

lemma ofPNatHom_toPNatHom (f : MulMap M) : ofPNatHom f.toPNatHom = f :=
  MulMap.ext λ n ↦ n.eq_zero_or_pos.elim (λ h ↦ h ▸ f.map_zero.symm) (λ h ↦ dif_pos h)

def toPNatHomEquiv : MulMap M ≃ (ℕ+ →* M) :=
  { toFun := toPNatHom
    invFun := ofPNatHom
    left_inv := ofPNatHom_toPNatHom
    right_inv := toPNatHom_ofPNatHom }
