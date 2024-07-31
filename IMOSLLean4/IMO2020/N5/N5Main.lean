/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.N5Defs
import IMOSLLean4.IMO2020.N5.Nat.N5Nat
import IMOSLLean4.IMO2020.N5.Nat.ToPNatHom

/-!
# IMO 2020 N5 (Main results)

This file proves the main results about local class and global class maps.
Namely, we characterize all local class maps.
-/

namespace IMOSL
namespace IMO2020N5

variable [MulOneClass M] {p : Nat.Primes}

/-! ### Transferring between `MulMap M` and `ℕ+ →* M` -/

lemma PNat.reflexive.toNatReflexive {f : ℕ+ →* M} (hf : PNat.reflexive f p) :
    Nat.reflexive (Nat.MulMap.ofPNatHom f) p := λ a ha b hb h ↦ by
  lift a to ℕ+ using ha; lift b to ℕ+ using hb
  rw [Nat.MulMap.ofPNatHom_apply_PNat, Nat.MulMap.ofPNatHom_apply_PNat]
  exact hf a b (PNat.coe_injective h)

lemma Nat.reflexive.toPNatReflexive {f : Nat.MulMap M} (hf : Nat.reflexive f p) :
    PNat.reflexive f.toPNatHom p :=
  λ a b h ↦ hf a.1 a.2 b.1 b.2 (congrArg (λ x : ℕ+ ↦ x.1) h)

lemma PNat.reflexive_iff_MulMap {f : ℕ+ →* M} :
    PNat.reflexive f p ↔ Nat.reflexive (Nat.MulMap.ofPNatHom f) p :=
  ⟨PNat.reflexive.toNatReflexive, λ h ↦ Nat.MulMap.toPNatHom_ofPNatHom f ▸ h.toPNatReflexive⟩





/-! ### The main results -/

/- ... -/
