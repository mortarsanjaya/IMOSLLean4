/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.Nat.MulMap.PNatHomEquiv
import IMOSLLean4.IMO2020.N5.Nat.Basic

/-!
# IMO 2020 N5 (Basic File)

Let `M` be a commutative cancellative monoid.
Given `f : ℕ+ →* M`, a natural number `n : ℕ` is said to be `f`-*nice* if
  for any `a b : ℕ+` such that `a + b = n`, we have `f(a) = f(b)`.
We say that `f` is *good* if the set of `f`-nice numbers is infinite.
Find all `f : ℕ+ →* M` such that `f` is good.

This file provides the definition of `f`-nice numbers.
We also prove that the set of `f`-nice numbers is divisor-closed.
That is, if `n ∣ m` and `n` is `f`-nice, then `m` is `f`-nice.
The others are deferred into other files, since they need more import.
-/

namespace IMOSL
namespace IMO2020N5

def nice (f : ℕ+ → α) (n : ℕ+) := ∀ a b, a + b = n → f a = f b

lemma nice_one (f : ℕ+ → α) : nice f 1 :=
  λ a b h ↦ absurd (add_le_add a.one_le b.one_le) h.not_gt

lemma nice_of_dvd_nice [CancelMonoid M]
    {f : ℕ+ →* M} (h : nice f n) (h0 : m ∣ n) : nice f m := by
  rcases h0 with ⟨k, rfl⟩
  rintro a b rfl
  specialize h (a * k) (b * k) (add_mul a b k).symm
  rwa [f.map_mul, f.map_mul, mul_left_inj] at h



/-! ### Equivalence with the ℕ version -/

variable [CancelMonoid M]

lemma niceNat_of_nice {φ : ℕ+ →* M} (h : nice φ n) :
    Nat.nice (MulMap.ofPNatHom φ) n := λ a b ha hb h0 ↦ by
  specialize h ⟨a, ha⟩ ⟨b, hb⟩ (PNat.coe_injective h0)
  rwa [← MulMap.ofPNatHom_spec, ← MulMap.ofPNatHom_spec] at h

lemma nice_of_niceNat {f : MulMap M} (n_pos : 0 < n) (h : Nat.nice f n) :
    nice f.toPNatHom ⟨n, n_pos⟩ :=
  λ a b h0 ↦ h a.1 b.1 a.2 b.2 (congr_arg (λ (n : ℕ+) ↦ (n : ℕ)) h0)

lemma nice_iff_niceNat {φ : ℕ+ →* M} :
    nice φ n ↔ Nat.nice (MulMap.ofPNatHom φ) n :=
  ⟨niceNat_of_nice, λ h ↦ MulMap.toPNatHom_ofPNatHom φ ▸ nice_of_niceNat n.pos h⟩
