/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.Nat.MulMap.Basic

/-!
# IMO 2020 N5, ℕ-version (Basic File)

(The ℕ-version files store the bulk of the proofs of the main lemmas.)

Let `M` be a commutative cancellative monoid.
Given `f : MulMap M` (as defined in `N5MulMap.lean`), a natural number
  `n : ℕ` is said to be `f`-*nice* if the following holds:
  for any `a b : ℕ` such that `a, b > 0` and `a + b = n`, we have `f(a) = f(b)`.
We say that `f` is *good* if the set of `f`-nice numbers is infinite.
Find all `f : MulMap M` such that `f` is good.

This file provides the definition of `f`-nice numbers.
We also prove that the set of `f`-nice numbers is divisor-closed.
That is, if `n ∣ m` and `n ≠ 0` is `f`-nice, then `n` is `f`-nice.
The others are deferred into other files, since they need more import.
-/

namespace IMOSL
namespace IMO2020N5
namespace Nat

def nice (f : ℕ → α) (n : ℕ) := ∀ a b, 0 < a → 0 < b → a + b = n → f a = f b

lemma nice_one (f : ℕ → α) : nice f 1 :=
  λ _ _ ha hb h ↦ absurd h (Nat.ne_of_lt <| Nat.add_le_add ha hb).symm

lemma nice_of_dvd_nice [CancelMonoid M] (h : 0 < n)
    {f : MulMap M} (h0 : nice f n) (h1 : m ∣ n) : nice f m := by
  rcases h1 with ⟨k, rfl⟩
  rintro a b ha hb rfl
  replace h : 0 < k := Nat.pos_of_dvd_of_pos (k.dvd_mul_left _) h
  specialize h0 (a * k) (b * k) (Nat.mul_pos ha h)
    (Nat.mul_pos hb h) (a.add_mul b k).symm
  rwa [f.map_mul ha h, f.map_mul hb h, mul_left_inj] at h0
