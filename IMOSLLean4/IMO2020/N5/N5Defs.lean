/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.PNat.Prime

/-!
# IMO 2020 N5 (Definitions)

Fix a monoid `M` and a monoid homomorphism `f : ℕ+ → M`.
Given `n : ℕ+`, we say that `n` is *`f`-reflexive* if `f(a) = f(b)` whenever `a + b = n`.
We say that `f` is:
1. *good*, if there exists infinitely many `f`-reflexive integers;
2. of *local class* at a prime `p`, if `p^k` is `f`-reflexive for all `k : ℕ`;
3. of *global class* if infinitely many primes are `f`-reflexive.
We prove basic properties of these maps.
-/

namespace IMOSL
namespace IMO2020N5

variable [MulOneClass M]

abbrev reflexive (f : ℕ+ →* M) (n : ℕ+) := ∀ a b, a + b = n → f a = f b

def good (f : ℕ+ →* M) := ∀ N, ∃ n > N, reflexive f n

def localClass (p : Nat.Primes) (f : ℕ+ →*  M) := ∀ k, reflexive f (p ^ k)

def globalClass (f : ℕ+ →* M) := ∀ N : ℕ+, ∃ p : Nat.Primes, N < p ∧ reflexive f p



lemma localClass.is_good {f : ℕ+ →* M} (hf : localClass p f) : good f :=
  λ N ↦ ⟨p ^ N.1, Nat.lt_pow_self p.2.one_lt N, hf N⟩

lemma globalClass.is_good {f : ℕ+ →* M} (hf : globalClass f) : good f :=
  λ N ↦ (hf N).elim λ p h ↦ ⟨p, h⟩

lemma reflexive.one (f : ℕ+ →* M) : reflexive f 1 :=
  λ _ b h ↦ h.not_gt.elim (b.one_le.trans_lt (PNat.lt_add_left _ _))
