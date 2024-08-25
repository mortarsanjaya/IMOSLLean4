/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs

/-!
# IMO 2021 A8 (Definitions)

Let $F$ be a field and $S$ be a domain.
Find all functions $f : F → S$ such that for any $a, b, c ∈ F$,
$$ (f(a) - f(b))(f(b) - f(c))(f(c) - f(a))
  = f(ab^2 + bc^2 + ca^2) - f(ba^2 + ac^2 + cb^2). $$

...
-/

namespace IMOSL
namespace IMO2021A8

variable [Semiring R] [NonAssocRing S]

/-- The main problem. -/
def good (f : R → S) := ∀ a b c : R, (f a - f b) * (f b - f c) * (f c - f a)
    = f (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) - f (b * a ^ 2 + c * b ^ 2 + a * c ^ 2)
