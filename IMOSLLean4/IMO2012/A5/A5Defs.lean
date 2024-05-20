/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs

/-!
# IMO 2012 A5 (Definitions)

Let $R$ be a ring and $S$ be a domain.
Find all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(xy + 1) = f(x) f(y) + f(x + y). $$

This file defines the functional equation and prove some basic properties.
We also define some notions; we say that $f$ is
* *good* if it satisfies the above functional equation;
* *non-trivial good* if $f$ is good, $f(1) = 0$, and $f(0) = -1$;
* *reduced good* if $f$ is non-trivial good and there is no non-zero $f$-periodic element.
-/

namespace IMOSL
namespace IMO2012A5

variable [NonAssocSemiring R] [NonAssocSemiring S]

/-- The main problem. -/
def good (f : R → S) := ∀ x y : R, f (x * y + 1) = f x * f y + f (x + y)

structure NontrivialGood (f : R → S) : Prop where
  is_good : good f
  map_one : f 1 = 0
  map_zero_add_one : f 0 + 1 = 0

lemma NontrivialGood.map_zero {S} [NonAssocRing S]
    {f : R → S} (hf : NontrivialGood f) : f 0 = -1 :=
  eq_neg_of_add_eq_zero_left hf.map_zero_add_one

structure ReducedGood (f : R → S) extends NontrivialGood f : Prop where
  period_imp_eq (c d) (_ : ∀ x, f (x + c) = f (x + d)) : c = d

lemma ReducedGood.period_imp_zero {f : R → S} (hf : ReducedGood f)
    (h : ∀ x, f (x + c) = f x) : c = 0 :=
  hf.period_imp_eq c 0 λ x ↦ by rw [h, add_zero]
