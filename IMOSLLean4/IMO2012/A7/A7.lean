/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A7.A7PiRing
import Mathlib.Data.MvPolynomial.CommRing

/-!
# IMO 2012 A7

Given a distributing lattice $α$, the *inf-closure* (resp. *sup-closure*) of a subset
  $S ⊆ α$ is the smallest set containing $S$ that is closed under infimum (resp. supremum).
The *meta-closure* of $S$ is the sup-closure of the inf-closure of $S$.

Let $R$ be a totally ordered commutative ring and $σ$ be a set.
Let $R[σ]$ denote the ring of multivariate polynomials with variable set $σ$.
Let $S$ denote the meta-closure of $R[σ]$ as a subset of $R^σ → R$.
Prove that $S$ is a subring of $R^σ → R$.

### Note

The original formulation only asks to prove that $S$ is closed under multiplication.
However, the official solution states that it is easier to prove that $S$ is a ring.
-/

namespace IMOSL
namespace IMO2012A7

/-- Curry-ed version of `MvPolynomial.eval` -/
abbrev MvPolynomial_evalCurry [CommRing R] : MvPolynomial σ R →+* ((σ → R) → R) :=
  Pi.ringHom MvPolynomial.eval

/-- The image of `MvPolynomial σ R` in `(σ → R) → R` as a ring -/
abbrev MvPolynomial_image (σ R : Type*) [CommRing R] : Subring ((σ → R) → R) :=
  (MvPolynomial_evalCurry (R := R) (σ := σ)).range

theorem final_solution (σ R : Type*) [LinearOrderedCommRing R] :
    ∃ T : Subring ((σ → R) → R), T.carrier =
      setOf (BinOpClosure Sup.sup <| BinOpClosure Inf.inf
        λ x ↦ x ∈ MvPolynomial_image σ R) :=
  SupInfClosure_exists_Subring _
