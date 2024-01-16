/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A7.A7General
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# IMO 2012 A7, Subalgebra Structure

Let `R` be a totally ordered commutative ring and `σ` be a set.
Let `S` be an `R`-subalgebra of `σ → R`.
We prove that the meta-closure of `S` is also an `R`-subalgebra of `σ → R`.
-/

namespace IMOSL
namespace IMO2012A7

variable {σ R : Type*} [LinearOrderedCommRing R]

/-! ### Extra lemmas -/

lemma Pi_smul_inf_of_nonneg {r : R} (h : 0 ≤ r) (a b : σ → R) :
    r • (a ⊓ b) = r • a ⊓ r • b :=
  funext λ i ↦ smul_min_of_nonneg h (a i) (b i)

lemma Pi_smul_sup_of_nonneg {r : R} (h : 0 ≤ r) (a b : σ → R) :
    r • (a ⊔ b) = r • a ⊔ r • b :=
  funext λ i ↦ smul_max_of_nonneg h (a i) (b i)

lemma Pi_smul_inf_of_nonpos {r : R} (h : r ≤ 0) (a b : σ → R) :
    r • (a ⊓ b) = r • a ⊔ r • b :=
  funext λ i ↦ smul_min_of_nonpos h (a i) (b i)

lemma Pi_smul_sup_of_nonpos {r : R} (h : r ≤ 0) (a b : σ → R) :
    r • (a ⊔ b) = r • a ⊓ r • b :=
  funext λ i ↦ smul_max_of_nonpos h (a i) (b i)





/-! ### Subalgebra structure of meta-closure -/

namespace MetaClosure

lemma algebraMap_mem (S : Subalgebra R (σ → R)) (r : R) :
    MetaClosure (λ x ↦ x ∈ S) (algebraMap R (σ → R) r) :=
  ofMem (Subalgebra.algebraMap_mem S r)

def PiSubalgebra_mk (S : Subalgebra R (σ → R)) : Subalgebra R (σ → R) :=
  { PiSubring_mk S.toSubring with
    algebraMap_mem' := algebraMap_mem S }

end MetaClosure





/-! ### Subalgebra structure via `BinOpClosure` -/

theorem SupInfClosure_exists_Subalgebra (S : Subalgebra R (σ → R)) :
    ∃ T : Subalgebra R (σ → R),
      setOf (BinOpClosure Sup.sup (BinOpClosure Inf.inf (λ x ↦ x ∈ S))) = T.carrier :=
  (SupInfClosure_eq_MetaClosure (λ x ↦ x ∈ S)) ▸ ⟨MetaClosure.PiSubalgebra_mk S, rfl⟩
