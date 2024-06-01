/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.A5Defs
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# IMO 2012 A5 (Lift to commutative subrings)

Let `f : R → S` be a non-trivial good function, and fix `x : R`.
We lift `f` to `f' : ℤ[x] → S'` for some commutative subring `S' ⊆ S`.
This is useful as this allows us to generalize commutative-based results.
-/

namespace IMOSL
namespace IMO2012A5
namespace CommSubring

/-! ### Restricting `S` to the subring generated by `f(R)` -/

section

variable [CommSemiring R] [Ring S]

def CommRing_of_good_map {f : R → S} (hf : good f) :
    CommRing (Subring.closure (Set.range f)) :=
  Subring.closureCommRingOfComm λ _ ⟨a, h⟩ _ ⟨b, h0⟩ ↦
    h ▸ h0 ▸ map_commute_of_commute hf (mul_comm a b)

def codomainLift (f : R → S) (x : R) : Subring.closure (Set.range f) :=
  ⟨f x, Subring.subset_closure (Set.mem_range_self x)⟩

lemma codomainLift_is_good {f : R → S} (hf : good f) : good (codomainLift f) :=
  λ a b ↦ Subtype.ext (hf a b)

lemma codomainLift_is_NontrivialGood {f : R → S} (hf : NontrivialGood f) :
    NontrivialGood (codomainLift f) :=
  ⟨codomainLift_is_good hf.is_good, Subtype.ext hf.map_one,
    Subtype.ext hf.map_zero_add_one⟩

end



/-! ### Restricting `R` to subring generated by one element -/

variable [Ring R] [Ring S] (c : R)

instance instCommRingClosure_of_singleton : CommRing (Subring.closure {c}) :=
  Subring.closureCommRingOfComm λ _ h _ h0 ↦ h ▸ h0 ▸ rfl

def oneVarDomainLift (f : R → S) (x : Subring.closure {c}) : S := f x

lemma oneVarDomainLift_is_good {f : R → S} (hf : good f) :
    good (oneVarDomainLift c f) :=
  λ _ _ ↦ hf _ _

lemma oneVarDomainLift_is_NontrivialGood {f : R → S} (hf : NontrivialGood f) :
    NontrivialGood (oneVarDomainLift c f) :=
  ⟨oneVarDomainLift_is_good c hf.is_good, hf.map_one, hf.map_zero_add_one⟩

abbrev OneVarRange (f : R → S) : Type* :=
  Subring.closure (Set.range (oneVarDomainLift c f))

def OneVarRange_commRing_of_good {f : R → S} (hf : good f) :
    CommRing (OneVarRange c f) :=
  CommRing_of_good_map (oneVarDomainLift_is_good c hf)

def oneVarCommLift (f : R → S) : Subring.closure {c} → OneVarRange c f :=
  codomainLift (oneVarDomainLift c f)

lemma oneVarCommLift_is_NontrivialGood {f : R → S} (hf : NontrivialGood f) :
    NontrivialGood (oneVarCommLift c f) :=
  codomainLift_is_NontrivialGood (oneVarDomainLift_is_NontrivialGood c hf)

/-- Existence version of the above -/
theorem oneVarCommLift_exists {R : Type u} {S : Type v} [Ring R] [Ring S]
    {f : R → S} (hf : NontrivialGood f) (c : R) :
    ∃ (R' : Type u) (_ : CommRing R')
        (φ : R' →+* R) (_ : Function.Injective φ) (_ : c ∈ Set.range φ)
      (S' : Type v) (_ : CommRing S') (ρ : S' →+* S) (_ : Function.Injective ρ)
      (f' : R' → S') (_ : ∀ a, f (φ a) = ρ (f' a)), NontrivialGood f' :=
  ---- Constructing `R'`
  ⟨Subring.closure {c},
  instCommRingClosure_of_singleton c,
  SubringClass.subtype _,
  λ _ _ ↦ Subtype.ext,
  ⟨⟨c, Subring.subset_closure rfl⟩, rfl⟩,
  ---- Constructing `S'`
  OneVarRange c f,
  OneVarRange_commRing_of_good c hf.is_good,
  SubringClass.subtype _,
  λ _ _ ↦ Subtype.ext,
  ---- Constructing `f'`
  λ a ↦ ⟨f a.1, Subring.subset_closure ⟨a, rfl⟩⟩,
  λ _ ↦ rfl,
  oneVarCommLift_is_NontrivialGood c hf⟩



/-- Existence version of the above (target has no zero divisors) -/
theorem oneVarCommLiftDomain_exists {R : Type u} {S : Type v} [Ring R] [Ring S]
    [NoZeroDivisors S] {f : R → S} (hf : NontrivialGood f) (c : R) :
    ∃ (R' : Type u) (_ : CommRing R')
        (φ : R' →+* R) (_ : Function.Injective φ) (_ : c ∈ Set.range φ)
      (S' : Type v) (_ : CommRing S') (_ : NoZeroDivisors S')
        (ρ : S' →+* S) (_ : Function.Injective ρ)
      (f' : R' → S') (_ : ∀ a, f (φ a) = ρ (f' a)), NontrivialGood f' :=
  ---- Constructing `R'`
  ⟨Subring.closure {c},
  instCommRingClosure_of_singleton c,
  SubringClass.subtype _,
  λ _ _ ↦ Subtype.ext,
  ⟨⟨c, Subring.subset_closure rfl⟩, rfl⟩,
  ---- Constructing `S'`
  OneVarRange c f,
  OneVarRange_commRing_of_good c hf.is_good,
  Subsemiring.noZeroDivisors _,
  SubringClass.subtype _,
  λ _ _ ↦ Subtype.ext,
  ---- Constructing `f'`
  λ a ↦ ⟨f a.1, Subring.subset_closure ⟨a, rfl⟩⟩,
  λ _ ↦ rfl,
  oneVarCommLift_is_NontrivialGood c hf⟩
