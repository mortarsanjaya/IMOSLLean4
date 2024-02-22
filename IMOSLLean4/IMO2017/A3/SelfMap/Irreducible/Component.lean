/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.Irreducible.Decomposition
import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Sigma
import Mathlib.Logic.Equiv.Basic

/-!
# Irreducible component of self-maps

Let `f : α → α` be a self-map with corresponding equivalence relation `∼`.
For each equivalence class `S`, there is an induced restriction map `S → S`.
We call this map an irreducible component of `f`.
We show that this restriction map is irreducible.
Furthermore, we show that these maps give a decomposition of `f`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

namespace ptEquiv

variable (f : α → α)

/-- The setoid induced by the point equivalence -/
def mkSetoid : Setoid α := ⟨ptEquiv f, ptEquiv.equivalence f⟩

/-- The quotient induced by the point equivalence -/
def mkQuotient : α → Quotient (mkSetoid f) := Quotient.mk _

end ptEquiv



section

variable (f : α → α) (s : Quotient (ptEquiv.mkSetoid f))

/-- The type defining the domain/codomain of the irreducible component -/
def IrredComponentType := {a : α // Quotient.mk (ptEquiv.mkSetoid f) a = s}

/-- The irreducible component -/
def IrredComponent (b : IrredComponentType f s) : IrredComponentType f s :=
  ⟨f b.1, Eq.trans (Quotient.sound (ptEquiv.of_self_apply_left f b.1)) b.2⟩

end



namespace IrredComponent

variable (f : α → α) (s : Quotient (ptEquiv.mkSetoid f))

/-- The component's underlying type is non-empty -/
lemma type_nonempty : Nonempty (IrredComponentType f s) :=
  s.exists_rep.elim λ a h ↦ ⟨a, h⟩

instance : Nonempty (IrredComponentType f s) := type_nonempty f s

lemma apply_fst (b : IrredComponentType f s) :
    (IrredComponent f s b).1 = f b.1 := rfl

lemma iterate_apply_fst : ∀ (k : ℕ) (b : IrredComponentType f s),
    ((IrredComponent f s)^[k] b).1 = f^[k] b.1
  | 0, _ => rfl
  | m + 1, _ => by rw [Function.iterate_succ_apply', apply_fst,
                  iterate_apply_fst m, f.iterate_succ_apply']

lemma is_irreducible : irreducible (IrredComponent f s) := λ a b ↦ by
  rcases Quotient.exact (a.2.trans b.2.symm) with ⟨m, n, h⟩
  refine ⟨m, n, Subtype.ext ?_⟩
  rwa [iterate_apply_fst, iterate_apply_fst]





/-! ### Decomposition via irreducible components -/

def inclusion : Hom (IrredComponent f s) f :=
  ⟨λ a ↦ a.1, apply_fst f s⟩

def mkEquiv : Equiv (Sigma.map _root_.id (IrredComponent f)) f where
  toEquiv := Equiv.sigmaFiberEquiv (Quotient.mk (ptEquiv.mkSetoid f))
  Semiconj := (SelfMap.Hom.sigma_mk (inclusion f)).Semiconj

def decomposition : Decomposition f where
  irreducible := is_irreducible f
  type_nonempty := type_nonempty f
  SelfMap_equiv := mkEquiv f

/-- Existence of decompositions without explicit description -/
instance : Inhabited (Decomposition f) := ⟨decomposition f⟩

end IrredComponent