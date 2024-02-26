/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A3.SelfMap.PeriodDecomposition.Cyclic
import IMOSLLean4.IMO2017.A3.SelfMap.PeriodDecomposition.IntSucc
import IMOSLLean4.IMO2017.A3.SelfMap.Instances.IntSuccHom
import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Equiv
import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Empty
import IMOSLLean4.IMO2017.A3.SelfMap.Hom.Sum

/-!
# Period decomposition

We show that any self-map `f : α → α` is isomorphic to a
  self-map of form `f_c ⊕ f_i`, where `f_c` is cyclic and
  `f_i` has a homomorphism to `Int.succ`.
Then we show that `f` has one of the following:
* A core instance consisting of non-empty coproducts of `FinMap n`s,
* A homomorphism to `Int.succ`.
-/

namespace IMOSL
namespace IMO2017A3
namespace SelfMap

open Function ptEquiv
open scoped Classical

lemma in_cyclicComponent_apply_iff {f : α → α} {x : α} :
    in_cyclicComponent f (f x) ↔ in_cyclicComponent f x :=
  exists_congr λ _ ↦ and_congr
    (trans_iff_right (of_self_apply_left f x)) Iff.rfl





/-! ### Cyclic part -/

def cyclicPart (f : α → α) := {x : α // in_cyclicComponent f x}


namespace cyclicPart

variable (f : α → α)

def lift (x : cyclicPart f) : cyclicPart f :=
  ⟨f x.1, in_cyclicComponent_apply_iff.mpr x.2⟩

lemma lift_fst (x : cyclicPart f) : (lift f x).1 = f x.1 := rfl

lemma lift_iterate_fst (x : cyclicPart f) : ∀ k, ((lift f)^[k] x).1 = f^[k] x.1
  | 0 => rfl
  | k + 1 => (lift_iterate_fst _ k).trans <| congr_arg f^[k] (lift_fst f _)

lemma ptEquiv_iff : ptEquiv (lift f) x y ↔ ptEquiv f x.1 y.1 :=
  exists_congr λ k ↦ exists_congr λ m ↦ by
    rw [Subtype.ext_iff, lift_iterate_fst, lift_iterate_fst]

lemma periodic_iff : y ∈ (lift f).periodicPts ↔ y.1 ∈ f.periodicPts :=
  exists_congr λ n ↦ and_congr Iff.rfl <|
    Subtype.ext_iff.trans ((lift_iterate_fst f y n).congr rfl)

lemma lift_is_cyclic : cyclic (lift f) := λ ⟨_, y, h, h0⟩ ↦
    ⟨⟨y, y, refl f y, h0⟩, (ptEquiv_iff f).mpr h, (periodic_iff f).mpr h0⟩

theorem exists_FinMapSetSigmaCore :
    ∃ S, Nonempty (Core (lift f) (FinMapSetSigma S)) :=
  SelfMap.exists_SigmaFinMapReducedCore (cyclicPart.lift_is_cyclic f)

theorem exists_nonempty_FinMapSetSigmaCore
    {f : α → α} (h : Nonempty (cyclicPart f)) :
    ∃ S, S.Nonempty ∧ Nonempty (Core (lift f) (FinMapSetSigma S)) :=
  SelfMap.exists_nonempty_SigmaFinMapReducedCore h (cyclicPart.lift_is_cyclic f)

end cyclicPart





/-! ### `Int.succ` part -/

def IntSuccPart (f : α → α) := {x : α // ¬in_cyclicComponent f x}


namespace IntSuccPart

variable (f : α → α)

def lift (x : IntSuccPart f) : IntSuccPart f :=
  ⟨f x.1, mt in_cyclicComponent_apply_iff.mp x.2⟩

lemma lift_fst (x : IntSuccPart f) : (lift f x).1 = f x.1 := rfl

lemma lift_iterate_fst (x : IntSuccPart f) : ∀ k, ((lift f)^[k] x).1 = f^[k] x.1
  | 0 => rfl
  | k + 1 => (lift_iterate_fst _ k).trans <| congr_arg f^[k] (lift_fst f _)

lemma ptEquiv_iff : ptEquiv (lift f) x y ↔ ptEquiv f x.1 y.1 :=
  exists_congr λ k ↦ exists_congr λ m ↦ by
    rw [Subtype.ext_iff, lift_iterate_fst, lift_iterate_fst]

lemma periodPts_empty : (lift f).periodicPts = ∅ :=
  Set.eq_empty_iff_forall_not_mem.mpr λ x ⟨n, h, h0⟩ ↦
    x.2 ⟨x.1, refl _ _, n, h,
      (lift_iterate_fst f x n).symm.trans (congr_arg _ h0)⟩

theorem exists_toIntSucc : Nonempty (Hom (lift f) Int.succ) :=
  toIntSucc_Nonempty_iff.mpr (periodPts_empty f)

end IntSuccPart





/-! ### The period decomposition -/

/-- The period decomposition -/
noncomputable def periodDecomposition (f : α → α) :
    SelfMap.Equiv (Sum.map (cyclicPart.lift f) (IntSuccPart.lift f)) f where
  toEquiv := Equiv.sumCompl (in_cyclicComponent f)
  Semiconj := λ x ↦ match x with
    | Sum.inl _ => rfl
    | Sum.inr _ => rfl

/-- If `S : Set ℕ` is non-empty, then `Int.succ` has a
  homomorphism to `FinMapSetSigma S`. -/
theorem IntSuccHom_to_FinMapSetSigma_of_Nonempty (h : S.Nonempty) :
    Nonempty (Hom Int.succ (FinMapSetSigma S)) :=
  h.elim λ n h0 ↦ ⟨(Hom.sigma_incl (λ n : S ↦ FinMap n) ⟨n, h0⟩).comp
    (IntSuccHom.mk (FinMap_asEquiv n) 0)⟩

/-- If the cyclic part is non-empty, then `FinMapSetSigma S` is a core. -/
theorem FinMapSetSigmaCore_of_cyclicPart (h : Nonempty (cyclicPart f)) :
    ∃ S, S.Nonempty ∧ Nonempty (Core f (FinMapSetSigma S)) := by
  obtain ⟨S, h0, ⟨C⟩⟩ := cyclicPart.exists_nonempty_FinMapSetSigmaCore h
  refine ⟨S, h0, ?_⟩
  let e := (periodDecomposition f).symm.toCore
  obtain ⟨I⟩ := IntSuccPart.exists_toIntSucc f
  obtain ⟨M⟩ := IntSuccHom_to_FinMapSetSigma_of_Nonempty h0
  exact ⟨e.trans (C.sum_Hom (M.comp I))⟩

/-- If the cyclic part is empty, then we have a homomorphism to `Int.succ`. -/
theorem IntSuccHom_of_cyclicPart (h : IsEmpty (cyclicPart f)) :
    Nonempty (Hom f Int.succ) := by
  let C := Hom_ofIsEmpty h (cyclicPart.lift f) Int.succ
  obtain ⟨I⟩ := IntSuccPart.exists_toIntSucc f
  exact ⟨(C.sum_elim I).comp (periodDecomposition f).symm.toHom⟩

/-- Either `f` maps to `Int.succ` or `FinMapSetSigma S` is a core. -/
theorem IntSuccHom_or_FinMapSetSigmaCore (f : α → α) :
    Nonempty (Hom f Int.succ) ∨
      ∃ S, S.Nonempty ∧ Nonempty (Core f (FinMapSetSigma S)) :=
  (isEmpty_or_nonempty (cyclicPart f)).imp
    IntSuccHom_of_cyclicPart FinMapSetSigmaCore_of_cyclicPart
