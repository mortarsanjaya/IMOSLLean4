/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2008.A3
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# IMO 2008 A3 (Generalization)

A *Spanish couple* on an ordered set $S$ is a pair of strictly increasing functions
  $(f, g)$ from $S$ to itself such that for any $x ∈ S$,
$$ f(g(g(x))) < g(f(x)). $$
Determine all **well-ordered sets** $S$ such that there exists a Spanish couple on $S$.

### Answer

Those order-isomorphic to lexicographic $T × ℕ × ℕ$, with order prioritizing $T$.
In terms of ordinals, this holds if and only if the ordinal number $o_S$ of $S$ is
  of the form $ω^2 o$ for some ordinal $o$, where $ω$ is the ordinal number of $ℕ$.

### Implementation details

We define an ordered set $S$ to be `good` if there exists a Spanish couple on $S$.
The theorem `good.conjOrderIso_iff` shows that `good` is preserved under order isomorphisms.
We define `isGoodOrdinal` to be the quotient predicate of `good` on ordinals.
We state the main result in terms of both ordinals and well-ordered sets;
  see `final_solution_ordinal` and `final_solution` (only on `Type 0`).

The construction of Spanish couple on lexicographical product is implemented via
  `SpanishCouple.prodLexLeft`, while the construction of Spanish couple on an upper subset
  is implemented via `SpanishCouple.sumLexRestrictRight`, where we view the whole set as a
  disjoint union `α ⊕ₗ β` with the subset being `β`.
-/

namespace IMOSL
namespace Generalization
namespace IMO2008A3

/-! ### Miscelanneous lemmas on ordered sets -/

/-- `StrictMono` transfers through an order isomorphism. -/
theorem StrictMono_conjOrderIso [Preorder α] [Preorder β]
    {f : α → α} (hf : StrictMono f) (e : α ≃o β) :
    StrictMono (e.toEquiv.conj f) :=
  λ _ _ h ↦ e.strictMono (hf (e.symm.strictMono h))

/-- Somehow this isn't on `mathlib`.
  TODO: Remove this instance once `mathlib` variant appears. -/
instance [LT α] [WellFoundedLT α] [LT β] [WellFoundedLT β] : WellFoundedLT (α ⊕ₗ β) :=
  ⟨Sum.lex_wf wellFounded_lt wellFounded_lt⟩


section

variable [LinearOrder α] [WellFoundedLT α] [LinearOrder β] [WellFoundedLT β]
  {f : α ⊕ₗ β → α ⊕ₗ β} (hf : StrictMono f)
include hf

/-- Given a strictly increasing function `f : α ⊕ₗ β → α ⊕ₗ β`, where `α` and `β`
  are well-ordered, the image `f(b) ∈ β` for any `b ∈ β`. -/
theorem sum_isRight_of_strictMono (b : β) : Sum.isRight (ofLex.conj f (Sum.inr b)) :=
  match h : ofLex.conj f (Sum.inr b) with
  | Sum.inl _ => absurd ((hf.id_le _).trans_eq h) Sum.lex_inr_inl
  | Sum.inr _ => rfl

/-- Given a strictly increasing function `f : α ⊕ₗ β → α ⊕ₗ β`, where `α` and `β`
  are well-ordered, `f` restricts to a function `g : β → β`. -/
def sum_getRight_of_strictMono (b : β) : β :=
  Sum.getRight _ (sum_isRight_of_strictMono hf b)

/-- Given a strictly increasing function `f : α ⊕ₗ β → α ⊕ₗ β`, where `α` and `β`
  are well-ordered, `g` given above is indeed a restriction on `f`. -/
theorem sum_getRight_of_strictMono_apply :
    toLex (Sum.inr (sum_getRight_of_strictMono hf b)) = f (toLex (Sum.inr b)) :=
  Sum.inr_getRight _ _

/-- Given a strictly increasing function `f : α ⊕ₗ β → α ⊕ₗ β`, where `α` and `β`
  are well-ordered, the restrictiion to `β` is also strictly increasing. -/
theorem sum_getRight_of_strictMono_strictMono :
    StrictMono (sum_getRight_of_strictMono hf) :=
  λ _ _ h ↦ by simpa only [← Sum.Lex.inr_lt_inr_iff (α := α) (β := β),
    sum_getRight_of_strictMono_apply] using hf (Sum.Lex.inr_lt_inr_iff.mpr h)

end




/-! ### More properties of Spanish couples -/

/-- Transferring definition of `SpanishCouple` through namespace. -/
alias SpanishCouple := IMOSL.IMO2008A3.SpanishCouple


namespace SpanishCouple

/-- Given a Spanish couple `f` on `α` and an order isomorphism `e : α ≃o β`,
  make a Spanish couple on `β` by conjugating with `e`. -/
def conjOrderIso [Preorder α] [Preorder β] (X : SpanishCouple α) (e : α ≃o β) :
    SpanishCouple β where
  f := e.toEquiv.conj X.f
  f_strictMono := StrictMono_conjOrderIso X.f_strictMono e
  g := e.toEquiv.conj X.g
  g_strictMono := StrictMono_conjOrderIso X.g_strictMono e
  spec x := by simpa using X.spec (e.symm x)

open IMOSL.IMO2008A3 in
/-- Given a Spanish couple `(f, g)` on `β`, make a Spanish couple `(f', g')` on `α ×ₗ β`,
  defined by `f'(a, b) = (a, f(b))` and `g'(a, b) = (a, g(b))`. -/
def prodLexLeft (α) [Preorder α] [Preorder β] (X : SpanishCouple β) :
    SpanishCouple (α ×ₗ β) where
  f := toLex.conj (Prod.map id X.f)
  f_strictMono := ProdMapLex_strictMono strictMono_id X.f_strictMono
  g := toLex.conj (Prod.map id X.g)
  g_strictMono := ProdMapLex_strictMono strictMono_id X.g_strictMono
  spec := Lex.rec λ p ↦ Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, X.spec p.2⟩)

/-- Given a spanish couple on `α ⊕ₗ β`, where `α` and `β` are well-ordered sets,
  make a Spanish couple on `β` by restricting into the `β` coordinate. -/
def sumLexRestrictRight [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (X : SpanishCouple (α ⊕ₗ β)) :
    SpanishCouple β where
  f := sum_getRight_of_strictMono X.f_strictMono
  f_strictMono := sum_getRight_of_strictMono_strictMono _
  g := sum_getRight_of_strictMono X.g_strictMono
  g_strictMono := sum_getRight_of_strictMono_strictMono _
  spec x := (Sum.Lex.inr_lt_inr_iff (α := α)).mp <| by
    simpa only [sum_getRight_of_strictMono_apply] using X.spec (toLex (Sum.inr x))

end SpanishCouple





/-! ### The `good` predicate on pre-orders -/

/-- A pre-order `α` is called `good` if there is a Spanish couple on `α`. -/
def good (α) [Preorder α] := Nonempty (SpanishCouple α)

/-- `PUnit` is not good. -/
theorem PUnit_is_not_good : ¬good PUnit :=
  λ ⟨X⟩ ↦ X.spec default

/-- `ℕ` is not good. -/
theorem Nat_is_not_good : ¬good ℕ :=
  λ ⟨X⟩ ↦ IMO2008A3.final_solution_part1.elim X

/-- `ℕ ×ₗ ℕ` is good. -/
theorem NatNatLex_is_good : good (ℕ ×ₗ ℕ) :=
  ⟨IMO2008A3.final_solution_part2⟩


namespace good

/-- If `α` is good and `α ≃o β`, then `β` is good. -/
theorem conjOrderIso [Preorder α] [Preorder β] (hα : good α) (e : α ≃o β) : good β :=
  hα.elim λ X ↦ ⟨X.conjOrderIso e⟩

/-- If `α ≃o β`, then `α` is good if and only if `β` is good. -/
theorem conjOrderIso_iff [Preorder α] [Preorder β] (e : α ≃o β) : good α ↔ good β :=
  ⟨λ hα ↦ hα.conjOrderIso e, λ hβ ↦ hβ.conjOrderIso e.symm⟩

/-- If `β` is good, then `α ×ₗ β` is good. -/
theorem prodLexLeft (α) [Preorder α] [Preorder β] (hβ : good β) : good (α ×ₗ β) :=
  hβ.elim λ X ↦ ⟨X.prodLexLeft α⟩

/-- If `α ⊕ₗ β` is good, then `β` is good. -/
theorem sumLexRestrictRight [LinearOrder α] [WellFoundedLT α]
    [LinearOrder β] [WellFoundedLT β] (h : good (α ⊕ₗ β)) : good β :=
  h.elim λ X ↦ ⟨X.sumLexRestrictRight⟩

end good





/-! ### Miscellaneous lemmas on ordinals -/

open Ordinal

/-- The ordinal type of `ℕ ×ₗ ℕ` is `ω^2`. -/
theorem type_NatNatLex : type (λ x y : ℕ ×ₗ ℕ ↦ x < y) = ω ^ 2 :=
  (sq (type λ m n : ℕ ↦ m < n)).symm.trans (congrArg (· ^ 2) type_nat_lt)

/-- Every ordinal is either a successor ordinal or is divisible by `ω`.
  TODO: If a version of `Ordinal.zero_or_succ_or_isSuccLimit` for `SuccPrelimit` appears,
    replace this with a `SuccPrelimit` version. -/
theorem succ_or_omega0_dvd (o : Ordinal) : o ∈ Set.range Order.succ ∨ ω ∣ o :=
  o.zero_or_succ_or_isSuccLimit.elim (λ ho ↦ Or.inr (ho ▸ dvd_zero _))
    (Or.imp_right λ ho ↦ (isSuccLimit_iff_omega0_dvd.mp ho).2)





/-! ### The quotient predicate `isGoodOrdinal` of `good` -/

namespace good

variable [LinearOrder α] [WellFoundedLT α] [LinearOrder β] [WellFoundedLT β]
  (h : type (λ x y : α ↦ x < y) = type (λ x y : β ↦ x < y))
include h

/-- If `α` and `β` are of the same ordinal type and `α` is good, then `β` is good. -/
theorem of_type_eq (hα : good α) : good β :=
  (type_eq.mp h).elim λ r ↦ hα.conjOrderIso (OrderIso.ofRelIsoLT r)

/-- If `α` and `β` are of the same ordinal type, then `α` is good iff `β` is good. -/
theorem iff_of_type_eq : good α ↔ good β :=
  ⟨good.of_type_eq h, good.of_type_eq h.symm⟩

end good


/-- The quotient predicate of `good`. -/
def isGoodOrdinal (o : Ordinal) : Prop :=
  o.liftOnWellOrder (λ α _ _ ↦ good α) (λ _ _ _ _ _ _ h ↦ Iff.eq (good.iff_of_type_eq h))

/-- Definition of `isGoodOrdinal` on a quotient of a well-ordered type. -/
theorem isGoodOrdinal_iff_good [LinearOrder α] [WellFoundedLT α] :
    isGoodOrdinal (type λ x y : α ↦ x < y) ↔ good α :=
  (liftOnWellOrder_type _ _).to_iff

/-- Definition of `isGoodOrdinal` of an ordinal with respect to a suitable well-order. -/
theorem isGoodOrdinal_iff_good'.{u, v} {α : Type u} [LinearOrder α] [WellFoundedLT α]
    {o : Ordinal.{v}} (ho : lift.{u, v} o = lift.{v, u} (type λ x y : α ↦ x < y)) :
    isGoodOrdinal o ↔ good α := by
  induction o using Ordinal.inductionOnWellOrder with | H β => ?_
  obtain ⟨e⟩ := lift_type_eq.{_, _, 0}.mp ho
  exact isGoodOrdinal_iff_good.trans (good.conjOrderIso_iff (OrderIso.ofRelIsoLT e))

/-- `1` is not a good ordinal. -/
theorem one_not_isGoodOrdinal : ¬isGoodOrdinal 1 := by
  rw [← type_eq_one_of_unique (λ x y : PUnit ↦ x < y), isGoodOrdinal_iff_good]
  exact PUnit_is_not_good

/-- `ω` is not a good ordinal. -/
theorem omega0_not_isGoodOrdinal : ¬isGoodOrdinal ω :=
  mt (isGoodOrdinal_iff_good' lift_omega0).mp Nat_is_not_good

/-- `ω^2` is a good ordinal. -/
theorem omega0_sq_isGoodOrdinal : isGoodOrdinal (ω ^ 2) := by
  refine (isGoodOrdinal_iff_good' ?_).mpr NatNatLex_is_good
  rw [type_NatNatLex, lift_uzero, sq, sq, lift_mul, lift_omega0]


namespace isGoodOrdinal

/-- If `a` is a good ordinal, then `ab` is a good ordinal for any ordinal `b`. -/
theorem mul_right (ha : isGoodOrdinal a) (b : Ordinal) : isGoodOrdinal (a * b) := by
  ---- Indeed, if `a = [α]` and `b = [β]`, then `ab = [β ×ₗ α]`.
  induction a using Ordinal.inductionOnWellOrder with | H α => ?_
  induction b using Ordinal.inductionOnWellOrder with | H β => ?_
  change isGoodOrdinal (type λ x y : β ×ₗ α ↦ x < y)
  exact isGoodOrdinal_iff_good.mpr ((isGoodOrdinal_iff_good.mp ha).prodLexLeft β)

/-- If `a` is a good ordinal and `a ∣ b`, then `b` is a good ordinal. -/
theorem trans_dvd (ha : isGoodOrdinal a) (h : a ∣ b) : isGoodOrdinal b :=
  h.elim λ c hc ↦ hc ▸ ha.mul_right c

/-- If `a + b` is a good ordinal, then `b` is a good ordinal. -/
theorem add_left_cancel (h : isGoodOrdinal (a + b)) : isGoodOrdinal b := by
  ---- Indeed, if `a = [α]` and `b = [β]`, then `a + b = [α ⊕ₗ β]`.
  induction a using Ordinal.inductionOnWellOrder with | H α => ?_
  induction b using Ordinal.inductionOnWellOrder with | H β => ?_
  change isGoodOrdinal (type (λ x y : α ⊕ₗ β ↦ x < y)) at h
  exact isGoodOrdinal_iff_good.mpr (isGoodOrdinal_iff_good.mp h).sumLexRestrictRight

/-- If `o` is a good ordinal, then `ω ∣ o`. -/
theorem omega0_dvd (ho : isGoodOrdinal o) : ω ∣ o := by
  ---- Suppose not; then `o = o₀ + 1` for some ordinal `o₀`.
  refine (succ_or_omega0_dvd o).resolve_left ?_
  rintro ⟨o₀, rfl⟩
  ---- Since `o = o₀ + 1` is good, `1` good; contradiction.
  exact one_not_isGoodOrdinal ho.add_left_cancel

/-- If `o` is a good ordinal, then `ω^2 ∣ o`. -/
theorem omega0_sq_dvd (ho : isGoodOrdinal o) : ω ^ 2 ∣ o := by
  ---- First write `o = ωo₀`, and reduce to `ω ∣ o₀`.
  obtain ⟨o₀, rfl⟩ : ω ∣ o := ho.omega0_dvd
  suffices ω ∣ o₀ from sq ω ▸ mul_dvd_mul_left ω this
  ---- Now suppose `ω ∤ o₀`, and write `o₀ = o₁ + 1`.
  refine (succ_or_omega0_dvd o₀).resolve_left ?_
  rintro ⟨o₁, rfl⟩
  ----- Then `o = ωo₀ = ωo_1 + ω` is good, so `ω` is good; contradiction.
  rw [mul_succ] at ho
  exact omega0_not_isGoodOrdinal ho.add_left_cancel

/-- An ordinal `o` is good if and only if `ω^2 ∣ o`. -/
theorem iff_omega0_sq_dvd : isGoodOrdinal o ↔ ω ^ 2 ∣ o :=
  ⟨isGoodOrdinal.omega0_sq_dvd, omega0_sq_isGoodOrdinal.trans_dvd⟩

end isGoodOrdinal





/-! ### Summary -/

/-- Final solution, ordinal form -/
alias final_solution_ordinal := isGoodOrdinal.iff_omega0_sq_dvd

/-- Final solution -/
theorem final_solution {α : Type} [LinearOrder α] [WellFoundedLT α] :
    good α ↔ ∃ (β : Type) (_ : LinearOrder β) (_ : WellFoundedLT β),
      Nonempty (α ≃o β ×ₗ ℕ ×ₗ ℕ) := by
  ---- The backwards direction is more straightforward.
  refine Iff.symm ⟨?_, λ hα ↦ ?_⟩
  · rintro ⟨β, _, _, ⟨e⟩⟩
    exact (good.conjOrderIso_iff e).mpr (NatNatLex_is_good.prodLexLeft β)
  ---- Now suppose that `α` is good. Then `ω^2` divides the ordinal number `o = [α]`.
  obtain ⟨o₀, ho₀⟩ : ω ^ 2 ∣ type (λ x y : α ↦ x < y) :=
    (isGoodOrdinal_iff_good.mpr hα).omega0_sq_dvd
  ---- Write `[α] = ω^2 [β]` for some well-ordered set `β`.
  induction o₀ using Ordinal.inductionOnWellOrder with | H β => ?_
  ---- Now this `β` works.
  refine ⟨β, by assumption, by assumption, ?_⟩
  rw [sq, ← type_nat_lt] at ho₀
  exact (type_eq.mp ho₀).elim λ e ↦ ⟨OrderIso.ofRelIsoLT e⟩
