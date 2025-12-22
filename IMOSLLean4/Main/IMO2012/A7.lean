/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# IMO 2012 A7

Given a lattice $α$, the *inf-closure* (resp. *sup-closure*) of a subset $S ⊆ α$ is the
  smallest set containing $S$ that is closed under infimum (resp. supremum).

Let $R$ be a totally ordered commutative ring and $σ$ be a set.
Let $R^{R^σ}$ be the ring of functions from $R^σ$ to $R$.
View $R^{R^σ}$ as a lattice via pointwise maximum and minimum.
Let $R[σ]$ denote the ring of multivariate polynomials with variable set $σ$.
Let $S ⊆ R^{R^σ}$ be the sup-closure of the inf-closure of $R[σ]$.
Prove that $S$ is a subring of $R^{R^σ}$.

### Solution

We follow and generalize the
  [official solution](https://www.imo-official.org/problems/IMO2012SL.pdf).
The original formulation only asks to prove that $S$ is closed under multiplication.
However, the official solution essentially proves that $S$ is a ring.

We define the *meta-closure* of a subset $S$ of a lattice to be the smallest set
  containing $S$ that is closed under both infimum and supremum.
-/

namespace IMOSL
namespace IMO2012A7

/-! ### Extra lemmas -/

section

variable {R : I → Type*} [(i : I) → Ring (R i)] [(i : I) → LinearOrder (R i)]
  [(i : I) → IsOrderedRing (R i)] (f g₁ g₂ : (i : I) → R i)

/-- For any `f, g₁, g₂ ∈ ∏_i R_i`, we have `f⁺ min{g₁, g₂} = min{f⁺ g₁, f⁺ g₂}`. -/
lemma Pi_posPart_mul_inf : f⁺ * (g₁ ⊓ g₂) = f⁺ * g₁ ⊓ f⁺ * g₂ :=
  funext λ i ↦ mul_min_of_nonneg (g₁ i) (g₂ i) (posPart_nonneg f i)

/-- For any `f, g₁, g₂ ∈ ∏_i R_i`, we have `f⁺ max{g₁, g₂} = max{f⁺ g₁, f⁺ g₂}`. -/
lemma Pi_posPart_mul_sup : f⁺ * (g₁ ⊔ g₂) = f⁺ * g₁ ⊔ f⁺ * g₂ :=
  funext λ i ↦ mul_max_of_nonneg (g₁ i) (g₂ i) (posPart_nonneg f i)

/-- For any `f, g₁, g₂ ∈ ∏_i R_i`, we have `min{g₁, g₂} f⁺ = min{g₁ f⁺, g₂ f⁺}`. -/
lemma Pi_inf_mul_posPart : (g₁ ⊓ g₂) * f⁺ = g₁ * f⁺ ⊓ g₂ * f⁺ :=
  funext λ i ↦ min_mul_of_nonneg (g₁ i) (g₂ i) (posPart_nonneg f i)

/-- For any `f, g₁, g₂ ∈ ∏_i R_i`, we have `max{g₁, g₂} f⁺ = max{g₁ f⁺, g₂ f⁺}`. -/
lemma Pi_sup_mul_posPart : (g₁ ⊔ g₂) * f⁺ = g₁ * f⁺ ⊔ g₂ * f⁺ :=
  funext λ i ↦ max_mul_of_nonneg (g₁ i) (g₂ i) (posPart_nonneg f i)

end





/-! ### Start of the problem -/

/-- Closure under simultaneous infimum and supremum. -/
inductive MetaClosure [Lattice α] (P : α → Prop) : α → Prop where
  | ofMem (a) : P a → MetaClosure P a
  | ofMin (a b) : MetaClosure P a → MetaClosure P b → MetaClosure P (a ⊓ b)
  | ofMax (a b) : MetaClosure P a → MetaClosure P b → MetaClosure P (a ⊔ b)

/-- Closure under one binary operation. -/
inductive BinOpClosure (op : α → α → α) (P : α → Prop) : α → Prop where
  | ofMem (a) : P a → BinOpClosure op P a
  | ofOp (a b) : BinOpClosure op P a → BinOpClosure op P b → BinOpClosure op P (op a b)



section Lattice

variable [Lattice α] (P : α → Prop)

/-- The inf-closure is contained in the meta-closure. -/
lemma InfClosure_imp_MetaClosure (ha : BinOpClosure Min.min P a) : MetaClosure P a := by
  induction ha with
  | ofMem a ha => exact MetaClosure.ofMem a ha
  | ofOp a b _ _ ha hb => exact MetaClosure.ofMin a b ha hb

/-- The sup-closure of inf-closure is contained in the meta-closure. -/
lemma SupInfClosure_imp_MetaClosure
    (ha : BinOpClosure Max.max (BinOpClosure Min.min P) a) : MetaClosure P a := by
  induction ha with
  | ofMem a ha => exact InfClosure_imp_MetaClosure P ha
  | ofOp a b _ _ ha hb => exact MetaClosure.ofMax a b ha hb

end Lattice


section Distrib

variable [DistribLattice α] (P : α → Prop)

open BinOpClosure in
/-- The meta-closure is contained in the sup-closure of inf-closure. -/
lemma MetaClosure_imp_SupInfClosure (ha : MetaClosure P a) :
    BinOpClosure Max.max (BinOpClosure Min.min P) a := by
  induction ha with
    | ofMem a ha => exact ofMem a (ofMem a ha)
    | ofMin a b ha' hb' ha hb => ?_
    | ofMax a b ha' hb' ha hb => exact ofOp a b ha hb
  clear ha' hb'
  induction ha with
    | ofMem c hc => ?_
    | ofOp c d _ _ hc hd => rw [inf_sup_right]; exact ofOp _ _ hc hd
  induction hb with
    | ofMem d hd => exact ofMem (c ⊓ d) (ofOp c d hc hd)
    | ofOp d e _ _ hd he => rw [inf_sup_left]; exact ofOp _ _ hd he

/-- The sup-closure of inf-closure is equal to the meta-closure. -/
theorem SupInfClosure_eq_MetaClosure :
    BinOpClosure Max.max (BinOpClosure Min.min P) = MetaClosure P :=
  funext λ _ ↦ propext ⟨SupInfClosure_imp_MetaClosure P, MetaClosure_imp_SupInfClosure P⟩

end Distrib



/-! ### Subgroup structure of meta-closure -/

namespace MetaClosure

section

variable [Lattice G] [AddGroup G] (S : AddSubgroup G)

/-- The meta-closure of a subgroup contains `0`. -/
lemma zero_mem : MetaClosure (· ∈ S) 0 :=
  ofMem 0 S.zero_mem

/-- The meta-closure of a subgroup is closed under taking maximum with zero. -/
lemma posPart_mem (ha : MetaClosure (· ∈ S) a) : MetaClosure (· ∈ S) a⁺ :=
  ofMax a 0 ha (zero_mem S)

variable [AddLeftMono G] [AddRightMono G]

/-- The meta-closure of a subgroup is closed under addition. -/
lemma add_mem (ha : MetaClosure (· ∈ S) a) (hb : MetaClosure (· ∈ S) b) :
    MetaClosure (· ∈ S) (a + b) := by
  induction ha with
    | ofMem a ha => ?_
    | ofMin a c _ _ ha hc => rw [inf_add]; exact ofMin _ _ ha hc
    | ofMax a c _ _ ha hc => rw [sup_add]; exact ofMax _ _ ha hc
  induction hb with
    | ofMem b hb => exact ofMem (a + b) (S.add_mem ha hb)
    | ofMin b c _ _ hb hc => rw [add_inf]; exact ofMin _ _ hb hc
    | ofMax b c _ _ hb hc => rw [add_sup]; exact ofMax _ _ hb hc

/-- The meta-closure of a subgroup is closed under taking positive part. -/
lemma neg_mem (ha : MetaClosure (· ∈ S) a) : MetaClosure (· ∈ S) (-a) := by
  induction ha with
  | ofMem a ha => exact ofMem (-a) (S.neg_mem ha)
  | ofMin a b _ _ ha hb => rw [neg_inf]; exact ofMax _ _ ha hb
  | ofMax a b _ _ ha hb => rw [neg_sup]; exact ofMin _ _ ha hb

/-- The meta-closure of a subgroup is closed under subtraction. -/
lemma sub_mem (ha : MetaClosure (· ∈ S) a) (hb : MetaClosure (· ∈ S) b) :
    MetaClosure (· ∈ S) (a - b) :=
  (sub_eq_add_neg a b) ▸ add_mem S ha (neg_mem S hb)

/-- The meta-closure of a subgroup as a subgroup. -/
def AddGroup_mk : AddSubgroup G :=
  { carrier := setOf (MetaClosure (· ∈ S))
    add_mem' := add_mem S
    zero_mem' := zero_mem S
    neg_mem' := neg_mem S }

end



/-! ### Subring structure of meta-closure -/

/- The main formula, expressing `a⁺b⁺` as the positive part of another element. -/
lemma posPart_mul_posPart_main_formula
    [Ring R] [LinearOrder R] [IsOrderedRing R] (a b : R) :
    a⁺ * b⁺ = (min (a * b) (min (max a (a * b ^ 2)) (max b (a ^ 2 * b))))⁺ := by
  ---- If `a ≤ 0`, then both sides are equal to `0`.
  obtain ha | ha : a ≤ 0 ∨ a ≥ 0 := le_total a 0
  · rw [posPart_eq_zero.mpr ha, zero_mul, eq_comm, posPart_eq_zero, min_le_iff, min_le_iff]
    right; left; exact max_le ha (mul_nonpos_of_nonpos_of_nonneg ha (sq_nonneg b))
  ---- If `b ≤ 0 ≤ a`, then both sides are equal to `0`.
  obtain hb | hb : b ≤ 0 ∨ b ≥ 0 := le_total b 0
  · rw [posPart_eq_zero.mpr hb, mul_zero, eq_comm, posPart_eq_zero]
    exact min_le_of_left_le (mul_nonpos_of_nonneg_of_nonpos ha hb)
  ---- If `a, b ≥ 0`, we claim that both sides are equal to `ab`.
  calc a⁺ * b⁺
    _ = a * b := by rw [posPart_of_nonneg ha, posPart_of_nonneg hb]
    _ = (a * b)⁺ := (posPart_of_nonneg (mul_nonneg ha hb)).symm
    _ = (min (a * b) (min (max a (a * b ^ 2)) (max b (a ^ 2 * b))))⁺ :=
      congrArg _ (min_eq_left ?_).symm
  ---- It remains to prove `ab ≤ min{max{a, ab^2}, max{b, a^2 b}}`.
  have X (t : R) : t ≤ max 1 (t ^ 2) :=
    (le_total t 1).elim le_max_of_le_left λ ht ↦
      le_max_of_le_right (Bound.le_self_pow_of_pos ht Nat.two_pos)
  have h : a * b ≤ max a (a * b ^ 2) := calc
    a * b ≤ a * max 1 (b ^ 2) := mul_le_mul_of_nonneg_left (X b) ha
    _ = max a (a * b ^ 2) := by rw [mul_max_of_nonneg _ _ ha, mul_one]
  have h0 : a * b ≤ max b (a ^ 2 * b) := calc
    a * b ≤ max 1 (a ^ 2) * b := mul_le_mul_of_nonneg_right (X a) hb
    _ = max b (a ^ 2 * b) := by rw [max_mul_of_nonneg _ _ hb, one_mul]
  exact le_min h h0


variable {R : I → Type*} [(i : I) → Ring (R i)] [(i : I) → LinearOrder (R i)]
  [(i : I) → IsOrderedRing (R i)] (S : Subring ((i : I) → R i))

omit [∀ (i : I), IsOrderedRing (R i)] in
/-- The meta-closure of a subring of `∏_i R_i` contains `1`. -/
lemma Pi_one_mem : MetaClosure (· ∈ S) 1 :=
  ofMem 1 S.one_mem

/- The main formula, expressing `f⁺g⁺` as the positive part of a function. -/
lemma Pi_posPart_mul_posPart_main_formula (f g : (i : I) → R i) :
    f⁺ * g⁺ = ((f * g) ⊓ ((f ⊔ f * g ^ 2) ⊓ (g ⊔ f ^ 2 * g)))⁺ :=
  funext λ i ↦ posPart_mul_posPart_main_formula (f i) (g i)

/-- If `f, g` belongs to a subring of `∏_i R_i`, then `fg` belongs to the meta-closure. -/
theorem Pi_posPart_mul_posPart_mem (hf : f ∈ S) (hg : g ∈ S) :
    MetaClosure (· ∈ S) (f⁺ * g⁺) :=
  (Pi_posPart_mul_posPart_main_formula f g).symm ▸
    posPart_mem S.toAddSubgroup <| ofMin _ _ (ofMem _ (S.mul_mem hf hg)) <| ofMin _ _
      (ofMax _ _ (ofMem _ hf) (ofMem _ <| S.mul_mem hf (S.pow_mem hg 2)))
      (ofMax _ _ (ofMem _ hg) (ofMem _ <| S.mul_mem (S.pow_mem hf 2) hg))

/-- If `f, g` belongs to the meta-clousre of a subring of `∏_i R_i`, then so is `f⁺g⁺`. -/
theorem Pi_closure_posPart_mul_closure_posPart_mem
    (hf : MetaClosure (· ∈ S) f) (hg : MetaClosure (· ∈ S) g) :
    MetaClosure (· ∈ S) (f⁺ * g⁺) := by
  induction hg with
    | ofMem g hg => ?_
    | ofMin g₁ g₂ _ _ hg₁ hg₂ =>
        rw [posPart_min, Pi_posPart_mul_inf]; exact ofMin _ _ hg₁ hg₂
    | ofMax g₁ g₂ _ _ hg₁ hg₂ =>
        rw [posPart_max, Pi_posPart_mul_sup]; exact ofMax _ _ hg₁ hg₂
  induction hf with
    | ofMem f hf => exact Pi_posPart_mul_posPart_mem S hf hg
    | ofMin f₁ f₂ _ _ hf₁ hf₂ =>
        rw [posPart_min, Pi_inf_mul_posPart]; exact ofMin _ _ hf₁ hf₂
    | ofMax f₁ f₂ _ _ hf₁ hf₂ =>
        rw [posPart_max, Pi_sup_mul_posPart]; exact ofMax _ _ hf₁ hf₂

/-- If `f, g` belongs to the meta-clousre of a subring of `∏_i R_i`, then so is `fg`. -/
theorem Pi_mul_mem (hf : MetaClosure (· ∈ S) f) (hg : MetaClosure (· ∈ S) g) :
    MetaClosure (· ∈ S) (f * g) := by
  rw [← posPart_sub_negPart f, sub_mul, ← posPart_sub_negPart g, mul_sub, mul_sub]
  let T := S.toAddSubgroup
  have hf₀ : MetaClosure (· ∈ S) (-f) := neg_mem T hf
  have hg₀ : MetaClosure (· ∈ S) (-g) := neg_mem T hg
  apply sub_mem T <;> apply sub_mem T <;> apply Pi_closure_posPart_mul_closure_posPart_mem
  all_goals assumption

/-- The meta-closure of a subring of `∏_i R_i` as a subring. -/
def PiSubring_mk : Subring ((i : I) → R i) :=
  { AddGroup_mk S.toAddSubgroup with
    mul_mem' := Pi_mul_mem S
    one_mem' := Pi_one_mem S }

end MetaClosure



/-! ### Summary for polynomials -/

/-- The image of `MvPolynomial σ R` in `(σ → R) → R` as a ring. -/
abbrev MvPolynomial_image (σ R : Type*) [CommRing R] : Subring ((σ → R) → R) :=
  (Pi.ringHom (MvPolynomial.eval (R := R) (σ := σ))).range

open MetaClosure in
/-- Final solution -/
theorem final_solution (σ R) [CommRing R] [LinearOrder R] [IsOrderedRing R] :
    ∃ T : Subring ((σ → R) → R), T.carrier =
      setOf (BinOpClosure Max.max (BinOpClosure Min.min (· ∈ MvPolynomial_image σ R))) :=
  ⟨PiSubring_mk (MvPolynomial_image σ R),
  congrArg setOf (SupInfClosure_eq_MetaClosure _).symm⟩
