/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2012.A7.A7Group
import Mathlib.Algebra.Ring.Pi
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Ring.Subring.Basic

/-!
# IMO 2012 A7, Pi-type Ring Version

Let `S = ∏_i R_i` be the product of totally ordered rings.
The rings `R_i` are not necessarily commutative.
We show that the meta-closure of a subring of `S` is again a subring of `S`.
This is the bulk of the original formulation of the IMO 2012 A7.

### Further directions

Can we generalize `S` to lattice ordered rings?
-/

namespace IMOSL
namespace IMO2012A7

/-! ### Extra lemmas -/

section LatticeOrderedGroup

variable [DistribLattice G] [AddGroup G]

lemma inf_pos_part (a b : G) : (a ⊓ b)⁺ = a⁺ ⊓ b⁺ :=
  sup_inf_right _ _ _

lemma sup_pos_part (a b : G) : (a ⊔ b)⁺ = a⁺ ⊔ b⁺ :=
  sup_sup_distrib_right a b 0

end LatticeOrderedGroup



section LinearOrderedRing

variable [Ring R] [LinearOrder R] [IsOrderedRing R]

lemma le_max_one_sq (a : R) : a ≤ max 1 (a ^ 2) := by
  apply (le_abs_self a).trans
  rw [← sq_abs, le_max_iff]
  exact (le_total |a| 1).imp_right λ h ↦ le_self_pow₀ h (Nat.succ_ne_zero 1)

lemma pos_part_mul_pos_part_main_formula (a b : R) :
    a⁺ * b⁺ = (min (a * b) <| min (max a (a * b ^ 2)) (max b (a ^ 2 * b)))⁺ := by
  rcases le_total a 0 with h | h
  ---- Case 1: `a ≤ 0`
  · rw [posPart_eq_zero.mpr h, zero_mul, eq_comm, posPart_eq_zero, min_le_iff, min_le_iff]
    right; left; exact max_le h (mul_nonpos_of_nonpos_of_nonneg h (sq_nonneg b))
  rcases le_total b 0 with h0 | h0
  ---- Case 2: `b ≤ 0`
  · rw [posPart_eq_zero.mpr h0, mul_zero, eq_comm, posPart_eq_zero, min_le_iff, min_le_iff]
    right; right; exact max_le h0 (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg a) h0)
  ---- Case 3: `ab ≥ 0`
  rw [posPart_eq_self.mpr h, posPart_eq_self.mpr h0, eq_comm]
  refine (congr_arg _ (min_eq_left <| le_min ?_ ?_)).trans
    (posPart_eq_self.mpr (mul_nonneg h h0))
  · have h1 := mul_le_mul_of_nonneg_left (le_max_one_sq b) h
    rwa [mul_max_of_nonneg _ _ h, mul_one] at h1
  · have h1 := mul_le_mul_of_nonneg_right (le_max_one_sq a) h0
    rwa [max_mul_of_nonneg _ _ h0, one_mul] at h1

end LinearOrderedRing





/-! ### Extra lemmas on products of totally ordered rings -/

variable {R : I → Type*} [(i : I) → Ring (R i)] [(i : I) → LinearOrder (R i)]
  [(i : I) → IsOrderedRing (R i)]

instance : CovariantClass ((i : I) → R i) ((i : I) → R i) (· + ·) (· ≤ ·) :=
  ⟨λ f _ _ h i ↦ add_le_add_left (h i) (f i)⟩

instance : CovariantClass ((i : I) → R i) ((i : I) → R i) (Function.swap (· + ·)) (· ≤ ·) :=
  ⟨λ f _ _ h i ↦ add_le_add_right (h i) (f i)⟩

section

variable {f : (i : I) → R i} (hf : 0 ≤ f) (a b : (i : I) → R i)
include hf

lemma Pi_mul_inf_of_nonneg : f * (a ⊓ b) = f * a ⊓ f * b :=
  funext λ i ↦ mul_min_of_nonneg (a i) (b i) (hf i)

lemma Pi_mul_sup_of_nonneg : f * (a ⊔ b) = f * a ⊔ f * b :=
  funext λ i ↦ mul_max_of_nonneg (a i) (b i) (hf i)

lemma Pi_inf_mul_of_nonneg : (a ⊓ b) * f = a * f ⊓ b * f :=
  funext λ i ↦ min_mul_of_nonneg (a i) (b i) (hf i)

lemma Pi_sup_mul_of_nonneg : (a ⊔ b) * f = a * f ⊔ b * f :=
  funext λ i ↦ max_mul_of_nonneg (a i) (b i) (hf i)

end


section

variable (f a b : (i : I) → R i)

lemma Pi_pos_part_mul_inf : f⁺ * (a ⊓ b) = f⁺ * a ⊓ f⁺ * b :=
  Pi_mul_inf_of_nonneg (posPart_nonneg f) a b

lemma Pi_pos_part_mul_sup : f⁺ * (a ⊔ b) = f⁺ * a ⊔ f⁺ * b :=
  Pi_mul_sup_of_nonneg (posPart_nonneg f) a b

lemma Pi_inf_mul_pos_part : (a ⊓ b) * f⁺ = a * f⁺ ⊓ b * f⁺ :=
  Pi_inf_mul_of_nonneg (posPart_nonneg f) a b

lemma Pi_sup_mul_pos_part : (a ⊔ b) * f⁺ = a * f⁺ ⊔ b * f⁺ :=
  Pi_sup_mul_of_nonneg (posPart_nonneg f) a b

end


lemma Pi_pos_part_mul_pos_part_main_formula (f g : (i : I) → R i) :
    f⁺ * g⁺ = ((f * g) ⊓ ((f ⊔ f * g ^ 2) ⊓ (g ⊔ f ^ 2 * g)))⁺ :=
  funext λ i ↦ pos_part_mul_pos_part_main_formula (f i) (g i)





/-! ### Subring structure of meta-closure -/

namespace MetaClosure

variable (S : Subring ((i : I) → R i))

omit [∀ (i : I), IsOrderedRing (R i)] in
lemma Pi_one_mem : MetaClosure (· ∈ S) 1 := ofMem S.one_mem

theorem Pi_pos_part_mul_pos_part_mem (hf : f ∈ S) (hg : g ∈ S) :
    MetaClosure (· ∈ S) (f⁺ * g⁺) :=
  (Pi_pos_part_mul_pos_part_main_formula f g).symm ▸
    pos_part_mem S.toAddSubgroup <| ofMin (ofMem <| S.mul_mem hf hg) <| ofMin
      (ofMax (ofMem hf) (ofMem <| S.mul_mem hf (S.pow_mem hg 2)))
      (ofMax (ofMem hg) (ofMem <| S.mul_mem (S.pow_mem hf 2) hg))

theorem Pi_closure_pos_part_mul_closure_pos_part_mem
    (hf : MetaClosure (· ∈ S) f) (hg : MetaClosure (· ∈ S) g) :
    MetaClosure (· ∈ S) (f⁺ * g⁺) :=
  hg.recOn
    (λ hg ↦ hf.recOn
      (λ hf ↦ Pi_pos_part_mul_pos_part_mem S hf hg)
      (λ _ _ ↦ by rw [inf_pos_part, Pi_inf_mul_pos_part]; exact ofMin)
      (λ _ _ ↦ by rw [sup_pos_part, Pi_sup_mul_pos_part]; exact ofMax))
    (λ _ _ ↦ by rw [inf_pos_part, Pi_pos_part_mul_inf]; exact ofMin)
    (λ _ _ ↦ by rw [sup_pos_part, Pi_pos_part_mul_sup]; exact ofMax)

theorem Pi_mul_mem (hf : MetaClosure (· ∈ S) f) (hg : MetaClosure (· ∈ S) g) :
    MetaClosure (· ∈ S) (f * g) := by
  rw [← posPart_sub_negPart f, sub_mul,
    ← posPart_sub_negPart g, mul_sub, mul_sub]
  let T := S.toAddSubgroup
  have hf₀ : MetaClosure (· ∈ S) (-f) := neg_mem T hf
  have hg₀ : MetaClosure (· ∈ S) (-g) := neg_mem T hg
  apply sub_mem T <;> apply sub_mem T <;>
    apply Pi_closure_pos_part_mul_closure_pos_part_mem <;> assumption

/-- The `MetaClosure` of `S` as a subring -/
def PiSubring_mk : Subring ((i : I) → R i) :=
  { AddGroup_mk S.toAddSubgroup with
    mul_mem' := Pi_mul_mem S
    one_mem' := Pi_one_mem S }

theorem PiSubring_mk_carrier :
    (PiSubring_mk S).carrier = setOf (BinOpClosure Max.max (BinOpClosure Min.min (· ∈ S))) :=
  AddGroup_mk_carrrier S.toAddSubgroup
