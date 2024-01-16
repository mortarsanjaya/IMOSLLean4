/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Pi
import Mathlib.RingTheory.Subring.Basic
import Mathlib.Algebra.Order.Group.PosPart

/-!
# IMO 2012 A7, General Version

Given a lattice `α`, the *inf-closure* (resp. *sup-closure*) of a subset `S ⊆ α` is the
  smallest set containing `S` that is closed under infimum (resp. supremum).
The *meta-closure* of `S` is the sup-closure of the inf-closure of `S`.

Let `R` be a totally ordered ring and `σ` be a set.
Prove that if `S` is a subring of `σ → R`, then the
  meta-closure of `S` is also a subring of `σ → R`.

### Note

We actually provide more structure.
One can show that given a lattice `α` and a subset `S`, the meta-closure of `S` is
  exactly the smallest set containing `α` that is closed under infimum and supremum.
Furthermore, given a lattice ordered group `G` and a subgroup `H ≤ G`,
  the meta-closure of `H` is also a subgroup of `G`.
Thus one only has to prove that `S` is closed under multiplication.
-/

namespace IMOSL
namespace IMO2012A7

/-! ### Extra lemmas -/

section extra_ineq

lemma side_ineq [LinearOrderedRing R] {a b : R} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ max (max 1 (a * b) * min a b) (min 1 (a * b) * max a b) := by
  have hab := mul_nonneg ha hb
  rcases le_total (a * b) 1 with h | h
  · rw [max_eq_left h, one_mul, min_eq_right h]
    rcases le_total a b with h0 | h0
    · rw [min_eq_left h0, max_eq_right h0, le_max_iff]
      exact (le_total b 1).imp (mul_le_of_le_one_right ha) (le_mul_of_one_le_right hab)
    · rw [min_eq_right h0, max_eq_left h0, le_max_iff]
      exact (le_total a 1).imp (mul_le_of_le_one_left hb) (le_mul_of_one_le_right hab)
  · rw [max_eq_right h, min_eq_left h, one_mul]
    rcases le_total a b with h0 | h0
    · rw [min_eq_left h0, max_eq_right h0, le_max_iff]
      exact (le_total 1 a).imp (le_mul_of_one_le_right hab) (mul_le_of_le_one_left hb)
    · rw [min_eq_right h0, max_eq_left h0, le_max_iff]
      exact (le_total 1 b).imp (le_mul_of_one_le_right hab) (mul_le_of_le_one_right ha)

lemma pos_part_mul_pos_part_main_formula [LinearOrderedRing R] (a b : R) :
    a⁺ * b⁺ = (min (a * b) <| max (max (min a b) (min (a * b * a) (a * b * b)))
      (max (min a (a * b * a)) (min b (a * b * b))))⁺ := by
  rcases le_or_lt (a * b) 0 with h | h
  ---- Case 1: `ab ≤ 0`
  · rw [LatticeOrderedGroup.pos_eq_zero_iff.mpr (min_le_of_left_le h),
      mul_eq_zero, LatticeOrderedGroup.pos_eq_zero_iff, ← not_lt,
      LatticeOrderedGroup.pos_eq_zero_iff, ← not_lt, ← not_and_or]
    intro h0; exact h.not_lt (mul_pos h0.1 h0.2)
  rw [← mul_min_of_nonneg _ _ h.le]
  rcases le_or_lt a 0 with h0 | h0
  ---- Case 2: `a, b < 0`
  · rw [LatticeOrderedGroup.pos_eq_zero_iff.mpr h0,
      zero_mul, eq_comm, LatticeOrderedGroup.pos_eq_zero_iff]
    have h1 : min a b ≤ 0 := min_le_of_left_le h0
    exact min_le_of_right_le <| max_le
      (max_le h1 (mul_nonpos_of_nonneg_of_nonpos h.le h1))
      (max_le (min_le_of_left_le h0) (min_le_of_left_le (neg_of_mul_pos_right h h0).le))
  ---- Case 3: `a, b > 0`
  have h1 : 0 ≤ b := ((mul_pos_iff_of_pos_left h0).mp h).le
  apply le_of_lt at h0
  have h2 := min_mul_of_nonneg 1 (a * b) h0
  have h3 := min_mul_of_nonneg 1 (a * b) h1
  have h4 := max_mul_of_nonneg 1 (a * b) (le_min h0 h1)
  rw [one_mul] at h2 h3 h4
  rw [← h2, ← h3, ← h4, ← mul_max_of_nonneg _ _ (le_min zero_le_one h.le), eq_comm,
    LatticeOrderedGroup.pos_of_nonneg _ h0, LatticeOrderedGroup.pos_of_nonneg _ h1]
  exact (congr_arg _ <| min_eq_left (side_ineq h0 h1)).trans
    (LatticeOrderedGroup.pos_of_nonneg _ h.le)

end extra_ineq


section LinearOrderedRingPi

variable {σ R : Type*} [LinearOrderedRing R]

instance : CovariantClass (σ → R) (σ → R) (· + ·) (· ≤ ·) :=
  ⟨λ f _ _ h i ↦ add_le_add_left (h i) (f i)⟩

instance : CovariantClass (σ → R) (σ → R) (Function.swap (· + ·)) (· ≤ ·) :=
  ⟨λ f _ _ h i ↦ add_le_add_right (h i) (f i)⟩

lemma Pi_mul_inf_of_nonneg {f : σ → R} (hf : 0 ≤ f) (a b : σ → R) :
    f * (a ⊓ b) = f * a ⊓ f * b :=
  funext λ i ↦ mul_min_of_nonneg (a i) (b i) (hf i)

lemma Pi_pos_part_mul_inf (f : σ → R) (a b : σ → R) :
    f⁺ * (a ⊓ b) = f⁺ * a ⊓ f⁺ * b :=
  Pi_mul_inf_of_nonneg (LatticeOrderedGroup.pos_nonneg f) a b

lemma Pi_mul_sup_of_nonneg {f : σ → R} (hf : 0 ≤ f) (a b : σ → R) :
    f * (a ⊔ b) = f * a ⊔ f * b :=
  funext λ i ↦ mul_max_of_nonneg (a i) (b i) (hf i)

lemma Pi_pos_part_mul_sup (f : σ → R) (a b : σ → R) :
    f⁺ * (a ⊔ b) = f⁺ * a ⊔ f⁺ * b :=
  Pi_mul_sup_of_nonneg (LatticeOrderedGroup.pos_nonneg f) a b

lemma Pi_inf_mul_of_nonneg {f : σ → R} (hf : 0 ≤ f) (a b : σ → R) :
    (a ⊓ b) * f = a * f ⊓ b * f :=
  funext λ i ↦ min_mul_of_nonneg (a i) (b i) (hf i)

lemma Pi_inf_mul_pos_part (f : σ → R) (a b : σ → R) :
    (a ⊓ b) * f⁺ = a * f⁺ ⊓ b * f⁺ :=
  Pi_inf_mul_of_nonneg (LatticeOrderedGroup.pos_nonneg f) a b

lemma Pi_sup_mul_of_nonneg {f : σ → R} (hf : 0 ≤ f) (a b : σ → R) :
    (a ⊔ b) * f = a * f ⊔ b * f :=
  funext λ i ↦ max_mul_of_nonneg (a i) (b i) (hf i)

lemma Pi_sup_mul_pos_part (f a b : σ → R) :
    (a ⊔ b) * f⁺ = a * f⁺ ⊔ b * f⁺ :=
  Pi_sup_mul_of_nonneg (LatticeOrderedGroup.pos_nonneg f) a b

lemma Pi_pos_part_mul_pos_part_main_formula (f g : σ → R) :
    f⁺ * g⁺ = ((f * g) ⊓ (((f ⊓ g) ⊔ (f * g * f ⊓ f * g * g)) ⊔
      ((f ⊓ (f * g * f)) ⊔ (g ⊓ f * g * g))))⁺ :=
  funext λ i ↦ pos_part_mul_pos_part_main_formula (f i) (g i)

end LinearOrderedRingPi


section LatticeOrderedGroup

variable [DistribLattice G] [AddGroup G] [CovariantClass G G (· + ·) (· ≤ ·)]
    [CovariantClass G G (Function.swap (· + ·)) (· ≤ ·)]

lemma inf_pos_part (a b : G) : (a ⊓ b)⁺ = a⁺ ⊓ b⁺ :=
  sup_inf_right

lemma sup_pos_part (a b : G) : (a ⊔ b)⁺ = a⁺ ⊔ b⁺ :=
  sup_sup_distrib_right a b 0

end LatticeOrderedGroup





/-! ### Meta-closure and alternative definition -/

/-- The "alternative" lattice closure under infimum and supremum -/
inductive MetaClosure [Lattice α] (P : α → Prop) : α → Prop where
  | ofMem (_ : P a) : MetaClosure P a
  | ofInf (_ : MetaClosure P a) (_ : MetaClosure P b) : MetaClosure P (a ⊓ b)
  | ofSup (_ : MetaClosure P a) (_ : MetaClosure P b) : MetaClosure P (a ⊔ b)

inductive BinOpClosure (op : α → α → α) (P : α → Prop) : α → Prop where
  | ofMem (_ : P a) : BinOpClosure op P a
  | ofOp (_ : BinOpClosure op P a) (_ : BinOpClosure op P b) : BinOpClosure op P (op a b)


section Equivalence

variable [Lattice α] (P : α → Prop)

lemma InfClosure_imp_MetaClosure (h : BinOpClosure Inf.inf P a) : MetaClosure P a :=
  h.recOn MetaClosure.ofMem λ _ _ ↦ MetaClosure.ofInf

lemma SupInfClosure_imp_MetaClosure
    (h : BinOpClosure Sup.sup (BinOpClosure Inf.inf P) a) : MetaClosure P a :=
  h.recOn (InfClosure_imp_MetaClosure P) (λ _ _ ↦ MetaClosure.ofSup)

lemma MetaClosure_imp_SupInfClosure (h : MetaClosure P a) :
    BinOpClosure Sup.sup (BinOpClosure Inf.inf P) a :=
  h.recOn (λ h ↦ BinOpClosure.ofMem (BinOpClosure.ofMem h))
    (λ _ _ ha hb ↦ sorry)
    (λ _ _ ↦ BinOpClosure.ofOp)

lemma SupInfClosure_iff_MetaClosure :
    BinOpClosure Sup.sup (BinOpClosure Inf.inf P) a ↔ MetaClosure P a :=
  ⟨SupInfClosure_imp_MetaClosure P, MetaClosure_imp_SupInfClosure P⟩

lemma SupInfClosure_eq_MetaClosure :
    BinOpClosure Sup.sup (BinOpClosure Inf.inf P) = MetaClosure P :=
  funext λ _ ↦ propext (SupInfClosure_iff_MetaClosure P)

end Equivalence





/-! ### Properties of meta-closure via alternative definition -/

namespace MetaClosure

section AddGroup

variable [Lattice G] [AddGroup G] [CovariantClass G G (· + ·) (· ≤ ·)]
    [CovariantClass G G (Function.swap (· + ·)) (· ≤ ·)] (S : AddSubgroup G)

lemma add_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) (hb : MetaClosure (λ x ↦ x ∈ S) b) :
    MetaClosure (λ x ↦ x ∈ S) (a + b) :=
  ha.recOn
    (λ ha ↦ hb.recOn
      (λ hb ↦ ofMem (S.add_mem ha hb))
      (λ _ _ ↦ by rw [add_inf]; exact ofInf)
      (λ _ _ ↦ by rw [add_sup]; exact ofSup))
    (λ _ _ ↦ by rw [inf_add]; exact ofInf)
    (λ _ _ ↦ by rw [sup_add]; exact ofSup)

lemma zero_mem : MetaClosure (λ x ↦ x ∈ S) 0 := ofMem S.zero_mem

lemma neg_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) : MetaClosure (λ x ↦ x ∈ S) (-a) :=
  ha.recOn (λ ha ↦ ofMem (S.neg_mem ha))
    (λ _ _ ↦ by rw [neg_inf]; exact ofSup)
    (λ _ _ ↦ by rw [neg_sup]; exact ofInf)

lemma sub_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) (hb : MetaClosure (λ x ↦ x ∈ S) b) :
    MetaClosure (λ x ↦ x ∈ S) (a - b) :=
  (sub_eq_add_neg a b) ▸ add_mem S ha (neg_mem S hb)

lemma pos_part_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) : MetaClosure (λ x ↦ x ∈ S) a⁺ :=
  ofSup ha (zero_mem S)

lemma neg_part_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) : MetaClosure (λ x ↦ x ∈ S) a⁻ :=
  ofSup (neg_mem S ha) (zero_mem S)

lemma abs_mem (ha : MetaClosure (λ x ↦ x ∈ S) a) : MetaClosure (λ x ↦ x ∈ S) |a| :=
  ofSup ha (neg_mem S ha)

def AddGroup_mk : AddSubgroup G :=
  { carrier := {a | MetaClosure (λ x ↦ x ∈ S) a}
    add_mem' := add_mem S
    zero_mem' := zero_mem S
    neg_mem' := neg_mem S }

end AddGroup


section LinearOrderedRingPi

variable {σ R : Type*} [LinearOrderedRing R] (S : Subring (σ → R))

lemma Pi_one_mem : MetaClosure (λ x ↦ x ∈ S) 1 := ofMem S.one_mem

theorem Pi_pos_part_mul_pos_part_mem (hf : f ∈ S) (hg : g ∈ S) :
    MetaClosure (λ x ↦ x ∈ S) (f⁺ * g⁺) :=
  let T := S.toAddSubgroup
  have hfg := S.mul_mem hf hg
  have hfgf := S.mul_mem hfg hf
  have hfgg := S.mul_mem hfg hg
  have Xf : MetaClosure (λ x ↦ x ∈ T) f := ofMem hf
  have Xg : MetaClosure (λ x ↦ x ∈ T) g := ofMem hg
  have Xfg : MetaClosure (λ x ↦ x ∈ T) (f * g) := ofMem hfg
  have Xfgf : MetaClosure (λ x ↦ x ∈ T) (f * g * f) := ofMem hfgf
  have Xfgg : MetaClosure (λ x ↦ x ∈ T) (f * g * g) := ofMem hfgg
  (Pi_pos_part_mul_pos_part_main_formula f g).symm ▸ pos_part_mem T <| ofInf Xfg <|
    ofSup (ofSup (ofInf Xf Xg) (ofInf Xfgf Xfgg)) (ofSup (ofInf Xf Xfgf) (ofInf Xg Xfgg))

theorem Pi_closure_pos_part_mul_closure_pos_part_mem
    (hf : MetaClosure (λ x ↦ x ∈ S) f) (hg : MetaClosure (λ x ↦ x ∈ S) g) :
    MetaClosure (λ x ↦ x ∈ S) (f⁺ * g⁺) :=
  hg.recOn
    (λ hg ↦ hf.recOn
      (λ hf ↦ Pi_pos_part_mul_pos_part_mem S hf hg)
      (λ _ _ ↦ by rw [inf_pos_part, Pi_inf_mul_pos_part]; exact ofInf)
      (λ _ _ ↦ by rw [sup_pos_part, Pi_sup_mul_pos_part]; exact ofSup))
    (λ _ _ ↦ by rw [inf_pos_part, Pi_pos_part_mul_inf]; exact ofInf)
    (λ _ _ ↦ by rw [sup_pos_part, Pi_pos_part_mul_sup]; exact ofSup)

theorem Pi_mul_mem
    (hf : MetaClosure (λ x ↦ x ∈ S) f) (hg : MetaClosure (λ x ↦ x ∈ S) g) :
    MetaClosure (λ x ↦ x ∈ S) (f * g) := by
  rw [← LatticeOrderedGroup.pos_sub_neg f, sub_mul,
    ← LatticeOrderedGroup.pos_sub_neg g, mul_sub, mul_sub]
  let T := S.toAddSubgroup
  have hf₀ : MetaClosure (λ x ↦ x ∈ S) (-f) := neg_mem T hf
  have hg₀ : MetaClosure (λ x ↦ x ∈ S) (-g) := neg_mem T hg
  apply sub_mem T <;> apply sub_mem T <;>
    apply Pi_closure_pos_part_mul_closure_pos_part_mem <;> assumption

/-- The `MetaClosure` of `S` as a subring -/
def PiSubring_mk : Subring (σ → R) :=
  { AddGroup_mk S.toAddSubgroup with
    mul_mem' := Pi_mul_mem S
    one_mem' := Pi_one_mem S }

end LinearOrderedRingPi

end MetaClosure





/-! ### Subring structure via `BinOpClosure` -/

/-- Subring structure over `BinOpClosure` version of meta-closure -/
theorem SupInfClosure_exists_Subring
    {σ R : Type*} [LinearOrderedRing R] (S : Subring (σ → R)) :
    ∃ T : Subring (σ → R),
      setOf (BinOpClosure Sup.sup (BinOpClosure Inf.inf (λ x ↦ x ∈ S))) = T.carrier :=
  (SupInfClosure_eq_MetaClosure (λ x ↦ x ∈ S)) ▸ ⟨MetaClosure.PiSubring_mk S, rfl⟩
