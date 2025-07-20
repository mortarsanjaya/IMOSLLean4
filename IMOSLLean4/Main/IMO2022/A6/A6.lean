/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.GroupTheory.OrderOfElement

/-!
# IMO 2022 A6

Let $G$ be a commutative group.
A function $f : G → G$ is called *infectious* if
$$ f(x + f(y)) = f(x) + f(y) \quad ∀ x, y ∈ G. $$
Find all pairs $(m, n)$ of integers such that for any infectious functions
  $f : G → G$, there exists $z ∈ G$ such that $m f(z) = nz$.
-/

namespace IMOSL
namespace IMO2022A6

/-! ### Infectious functions -/

structure InfectiousFun (G) [Add G] where
  toFun : G → G
  infectious_def' : ∀ x y, toFun (x + toFun y) = toFun x + toFun y


namespace InfectiousFun

instance [Add G] : FunLike (InfectiousFun G) G G where
  coe f := f.toFun
  coe_injective' f g h := by rwa [InfectiousFun.mk.injEq]

@[ext] theorem ext [Add G] {f g : InfectiousFun G} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

theorem infectious_def [Add G] (f : InfectiousFun G) (x y) : f (x + f y) = f x + f y :=
  f.infectious_def' x y


section

variable [AddGroup G] (f : InfectiousFun G)

theorem infectious_sub (x y) : f (x - f y) = f x - f y := by
  rw [eq_sub_iff_add_eq, ← f.infectious_def, sub_add_cancel]

/-- The range of an infectious function as a subgroup -/
def rangeSubgroup : AddSubgroup G :=
  AddSubgroup.ofSub (Set.range f) ⟨f 0, 0, rfl⟩ <| by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨x - f y, (f.infectious_sub x y).trans (sub_eq_add_neg _ _)⟩

theorem map_zsmul_map_zero (k : ℤ) : f (k • f 0) = (k + 1) • f 0 := by
  obtain ⟨g, h⟩ : k • f 0 ∈ rangeSubgroup f := f.rangeSubgroup.zsmul_mem ⟨0, rfl⟩ k
  rw [← zero_add (k • _), Int.add_comm, one_add_zsmul, ← h, f.infectious_def]

end


/-- General construction of infectious function -/
def mk_of_repFn [AddGroup G] (H : AddSubgroup G) (φ : G ⧸ H → H)
  (rep : G ⧸ H → G) (hrep : ∀ x, (rep x : G ⧸ H) = x) : InfectiousFun G where
  toFun x := φ x + (-rep x + x)
  infectious_def' x y := by
    have h (x : G) : -rep x + x ∈ H := by rw [← QuotientAddGroup.eq, hrep]
    rw [← add_assoc x, QuotientAddGroup.mk_add_of_mem _ (h y), add_assoc,
      QuotientAddGroup.mk_add_of_mem _ (SetLike.coe_mem _), add_assoc, add_assoc]

end InfectiousFun





/-! ### The main problem -/

/-- The main definition -/
def good (G) [AddGroup G] (m n : ℤ) := ∀ f : InfectiousFun G, ∃ z, m • f z = n • z

lemma gcd_addOrderOf_dvd_iff [AddGroup G] {g : G} {a b : ℤ} :
    a.gcd (addOrderOf g) ∣ b.natAbs ↔ ∃ k : ℤ, (a * k) • g = b • g := by
  have h : b.natAbs = b ∨ b.natAbs = -b := b.natAbs_eq.imp Eq.symm Int.eq_neg_comm.mp
  simp_rw [← addOrderOf_dvd_sub_iff_zsmul_eq_zsmul, Int.gcd_dvd_iff]
  generalize (b.natAbs : ℤ) = c at h ⊢
  rcases h with rfl | rfl
  ---- Case 1: `b ≥ 0`
  · refine ⟨?_, ?_⟩
    · rintro ⟨x, y, rfl⟩; refine ⟨x, -y, ?_⟩
      rw [sub_add_cancel_left, mul_neg]
    · rintro ⟨k, y, h⟩; refine ⟨k, -y, ?_⟩
      rw [mul_neg, ← h, neg_sub, add_sub_cancel]
  ---- Case 2: `b < 0`
  · refine ⟨?_, ?_⟩
    · rintro ⟨x, y, h⟩; refine ⟨-x, y, ?_⟩
      rw [sub_eq_add_neg, h, mul_neg, neg_add_cancel_left]
    · intro ⟨k, y, h⟩; refine ⟨-k, y, ?_⟩
      rw [← h, mul_neg, ← add_sub_assoc, neg_add_cancel, zero_sub]

theorem imp_good [AddGroup G] (h : ∀ g : G, (m - n).gcd (addOrderOf g) ∣ m.natAbs) :
    good G m n := by
  intro f; replace h := gcd_addOrderOf_dvd_iff.mp (h (f 0))
  rcases h with ⟨k, h⟩; refine ⟨-k • f 0, ?_⟩
  rw [f.map_zsmul_map_zero, ← mul_zsmul, ← mul_zsmul, mul_add_one, add_zsmul, Int.mul_neg,
    neg_zsmul, neg_add_eq_iff_eq_add, Int.mul_neg, neg_zsmul, ← sub_zsmul, ← sub_mul, h]


section

variable [AddCommGroup G] (h : good G m n) (H : AddSubgroup G)
include h

theorem good_mk_of_repFn_prop
    (φ : G ⧸ H → H) (rep : G ⧸ H → G) (hrep : ∀ x, (rep x : G ⧸ H) = x) :
    ∃ (j : G ⧸ H) (h : H), (m - n) • h = -(m • φ j) + n • rep j := by
  ---- Apply `good` on the infectious function constructed from `H, φ, rep`
  obtain ⟨z, hz⟩ : ∃ z : G, m • (↑(φ z) + (-rep ↑z + z)) = n • z :=
    h (InfectiousFun.mk_of_repFn H φ rep hrep)
  ---- Choose `j = ⟦z⟧` and `h = z - rep z ∈ H`, and do some algebraic manipulation
  refine ⟨z, ⟨-rep z + z, by rw [← QuotientAddGroup.eq, hrep]⟩, ?_⟩
  rw [eq_neg_add_iff_add_eq, sub_zsmul, ← add_assoc, ← zsmul_add, hz,
    ← zsmul_neg, neg_add_rev, neg_neg, ← zsmul_add, add_neg_cancel_left]

/-- Version of `good_mk_of_repFn'_prop` -/
theorem good_mk_of_Quot_prop (φ : G ⧸ H → H) :
    ∃ (j : G ⧸ H) (h : H), (m - n) • h = -(m • φ j) + n • Quot.out j :=
  good_mk_of_repFn_prop h H φ Quot.out Quot.out_eq

theorem good_m_zsmul_eq_sub_zsmul (a : H) : ∃ b : H, (m - n) • (b : G) = m • a := by
  classical
  obtain ⟨j, b, h0⟩ := good_mk_of_Quot_prop h H
    λ j ↦ if (∃ h : H, (m - n) • h = n • Quot.out j) then a else 0
  split_ifs at h0 with h1
  ---- Case 1: `n x_j ∈ (m - n) H`
  · rcases h1 with ⟨c, h1⟩; refine ⟨c - b, ?_⟩
    rw [AddSubgroupClass.coe_sub, zsmul_sub, h1, h0, sub_add_cancel_right, neg_neg]
  ---- Case 2: `n x_j ∉ (m - n) H`
  · rw [ZeroMemClass.coe_zero, smul_zero, neg_zero, zero_add] at h0
    exact absurd ⟨b, h0⟩ h1

end


theorem good_imp [AddCommGroup G] (h : good G m n) (g : G) :
    (m - n).gcd (addOrderOf g) ∣ m.natAbs := by
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    good_m_zsmul_eq_sub_zsmul h _ ⟨g, AddSubgroup.mem_zmultiples g⟩
  exact gcd_addOrderOf_dvd_iff.mpr ⟨k, (mul_zsmul _ _ _).trans hk⟩

/-- Final solution -/
theorem final_solution [AddCommGroup G] :
    good G m n ↔ ∀ g : G, (m - n).gcd (addOrderOf g) ∣ m.natAbs :=
  ⟨good_imp, imp_good⟩
