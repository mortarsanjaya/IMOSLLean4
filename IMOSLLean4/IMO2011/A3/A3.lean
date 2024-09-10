/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Prod
import Mathlib.RingTheory.Ideal.Quotient

/-!
# IMO 2011 A3

Let $R$ be a commutative ring where $2$ is not a zero divisor.
Find all functions $f, g : R → R$ such that for any $x, y ∈ R$,
$$ g(f(x + y)) = f(x) + (2x + y) g(y). $$

### Further directions

A lot of the steps are implemented without assuming that $R$ is commutative.
Not only that, we have a complete solution without commutativity if
  we do not look into some structural decomposition of $R$.
Can we get a nice description of the result with either a
  structural decomposition or using ring homomorphisms?
-/

namespace IMOSL
namespace IMO2011A3

def good [NonUnitalNonAssocSemiring R] (f g : R → R) :=
  ∀ x y, g (f (x + y)) = f x + (2 • x + y) * g y

theorem main_answer_is_good [NonUnitalCommRing R] (C : R) :
    good (λ x ↦ x * x + C) id := λ x y ↦ by
  rw [id, id, add_right_comm, add_left_inj, two_nsmul, mul_add,
    add_mul, mul_comm y, add_assoc, ← add_mul, add_assoc]

theorem zero_is_good [NonUnitalNonAssocSemiring R] : good (0 : R → R) 0 :=
    λ _ _ ↦ ((zero_add _).trans (mul_zero _)).symm

theorem prod_is_good [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    {fR gR : R → R} (hR : good fR gR) {fS gS : S → S} (hS : good fS gS) :
    good (Prod.map fR fS) (Prod.map gR gS) :=
  λ x y ↦ Prod.ext (hR x.1 y.1) (hS x.2 y.2)

theorem good_Equiv_conj_iff [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring S]
    {f g : R → R} (φ : R ≃+* S) : good f g ↔ good (φ.conj f) (φ.conj g) :=
  φ.toEquiv.forall₂_congr φ.toEquiv <| by
    have X (z : R) : φ.toEquiv z = (φ : R ≃+* S) z := rfl
    intro x y; simp only [φ.conj_apply, X]
    rw [← φ.map_add, ← map_nsmul, ← φ.map_add]
    simp only [φ.toEquiv_eq_coe, EquivLike.coe_symm_apply_apply]
    rw [← φ.map_mul, ← φ.map_add]
    exact φ.apply_eq_iff_eq.symm



lemma step1_1 [NonUnitalNonAssocRing R] {f g : R → R} (h : good f g) (x y) :
    (f x - x * g x) - (f y - y * g y) = 2 • (y * g x - x * g y) := by
  rw [nsmul_sub, sub_eq_sub_iff_add_eq_add, ← add_sub_right_comm, ← add_sub_assoc,
    sub_eq_sub_iff_add_eq_add, two_nsmul, ← add_mul, add_assoc, ← add_mul,
    ← two_nsmul, ← h, add_comm _ (f y), add_assoc, two_nsmul, ← add_mul,
    ← add_mul, ← two_nsmul, ← h, add_comm]

theorem step1 [NonAssocRing R] (hR : ∀ x y : R, 2 • x = 2 • y → x = y)
    {f g : R → R} (h : good f g) :
    ∃ A B C : R, (f = λ x ↦ x * (x * A) - x * B + C) ∧ (g = (· * A + B)) := by
  ---- First obtain the equation for `g`
  obtain ⟨A, h0⟩ : ∃ A, ∀ x, g x = x * A + g 0 := ⟨g 1 - g 0, λ x ↦ by
    have h0 : _ + _ = _ + _ := congrArg₂ _ (step1_1 h x 1) (step1_1 h 1 0)
    rw [sub_add_sub_cancel, step1_1 h, ← nsmul_add] at h0
    replace h0 := hR _ _ h0
    rwa [zero_mul, zero_sub, one_mul, zero_mul, one_mul, zero_sub, eq_add_neg_iff_add_eq,
      eq_sub_iff_add_eq', ← add_assoc, ← sub_eq_add_neg, ← mul_sub, eq_comm] at h0⟩
  ---- Now obtain the equation for `f`
  refine ⟨A, g 0, f 0, funext λ x ↦ ?_, funext h0⟩
  have h1 := step1_1 h x 0
  rwa [zero_mul, sub_zero, zero_mul, zero_sub, sub_eq_iff_eq_add,
    sub_eq_iff_eq_add', h0, mul_add, two_nsmul, add_assoc _ _ (f 0),
    add_add_add_comm, add_neg_cancel_left, ← sub_eq_add_neg] at h1

theorem step2 [Ring R] (hR : ∀ x y : R, 2 • x = 2 • y → x = y)
    {A B C : R} (h : good (λ x ↦ x * (x * A) - x * B + C) (λ x ↦ x * A + B)) :
    B = 0 ∧ A * A = A ∧ C * A = C := by
  ---- First plug `y = -2x`
  have h0 (x) : (x * (x * A) + x * B + C) * A + B = x * (x * A) - x * B + C := by
    specialize h x (-(2 • x)); simp only at h
    rwa [add_neg_cancel, zero_mul, add_zero, two_nsmul, neg_add,
      add_neg_cancel_comm_assoc, neg_mul x A, neg_mul_neg, neg_mul, sub_neg_eq_add] at h
  ---- Now plug `h0` at various values of `x`
  have h1 := h0 0; rw [zero_mul, zero_mul, zero_add, sub_zero, zero_add] at h1
  have h2 := h0 1; rw [one_mul, one_mul, one_mul, add_mul, add_assoc, h1, add_left_inj] at h2
  have h3 := h0 (-1); rw [neg_one_mul, neg_one_mul, neg_one_mul, neg_neg,
    ← sub_eq_add_neg, sub_neg_eq_add, add_mul, add_assoc, h1, add_left_inj] at h3
  ---- Simplify more
  replace h3 : _ - _ = _ - _ := congrArg₂ (· - ·) h2 h3
  rw [← sub_mul, add_sub_sub_cancel, add_mul, ← two_nsmul, ← sub_sub,
    sub_sub_cancel_left, sub_eq_add_neg, ← two_nsmul] at h3
  replace h3 := hR _ _ h3
  rw [add_mul, h3, sub_eq_add_neg, add_left_inj] at h2
  ---- The rest needs associativity assumption on `R`
  replace h0 : _ * A = _ * A := congrArg (· * A) h1
  rw [add_mul, mul_assoc, h2, add_right_eq_self, h3, neg_eq_zero] at h0
  rw [h0, add_zero] at h1; exact ⟨h0, h2, h1⟩

theorem relation_summary [Ring R] (hR : ∀ x y : R, 2 • x = 2 • y → x = y)
    {f g : R → R} (h : good f g) :
    ∃ A C : R, A * A = A ∧ C * A = C ∧ (f = λ x ↦ x * x * A + C) ∧ (g = (· * A)) := by
  rcases step1 hR h with ⟨A, B, C, rfl, rfl⟩
  rcases step2 hR h with ⟨rfl, h0, h1⟩
  refine ⟨A, C, h0, h1, ?_, ?_⟩
  · funext x; rw [mul_zero, sub_zero, ← mul_assoc]
  · simp only [add_zero]





/-! ### Idempotent decomposition -/

section

variable [CommRing R] {a : R} (h : a * a = a)

def idempotent_self_mul_part : R ⧸ Ideal.span {1 - a} →+ R :=
  QuotientAddGroup.lift _ (AddMonoidHom.mulRight a) λ x h0 ↦ by
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at h0
    rcases h0 with ⟨y, rfl⟩; change (1 - a) * y * a = 0
    rw [mul_right_comm, one_sub_mul, h, sub_self, zero_mul]

theorem idempotent_self_mul_part_map_quot (x : R) :
    idempotent_self_mul_part h x = x * a := rfl

theorem quot_self_comp_idempotent_self_mul_part :
    ∀ x, Ideal.Quotient.mk _ (idempotent_self_mul_part h x) = x :=
  Quotient.ind λ x ↦ Ideal.Quotient.eq.mpr <| Ideal.mem_span_singleton.mpr
    ⟨-x, by rw [mul_neg, ← neg_mul, neg_sub, sub_one_mul, mul_comm]; rfl⟩

theorem quot_compl_comp_idempotent_self_mul_part :
    ∀ x, Ideal.Quotient.mk (Ideal.span {a}) (idempotent_self_mul_part h x) = 0 :=
  Quotient.ind λ x ↦ Ideal.Quotient.eq.mpr <| Ideal.mem_span_singleton.mpr
    ⟨x, (sub_zero _).trans (mul_comm _ _)⟩

def idempotent_compl_mul_part : R ⧸ Ideal.span {a} →+ R :=
  QuotientAddGroup.lift _ (AddMonoidHom.mulRight (1 - a)) λ x h0 ↦ by
    rw [Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton] at h0
    rcases h0 with ⟨y, rfl⟩; change a * y * (1 - a) = 0
    rw [mul_right_comm, mul_one_sub, h, sub_self, zero_mul]

theorem idempotent_compl_mul_part_map_quot (x : R) :
    idempotent_compl_mul_part h x = x * (1 - a) := rfl

theorem quot_compl_comp_idempotent_compl_mul_part :
    ∀ x, Ideal.Quotient.mk _ (idempotent_compl_mul_part h x) = x :=
  Quotient.ind λ x ↦ Ideal.Quotient.eq.mpr <| Ideal.mem_span_singleton.mpr ⟨-x, by
    change x * (1 - a) - x = _
    rw [mul_one_sub, sub_sub_cancel_left, mul_neg, mul_comm]⟩

theorem quot_self_comp_idempotent_compl_mul_part :
    ∀ x, Ideal.Quotient.mk (Ideal.span {1 - a}) (idempotent_compl_mul_part h x) = 0 :=
  Quotient.ind λ x ↦ Ideal.Quotient.eq.mpr <| Ideal.mem_span_singleton.mpr
    ⟨x, (sub_zero _).trans (mul_comm _ _)⟩

def idempotent_decomp_AddHom : (R ⧸ Ideal.span {1 - a}) × R ⧸ Ideal.span {a} →+ R :=
  AddMonoidHom.coprod (idempotent_self_mul_part h) (idempotent_compl_mul_part h)

theorem idempotent_decomp_AddHom_map (p) :
    idempotent_decomp_AddHom h p
      = idempotent_self_mul_part h p.1 + idempotent_compl_mul_part h p.2 := rfl

theorem idempotent_decomp_AddHom_map_quot (x y : R) :
    idempotent_decomp_AddHom h (x, y) = x * a + y * (1 - a) := rfl

theorem idempotent_decomp_AddHom_map_quot_self (x : R) :
    idempotent_decomp_AddHom h (x, x) = x := by
  rw [idempotent_decomp_AddHom_map_quot, ← mul_add, add_sub_cancel, mul_one]

theorem quot_self_comp_idempotent_decomp_AddHom
    (p : (R ⧸ Ideal.span {1 - a}) × R ⧸ Ideal.span {a}) :
    Ideal.Quotient.mk (Ideal.span {1 - a}) (idempotent_decomp_AddHom h p) = p.1 := by
  rw [idempotent_decomp_AddHom, AddMonoidHom.coprod_apply,
    map_add, quot_self_comp_idempotent_self_mul_part,
    quot_self_comp_idempotent_compl_mul_part, add_zero]

theorem quot_compl_comp_idempotent_decomp_AddHom
    (p : (R ⧸ Ideal.span {1 - a}) × R ⧸ Ideal.span {a}) :
    Ideal.Quotient.mk (Ideal.span {a}) (idempotent_decomp_AddHom h p) = p.2 := by
  rw [idempotent_decomp_AddHom, AddMonoidHom.coprod_apply,
    map_add, quot_compl_comp_idempotent_self_mul_part,
    quot_compl_comp_idempotent_compl_mul_part, zero_add]

def idempotent_decomp : R ≃+* (R ⧸ Ideal.span {1 - a}) × R ⧸ Ideal.span {a} :=
  { RingHom.prod (Ideal.Quotient.mk _) (Ideal.Quotient.mk _) with
    invFun := idempotent_decomp_AddHom h
    left_inv := idempotent_decomp_AddHom_map_quot_self h
    right_inv := λ p ↦ Prod.ext (quot_self_comp_idempotent_decomp_AddHom h p)
      (quot_compl_comp_idempotent_decomp_AddHom h p) }

lemma idempotent_decomp_apply (x : R) :
    idempotent_decomp h x = ((x, x) : (R ⧸ Ideal.span {1 - a}) × R ⧸ Ideal.span {a}) := rfl

lemma idempotent_decomp_symm_apply (p) :
    (idempotent_decomp h).symm p
      = idempotent_self_mul_part h p.1 + idempotent_compl_mul_part h p.2 := rfl

end





/-! ### Final solution -/

theorem final_solution (R : Type u) [CommRing R] (hR : ∀ x y : R, 2 • x = 2 • y → x = y)
    {f g : R → R} : good f g ↔
      ∃ (R₁ R₂ : Type u) (_ : CommRing R₁) (_ : CommRing R₂) (φ : R₁ × R₂ ≃+* R) (c : R₁),
      f = φ.conj (Prod.map (λ x ↦ x * x + c) 0) ∧ g = φ.conj (Prod.map id 0) :=
  ⟨λ h ↦ by
    rcases relation_summary hR h with ⟨A, C, h0, h1, rfl, rfl⟩
    refine ⟨R ⧸ Ideal.span {1 - A}, R ⧸ Ideal.span {A},
      Ideal.Quotient.commRing _, Ideal.Quotient.commRing _,
      (idempotent_decomp h0).symm, idempotent_self_mul_part h0 C,
      funext λ x ↦ ?_, funext λ x ↦ ?_⟩
    · change _ = (idempotent_decomp h0).symm (_, 0)
      rw [idempotent_decomp_symm_apply, idempotent_self_mul_part_map_quot, map_zero,
        add_zero, h1, map_add, idempotent_self_mul_part_map_quot, ← map_mul,
        idempotent_self_mul_part_map_quot, h1]
    · change x * A = x * A + 0 * (1 - A)
      rw [zero_mul, add_zero],
  λ ⟨R₁, R₂, hR₁, hR₂, φ, c, h, h0⟩ ↦ by
    rw [h, h0, ← good_Equiv_conj_iff]
    exact prod_is_good (main_answer_is_good c) zero_is_good⟩
