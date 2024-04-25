/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Floor
import Mathlib.Algebra.Ring.Equiv

/-!
# IMO 2010 A1 (P1)

A *floor function* $⌊⬝⌋ : R → ℤ$ on a totally ordered ring $R$
  is a function such that, for any $r ∈ R$ and $n ∈ ℤ$,
$$ n ≤ ⌊r⌋ ↔ n ≤ r. $$

Let $R$ and $S$ be totally ordered rings with floor.
Find all functions $f : R → S$ such that, for any $x, y ∈ R$,
$$ f(⌊x⌋ y) = ⌊f(y)⌋ f(x). $$
-/

namespace IMOSL
namespace IMO2010A1

open Function

/-! ###### Extra lemmas -/

section

variable [Ring R] [CharZero R] [IsDomain R]

lemma zsmul_eq_zsmul_right_iff {m n : ℤ} {x : R} :
    m • x = n • x ↔ m = n ∨ x = 0 := by
  rw [zsmul_eq_mul, zsmul_eq_mul, mul_eq_mul_right_iff, Int.cast_inj]

lemma zsmul_left_eq_self₀ {n : ℤ} {x : R} :
    n • x = x ↔ n = 1 ∨ x = 0 := by
  rw [← zsmul_eq_zsmul_right_iff, one_zsmul]

end





/-! ### The interval (0, 1) on a floor ring -/

section FloorRing

variable [LinearOrderedRing R] [FloorRing R]

/-- An isomorphism `ℤ → R` given that `x < 1 → x ≤ 0` in `R` -/
def IntEquiv_of_zero_one_discrete (h : ∀ x : R, x < 1 → x ≤ 0) : ℤ ≃+* R :=
  { Int.castRingHom R with
    invFun := Int.floor
    left_inv := Int.floor_intCast
    right_inv := λ x ↦ (Int.floor_le x).antisymm <| le_of_sub_nonpos <|
      h _ (sub_left_lt_of_lt_add (Int.lt_floor_add_one x)) }

/-- For any floor ring `R` not isomorphic to `ℤ`,
  there exists an element `x : R` strictly between `0` and `1`. -/
theorem exists_equiv_Int_or_zero_one_dense :
    Nonempty (ℤ ≃+* R) ∨ (∃ x : R, 0 < x ∧ x < 1) :=
  (em (∀ x : R, x < 1 → x ≤ 0)).imp
    (λ h ↦ ⟨IntEquiv_of_zero_one_discrete h⟩)
    (λ h ↦ (not_forall.mp h).elim λ x h ↦
      ⟨x, (not_imp.mp h).symm.imp_left lt_of_not_le⟩)

theorem FloorRing_zero_one_dense [h : IsEmpty (ℤ ≃+* R)] :
    ∃ x : R, 0 < x ∧ x < 1 :=
  by_contra λ h0 ↦ h.false <| IntEquiv_of_zero_one_discrete
    λ x h1 ↦ le_of_not_lt λ h2 ↦ h0 ⟨x, h2, h1⟩

end FloorRing





/-! ### Main definition -/

section general

variable [LinearOrderedRing R] [FloorRing R]
  [LinearOrderedRing S] [FloorRing S]

def good (f : R → S) := ∀ x y : R, f (⌊x⌋ • y) = ⌊f y⌋ • f x



/-! ### General case -/

lemma good_zero : good (0 : R → S) :=
  λ _ _ ↦ (zsmul_zero _).symm

lemma good_const_of_floor_eq_one (h : ⌊(C : S)⌋ = 1) : good (const R C) :=
  λ _ _ ↦ h ▸ (one_zsmul _).symm



section

variable {f : R → S} (h : good f)

lemma map_zero_eq_zero_or_const_floor_eq_one :
    f 0 = 0 ∨ ∃ C : S, ⌊C⌋ = 1 ∧ f = const R C := by
  have h0 := h 0 0
  rw [zsmul_zero, eq_comm, zsmul_left_eq_self₀] at h0
  refine h0.symm.imp_right λ h0 ↦ ⟨f 0, h0, funext λ x ↦ ?_⟩
  specialize h x 0; rwa [zsmul_zero, h0, one_zsmul, eq_comm] at h

lemma eq_zero_or_floor_map_one : f = 0 ∨ ⌊f 1⌋ = 1 := by
  have h0 := h 1 1
  rw [Int.floor_one, one_zsmul, eq_comm, zsmul_left_eq_self₀] at h0
  refine h0.symm.imp_left λ h0 ↦ funext λ x ↦ ?_
  specialize h 1 x; rwa [Int.floor_one, one_zsmul, h0, zsmul_zero] at h

lemma solution_of_zero_one_dense (hc : ∃ x : R, 0 < x ∧ x < 1) :
    f = 0 ∨ ∃ C : S, ⌊C⌋ = 1 ∧ f = const R C :=
  (map_zero_eq_zero_or_const_floor_eq_one h).imp_left λ h0 ↦
    (eq_zero_or_floor_map_one h).elim id λ h1 ↦ by
  rcases hc with ⟨c, hc⟩
  have h2 := h c 1
  rw [Int.floor_eq_zero_iff.mpr ⟨hc.1.le, hc.2⟩,
    h1, one_zsmul, zero_zsmul, h0] at h2
  replace h0 : ⌊(-1 : R)⌋ = -1 := by
    rw [← Int.cast_one, ← Int.cast_neg, Int.floor_intCast]
  replace h1 := h (-1) c
  rw [h0, neg_one_zsmul, ← h2, Int.floor_zero, zero_zsmul] at h1
  replace hc : ⌊-c⌋ = -1 := by
    rw [Int.floor_eq_iff, Int.cast_neg, Int.cast_one, neg_add_self]
    exact ⟨neg_le_neg hc.2.le, neg_lt_zero.mpr hc.1⟩
  replace h2 := h (-c) 1
  rw [hc, neg_one_zsmul, h1, zsmul_zero] at h2
  funext x; specialize h (-1) (-x)
  rwa [h0, neg_one_zsmul, h2, zsmul_zero, neg_neg] at h

end



/-- Final solution for the case `R ≠ ℤ` -/
theorem final_solution_non_Int [IsEmpty (ℤ ≃+* R)] {f : R → S} :
    good f ↔ f = 0 ∨ ∃ C : S, ⌊C⌋ = 1 ∧ f = const R C :=
  ⟨λ h ↦ solution_of_zero_one_dense h FloorRing_zero_one_dense,
  λ h ↦ by rcases h with rfl | ⟨C, h, rfl⟩
           exacts [good_zero, good_const_of_floor_eq_one h]⟩

end general





/-! ### Integer case -/

/-- A predicate for a subset of `ℤ` to be a submonoid closed under divisor. -/
structure DvdClosedSubmonoid (M : Set ℤ) : Prop where
  one_mem : 1 ∈ M
  mul_mem : ∀ {m n}, m ∈ M → n ∈ M → m * n ∈ M
  dvd_mem : ∀ {m n}, m ∈ M → n ∣ m → n ∈ M



section Int

open scoped Classical

variable [LinearOrderedRing S] [FloorRing S]

lemma castMonoidHom_is_good (φ : ℤ →* ℤ) :
    good ((Int.cast : ℤ → S) ∘ φ.toFun) := λ m n ↦ by
  change (φ.toFun (m * n) : S) = ⌊(φ.toFun n : S)⌋ • (φ.toFun m : S)
  rw [Int.floor_intCast, zsmul_eq_mul, ← Int.cast_mul, mul_comm]
  exact congr_arg Int.cast (φ.map_mul n m)

lemma hom_smul_one_add_infinitesimal_is_good
    (φ : ℤ →* ℕ) {ε : S} (h : 0 ≤ ε) (h0 : ∀ k : ℕ, k • ε < 1) :
    good (λ x ↦ φ.toFun x • (1 + ε)) := λ m n ↦ by
  change φ (m * n) • (1 + ε) = ⌊φ.toFun n • (1 + ε)⌋ • φ.toFun m • (1 + ε)
  rw [nsmul_add _ _ (φ.toFun n), nsmul_one, Int.floor_nat_add,
    Int.floor_eq_zero_iff.mpr ⟨nsmul_nonneg h _, h0 _⟩,
    add_zero]
  rw [zsmul_eq_mul, Int.cast_natCast, ← nsmul_eq_mul, ← mul_nsmul, φ.map_mul]
  rfl

lemma indicator_smul_is_good (h : DvdClosedSubmonoid M) (h0 : ⌊(C : S)⌋ = 1) :
    good (λ n ↦ ite (n ∈ M) C 0) := λ m n ↦ by
  change ite (m * n ∈ M) C 0 = ⌊ite _ _ _⌋ • ite _ _ _
  by_cases h1 : m * n ∈ M
  · rw [if_pos h1, if_pos (h.dvd_mem h1 ⟨m, m.mul_comm n⟩),
      h0, one_zsmul, if_pos (h.dvd_mem h1 ⟨n, rfl⟩)]
  by_cases h2 : m ∈ M
  · rw [if_neg h1, if_neg (λ h3 ↦ h1 (h.mul_mem h2 h3)),
      Int.floor_zero, zero_zsmul]
  · rw [if_neg h1, if_neg h2, zsmul_zero]



section

variable {f : ℤ → S} (h : good f) (h0 : ⌊f 1⌋ = 1)

lemma eq_floor_smul_map_one (n : ℤ) : f n = ⌊f n⌋ • f 1 := by
  rw [← h, Int.floor_one, one_zsmul]

lemma floor_map_mul (m n : ℤ) : ⌊f (m * n)⌋ = ⌊f m⌋ * ⌊f n⌋ := by
  have h1 := eq_floor_smul_map_one h
  specialize h m n
  rw [Int.floor_int, h1 m, ← mul_zsmul, h1,
    Int.mul_comm, zsmul_eq_zsmul_right_iff] at h
  refine h.resolve_right λ h ↦ ?_
  rw [h, Int.floor_zero] at h0
  exact one_ne_zero h0.symm

lemma floor_map_pow (m : ℤ) : ∀ k, ⌊f (m ^ k)⌋ = ⌊f m⌋ ^ k
  | 0 => h0
  | k + 1 => by rw [pow_succ, floor_map_mul h h0, floor_map_pow m k, pow_succ]

lemma eq_castMonoidHom (h1 : ⌊f n⌋ < 0) :
    ∃ φ : ℤ →* ℤ, f = Int.cast ∘ φ.toFun := by
  suffices f 1 = 1 from ⟨⟨⟨λ n ↦ ⌊f n⌋, h0⟩, floor_map_mul h h0⟩,
    funext λ k ↦ (eq_floor_smul_map_one h k).trans (this ▸ zsmul_one _)⟩
  specialize h 1 n
  rw [← Int.floor_add_fract (f 1), h0, Int.cast_one] at h ⊢
  rw [add_right_eq_self]; refine (Int.fract_nonneg _).antisymm'
    (nonpos_of_mul_nonneg_right ?_ (Int.cast_lt_zero.mpr h1))
  rw [Int.floor_one, one_zsmul, zsmul_add, zsmul_one,
    ← sub_eq_iff_eq_add', ← Int.fract, zsmul_eq_mul] at h
  exact (Int.fract_nonneg (f n)).trans_eq h

lemma eq_hom_smul_one_add_infinitesimal (h1 : ∀ n, 0 ≤ ⌊f n⌋) (h2 : 1 < ⌊f N⌋) :
    ∃ (φ : ℤ →* ℕ) (ε : S) (_ : 0 ≤ ε) (_ : ∀ k : ℕ, k • ε < 1),
      f = λ x ↦ φ.toFun x • (1 + ε) := by
  refine ⟨⟨⟨λ n ↦ ⌊f n⌋.natAbs, congr_arg _ h0⟩, ?_⟩, ?_⟩
  · intro m n; change ⌊f (m * n)⌋.natAbs = ⌊f m⌋.natAbs * ⌊f n⌋.natAbs
    rw [floor_map_mul h h0, Int.natAbs_mul]
  have h3 : 0 ≤ f 1 - 1 := sub_nonneg_of_le (Int.floor_pos.mp h0.ge)
  refine ⟨f 1 - 1, h3, λ k ↦ ?_, funext λ k ↦ ?_⟩
  · have h4 := Int.floor_add_fract (f 1)
    rw [h0, Int.cast_one] at h4
    rw [← h4, add_sub_cancel_left, ← natCast_zsmul]
    suffices k ≤ ⌊f (N ^ k)⌋ by
      have h5 := eq_floor_smul_map_one h (N ^ k)
      rw [← h4, zsmul_add, zsmul_one, ← sub_eq_iff_eq_add'] at h5
      exact (zsmul_le_zsmul (Int.fract_nonneg (f 1)) this).trans_lt
        (h5.symm.trans_lt <| Int.fract_lt_one _)
    have h4 := Int.natAbs_of_nonneg (h1 N)
    rw [floor_map_pow h h0, ← h4, ← Nat.cast_pow, Int.ofNat_le]
    refine (Nat.lt_pow_self ?_ _).le
    rwa [← Int.ofNat_lt, h4]
  · change f k = (⌊f k⌋).natAbs • (1 + (f 1 - 1))
    rw [add_sub_cancel, ← natCast_zsmul, Int.natAbs_of_nonneg (h1 k)]
    exact eq_floor_smul_map_one h k

lemma eq_indicator_smul (h1 : ∀ n, ⌊f n⌋ = 0 ∨ ⌊f n⌋ = 1) :
    ∃ (M : Set ℤ) (_ : DvdClosedSubmonoid M) (C : S) (_ : ⌊C⌋ = 1),
      f = λ n ↦ ite (n ∈ M) C 0 :=
  ⟨{n : ℤ | ⌊f n⌋ ≠ 0},
  ---- `DvdClosedSubmonoid M`
  ⟨h0.trans_ne one_ne_zero,
    λ hm hn ↦ (floor_map_mul h h0 _ _).trans_ne (mul_ne_zero hm hn),
    λ h2 h3 h4 ↦ h3.elim λ k h3 ↦ h3 ▸ h2 <|
      (floor_map_mul h h0 _ k).trans (mul_eq_zero_of_left h4 _)⟩,
  ---- Choice of `C` and proof that it works
  f 1, h0, funext λ n ↦ by
    specialize h 1 n; rw [Int.floor_one, one_zsmul] at h
    by_cases h2 : ⌊f n⌋ = 0
    · rw [h2, zero_zsmul] at h
      exact h.trans (if_neg (not_not.mpr h2)).symm
    · rw [(h1 n).resolve_left h2, one_zsmul] at h
      exact h.trans (if_pos h2).symm⟩

lemma solution_of_Int :
    (∃ φ : ℤ →* ℤ, f = Int.cast ∘ φ.toFun) ∨
    (∃ (φ : ℤ →* ℕ) (ε : S) (_ : 0 ≤ ε) (_ : ∀ k : ℕ, k • ε < 1),
      f = λ x ↦ φ.toFun x • (1 + ε)) ∨
    (∃ (M : Set ℤ) (_ : DvdClosedSubmonoid M) (C : S) (_ : ⌊C⌋ = 1),
      f = λ n ↦ ite (n ∈ M) C 0) :=
  (em (∃ n, ⌊f n⌋ < 0)).imp
    (λ h1 ↦ h1.elim λ n ↦ eq_castMonoidHom h h0)
    λ h1 ↦ by
      rw [not_exists] at h1; simp_rw [not_lt] at h1
      refine (em (∃ n, 1 < ⌊f n⌋)).imp
        (λ h2 ↦ h2.elim λ n ↦ eq_hom_smul_one_add_infinitesimal h h0 h1)
        (λ h2 ↦ eq_indicator_smul h h0 λ n ↦ ?_)
      specialize h1 n; rw [le_iff_eq_or_lt, ← Int.add_one_le_iff] at h1
      exact h1.imp Eq.symm (le_of_not_lt (not_exists.mp h2 n)).antisymm

end



/-- Final solution for the case `R = ℤ` -/
theorem final_solution_Int : good f ↔
    f = 0 ∨ (∃ φ : ℤ →* ℤ, f = Int.cast ∘ φ.toFun) ∨
    (∃ (φ : ℤ →* ℕ) (ε : S) (_ : 0 ≤ ε) (_ : ∀ k : ℕ, k • ε < 1),
      f = λ x ↦ φ.toFun x • (1 + ε)) ∨
    (∃ (M : Set ℤ) (_ : DvdClosedSubmonoid M) (C : S) (_ : ⌊C⌋ = 1),
      f = λ n ↦ ite (n ∈ M) C 0) :=
  ⟨λ h ↦ (eq_zero_or_floor_map_one h).imp_right (solution_of_Int h),
  λ h ↦ by rcases h with rfl | ⟨φ, rfl⟩ |
             ⟨φ, ε, h, h0, rfl⟩ | ⟨M, h, C, h0, rfl⟩
           exacts [good_zero, castMonoidHom_is_good φ,
             hom_smul_one_add_infinitesimal_is_good φ h h0,
             indicator_smul_is_good h h0]⟩

end Int
