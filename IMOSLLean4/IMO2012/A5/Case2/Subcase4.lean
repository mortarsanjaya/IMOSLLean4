/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2012.A5.Case2.Basic
import IMOSLLean4.IMO2012.A5.A5Quotient

/-!
# IMO 2012 A5, Subcase 2.4: $f(-1) = 0$ and $f(2) = 1$

This file solves Subcase 2.4.
-/

namespace IMOSL
namespace IMO2012A5

/-! #### Some lemmas in characteristic two (to avoid `CharP` imports) -/

namespace Char2

variable [CommRing R] (h : (2 : R) = 0)

theorem add_self (x : R) : x + x = 0 :=
  (two_mul x).symm.trans (mul_eq_zero_of_left h x)

theorem add_add_cancel (x y : R) : x + y + y = x :=
  by rw [add_assoc, add_self h, add_zero]

theorem sub_eq_add (x y : R) : x - y = x + y :=
  sub_eq_of_eq_add (add_add_cancel h x y).symm

theorem add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  by rw [add_sq', h, zero_mul, zero_mul, add_zero]

theorem add_one_sq (x : R) : (x + 1) ^ 2 = x ^ 2 + 1 :=
  by rw [add_sq h, one_pow]

theorem add_eq_iff_eq_add {x y z : R} : x + y = z ↔ x = z + y :=
  sub_eq_add h x y ▸ sub_eq_iff_eq_add

theorem add_eq_iff_eq_add' {x y z : R} : x + y = z ↔ x = y + z :=
  sub_eq_add h x y ▸ sub_eq_iff_eq_add'

theorem add_eq_zero_iff_eq {x y : R} : x + y = 0 ↔ x = y :=
  by rw [add_eq_iff_eq_add h, zero_add]

end Char2





/-! ## The solution -/

variable [CommRing R] [CommRing S] [IsDomain S] {f : R → S} (h : good f)

/-- `2 ∈ I` -/
theorem case2_4_lem1 (h0 : f (-1) = 0) (h1 : f 2 = -1) :
    2 ∈ periodIdeal h := by
  have h2 x : f (x + 1) = f (x - 1) ∨ f x + f (x - 1) = -1 := by
    have h2 := case2_special_identity h h0 x
    rwa [case2_map_add_two_eq h h0, h1, neg_one_mul, neg_sub, sub_add,
      mul_neg_one, ← add_sub_assoc, neg_add_self, eq_sub_iff_add_eq, mul_sub,
      ← sub_add, mul_comm _ (f x), ← mul_sub, ← add_mul, ← add_one_mul (α := S),
      mul_eq_zero, add_eq_zero_iff_eq_neg, sub_eq_zero, or_comm] at h2
  intro x
  rw [← one_add_one_eq_two, ← add_rotate]
  rcases h2 (x + 1) with h3 | h3
  rwa [add_sub_cancel] at h3
  specialize h2 (-(x + 1))
  have h4 := case2_map_even h h0
  rw [← neg_add', h4, h4, neg_add_eq_sub, sub_add_cancel'', h4] at h2
  refine h2.elim Eq.symm λ h2 ↦ ?_
  rwa [add_sub_cancel, ← h2, add_right_inj, eq_comm] at h3

section Rchar2

variable (h0 : (2 : R) = 0) (h1 : f 0 = -1)

theorem case2_4_lem2 : f (-1) = 0 := by
  rw [← one_add_one_eq_two, add_eq_zero_iff_eq_neg] at h0
  rw [← h0, good_map_one h]

/-- (10.1) -/
theorem case2_4_lem3 (x : R) : f (x * (x + 1) + 1) = f x * f (x + 1) :=
  Char2.sub_eq_add h0 (x * (x + 1)) 1 ▸
    case2_map_self_mul_add_one_sub_one h (case2_4_lem2 h h0) x

/-- (10.2) -/
theorem case2_4_lem4 (x : R) : f (x ^ 2 + 1) = f x ^ 2 - 1 :=
  Char2.sub_eq_add h0 (x ^ 2) 1 ▸ case2_map_sq_sub_one h (case2_4_lem2 h h0) h1 x

/-- (10.3) -/
theorem case2_4_lem5 (x : R) : f (x ^ 2) = f (x + 1) ^ 2 - 1 := by
  rw [← case2_4_lem4 h h0 h1, Char2.add_one_sq h0, Char2.add_add_cancel h0]

/-- Lemma 4 (TODO: Optimize the proof, if possible) -/
theorem case2_4_lem6 (x : R) :
    f x ^ 2 + f (x + 1) ^ 2 = 1 ∨ f x + f (x + 1) = 1 := by
  have h3 := case2_4_lem3 h h0
  have h4 := case2_4_lem5 h h0 h1
  ---- (10.L1.1)
  have h5 x :
      (f (x + 1) ^ 2 - 1) * (f (x + 1) - 1) + f x * f (x + 1)
        = f x * f (x * (x + 1)) := by
    rw [← h3, ← h4, ← h, eq_sub_iff_add_eq, add_right_comm, ← eq_sub_iff_add_eq,
      ← mul_assoc, mul_add_one x, ← sq, add_left_comm, Char2.add_self h0,
      add_zero, ← mul_add_one (f (x ^ 2)), sub_add_cancel, add_assoc, h]
  ---- Now use (10.L1.1) for more reduction
  have h6 : (f x) * _ = _ := congr_arg₂ _ rfl (h5 (x + 1))
  rw [Char2.add_add_cancel h0, mul_left_comm, mul_comm (x + 1), ← h5] at h6
  replace h6 :
      (f x ^ 2 + f (x + 1) ^ 2 - 1) * (f x + f (x + 1) - 1)
        * (f x - f (x + 1)) = 0 :=
    sub_eq_zero_of_eq h6 ▸ by ring
  rw [mul_eq_zero, mul_eq_zero, sub_eq_zero, sub_eq_zero, sub_eq_zero] at h6
  rcases h6 with h6 | h6; exact h6; right
  ---- Assuming `f(x) = f(x + 1)`, prove that `f(x) + f(x + 1) = 1`
  specialize h3 (x ^ 2)
  have h2 := case2_4_lem4 h h0 h1
  rw [h4, h2, ← Char2.add_one_sq h0, ← mul_pow, h2] at h3
  replace h3 : _ * _ = _ * _ := congr_arg ((f x) ^ 2 * ·) h3
  rw [mul_sub_one, ← mul_pow, ← h5, ← h6, ← sq, mul_sub_one,
    ← add_sub_right_comm, add_sub_assoc, sub_sub_cancel, ← sq, add_sq,
    mul_comm, one_pow, add_assoc, mul_pow, sub_eq_iff_eq_add, add_right_inj,
    mul_one, ← eq_sub_iff_add_eq,← mul_assoc, mul_left_eq_self₀] at h3
  rcases h3 with h3 | h3
  · rwa [← h6, ← two_mul]
  · specialize h5 (x ^ 2)
    rw [h2, h4, ← h6, h3, sq, zero_mul, zero_mul,
      zero_sub, neg_mul_neg, mul_one, add_zero] at h5
    exact absurd h5 one_ne_zero

/-- Solution for the current sub-subcase (`hom_sub_one: x ↦ φ(x) - 1`).
  (TODO: Optimize the proof, if possible) -/
theorem case2_4_Schar2_quot_IsAnswer (h3 : (2 : S) = 0) : IsAnswer f :=
  IsAnswer_of_add_one_additive h <| by
    ---- (10.L2.1)
    have h4 x : f (x + 1) = f x + 1 := by
      rw [← Char2.add_eq_iff_eq_add' h3, add_comm]
      refine (case2_4_lem6 h h0 h1 x).elim (λ h4 ↦ ?_) id
      rwa [← Char2.add_sq h3, ← Char2.add_eq_zero_iff_eq h3,
        ← Char2.add_one_sq h3, sq_eq_zero_iff, Char2.add_eq_zero_iff_eq h3] at h4
    ---- (10.L2.2)
    replace h x y : f (x * y) = f x * f y + f (x + y) + 1 :=
      by rw [← h, sub_add_cancel, h4, Char2.add_add_cancel h3]
    ---- Back to the main equality
    intros x y
    let a := f x
    let b := f y
    let c := f (x + y)
    have h6 := h (x * y) ((y + 1) * (x + 1))
    rw [mul_mul_mul_comm, h, add_left_inj] at h6
    have h7 : x * y + (y + 1) * (x + 1) = x * (y + 1) + y * (x + 1) + 1 := by ring
    rw [h7, h4, ← add_assoc, ← sub_eq_iff_eq_add', add_sub_add_right_eq_sub] at h6
    replace h7 : f (x * y) = a * b + c + 1 := h x y
    have h8 : f (x * (y + 1)) = a * (b + 1) + (c + 1) + 1 := by rw [h, ← add_assoc, h4, h4]
    have h9 : f (y * (x + 1)) = b * (a + 1) + (c + 1) + 1 := by
      rw [h, add_left_comm, ← add_assoc, h4, h4]
    have h10 : f ((y + 1) * (x + 1)) = (b + 1) * (a + 1) + c + 1 := by
      rw [h, add_add_add_comm, one_add_one_eq_two, h0, add_zero, add_comm y x, h4, h4]
    replace h6 := (congr_arg₂ _ (congr_arg₂ _ h8 h9) (congr_arg₂ _ h7 h10)).symm.trans h6
    rw [← sub_eq_iff_eq_add', ← h6, eq_comm, ← sub_eq_zero]
    refine' Eq.trans _ (mul_eq_zero_of_left h3 <| (a + 1) * (b + 1))
    ring

variable (h2 : ∀ c ∈ periodIdeal h, c = 0) (h3 : (2 : S) ≠ 0)

/-- Lemma 5 -/
theorem case2_4_lem7 (x : R) :
    f x * f (x + 1) = 0 ∨ f x + f (x + 1) = 1 ∧ f x * f (x + 1) = -1 := by
  have h4 x : f ((x ^ 2) ^ 2) = f x ^ 2 * (f x ^ 2 - 2) := by
    rw [case2_4_lem5 h h0 h1, case2_4_lem4 h h0 h1, ← one_pow 2,
      sq_sub_sq, one_pow, sub_add_cancel, sub_sub, one_add_one_eq_two]
  have h5 := case2_4_lem3 h h0
  have h6 := Char2.add_one_sq h0
  have h7 := h4 (x * (x + 1) + 1)
  rw [h5, h6, h6, mul_pow, h6, mul_pow, h6, h5, h4, ← h6, ← h6, h4,
    mul_mul_mul_comm, ← mul_pow, mul_eq_mul_left_iff, or_comm] at h7
  refine h7.imp sq_eq_zero_iff.mp λ h8 ↦ ?_
  rw [sub_mul, mul_sub, ← mul_pow, sub_sub, sub_right_inj, mul_comm, ← mul_add,
    mul_right_eq_self₀, or_iff_left h3, ← add_sub_assoc, sub_eq_iff_eq_add] at h8
  replace h7 := case2_4_lem6 h h0 h1 x
  rw [h8, add_right_eq_self, or_iff_right h3] at h7
  refine ⟨h7, ?_⟩
  apply congr_arg (· ^ 2) at h7
  rw [add_sq', h8, one_pow, add_assoc, add_right_eq_self, mul_assoc,
    ← mul_one_add (2 : S), mul_eq_zero, or_iff_right h3] at h7
  exact eq_neg_of_add_eq_zero_right h7

/-- Lemma 6 (TODO: Refactor the proof, if possible) -/
theorem case2_4_lem8 : ∀ c, f c = -1 → c = 0 := by
  ---- (10.L3.1)
  have A1 x (h6 : f x = -1) : f (x + 1) = 0 := by
    rcases case2_4_lem7 h h0 h1 h3 x with h7 | ⟨h7, h8⟩
    · rwa [h6, neg_one_mul, neg_eq_zero] at h7
    · rw [h6, neg_one_mul, neg_inj] at h8
      rw [h6, h8, neg_add_self] at h7
      rw [h8, h7]
  ---- (10.L3.2)
  have A2 c (h6 : f c = -1) x : f (c ^ 2 + c * x + 1) = -f (c * x + 1) := by
    rw [sq, ← mul_add, eq_add_of_sub_eq (h _ _), ← add_assoc,
      Char2.add_self h0, zero_add, eq_add_of_sub_eq (h _ _), h6,
      neg_one_mul, neg_one_mul, neg_add, neg_neg, add_comm]
  ---- Reduce to `c^4 = 0`
  intro c h4
  have X := case2_4_lem5 h h0 h1
  have h5 := X c
  rw [A1 c h4, sq (0 : S), zero_mul, zero_sub] at h5
  have h6 (d : R) (h7 : f d = -1) (h8 : d ^ 2 = 0) : d = 0 := h2 d <| by
    rw [mem_periodIdeal_iff, h1]
    refine ⟨λ x ↦ ?_, h7⟩
    have h9 := A2 d h7 x
    rwa [h8, zero_add, eq_neg_iff_add_eq_zero,
      ← two_mul, mul_eq_zero, or_iff_right h3] at h9
  refine h6 c h4 (h6 _ h5 ?_)
  ---- Prove that `c^6 + c^4 = 0`
  replace h6 : ((c ^ 2) ^ 2 + c ^ 2) * c ^ 2 = 0 := h2 _ <| by
    rw [mem_periodIdeal_iff, h1]
    have h7 := Char2.add_sq h0
    specialize A1 c h4
    have h8 : f (c ^ 2 + c + 1) = 0 := by
      rw [sq c, ← mul_add_one c, case2_4_lem3 h h0, A1, mul_zero]
    constructor
    · replace h6 x : f ((c ^ 2) ^ 2 + c ^ 2 + c ^ 2 * x + 1) = f (c ^ 2 * x + 1) :=
        by rw [add_assoc ((c ^ 2) ^ 2), ← mul_one_add (c ^ 2) x, A2 _ h5,
          mul_one_add (c ^ 2) x, sq, mul_assoc, ← sq, A2 _ h4, neg_neg]
      intro x
      rw [mul_assoc, mul_left_comm, ← h6, mul_left_comm,
        ← mul_one_add (α := R), eq_add_of_sub_eq (h _ _),
        add_comm (1 : R), ← add_assoc, h6, ← add_one_mul (α := S)]
      apply mul_eq_zero_of_left
      rw [← h7, X, sub_add_cancel, h8, sq, zero_mul]
    · rwa [← h7, ← mul_pow, X, sub_eq_neg_self, sq_eq_zero_iff,
        sq, ← add_one_mul c, mul_assoc, eq_add_of_sub_eq (h _ _),
        A1, zero_mul, zero_add, ← sq, ← add_rotate]
  ---- Final step
  apply h2
  rw [mem_periodIdeal_iff, h1, and_comm]
  have h7 := A1 (c ^ 2) h5
  constructor
  · rw [X, h7, sq, zero_mul, zero_sub]
  · intro x
    rw [sq, ← add_one_mul (α := R), mul_assoc, ← sq] at h6
    have h8 := h (c ^ 2 + 1) ((c ^ 2) ^ 2 * x + 1)
    rw [h7, zero_mul, sub_eq_zero, add_add_add_comm, Char2.add_self h0,
      add_zero, mul_add_one (α := R), ← mul_assoc, h6, zero_mul,
      zero_add, Char2.add_add_cancel h0, h5] at h8
    replace h6 : (c ^ 2) ^ 2 = c * (c * c ^ 2) := by rw [← mul_assoc, ← sq, ← sq]
    rw [h6, mul_assoc, ← neg_eq_zero, ← A2 c h4, ← mul_assoc, ← h6]
    exact A1 _ h8.symm

/-- Lemma 7 -/
theorem case2_4_lem9 (x : R) :
    (x ^ 2 = 0 ∨ x ^ 2 = 1) ∨ f x + f (x + 1) = 1 ∧ x * (x + 1) + 1 = 0 := by
  have h4 := case2_4_lem8 h h0 h1 h2 h3
  refine (case2_4_lem7 h h0 h1 h3 x).imp ?_ (λ h5 ↦ ?_)
  · rw [mul_eq_zero, or_comm]
    refine Or.imp (λ h5 ↦ h4 _ <| ?_) (λ h5 ↦ ?_)
    · rw [case2_4_lem5 h h0 h1, h5, sq, zero_mul, zero_sub]
    · rw [← Char2.add_eq_zero_iff_eq h0]
      apply h4; rw [case2_4_lem4 h h0 h1, h5, sq, zero_mul, zero_sub]
  · exact ⟨h5.1, h4 _ <| (case2_4_lem3 h h0 x).trans h5.2⟩

theorem case2_4_lem10 (h4 : ∀ x : R, x ^ 2 = 0 → x = 0) (x : R) :
    (x = 0 ∨ x = 1) ∨ f x + f (x + 1) = 1 ∧ x * (x + 1) + 1 = 0 :=
  (case2_4_lem9 h h0 h1 h2 h3 x).imp_left <| Or.imp (h4 x) λ h5 ↦ by
    rw [← Char2.add_eq_zero_iff_eq h0] at h5 ⊢
    exact h4 _ ((Char2.add_one_sq h0 x).trans h5)



/-- The main lemma for the `𝔽₂[X]/⟨X^2⟩` subcase -/
theorem case2_4_𝔽₂ε_main_lemma {c : R} (h4 : c ≠ 0) (h5 : c * c = 0) :
    ∀ x, (x = 0 ∨ x = c) ∨ x = 1 ∨ x = c + 1 := by
  refine cases_of_nonperiod_quasi_period h h2 h1 (λ x ↦ ?_) h4
  have h6 := case2_4_lem5 h h0 h1 (c * x)
  rwa [mul_pow, sq, h5, zero_mul, h1, eq_comm,
    sub_eq_neg_self, sq_eq_zero_iff] at h6

/-- Solution for the current sub-subcase (`𝔽₂εMap`) -/
theorem case2_4_𝔽₂ε_quot_IsAnswer {c : R} (h4 : c ≠ 0) (h5 : c * c = 0) :
    IsAnswer f :=
  -- `𝔽₂[X]/⟨X^2⟩ → R/I` induced by `X ↦ c` is bijective
  have X :Function.Bijective (𝔽₂ε.castHom h0 h5) :=
    ⟨𝔽₂ε.castHom_injective _ _ h4,
    λ x ↦ by rcases case2_4_𝔽₂ε_main_lemma h h0 h1 h2 h4 h5 x
               with (h5 | h5) | (h5 | h5)
             exacts [⟨𝔽₂ε.O, h5.symm⟩, ⟨𝔽₂ε.X, h5.symm⟩,
                     ⟨𝔽₂ε.I, h5.symm⟩, ⟨𝔽₂ε.Y, h5.symm⟩]⟩
  -- Factor `f` out as `𝔽₂εMap ∘ π`
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₂εMap S ∘ π
    from this.symm ▸ IsAnswer.𝔽₂ε_map_comp π.toRingHom π.surjective
  have h6 := good_map_one h
  (MulEquiv.eq_comp_symm _ _ _).mpr <| funext λ x ↦
    match x with
      | 𝔽₂ε.O => h1
      | 𝔽₂ε.I => h6
      | 𝔽₂ε.X => by
          have h7 := case2_4_lem4 h h0 h1 c
          rw [sq, h5, zero_add, h6, eq_comm, sub_eq_zero, sq_eq_one_iff] at h7
          exact h7.resolve_right <| mt (case2_4_lem8 h h0 h1 h2 h3 c) h4
      | 𝔽₂ε.Y => by
          have h7 := case2_4_lem5 h h0 h1 c
          rwa [sq, h5, h1, eq_comm, sub_eq_neg_self, sq_eq_zero_iff] at h7



/-- The main lemma for the `𝔽₄` subcase -/
theorem case2_4_𝔽₄_main_lemma
    (h4 : ∀ x : R, x ^ 2 = 0 → x = 0) (h5 : c * (c + 1) = 1) (x : R) :
    (x = 0 ∨ x = 1) ∨ x = c ∨ x = c + 1 := by
  have h7 := case2_4_lem10 h h0 h1 h2 h3 h4
  refine (h7 x).imp_right λ h8 ↦ (h7 (x + c)).elim ?_ ?_
  · exact Or.imp (Char2.add_eq_zero_iff_eq h0).mp (Char2.add_eq_iff_eq_add' h0).mp
  · rintro ⟨-, h9⟩
    rw [mul_add_one (x + c), ← sq, Char2.add_sq h0, add_add_add_comm, sq,
      sq, ← mul_add_one c, h5, ← mul_add_one x, h8.2, zero_add] at h9
    exact absurd h9 (one_ne_zero_of_map_zero h h1)

/-- Solution for the current sub-subcase (`𝔽₄Map`) -/
theorem case2_4_𝔽₄_quot_IsAnswer (h4 : ∀ x : R, x ^ 2 = 0 → x = 0)
    (h5 : f c + f (c + 1) = 1) (h6 : c * (c + 1) = 1) : IsAnswer f :=
  -- `𝔽₄ → R/I` is bijective
  have X :Function.Bijective (𝔽₄.castHom h0 h6) :=
    ⟨𝔽₄.castHom_injective _ _ (one_ne_zero_of_map_zero h h1),
    λ x ↦ by rcases case2_4_𝔽₄_main_lemma h h0 h1 h2 h3 h4 h6 x
               with (h7 | h7) | (h7 | h7)
             exacts [⟨𝔽₄.O, h7.symm⟩, ⟨𝔽₄.I, h7.symm⟩,
                     ⟨𝔽₄.X, h7.symm⟩, ⟨𝔽₄.Y, h7.symm⟩]⟩
  -- Factor `f` out as `𝔽₄Map ∘ π`
  let π := (RingEquiv.ofBijective _ X).symm
  have h7 := eq_sub_of_add_eq' h5
  suffices f = 𝔽₄Map S (f c) ∘ π
    from this.symm ▸ IsAnswer.𝔽₄_map_comp π.toRingHom π.surjective (f c) <|
      by rwa [← h7, ← case2_4_lem3 h h0, h6, Char2.add_self h0]
  (MulEquiv.eq_comp_symm _ _ _).mpr <| funext λ x ↦
    match x with
      | 𝔽₄.O => h1
      | 𝔽₄.I => good_map_one h
      | 𝔽₄.X => rfl
      | 𝔽₄.Y => h7



/-- The main lemma for the `𝔽₂` subcase -/
theorem case2_4_𝔽₂_main_lemma (h4 : ∀ x : R, x ^ 2 = 0 → x = 0)
    (h5 : ¬∃ c, f c + f (c + 1) = 1 ∧ c * (c + 1) = 1) (x : R) : x = 0 ∨ x = 1 :=
  (case2_4_lem10 h h0 h1 h2 h3 h4 x).resolve_right λ h6 ↦
    h5 ⟨x, h6.1, (Char2.add_eq_zero_iff_eq h0).mp h6.2⟩

/-- Solution for the current sub-subcase (`𝔽₂Map`) -/
theorem case2_4_𝔽₂_quot_IsAnswer (h4 : ∀ x : R, x ^ 2 = 0 → x = 0)
    (h5 : ¬∃ c, f c + f (c + 1) = 1 ∧ c * (c + 1) = 1) : IsAnswer f :=
  -- `𝔽₂ → R/I` is bijective
  have X :Function.Bijective (𝔽₂.castHom h0) :=
    ⟨𝔽₂.castHom_injective _ (one_ne_zero_of_map_zero h h1),
    λ x ↦ by rcases case2_4_𝔽₂_main_lemma h h0 h1 h2 h3 h4 h5 x with h5 | h5
             exacts [⟨𝔽₂.O, h5.symm⟩, ⟨𝔽₂.I, h5.symm⟩]⟩
  -- Factor `f` out as `𝔽₂Map ∘ π`
  let π := (RingEquiv.ofBijective _ X).symm
  suffices f = 𝔽₂Map S ∘ π
    from this.symm ▸ IsAnswer.𝔽₂_map_comp π.toRingHom π.surjective
  (MulEquiv.eq_comp_symm _ _ _).mpr <| funext λ x ↦
    match x with
      | 𝔽₂.O => h1
      | 𝔽₂.I => good_map_one h

end Rchar2



/-- Solution for the current subcase (4 classes) -/
theorem case2_4_quot_IsAnswer
    (h0 : f (-1) = 0) (h1 : f 2 = -1) (h2 : ∀ c ∈ periodIdeal h, c = 0) :
    IsAnswer f := by
  have h3 := h2 _ (case2_4_lem1 h h0 h1)
  have h4 : f 0 = -1 := h3 ▸ h1
  by_cases h5 : (2 : S) = 0
  · exact case2_4_Schar2_quot_IsAnswer h h3 h4 h5
  by_cases h6 : ∃ x : R, ¬(x ^ 2 = 0 → x = 0)
  · rcases h6 with ⟨c, h6⟩; rw [not_imp] at h6
    exact case2_4_𝔽₂ε_quot_IsAnswer h h3 h4 h2 h5 h6.2 ((sq c).symm.trans h6.1)
  rw [← not_forall, not_not] at h6
  rcases em (∃ c, f c + f (c + 1) = 1 ∧ c * (c + 1) = 1) with ⟨c, h7, h8⟩ | h7
  · exact case2_4_𝔽₄_quot_IsAnswer h h3 h4 h2 h5 h6 h7 h8
  · exact case2_4_𝔽₂_quot_IsAnswer h h3 h4 h2 h5 h6 h7
