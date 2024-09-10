/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-!
# IMO 2007 C3

Find all finite groups $G$ such that there exists a subset $S ⊆ G$ for which
  the number of triples $(x, y, z) ∈ S^3 ∪ (G \ S)^3$ such that $xyz = 1$ is $2007$.
-/

namespace IMOSL
namespace IMO2007C3

/-! ### `Fin 3` lemmas -/

theorem Fin3_add_comm (i j : Fin 3) : i + j = j + i :=
  match i, j with
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 0, 2 => rfl
  | 1, 0 => rfl
  | 1, 1 => rfl
  | 1, 2 => rfl
  | 2, 0 => rfl
  | 2, 1 => rfl
  | 2, 2 => rfl

theorem Fin3_add_zero (i : Fin 3) : i + 0 = i :=
  match i with | 0 => rfl | 1 => rfl | 2 => rfl

theorem Fin3_sub_self (i : Fin 3) : i - i = 0 :=
  match i with | 0 => rfl | 1 => rfl | 2 => rfl

theorem Fin3_add_sub_cancel (i j : Fin 3) : (i + j) - i = j :=
  match i, j with
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 0, 2 => rfl
  | 1, 0 => rfl
  | 1, 1 => rfl
  | 1, 2 => rfl
  | 2, 0 => rfl
  | 2, 1 => rfl
  | 2, 2 => rfl

theorem Fin3_add_sub_cancel' (i j : Fin 3) : i + (j - i) = j :=
  match i, j with
  | 0, 0 => rfl
  | 0, 1 => rfl
  | 0, 2 => rfl
  | 1, 0 => rfl
  | 1, 1 => rfl
  | 1, 2 => rfl
  | 2, 0 => rfl
  | 2, 1 => rfl
  | 2, 2 => rfl





/-! ### Start of the problem -/

open Finset

section

variable [Fintype G] [DecidableEq G]

def tripleSet (S : Finset G) : Finset (Fin 3 → G) :=
  (Fintype.piFinset λ _ ↦ S) ∪ (Fintype.piFinset λ _ ↦ Sᶜ)

lemma mem_tripleSet {S : Finset G} : p ∈ tripleSet S ↔ (∀ i, p i ∈ S) ∨ (∀ i, p i ∉ S) := by
  simp only [tripleSet, mem_union, Fintype.mem_piFinset, mem_compl]

lemma mem_tripleSet' {S : Finset G} : p ∈ tripleSet S ↔ ¬∃ i, p i ∈ S ∧ p (i + 1) ∉ S := by
  refine mem_tripleSet.trans ⟨λ h h0 ↦ ?_, λ h ↦ ?_⟩
  · rcases h0 with ⟨i, hi, hi0⟩
    rcases h with h | h
    exacts [hi0 (h _), h _ hi]
  · replace h {i} (hi : p i ∈ S) : p (i + 1) ∈ S :=
      (em (p (i + 1) ∈ S)).resolve_right λ h1 ↦ h ⟨i, hi, h1⟩
    apply (em (p 0 ∈ S)).imp (λ h0 ↦ ?_) (λ h0 ↦ ?_)
    · have h1 : p 1 ∈ S := h h0
      intro i; match i with | 0 => exact h0 | 1 => exact h1 | 2 => exact h h1
    · replace h {i} (hi : p (i + 1) ∉ S) : p i ∉ S := λ h1 ↦ hi (h h1)
      have h1 : p 2 ∉ S := h h0
      intro i; match i with | 0 => exact h0 | 1 => exact h h1 | 2 => exact h1

def filtered_tripleSet [Group G] (S : Finset G) : Finset (Fin 3 → G) :=
  (tripleSet S).filter λ p ↦ p 0 * p 1 * p 2 = 1

end





/-! ### Cardinality of filtered `tripleSet` -/

section

variable [Group G]

def toSumCompl (p : Fin 3 × G × G) : Fin 3 → G :=
  λ k ↦ ![p.2.1, p.2.2, (p.2.1 * p.2.2)⁻¹] (k - p.1)

lemma toSumCompl_self (p : G × G) (k) : toSumCompl (k, p) k = p.1 := by
  rw [toSumCompl, Fin3_sub_self]; rfl

lemma toSumCompl_self_add_one (p : G × G) (k) : toSumCompl (k, p) (k + 1) = p.2 := by
  rw [toSumCompl, Fin3_add_sub_cancel]; rfl

lemma toSumCompl_self_add_two (p : G × G) (k) :
    toSumCompl (k, p) (k + 2) = (p.1 * p.2)⁻¹ := by
  rw [toSumCompl, Fin3_add_sub_cancel]; rfl

lemma toSumCompl_prod (p : G × G) (k) :
    toSumCompl (k, p) 0 * toSumCompl (k, p) 1 * toSumCompl (k, p) 2 = 1 :=
  match k with
  | 0 => mul_inv_cancel (p.1 * p.2)
  | 1 => mul_assoc _ p.1 p.2 ▸ inv_mul_cancel (p.1 * p.2)
  | 2 => by
      show p.2 * (p.1 * p.2)⁻¹ * p.1 = 1
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel_right, mul_inv_cancel]

end


section

variable [Fintype G] [DecidableEq G] [Group G]

lemma toSumCompl_injOn (S : Finset G) :
    ((univ ×ˢ S ×ˢ Sᶜ : Finset (Fin 3 × G × G)) : Set (Fin 3 × G × G)).InjOn toSumCompl := by
  rintro ⟨i, x, y⟩ h ⟨j, z, w⟩ h0 h1
  rw [mem_coe, mem_product, mem_product, mem_compl] at h h0
  rcases h with ⟨-, hx : x ∈ S, hy : y ∉ S⟩
  rcases h0 with ⟨-, hz : z ∈ S, hw : w ∉ S⟩
  obtain rfl : i = j := by
    revert h1; rw [← Fin3_add_sub_cancel' i j]
    match j - i with
    | 0 => exact λ _ ↦ (Fin3_add_zero i).symm
    | 1 =>
        intro h; obtain rfl : y = z := calc
          _ = toSumCompl (i, x, y) (i + 1) := (toSumCompl_self_add_one _ _).symm
          _ = toSumCompl (i + 1, z, w) (i + 1) := congrFun h _
          _ = _ := toSumCompl_self _ _
        exact absurd hz hy
    | 2 =>
        intro h; obtain rfl : x = w := calc
          _ = toSumCompl (i, x, y) i := (toSumCompl_self _ _).symm
          _ = toSumCompl (i + 2, z, w) i := congrFun h i
          _ = _ := match i with | 0 => rfl | 1 => rfl | 2 => rfl
        exact absurd hx hw
  rw [Prod.mk.injEq, Prod.mk.injEq]
  replace h1 (j : Fin 3) : ![x, y, (x * y)⁻¹] j = ![z, w, (z * w)⁻¹] j :=
    Fin3_add_sub_cancel i j ▸ congrFun h1 _
  exact ⟨rfl, h1 0, h1 1⟩

lemma mem_toSumCompl_image_iff {S : Finset G} :
    p ∈ (univ ×ˢ S ×ˢ Sᶜ).image toSumCompl ↔ p ∉ tripleSet S ∧ p 0 * p 1 * p 2 = 1 := by
  simp only [mem_image, mem_product, mem_compl, mem_tripleSet', not_not]
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · rcases h with ⟨⟨i, x, y⟩, ⟨-, hx : x ∈ S, hy : y ∉ S⟩, rfl⟩
    refine ⟨⟨i, ?_, ?_⟩, toSumCompl_prod _ _⟩
    exacts [(toSumCompl_self (x, y) i).symm ▸ hx,
      (toSumCompl_self_add_one (x, y) i).symm ▸ hy]
  · rcases h with ⟨⟨i, hi, hi0⟩, h⟩
    refine ⟨⟨i, p i, p (i + 1)⟩, ⟨mem_univ _, hi, hi0⟩, funext λ j ↦ ?_⟩
    rw [← Fin3_add_sub_cancel' i j]; match j - i with
      | 0 => rw [Fin3_add_zero, toSumCompl_self]
      | 1 => exact toSumCompl_self_add_one _ _
      | 2 => ?_
    replace h : p i * p (i + 1) * p (i + 2) = 1 := match i with
      | 0 => h
      | 1 => by rwa [← eq_inv_iff_mul_eq_one, eq_comm, inv_eq_iff_mul_eq_one, ← mul_assoc]
      | 2 => by rwa [mul_assoc, ← inv_eq_iff_mul_eq_one, eq_comm, eq_inv_iff_mul_eq_one]
    rw [toSumCompl_self_add_two, inv_eq_of_mul_eq_one_right h]

lemma toSumCompl_image_disjoint_tripleSet (S : Finset G) :
    Disjoint ((univ ×ˢ S ×ˢ Sᶜ).image toSumCompl) (tripleSet S) :=
  disjoint_left.mpr λ _ h ↦ (mem_toSumCompl_image_iff.mp h).1

lemma toSumCompl_image_disjoint_filtered_tripleSet (S : Finset G) :
    Disjoint ((univ ×ˢ S ×ˢ Sᶜ).image toSumCompl) (filtered_tripleSet S) :=
  disjoint_of_subset_right (filter_subset _ _) (toSumCompl_image_disjoint_tripleSet S)

lemma toSumCompl_image_union_tripleSet (S : Finset G) :
    disjUnion ((univ ×ˢ S ×ˢ Sᶜ).image toSumCompl) (filtered_tripleSet S)
        (toSumCompl_image_disjoint_filtered_tripleSet S)
      = univ.filter λ p ↦ p 0 * p 1 * p 2 = 1 := by
  ext p; rw [mem_disjUnion, mem_toSumCompl_image_iff, filtered_tripleSet, mem_filter,
    ← or_and_right, mem_filter, and_iff_right (dec_em' _), and_iff_right (mem_univ _)]

lemma filter_mul_eq_one_eq_image :
    (univ : Finset (Fin 3 → G)).filter (λ p ↦ p 0 * p 1 * p 2 = 1)
      = (univ : Finset (G × G)).image (λ (x, y) ↦ ![x, y, (x * y)⁻¹]) := by
  ext p; simp only [mem_filter, mem_image, mem_univ, true_and]
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · refine ⟨⟨p 0, p 1⟩, funext λ i ↦ ?_⟩
    match i with | 0 => rfl | 1 => rfl | 2 => exact inv_eq_of_mul_eq_one_right h
  · rcases h with ⟨p, rfl⟩
    exact mul_inv_cancel _

theorem filtered_tripleSet_card_formula (S : Finset G) :
    3 * S.card * Sᶜ.card + (filtered_tripleSet S).card = Fintype.card G ^ 2 := calc
  _ = ((univ ×ˢ S ×ˢ Sᶜ).image toSumCompl).card + (filtered_tripleSet S).card := by
    rw [card_image_of_injOn (toSumCompl_injOn S), card_product,
      card_product, card_univ, Fintype.card_fin, Nat.mul_assoc]
  _ = (disjUnion ((univ ×ˢ S ×ˢ Sᶜ).image toSumCompl) (filtered_tripleSet S)
      (toSumCompl_image_disjoint_filtered_tripleSet S)).card :=
    (card_disjUnion _ _ _).symm
  _ = ((univ : Finset (G × G)).image λ (x, y) ↦ ![x, y, (x * y)⁻¹]).card := by
    rw [toSumCompl_image_union_tripleSet, filter_mul_eq_one_eq_image]
  _ = (univ : Finset (G × G)).card := by
    exact card_image_of_injective _ λ p q h ↦ Prod.ext (congrFun h 0) (congrFun h 1)
  _ = _ := by rw [card_univ, Fintype.card_prod, sq]

end





/-! ### The main problem -/

theorem exists_filtered_tripleSet_card_eq_iff' [Fintype G] [DecidableEq G] [Group G] {N} :
    (∃ S : Finset G, (filtered_tripleSet S).card = N)
      ↔ ∃ a b, a + b = Fintype.card G ∧ 3 * a * b + N = Fintype.card G ^ 2 := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · rcases h with ⟨S, rfl⟩
    exact ⟨S.card, Sᶜ.card, S.card_add_card_compl, filtered_tripleSet_card_formula S⟩
  · rcases h with ⟨a, b, h, h0⟩
    obtain ⟨S, -, rfl⟩ : ∃ S ⊆ univ, S.card = a :=
      exists_subset_card_eq (Nat.le_of_add_right_le h.le)
    rw [← S.card_add_card_compl, Nat.add_right_inj] at h
    subst b; rw [← filtered_tripleSet_card_formula S, Nat.add_right_inj] at h0
    exact ⟨S, h0.symm⟩

theorem formula1 {b c N : ℕ} :
    3 * (b + c) * b + N = (b + c + b) ^ 2 ↔ b ^ 2 + c ^ 2 + b * c = N :=
  suffices (b + c + b) ^ 2 = 3 * (b + c) * b + (b ^ 2 + c ^ 2 + b * c)
    by rw [this, Nat.add_right_inj, eq_comm]
  calc
    _ = (b + c) * (b + c) + (b + c) * b + (b * (b + c) + b ^ 2) := by
      rw [sq, sq, ← Nat.mul_add, ← Nat.mul_add, Nat.add_mul]
    _ = (b + c) * b + (b + c) * c + ((b + c) * b + (b * (b + c) + b ^ 2)) := by
      rw [Nat.add_assoc, ← Nat.mul_add]
    _ = (b + c) * b + (b + c) * c + (2 * ((b + c) * b) + b ^ 2) := by
      rw [Nat.add_right_inj, ← Nat.add_assoc, Nat.mul_comm, Nat.two_mul]
    _ = (b + c) * b + 2 * (b + c) * b + ((b + c) * c + b ^ 2) := by
      rw [Nat.add_add_add_comm, ← Nat.mul_assoc]
    _ = 3 * (b + c) * b + (b * c + c ^ 2 + b ^ 2) := by
      rw [← Nat.add_mul, (b + c).add_comm, ← Nat.succ_mul, Nat.add_mul, ← sq]
    _ = _ := by rw [Nat.add_right_inj, Nat.add_right_comm, add_rotate]

theorem formula2 {n N : ℕ} :
    (∃ a b, a + b = n ∧ 3 * a * b + N = n ^ 2)
      ↔ (∃ b c, 2 * b + c = n ∧ b ^ 2 + c ^ 2 + b * c = N) := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · rcases h with ⟨a, b, rfl, h⟩
    wlog h0 : b ≤ a generalizing a b
    · rw [Nat.mul_right_comm, a.add_comm] at h
      exact a.add_comm b ▸ this b a h (Nat.le_of_not_ge h0)
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h0
    refine ⟨b, c, ?_, formula1.mp h⟩
    rw [Nat.add_right_comm, Nat.two_mul]
  · rcases h with ⟨b, c, rfl, rfl⟩
    rw [Nat.two_mul, Nat.add_right_comm]
    exact ⟨b + c, b, rfl, formula1.mpr rfl⟩

theorem formula3 (b c) : 3 * c ^ 2 + (2 * b + c) ^ 2 = 4 * (b ^ 2 + c ^ 2 + b * c) := calc
  _ = 3 * c ^ 2 + ((2 * b + c) * (2 * b) + 2 * b * c + c * c) := by
    rw [Nat.add_right_inj, sq, Nat.mul_add, Nat.add_assoc, ← Nat.add_mul]
  _ = (2 * b) * (2 * b + c + c) + 4 * c ^ 2 := by
    rw [Nat.add_left_comm, Nat.mul_comm, ← Nat.mul_add, ← sq, ← Nat.succ_mul]
  _ = 4 * (b * (b + c) + c ^ 2) := by
    rw [Nat.add_assoc, ← Nat.two_mul, ← Nat.mul_add, Nat.mul_mul_mul_comm, ← Nat.mul_add]
  _ = _ := by rw [b.mul_add, ← sq, Nat.add_right_comm]

theorem formula4 (h : ∃ b c, 2 * b + c = n ∧ b ^ 2 + c ^ 2 + b * c = N) :
    ∃ c ≤ n, 4 * N = 3 * c ^ 2 + n ^ 2 := by
  rcases h with ⟨b, c, rfl, rfl⟩
  refine ⟨c, Nat.le_add_left _ _, (formula3 b c).symm⟩

theorem three_dvd_sq_imp (hn : 3 ∣ n ^ 2) : 3 ∣ n := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.pow_mod] at hn
  obtain (h0 | h0) | h0 : (n % 3 = 0 ∨ n % 3 = 1) ∨ n % 3 = 2 := by
    rw [← Nat.le_one_iff_eq_zero_or_eq_one, ← Nat.le_succ_iff, ← Nat.lt_succ_iff]
    exact n.mod_lt (Nat.succ_pos 2)
  · exact Nat.dvd_of_mod_eq_zero h0
  · rw [h0] at hn; exact absurd hn Nat.one_ne_zero
  · rw [h0] at hn; exact absurd hn Nat.one_ne_zero

theorem formula5 (h : ∃ c ≤ n, 4 * 2007 = 3 * c ^ 2 + n ^ 2) : n = 69 ∨ n = 84 := by
  have X : 0 < 3 := Nat.succ_pos 2
  ---- For the converse, first show that `3 ∣ n` and write `n = 3k`
  rcases h with ⟨c, hc, h⟩
  obtain ⟨k, rfl⟩ : 3 ∣ n := by
    replace h : 0 = _ % 3 := congrArg (· % 3) h
    rw [Nat.mul_add_mod, eq_comm, ← Nat.dvd_iff_mod_eq_zero] at h
    exact three_dvd_sq_imp h
  ---- Now the main equation reduces to `2676 = c^2 + 3k^2`
  replace h : 2676 = c ^ 2 + 3 * k ^ 2 := by
    rw [Nat.mul_pow, Nat.mul_assoc 3 3, ← Nat.mul_add] at h
    exact Nat.eq_of_mul_eq_mul_left X h
  ---- Now prove that `3 ∣ c` and write `c = 3d`
  obtain ⟨d, rfl⟩ : 3 ∣ c := by
    replace h : 0 = _ % 3 := congrArg (· % 3) h
    rw [Nat.add_comm, Nat.mul_add_mod, eq_comm, ← Nat.dvd_iff_mod_eq_zero] at h
    exact three_dvd_sq_imp h
  ---- The main equation reduces to `892 = 3d^2 + k^2`
  replace h : 892 = 3 * d ^ 2 + k ^ 2 := by
    rw [Nat.mul_pow, Nat.mul_assoc 3 3, ← Nat.mul_add] at h
    exact Nat.eq_of_mul_eq_mul_left X h
  ---- Now notice `k < 30` and `d < 18`, and bash out one-by-one
  ---- (Note: This could be done much faster, I think, but...)
  replace h0 : k < 30 := Nat.lt_of_not_le λ h0 ↦ h.not_lt <| calc
    892 < 30 ^ 2 := by decide
    _ ≤ k ^ 2 := Nat.pow_le_pow_left h0 2
    _ ≤ 3 * d ^ 2 + k ^ 2 := Nat.le_add_left _ _
  replace hc : d ≤ min k 17 := by
    refine Nat.le_min.mpr ⟨Nat.le_of_mul_le_mul_left hc X, Nat.le_of_not_lt λ h1 ↦ ?_⟩
    apply h.not_lt; calc
      892 < 3 * 18 ^ 2 := by decide
      _ ≤ 3 * d ^ 2 := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left h1 2)
      _ ≤ 3 * d ^ 2 + k ^ 2 := Nat.le_add_right _ _
  revert h; revert d; revert k
  decide

/-- Final solution -/
theorem final_solution [Fintype G] [DecidableEq G] [Group G] :
    (∃ S : Finset G, (filtered_tripleSet S).card = 2007)
      ↔ Fintype.card G = 69 ∨ Fintype.card G = 84 := by
  rw [exists_filtered_tripleSet_card_eq_iff', formula2]
  refine ⟨λ h ↦ formula5 (formula4 h), λ h ↦ ?_⟩
  generalize Fintype.card G = N at h ⊢
  rcases h with rfl | rfl
  exacts [⟨18, 33, rfl, rfl⟩, ⟨33, 18, rfl, rfl⟩]
