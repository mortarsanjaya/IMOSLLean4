/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.FieldTheory.Finite.Basic

/-!
# IMO 2006 N5

Let $p > 3$ be a prime.
Determine all pairs $(x, y)$ of integers such that
$$ \sum_{k = 0}^{p - 1} x^k = y^{p - 2} - 1. $$
-/

namespace IMOSL
namespace IMO2006N5

open Finset

theorem FiniteField_prime_geom_sum_eq_zero_imp [Field F] [Fintype F] [DecidableEq F]
    (hp : Nat.Prime p) {x : F} (hx : x ≠ 1) (h : (range p).sum (x ^ ·) = 0) :
    p ∣ Fintype.card F - 1 := by
  rw [geom_sum_eq hx, div_eq_zero_iff, or_iff_left (sub_ne_zero_of_ne hx), sub_eq_zero] at h
  haveI : Fact p.Prime := ⟨hp⟩
  have h0 : x ≠ 0 := λ h0 ↦ absurd h (by rw [h0, zero_pow hp.ne_zero]; exact zero_ne_one' F)
  let xᵤ : Fˣ := ⟨x, x⁻¹, mul_inv_cancel₀ h0, inv_mul_cancel₀ h0⟩
  have h1 : orderOf xᵤ = p := orderOf_eq_prime (Units.val_inj.mp h) (mt Units.val_inj.mpr hx)
  rw [← h1, ← Fintype.card_units]; exact orderOf_dvd_card

theorem ZMod_prime_geom_sum_eq_zero_imp [Fact (Nat.Prime q)]
    (hp : Nat.Prime p) {x : ZMod q} (h : (range p).sum (x ^ ·) = 0) :
    p = q ∨ p ∣ q - 1 := by
  refine (eq_or_ne x 1).imp (λ h0 ↦ ?_)
    (λ h0 ↦ ZMod.card q ▸ FiniteField_prime_geom_sum_eq_zero_imp hp h0 h)
  simp only [h0, one_pow] at h
  rwa [sum_const, card_range, nsmul_one, CharP.cast_eq_zero_iff _ q,
    Nat.prime_dvd_prime_iff_eq Fact.out hp, eq_comm] at h

theorem prime_dvd_prime_geom_sum_imp (hq : Nat.Prime q)
    (hp : Nat.Prime p) {x : ℤ} (h : (q : ℤ) ∣ (range p).sum (x ^ ·)) :
    p = q ∨ p ∣ q - 1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  rw [← CharP.intCast_eq_zero_iff (ZMod q) q, Int.cast_sum] at h
  simp only [Int.cast_pow] at h
  exact ZMod_prime_geom_sum_eq_zero_imp hp h

theorem Nat_dvd_prime_geom_sum_imp (hp : Nat.Prime p) :
    ∀ d : ℕ, (∃ x : ℤ, (d : ℤ) ∣ (range p).sum (x ^ ·)) → p ∣ d ∨ p ∣ d - 1 := by
  refine Nat.recOnMul (λ _ ↦ Or.inl p.dvd_zero) (λ _ ↦ Or.inr p.dvd_zero) ?_ ?_
  · rintro q hq ⟨x, h⟩
    refine (prime_dvd_prime_geom_sum_imp hq hp h).imp_left λ h0 ↦ ?_
    subst h0; exact p.dvd_refl
  · rintro a b ha hb ⟨x, h⟩
    rw [Nat.cast_mul] at h
    specialize ha ⟨x, dvd_of_mul_right_dvd h⟩
    specialize hb ⟨x, dvd_of_mul_left_dvd h⟩
    rw [hp.dvd_mul, or_assoc]
    revert ha; refine Or.imp_right λ ha ↦ ?_
    revert hb; refine Or.imp_right λ hb ↦ ?_
    rcases a with _ | a
    · rwa [b.zero_mul]
    rcases b with _ | b
    · rwa [Nat.mul_zero]
    rw [Nat.add_sub_cancel] at ha hb
    rw [a.succ_mul, ← Nat.add_assoc, Nat.add_sub_cancel]
    exact dvd_add (dvd_mul_of_dvd_left ha _) hb

theorem Int_dvd_prime_geom_sum_imp (hp : Nat.Prime p)
    {d : ℤ} (h : 0 < d) (h0 : ∃ x, d ∣ (range p).sum (x ^ ·)) :
    (p : ℤ) ∣ d ∨ (p : ℤ) ∣ d - 1 := by
  replace h0 : p ∣ d.natAbs ∨ p ∣ d.natAbs - 1 := by
    rcases h0 with ⟨x, h0⟩
    apply Nat_dvd_prime_geom_sum_imp hp _ ⟨x, ?_⟩
    rwa [Int.natCast_natAbs, abs_dvd]
  revert h0; refine Or.imp Int.ofNat_dvd_left.mpr (λ h0 ↦ ?_)
  rwa [← d.sub_add_cancel 1, Int.natAbs_add_of_nonneg (Int.le_sub_one_of_lt h) Int.one_nonneg,
    Int.natAbs_one, Nat.add_sub_cancel, ← Int.natCast_dvd] at h0





/-- Final solution -/
theorem final_solution {p : ℕ} (hp : p.Prime) (h : 3 < p) (x y : ℤ) :
    ¬(range p).sum (x ^ ·) = y ^ (p - 2) - 1 := by
  intro h0
  have h1 : Odd p := hp.eq_two_or_odd'.resolve_left (Nat.lt_of_succ_lt h).ne.symm
  have h2 : 0 < (range (p - 2)).sum (y ^ ·) :=
    (Nat.Odd.sub_even hp.two_le h1 even_two).geom_sum_pos
  replace h1 : 0 < y - 1 := by
    have h3 : 0 < (range p).sum (x ^ ·) := h1.geom_sum_pos
    rwa [h0, ← geom_sum_mul, mul_pos_iff_of_pos_left h2] at h3
  replace h0 {d : ℤ} (hd : 0 < d) (hd0 : d ∣ y ^ (p - 2) - 1) :
      (p : ℤ) ∣ d ∨ (p : ℤ) ∣ d - 1 :=
    Int_dvd_prime_geom_sum_imp hp hd ⟨x, h0 ▸ hd0⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have X : 0 < p - 2 := Nat.sub_pos_of_lt (Nat.lt_of_succ_lt h)
  obtain h3 | h3 : (p : ℤ) ∣ y - 1 ∨ (p : ℤ) ∣ (y - 1) - 1 :=
    h0 h1 (sub_one_dvd_pow_sub_one y (p - 2))
  ---- Case 1: `y ≡ 1 (mod p)`
  · rw [← CharP.intCast_eq_zero_iff (ZMod p), Int.cast_sub, sub_eq_zero, Int.cast_one] at h3
    specialize h0 h2 ⟨y - 1, (geom_sum_mul y _).symm⟩
    rw [← CharP.intCast_eq_zero_iff (ZMod p), ← CharP.intCast_eq_zero_iff (ZMod p),
      Int.cast_sub, Int.cast_one, Int.cast_sum, sub_eq_zero] at h0
    simp only [Int.cast_pow, h3, one_pow] at h0
    rw [sum_const, card_range, nsmul_one] at h0
    clear! x y; rcases h0 with h0 | h0
    · rw [CharP.cast_eq_zero_iff _ p] at h0
      exact (Nat.sub_lt hp.pos Nat.two_pos).not_ge (Nat.le_of_dvd X h0)
    · rw [← Nat.sub_add_cancel X, Nat.cast_add, Nat.sub_sub,
        Nat.cast_one, add_eq_right, CharP.cast_eq_zero_iff _ p] at h0
      exact (Nat.sub_lt hp.pos (Nat.succ_pos 2)).not_ge
        (Nat.le_of_dvd (Nat.sub_pos_of_lt h) h0)
  ---- Case 2: `y ≡ 2 (mod p)`
  · rw [sub_sub, ← CharP.intCast_eq_zero_iff (ZMod p), Int.cast_sub,
      sub_eq_zero, one_add_one_eq_two, Int.cast_two] at h3
    replace h2 : 0 < y ^ (p - 2) - 1 :=
      sub_pos_of_lt (one_lt_pow₀ (lt_of_sub_pos h1) X.ne.symm)
    specialize h0 h2 (dvd_refl _)
    rw [← CharP.intCast_eq_zero_iff (ZMod p), ← CharP.intCast_eq_zero_iff (ZMod p),
      Int.cast_sub, Int.cast_sub, Int.cast_sub, Int.cast_one, Int.cast_pow, h3,
      sub_eq_zero, sub_sub, sub_eq_zero, one_add_one_eq_two] at h0
    replace X : (2 : ZMod p) * 2 ^ (p - 2) = 1 := by
      rw [← pow_succ', ← p.sub_sub 1 1, Nat.sub_add_cancel (Nat.sub_pos_of_lt hp.one_lt)]
      refine ZMod.pow_card_sub_one_eq_one (?_ : ((2 : ℕ) : ZMod p) ≠ 0)
      rw [Ne, CharP.cast_eq_zero_iff _ p, Nat.prime_dvd_prime_iff_eq hp Nat.prime_two]
      rintro rfl; exact h.not_gt (Nat.lt_succ_self 2)
    clear! x y; rcases h0 with h0 | h0
    · rw [h0, mul_one, ← one_add_one_eq_two, add_eq_left] at X
      exact one_ne_zero X
    · rw [h0, mul_two, ← one_add_one_eq_two, ← add_assoc, add_eq_right, ← Nat.cast_one,
        ← Nat.cast_add, ← Nat.cast_add, CharP.cast_eq_zero_iff _ p] at X
      exact h.not_ge (Nat.le_of_dvd (Nat.succ_pos 2) X)
