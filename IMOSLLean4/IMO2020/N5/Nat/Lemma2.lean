/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.Nat.Basic
import Mathlib.Data.Nat.Prime

/-!
# IMO 2020 N5 (Some Lemmas)

This file proves the following crucial result.
* Let `f : MulMap M` and `p : ℕ` be an `f`-nice prime.
  Then `f(km % p) = f(k) f(m)` for any `0 < k, m < p`.
We also prove some variants of the lemma.
They will be useful for the construction of the solutions.
We also prove some other useful lemmas.
-/

namespace IMOSL
namespace IMO2020N5

/-! #### Extra lemmas -/

lemma mod_add_mod_eq_of_dvd_of_mod_pos {n a b : ℕ}
    (h : n ∣ a + b) (h0 : 0 < a % n) : a % n + b % n = n := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, ← Nat.dvd_iff_mod_eq_zero] at h
  rcases h with ⟨k, h⟩
  suffices k = 1 by rw [h, this, mul_one]
  have h1 := (Nat.add_pos_left h0 _).trans_eq h
  refine Nat.le_antisymm (Nat.le_of_lt_succ ?_)
    (Nat.pos_of_dvd_of_pos (k.dvd_mul_left n) h1)
  replace h1 := Nat.pos_of_dvd_of_pos (n.dvd_mul_right k) h1
  replace h0 := Nat.add_lt_add (a.mod_lt h1) (b.mod_lt h1)
  rwa [h, ← mul_two, mul_lt_mul_left h1] at h0

lemma not_dvd_mul_of_pos_of_lt_prime (h : Nat.Prime p)
    (ha : 0 < a) (hap : a < p) (hb : 0 < b) (hbp : b < p) : ¬p ∣ a * b :=
  h.not_dvd_mul (Nat.not_dvd_of_pos_of_lt ha hap)
    (Nat.not_dvd_of_pos_of_lt hb hbp)

private lemma mul_mod_of_lt_equiv_not_dvd
    (f : ℕ → α) (op : α → α → α) (h : Nat.Prime p) :
    (∀ k m, 0 < k → k < p → 0 < m → m < p → f (k * m % p) = op (f k) (f m))
      ↔ (∀ k m, ¬p ∣ k → ¬p ∣ m → f (k * m % p) = op (f (k % p)) (f (m % p))) :=
  ⟨λ h0 k m hk hm ↦ (k.mul_mod m p).symm ▸ h0 _ _
    (Nat.emod_pos_of_not_dvd hk) (k.mod_lt h.pos)
    (Nat.emod_pos_of_not_dvd hm) (m.mod_lt h.pos),
  λ h0 k m hk hkp hm hmp ↦
    (h0 _ _ (Nat.not_dvd_of_pos_of_lt hk hkp)
      (Nat.not_dvd_of_pos_of_lt hm hmp)).trans
    (by rw [k.mod_eq_of_lt hkp, m.mod_eq_of_lt hmp])⟩

private lemma mul_mod_of_not_dvd_equiv_coprime
    (f : ℕ → α) (op : α → α → α) (h : Nat.Prime p) :
    (∀ k m, ¬p ∣ k → ¬p ∣ m → f (k * m % p) = op (f (k % p)) (f (m % p)))
      ↔ (∀ k m, p.Coprime k → p.Coprime m →
          f (k * m % p) = op (f (k % p)) (f (m % p))) :=
  forall_congr' λ k ↦ forall_congr' λ m ↦ by simp_rw [h.coprime_iff_not_dvd]





/-! #### Main results -/

variable [CancelMonoid M] {f : MulMap M} (h : Nat.Prime p)


section

variable (h0 : nice f p)

theorem nice_prime_map_pred : f (p - 1) = 1 :=
  f.map_one ▸ h0 _ _ h.pred_pos Nat.one_pos (Nat.sub_add_cancel h.pos)

theorem nice_prime_mul_mod_of_lt (k₀ m₀) (hk₀ : 0 < k₀) (hk₀p : k₀ < p) :
    (hm₀ : 0 < m₀) → (hm₀p : m₀ < p) → f (k₀ * m₀ % p) = f k₀ * f m₀ := by
  ---- Induction setup
  revert m₀; induction' k₀ using Nat.strong_induction_on with k₀ ih_k₀; intro m₀
  induction' m₀ using Nat.strong_induction_on with m₀ ih_m₀; intro hm₀ hm₀p
  ---- The case `k₀m₀ < p` is easy to pick
  rcases lt_or_le (k₀ * m₀) p with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]; exact f.map_mul hk₀ hm₀
  ---- Specialize `ih_m₀` for `m := p % m₀`
  have X := p.mod_lt hm₀
  have not_m_dvd_p := (Nat.prime_def_lt'.mp h).2 m₀
    (one_lt_of_lt_mul_right <| hk₀p.trans_le h1) hm₀p
  have X0 := Nat.emod_pos_of_not_dvd not_m_dvd_p
  specialize ih_m₀ (p % m₀) X X0 (X.trans hm₀p)
  ---- Specialize `ih_k₀` for `m := p / m₀` and `m_1 := k₀ * m₀ % p`
  replace X {n : ℕ} (hn : 0 < n) (hnp : n < p) : ¬p ∣ k₀ * n :=
    not_dvd_mul_of_pos_of_lt_prime h hk₀ hk₀p hn hnp
  replace h1 := h1.lt_of_ne (mt dvd_of_eq <| X hm₀ hm₀p)
  have X1 := Nat.div_lt_of_lt_mul (h1.trans_eq <| k₀.mul_comm _)
  have X2 := (Nat.div_pos_iff hm₀.ne.symm).mpr hm₀p.le
  replace X {n : ℕ} (hn : 0 < n) (hnp : n < p) : 0 < k₀ * n % p :=
    Nat.emod_pos_of_not_dvd (X hn hnp)
  specialize ih_k₀ (p / m₀) X1 X2 (X1.trans hk₀p)
    _ (X hm₀ hm₀p) (Nat.mod_lt _ h.pos)
  ---- Finishing
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_rotate'] at ih_k₀
  replace X1 := Nat.div_add_mod p m₀
  have X3 := Nat.mul_pos hm₀ X2
  rw [← h0 _ _ X3 X0 X1, ← f.map_mul hk₀ X3, ← mul_rotate',
    f.map_mul X2 (Nat.mul_pos hk₀ hm₀), f.map_mul hk₀ hm₀] at ih_m₀
  rw [← mul_right_inj (f (p / m₀)), ← ih_k₀, ← ih_m₀]
  have X4 := X (Nat.mul_pos hm₀ X2) (Nat.mul_div_lt_iff_not_dvd.mpr not_m_dvd_p)
  refine h0 (k₀ * _ % p) (k₀ * _ % p) X4 (X X0 <| (p.mod_lt hm₀).trans hm₀p)
    (mod_add_mod_eq_of_dvd_of_mod_pos ⟨k₀, ?_⟩ X4)
  rw [← mul_add, X1, mul_comm]

theorem nice_prime_mul_mod_of_not_dvd :
    ∀ k m, (hk : ¬p ∣ k) → (hm : ¬p ∣ m) →
      f (k * m % p) = f (k % p) * f (m % p) :=
  (mul_mod_of_lt_equiv_not_dvd _ _ h).mp (nice_prime_mul_mod_of_lt h h0)

theorem nice_prime_mul_mod_of_coprime :
    ∀ k m, (hk : p.Coprime k) → (hm : p.Coprime m) →
      f (k * m % p) = f (k % p) * f (m % p) :=
  (mul_mod_of_not_dvd_equiv_coprime _ _ h).mp
    (nice_prime_mul_mod_of_not_dvd h h0)

end


theorem nice_prime_of_map_pred_of_mul_mod_of_lt (h0 : f (p - 1) = 1)
    (h1 : ∀ k m, 0 < k → k < p → 0 < m → m < p → f (k * m % p) = f k * f m) :
    nice f p := λ a b ha hb h2 ↦ by
  ---- First reduce to `a * (p - 1) % p = b`
  have h3 : a < p := (Nat.lt_add_of_pos_right hb).trans_eq h2
  specialize h1 (p - 1) a h.pred_pos (Nat.pred_lt_self h.pos) ha h3
  rw [h0, one_mul] at h1
  refine h1.symm.trans (congr_arg f ?_)
  ---- Now prove `a * (p - 1) % p = b`
  rw [← add_right_inj a, h2]
  apply Nat.mod_eq_of_lt at h3; nth_rw 1 [← h3]
  refine mod_add_mod_eq_of_dvd_of_mod_pos ⟨a, ?_⟩ (ha.trans_eq h3.symm)
  rw [← one_add_mul, Nat.add_sub_cancel' h.one_lt.le]

theorem nice_prime_of_map_pred_of_mul_mod_of_not_dvd (h0 : f (p - 1) = 1)
    (h1 : ∀ k m, ¬p ∣ k → ¬p ∣ m → f (k * m % p) = f (k % p) * f (m % p)) :
    nice f p :=
  nice_prime_of_map_pred_of_mul_mod_of_lt h h0 <|
    (mul_mod_of_lt_equiv_not_dvd _ _ h).mpr h1

theorem nice_prime_of_map_pred_of_mul_mod_of_coprime
    (h0 : f (p - 1) = 1)
    (h1 : ∀ k m, p.Coprime k → p.Coprime m →
      f (k * m % p) = f (k % p) * f (m % p)) :
    nice f p :=
  nice_prime_of_map_pred_of_mul_mod_of_not_dvd h h0 <|
    (mul_mod_of_not_dvd_equiv_coprime _ _ h).mpr h1

theorem nice_prime_iff_map_pred_of_mul_mod_of_lt :
    nice f p ↔ (f (p - 1) = 1 ∧ ∀ k m,
      0 < k → k < p → 0 < m → m < p → f (k * m % p) = f k * f m) :=
  ⟨λ h0 ↦ ⟨nice_prime_map_pred h h0, nice_prime_mul_mod_of_lt h h0⟩,
  λ h0 ↦ nice_prime_of_map_pred_of_mul_mod_of_lt h h0.1 h0.2⟩

theorem nice_prime_iff_map_pred_of_mul_mod_of_not_dvd :
    nice f p ↔ (f (p - 1) = 1 ∧ ∀ k m,
      ¬p ∣ k → ¬p ∣ m → f (k * m % p) = f (k % p) * f (m % p)) := by
  rw [← mul_mod_of_lt_equiv_not_dvd _ _ h]
  exact nice_prime_iff_map_pred_of_mul_mod_of_lt h

theorem nice_prime_iff_map_pred_of_mul_mod_of_coprime :
  nice f p ↔ (f (p - 1) = 1 ∧ ∀ k m,
    p.Coprime k → p.Coprime m → f (k * m % p) = f (k % p) * f (m % p)) := by
  rw [← mul_mod_of_not_dvd_equiv_coprime _ _ h]
  exact nice_prime_iff_map_pred_of_mul_mod_of_not_dvd h
