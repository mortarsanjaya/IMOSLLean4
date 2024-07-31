/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.Nat.MulMap
import Mathlib.Data.Nat.Prime.Defs

/-!
# IMO 2020 N5 (Good functions, ℕ version)

Fix a cancellative monoid `M` and a multiplicative map `f : ℕ → M`.
Given `n : ℕ`, we say that `n` is *`f`-reflexive* if
  `f(a) = f(b)` for all `a, b > 0` such that `a + b = n`.
We say that `f` is:
1. *good*, if there exists infinitely many `f`-reflexive integers;
2. of *local class* at a prime `p`, if `p^k` is `f`-reflexive for all `k : ℕ`;
3. of *global class* if infinitely many primes are `f`-reflexive.
We prove basic properties of these maps.
-/

namespace IMOSL
namespace IMO2020N5
namespace Nat

variable [MulOneClass M]

abbrev reflexive (f : MulMap M) (n : ℕ) := ∀ a > 0, ∀ b > 0, a + b = n → f a = f b

def good (f : MulMap M) := ∀ N, ∃ n > N, reflexive f n

def localClass (p : Nat.Primes) (f : MulMap M) := ∀ k, reflexive f (p ^ k)

def globalClass (f : MulMap M) := ∀ N, ∃ p : Nat.Primes, N < p.1 ∧ reflexive f p



lemma localClass.is_good {f : MulMap M} (hf : localClass p f) : good f :=
  λ N ↦ ⟨p.1 ^ N, Nat.lt_pow_self p.2.one_lt N, hf N⟩

lemma globalClass.is_good {f : MulMap M} (hf : globalClass f) : good f :=
  λ N ↦ (hf N).elim λ p h ↦ ⟨p, h⟩

lemma reflexive.one (f : MulMap M) : reflexive f 1 :=
  λ _ ha _ hb h ↦ h.not_gt.elim (Nat.add_le_add ha hb)

lemma reflexive.zero (f : MulMap M) : reflexive f 0 :=
  λ _ ha _ _ h ↦ h.not_gt.elim (Nat.add_pos_left ha _)

lemma reflexive.of_dvd [IsRightCancelMul M] {f : MulMap M}
    (hd : 0 < d) (h : reflexive f d) (h0 : c ∣ d) :
    reflexive f c := λ a ha b hb h1 ↦ by
  subst h1; rcases h0 with ⟨k, rfl⟩
  have hk : 0 < k := Nat.pos_of_mul_pos_left hd
  specialize h (a * k) (Nat.mul_pos ha hk) (b * k) (Nat.mul_pos hb hk) (add_mul a b k).symm
  rwa [f.map_mul ha hk, f.map_mul hb hk, mul_left_inj] at h



/-- TODO: Get this to mathlib, or delete it once it gets into mathlib -/
lemma mod_add_mod_eq_of_dvd_add_of_not_dvd {a b c : ℕ} (h : c ∣ a + b) (ha : ¬c ∣ a) :
    c = a % c + b % c := by
  have h0 : 0 < a % c + b % c := Nat.add_pos_left (Nat.emod_pos_of_not_dvd ha) _
  have h1 : a % c + b % c < c * 2 := by
    have h1 : 0 < c := by
      refine Nat.pos_of_ne_zero λ h1 ↦ ha ?_
      rw [h1, Nat.zero_dvd] at h ⊢
      exact Nat.eq_zero_of_add_eq_zero_right h
    rw [Nat.mul_two]; exact Nat.add_lt_add (a.mod_lt h1) (b.mod_lt h1)
  obtain ⟨k, h2⟩ : c ∣ a % c + b % c := by
    rwa [Nat.dvd_iff_mod_eq_zero, ← Nat.add_mod, ← Nat.dvd_iff_mod_eq_zero]
  replace h0 : 0 < k := Nat.pos_of_mul_pos_left (h0.trans_eq h2)
  replace h1 : k < 2 := Nat.lt_of_mul_lt_mul_left (h2.symm.trans_lt h1)
  obtain rfl : k = 1 := Nat.le_antisymm (Nat.le_of_lt_succ h1) h0
  rw [h2, c.mul_one]


variable {p : Nat.Primes} {f : MulMap M}

/-- If a prime `p` is `f`-reflexive, then for any `0 < k < p`, then `f(k)` is the
  left inverse of some `f(m)`. Useful to remove the need of `M` to be cancellative. -/
lemma reflexive.map_invertible_of_lt_prime (hf : reflexive f p) :
    ∀ {k}, 0 < k → k < p.1 → ∃ m, 0 < m ∧ f k * f m = 1 := by
  ---- Set up strong induction and eliminate the case `k = 1`
  intro k hk hkp; induction' k using Nat.strong_induction_on with k₀ k_ih
  obtain rfl | hk0 : k₀ = 1 ∨ 1 < k₀ := eq_or_gt_of_le hk
  · refine ⟨1, Nat.one_pos, ?_⟩; rw [f.map_one, mul_one]
  ---- Restrict `k_ih` to `p % k₀`
  have h : 0 < p % k₀ :=
    Nat.emod_pos_of_not_dvd λ h ↦ hkp.ne.symm ((p.2.dvd_iff_eq hk0.ne.symm).mp h)
  replace k_ih : ∃ m, 0 < m ∧ f (p % k₀) * f m = 1 := by
    have h0 : p % k₀ < k₀ := p.1.mod_lt hk; exact k_ih _ h0 h (h0.trans hkp)
  rcases k_ih with ⟨m, hm, hm0⟩
  ---- Now take the desired `m` to be `(p / k₀) * m`
  have h0 : 0 < p / k₀ := Nat.div_pos hkp.le hk
  refine ⟨p / k₀ * m, Nat.mul_pos h0 hm, ?_⟩
  rw [f.map_mul h0 hm, ← f.map_assoc, ← f.map_mul hk h0, ← hm0]
  exact congrArg₂ _ (hf _ (Nat.mul_pos hk h0) _ h (Nat.div_add_mod _ k₀)) rfl

/-- The main claim on `f`-reflexive primes. -/
lemma reflexive.map_mul_mod_prime_formula (hf : reflexive f p) :
    ∀ {k}, 0 < k → k < p.1 → ∀ {m}, 0 < m → m < p.1 → f (k * m % p) = f k * f m := by
  ---- Set up the strong induction
  intro k hk hkp; induction' k using Nat.strong_induction_on with k₀ k_ih
  intro m hm hmp; induction' m using Nat.strong_induction_on with m₀ m_ih
  ---- Useful hypothesis to have around: `p ∤ k₀m₀`
  have h : ¬p.1 ∣ k₀ * m₀ := by
    rw [p.2.dvd_mul, not_or]
    exact ⟨Nat.not_dvd_of_pos_of_lt hk hkp, Nat.not_dvd_of_pos_of_lt hm hmp⟩
  ---- If `k₀m₀ ≤ p`, then we are done; equality case is actually impossible
  obtain h0 | h0 | h0 : k₀ * m₀ < p ∨ k₀ * m₀ = p ∨ p < k₀ * m₀ := lt_trichotomy _ _
  · rw [Nat.mod_eq_of_lt h0, f.map_mul hk hm]
  · exact absurd h0.symm.dvd h
  /- Now assume `k₀m₀ > p`. Let `0 < q = p / m₀ < k₀` and `0 < r = p % m₀ < m₀`.
    The main idea is to write `f(k₀qm₀ % p)` in two ways.
    By `k_ih`, it equals `f(q) f(k₀m₀ % p)`.
    By `m_ih`, it equals `f(k₀r % p) = f(k₀) f(r) = f(k₀) f(qm₀)`. -/
  ---- Just a useful lemma: `p / m₀ > 0`
  have p_div_m₀_pos : 0 < p / m₀ := Nat.div_pos hmp.le hm
  ---- Specialize `k_ih` to `f(qk₀m₀ % p) = f(q) f(k₀m₀ % p)`
  replace k_ih : f ((p / m₀) * (k₀ * m₀) % p) = f (p / m₀) * f (k₀ * m₀ % p) := by
    have h1 : p / m₀ < k₀ := Nat.div_lt_of_lt_mul (h0.trans_eq (mul_comm _ _))
    rw [← Nat.mul_mod_mod]
    exact k_ih _ h1 p_div_m₀_pos (h1.trans hkp)
      (Nat.emod_pos_of_not_dvd h) (Nat.mod_lt _ p.2.pos)
  ---- Specialize `m_ih` directly to `f(k₀qm₀ % p) = f(k₀) f(qm₀)`
  replace m_ih : f (k₀ * (m₀ * (p / m₀)) % p) = f k₀ * f (m₀ * (p / m₀)) := by
    have h1 : m₀ * (p / m₀) + p % m₀ = p := p.1.div_add_mod m₀
    have h2 : 0 < p % m₀ := by
      refine Nat.emod_pos_of_not_dvd λ h2 ↦ ((Nat.dvd_prime p.2).mp h2).elim ?_ hmp.ne
      rintro rfl; exact (hkp.trans h0).ne k₀.mul_one.symm
    have h3 : p % m₀ < m₀ := p.1.mod_lt hm
    -- Now do the calculation
    calc
      _ = f (k₀ * (p % m₀) % p) := by
        have h4 : ¬p.1 ∣ k₀ * (p.1 % m₀) :=
          λ h4 ↦ (p.2.dvd_mul.mp h4).elim (Nat.not_dvd_of_pos_of_lt hk hkp)
            (Nat.not_dvd_of_pos_of_lt h2 (h3.trans hmp))
        have h5 : p.1 ∣ k₀ * (↑p % m₀) + k₀ * (m₀ * (↑p / m₀)) :=
          ⟨k₀, by rw [← Nat.mul_add, add_comm, h1, Nat.mul_comm]⟩
        exact (hf _ (Nat.emod_pos_of_not_dvd h4) _
          (Nat.emod_pos_of_not_dvd λ h6 ↦ h4 ((Nat.dvd_add_iff_left h6).mpr h5))
          (mod_add_mod_eq_of_dvd_add_of_not_dvd h5 h4).symm).symm
      _ = f k₀ * f (p % m₀) := m_ih _ (p.1.mod_lt hm) h2 (h3.trans hmp)
      _ = f k₀ * f (m₀ * (p / m₀)) := by rw [hf _ (Nat.mul_pos hm p_div_m₀_pos) _ h2 h1]
  ---- Finally, unite the informations from `k_ih` and `m_ih`
  rw [← mul_rotate', k_ih, f.map_mul hm p_div_m₀_pos, f.map_comm, ← f.map_assoc] at m_ih
  obtain ⟨s, -, hs⟩ : ∃ s, 0 < s ∧ f (p / m₀) * f s = 1 := by
    refine hf.map_invertible_of_lt_prime p_div_m₀_pos
      (Nat.div_lt_self p.2.pos (lt_of_not_le λ h1 ↦ h0.not_le (hkp.le.trans_eq' ?_)))
    rw [← Nat.le_antisymm hm h1, Nat.mul_one]
  apply congrArg (· * f s) at m_ih
  rwa [f.map_assoc, ← f.map_mul hk hm, f.map_assoc,
    hs, mul_one, mul_one, f.map_mul hk hm] at m_ih

/-- The main claim on `f`-reflexive primes, stated purely in terms of modulus. -/
lemma reflexive.mul_mod_prime_eq_map_mod_mul_map_mod
    (hf : reflexive f p) (hk : ¬p.1 ∣ k) (hm : ¬p.1 ∣ m) :
    f (k * m % p) = f (k % p) * f (m % p) :=
  k.mul_mod m p ▸ hf.map_mul_mod_prime_formula (Nat.emod_pos_of_not_dvd hk)
    (k.mod_lt p.2.pos) (Nat.emod_pos_of_not_dvd hm) (m.mod_lt p.2.pos)

/-- The main claim on `f`-reflexive prime powers. -/
lemma reflexive.prime_power_map_eq_map_mod (hf : ∀ b ≤ a, reflexive f (p ^ b)) :
    ∀ {k}, k < p.1 ^ a → ¬p.1 ∣ k → f k = f (k % p) := by
  ---- Induction on `a`; resolve the base cases `a = 0` and `a = 1` immediately
  induction' a with a a_ih
  · intro k h h0; refine h0.elim ⟨0, ?_⟩
    rw [Nat.mul_zero, Nat.lt_one_iff.mp h]
  obtain rfl | ⟨a, rfl⟩ : a = 0 ∨ ∃ b, a = Nat.succ b :=
    (eq_or_ne a 0).imp_right Nat.exists_eq_succ_of_ne_zero
  · rintro k hk -; exact congrArg f (Nat.mod_eq_of_lt (hk.trans_eq p.1.pow_one)).symm
  ---- Now set up strong induction on `k`, resolving the case `k ≤ p^a`
  intro k hk hk0; induction' k using Nat.strong_induction_on with k k_ih
  obtain hk | rfl | hk1 : k < p ^ a.succ ∨ k = p ^ a.succ ∨ p ^ a.succ < k := lt_trichotomy _ _
  · exact a_ih (λ b hb ↦ hf b (Nat.le_add_right_of_le hb)) hk hk0
  · exact hk0.elim ⟨p ^ a, Nat.pow_succ'⟩
  clear a_ih
  /- This time, write `p^{a + 2} = qk + r`, where `0 < q < p` and `0 < r < k`.
    The main equality is `f(qk) = f(r) = f(r % p) = f((qk) % p) = f(q) f(k % p)`. -/
  have h : p ^ (a + 2) / k * k + p ^ (a + 2) % k = p ^ (a + 2) := Nat.div_add_mod' _ _
  have hk2 : 0 < k := Nat.zero_lt_of_lt hk1
  have hq : 0 < p ^ (a + 2) / k := Nat.div_pos hk.le hk2
  have hq0 : p ^ (a + 2) / k < p :=
    Nat.div_lt_of_lt_mul (Nat.mul_lt_mul_of_pos_right hk1 p.2.pos)
  have hq1 : ¬p.1 ∣ p ^ (a + 2) / k := Nat.not_dvd_of_pos_of_lt hq hq0
  have hqr : ¬p.1 ∣ p ^ (a + 2) / k * k := by rw [p.2.dvd_mul, not_or]; exact ⟨hq1, hk0⟩
  have hpa : p.1 ∣ p ^ (a + 2) := ⟨p ^ a.succ, Nat.pow_succ'⟩
  have hr : ¬p.1 ∣ p ^ (a + 2) % k := λ h0 ↦ hqr (by rwa [← Nat.dvd_add_left h0, h])
  have h0 : reflexive f p := p.1.pow_one ▸ hf 1 (Nat.le_add_left 1 _)
  ---- Multiply by `f(p^{a + 2} / k)` on the right (unnecessary if `M` is cancellative)
  suffices f (p ^ (a + 2) / k) * f k = f (p ^ (a + 2) / k) * f (k % p) by
    obtain ⟨s, -, hs⟩ : ∃ s, 0 < s ∧ f (p ^ (a + 2) / k) * f s = 1 :=
      h0.map_invertible_of_lt_prime hq hq0
    apply congrArg (f s * ·) at this
    rwa [← f.map_assoc, ← f.map_assoc, f.map_comm s, hs, one_mul, one_mul] at this
  ---- Now do the calculations
  calc
    _ = f (p ^ (a + 2) / k * k) := (f.map_mul hq hk2).symm
    _ = f (p ^ (a + 2) % k) :=
      hf (a + 2) (a + 2).le_refl _ (Nat.mul_pos hq hk2)
        _ (Nat.pos_of_ne_zero λ h1 ↦ hr ⟨0, h1.trans p.1.mul_zero.symm⟩) h
    _ = f (p ^ (a + 2) % k % p) := by
      have h0 : p ^ (a + 2) % k < k := Nat.mod_lt _ hk2
      exact k_ih _ h0 (h0.trans hk) hr
    _ = f (p ^ (a + 2) / k * k % p) := by
      refine h0 _ (Nat.emod_pos_of_not_dvd hr) _ (Nat.emod_pos_of_not_dvd hqr)
        (mod_add_mod_eq_of_dvd_add_of_not_dvd ?_ hr).symm
      rwa [Nat.add_comm, h]
    _ = f (p ^ (a + 2) / k % p) * f (k % p) :=
      h0.mul_mod_prime_eq_map_mod_mul_map_mod hq1 hk0
    _ = f (p ^ (a + 2) / k) * f (k % p) := by rw [Nat.mod_eq_of_lt hq0]

/-- Characterization of multiplicative maps of local class at a fixed prime -/
lemma localClass.map_eq_map_mod (hf : localClass p f) (h : ¬p.1 ∣ k) : f k = f (k % p) :=
  reflexive.prime_power_map_eq_map_mod (λ b _ ↦ hf b) (Nat.lt_pow_self p.2.one_lt k) h
