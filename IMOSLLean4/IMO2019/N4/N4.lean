/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.GCD.Basic

/-!
# IMO 2019 N4

Fix some $C ∈ ℕ$.
Find all functions $f : ℕ → ℕ$ such that $a + f(b) ∣ a^2 + b f(a)$
  for any $a, b ∈ ℕ$ satisfying $a + b > C$.

### Notes

The original functional equation is of type $ℕ^+ → ℕ^+$.
However, the solution can be deduced from this $ℕ$-version as well.
We do both versions in this file.
-/


namespace IMOSL
namespace IMO2019N4

/-! ### Extra lemmas -/

lemma dvd_iff_of_dvd_add {c : ℕ} (h : c ∣ a + b) : c ∣ a ↔ c ∣ b :=
  ⟨λ h0 ↦ (Nat.dvd_add_right h0).mp h, λ h0 ↦ (Nat.dvd_add_left h0).mp h⟩

theorem dvd_sq_iff_dvd_sq_of_dvd_add {c : ℕ} (h : c ∣ a + b) :
    c ∣ a ^ 2 ↔ c ∣ b ^ 2 :=
  have h0 {u v w : ℕ} (h0 : u ∣ v + w) : u ∣ v ^ 2 ↔ u ∣ v * w :=
    dvd_iff_of_dvd_add (by rw [sq, ← Nat.mul_add]; exact h0.mul_left v)
  by rw [h0 h, mul_comm, ← h0 (a.add_comm b ▸ h)]

theorem eq_zero_of_prime_add_dvd_sq (h : p.Prime) (h0 : a < p) (h1 : p + a ∣ p ^ 2) :
    a = 0 := by
  rw [Nat.dvd_prime_pow h] at h1
  rcases h1 with ⟨k, h1, h2⟩
  rw [Nat.le_add_one_iff, Nat.le_add_one_iff, zero_add, le_zero_iff] at h1
  rcases h1 with (rfl | rfl) | rfl
  · exact absurd h2 (h.one_lt.trans_le le_self_add).ne.symm
  · rwa [pow_one, add_eq_left] at h2
  · refine absurd ((add_lt_add_left h0 p).trans_le ?_) h2.not_lt
    rw [sq, ← two_mul]; exact Nat.mul_le_mul_right p h.two_le





/-! ### Start of the problem -/

def good (C : ℕ) (f : ℕ → ℕ) :=
  ∀ a b : ℕ, C < a + b → a + f b ∣ a ^ 2 + b * f a

theorem linear_is_good (C k : ℕ) : good C (k * ·) :=
  λ a b _ ↦ ⟨a, by rw [sq, add_mul, Nat.mul_assoc, mul_left_comm]⟩

theorem good_is_linear {f : ℕ → ℕ} (h : good C f) : ∃ k, f = (k * ·) := by
  ---- `f(n) ≤ n f(1)` for all `n`
  have h0 {n} (h0 : C < n) : f n ≤ n * f 1 := by
    rw [← Nat.succ_le_succ_iff, Nat.succ_eq_one_add, Nat.succ_eq_one_add]
    exact Nat.le_of_dvd (Nat.add_pos_left Nat.one_pos _)
      (h 1 n <| Nat.lt_one_add_iff.mpr h0.le)
  ---- For any `p` prime, there exists `k ≤ f(1)` such that `f(p) = kp`
  have h1 {p} (h1 : C < p) (h2 : p.Prime) : ∃ k ≤ f 1, f p = k * p := by
    suffices p ∣ f p ^ 2 by
      rcases h2.dvd_of_dvd_pow this with ⟨k, h3⟩
      exact ⟨k, Nat.le_of_mul_le_mul_left (h3.ge.trans (h0 h1)) h2.pos,
        h3.trans (p.mul_comm k)⟩
    rcases exists_gt (C + f p) with ⟨n, h3⟩
    replace h3 := Nat.exists_eq_add_of_le (h3.le.trans (Nat.le_mul_of_pos_right _ h2.pos))
    rcases h3 with ⟨a, h3⟩; rw [add_right_comm] at h3
    specialize h (C + a) p ((C.le_add_right a).trans_lt (Nat.lt_add_of_pos_right h2.pos))
    replace h3 : p ∣ C + a + f p := ⟨n, h3.symm.trans (n.mul_comm p)⟩
    rw [← dvd_sq_iff_dvd_sq_of_dvd_add h3, dvd_iff_of_dvd_add (h3.trans h)]
    exact p.dvd_mul_right _
  ---- The main claim
  have h2 (x) : ∃ B, ∀ p, p.Prime → B < p → ∃ k, f p = k * p ∧ f x = k * x := by
    refine ⟨max C (max (f x) (max (x * f 1) (x ^ 2))), λ p h2 h3 ↦ ?_⟩
    rw [max_lt_iff, max_lt_iff, max_lt_iff] at h3
    rcases h3 with ⟨hp1, hp2, hp3, hp4⟩
    rcases h1 hp1 h2 with ⟨k, h3, h4⟩
    refine ⟨k, h4, ?_⟩
    rcases (f x).eq_zero_or_pos with h5 | h5
    · rcases k.eq_zero_or_pos with rfl | h6
      · rw [h5, zero_mul]
      · suffices x ^ 2 = 0 by rw [h5, pow_eq_zero this, mul_zero]
        specialize h x p (Nat.lt_add_left x hp1)
        rw [h5, mul_zero, add_zero, h4] at h
        exact Nat.eq_zero_of_dvd_of_lt h <|
          Nat.lt_add_left x (lt_mul_of_one_le_of_lt h6 hp4)
    · specialize h p x (Nat.lt_add_right x hp1)
      have h6 : (p + f x).Coprime p := by
        rw [Nat.coprime_self_add_left, Nat.coprime_comm, h2.coprime_iff_not_dvd]
        exact Nat.not_dvd_of_pos_of_lt h5 hp2
      rw [sq, h4, ← mul_assoc, ← add_mul, h6.dvd_mul_right] at h
      clear h6; rcases h with ⟨_ | _ | t, h⟩
      · exact h.not_gt.elim (Nat.lt_add_right _ h2.pos)
      · rwa [Nat.mul_one, add_right_inj, eq_comm, mul_comm] at h
      · rw [add_assoc, mul_add, add_mul _ _ 2] at h
        refine h.not_lt.elim (Nat.lt_add_left _ (Nat.lt_add_right _ ?_))
        rw [mul_two, add_lt_add_iff_left]
        exact hp3.trans_le' (Nat.mul_le_mul_left x h3)
  ---- Finishing
  rcases C.succ.exists_infinite_primes with ⟨p, (h3 : C < p), h4⟩
  rcases h1 h3 h4 with ⟨k, -, h5⟩
  refine ⟨k, funext λ n ↦ ?_⟩
  rcases h2 p with ⟨Bp, hp⟩
  rcases h2 n with ⟨Bn, hn⟩
  rcases (max Bp Bn).succ.exists_infinite_primes with ⟨q, h6, h7⟩
  rw [Nat.succ_le_iff, max_lt_iff] at h6
  specialize hp q h7 h6.1; rcases hp with ⟨kp, h8, h9⟩
  rw [h5, Nat.mul_left_inj h4.ne_zero] at h9
  specialize hn q h7 h6.2; rcases hn with ⟨kn, h10, h11⟩
  rw [h8, Nat.mul_left_inj h7.ne_zero] at h10
  rw [h11, ← h10, ← h9]

/-- Final solution, `Nat` version -/
theorem final_solution_Nat : good C f ↔ ∃ k : ℕ, f = (k * ·) :=
  ⟨good_is_linear, λ h ↦ h.elim λ k h ↦ h ▸ linear_is_good C k⟩





/-! ### Extension from `ℕ+ → ℕ+` to `ℕ → ℕ` -/

def goodPNat (C : ℕ+) (f : ℕ+ → ℕ+) :=
  ∀ a b : ℕ+, C < a + b → a + f b ∣ a ^ 2 + b * f a

theorem linear_is_goodPNat (C k : ℕ+) : goodPNat C (k * ·) :=
  λ a b _ ↦ ⟨a, by rw [sq, add_mul, mul_assoc, mul_left_comm]⟩

theorem goodPNat_is_linear (h : goodPNat C f) : ∃ k : ℕ+, f = (k * ·) := by
  let g : ℕ → ℕ := λ n ↦ dite (0 < n) (λ h ↦ f ⟨n, h⟩) (λ _ ↦ 0)
  have h0 : good C g := λ a b H ↦ by
    rcases a.eq_zero_or_pos with rfl | ha
    · exact ⟨0, rfl⟩
    rcases b.eq_zero_or_pos with rfl | hb
    · rw [zero_mul]; exact ⟨a, sq a⟩
    · dsimp only [g]; rw [dif_pos ha, dif_pos hb]
      exact PNat.dvd_iff.mp (h ⟨a, ha⟩ ⟨b, hb⟩ H)
  rcases good_is_linear h0 with ⟨k, h1⟩
  replace h0 : 0 < k := by rw [← k.mul_one, ← congr_fun h1]; exact (f 1).pos
  refine ⟨⟨k, h0⟩, funext λ x ↦ ?_⟩
  rw [← PNat.coe_inj, PNat.mul_coe, PNat.mk_coe, ← congr_fun h1, eq_comm]
  exact dif_pos x.pos

/-- Final solution -/
theorem final_solution : goodPNat C f ↔ ∃ k : ℕ+, f = (k * ·) :=
  ⟨goodPNat_is_linear, λ h ↦ h.elim λ k h ↦ h ▸ linear_is_goodPNat C k⟩
