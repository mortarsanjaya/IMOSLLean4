/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.FieldTheory.Finite.Basic

/-!
# IMO 2024 N4 (P2)

Find all pairs $(a, b)$ of positive integers such that there exists a positive integer $g$
  for which $\gcd(a^n + b, b^n + a) = g$ for all sufficiently large $n$.

### Answer

$(1, 1)$.

### Solution

We follow the AoPS solution ♯9 by **Tintarn** in
  [this thread](https://artofproblemsolving.com/community/c6h3358926p31206647).
We make it even simpler by only substituting twice.
That is, pick some $n₀ ≥ N$ such that $a^{n₀ + 1} ≡ b^{n₀ + 1} ≡ 1 \pmod{ab + 1}$,
  then plug $n = n₀$ and $n = n₀ + 1$ (typically one chooses $n₀ ≡ -1 \pmod{φ(ab + 1)}$).
Note that all solutions that I am aware of so far considers $ab + 1$.
-/

namespace IMOSL
namespace IMO2024N4

/-- `a` is coprime with `ab + 1`. -/
lemma self_coprime_mul_succ (a b : ℕ) : a.Coprime (a * b + 1) := by simp

/-- `a^{φ(ab + 1) k} ≡ 1 (mod ab + 1)`. -/
lemma pow_totient_mul_succ_mul_modeq_one (a b k) :
    a ^ ((a * b + 1).totient * k) ≡ 1 [MOD a * b + 1] := by
  simpa only [Nat.one_pow, a.pow_mul] using
    (Nat.ModEq.pow_totient (self_coprime_mul_succ _ _)).pow k

/-- If `a^{n + 1} ≡ 1 (mod ab + 1)` then `ab + 1 ∣ a^n + b`. -/
lemma mul_succ_dvd_pow_add_of_pow_succ_modeq_one (h : a ^ (n + 1) ≡ 1 [MOD a * b + 1]) :
    a * b + 1 ∣ a ^ n + b := by
  rw [← (self_coprime_mul_succ a b).symm.dvd_mul_left,
    Nat.mul_add, ← Nat.pow_succ', Nat.add_comm _ (a * b)]
  exact ((h.add_left _).dvd_iff (Nat.dvd_refl _)).mpr (Nat.dvd_refl _)

/-- If `ab + 1 ∣ b + 1`, then `a = 1`. -/
lemma eq_one_of_mul_succ_right_dvd_succ
    (ha : 0 < a) (hb : 0 < b) (h : a * b + 1 ∣ b + 1) : a = 1 :=
  ha.succ_le.antisymm' <| (mul_le_iff_le_one_left hb).mp <|
    Nat.le_of_lt_succ (Nat.le_of_dvd b.succ_pos h)

/-- Final solution -/
theorem final_solution (ha : 0 < a) (hb : 0 < b) :
    (∃ g N, ∀ n ≥ N, (a ^ n + b).gcd (b ^ n + a) = g) ↔ (a = 1 ∧ b = 1) := by
  ---- First solve the `←` direction immediately.
  refine Iff.symm ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · refine ⟨2, 0, λ n _ ↦ ?_⟩
    rw [h.1, h.2, Nat.one_pow, Nat.gcd_self]
  ---- For `→`, first find `n₀ ≥ N` with `a^{n₀ + 1} ≡ b^{n₀ + 1} ≡ 1 (mod ab + 1)`.
  rcases h with ⟨g, N, h⟩
  obtain ⟨n₀, hn₀, hn₀a, hn₀b⟩ :
      ∃ n₀ ≥ N, a ^ (n₀ + 1) ≡ 1 [MOD a * b + 1] ∧ b ^ (n₀ + 1) ≡ 1 [MOD a * b + 1] := by
    -- Pick `n₀ = φ(ab + 1)(N + 1) - 1`.
    have h0 : 0 < (a * b + 1).totient := Nat.totient_pos.mpr (Nat.succ_pos _)
    refine ⟨(a * b + 1).totient * (N + 1) - 1,
      Nat.le_sub_of_add_le (Nat.le_mul_of_pos_left _ h0), ?_⟩
    rw [Nat.sub_add_cancel (Nat.mul_pos h0 N.succ_pos)]
    exact ⟨pow_totient_mul_succ_mul_modeq_one _ _ _,
      a.mul_comm b ▸ pow_totient_mul_succ_mul_modeq_one _ _ _⟩
  ---- By plugging `n = n₀`, deduce that `ab + 1 ∣ g`.
  have h0 : a * b + 1 ∣ g := by
    rw [← h _ hn₀, Nat.dvd_gcd_iff]
    refine ⟨mul_succ_dvd_pow_add_of_pow_succ_modeq_one hn₀a, ?_⟩
    rw [a.mul_comm b] at hn₀b ⊢
    exact mul_succ_dvd_pow_add_of_pow_succ_modeq_one hn₀b
  ---- Now by plugging `n = n₀ + 1`, deduce that `a = b = 1`.
  rw [← h _ (Nat.le_succ_of_le hn₀), Nat.dvd_gcd_iff] at h0
  revert h0; refine And.imp (λ h0 ↦ ?_) (λ h0 ↦ ?_)
  · rw [(hn₀a.add_right b).dvd_iff (Nat.dvd_refl _), Nat.add_comm 1] at h0
    exact eq_one_of_mul_succ_right_dvd_succ ha hb h0
  · rw [(hn₀b.add_right a).dvd_iff (Nat.dvd_refl _), a.mul_comm, Nat.add_comm 1] at h0
    exact eq_one_of_mul_succ_right_dvd_succ hb ha h0
