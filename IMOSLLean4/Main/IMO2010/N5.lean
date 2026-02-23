/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.ModEq

/-!
# IMO 2010 N5 (P3)

Find all functions $f : ℕ⁺ → ℕ⁺$ such that $(f(m) + n)(f(n) + m)$
 is a square for any positive integers $m$ and $n$.

### Answer

$f(n) = n$ and $f(n) = n + k$ for some $k ∈ ℕ⁺$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2010SL.pdf).
The implementation is more comfortably done over $ℕ$ (the natural numbers),
  so we also solve an even more general functional equation as follows:
  given a natural number $c$, find all functions $f : ℕ → ℕ$ such that
  $(f(m) + n + c)(f(n) + m + c)$ is a square any $m, n ∈ ℕ$.
-/

namespace IMOSL
namespace IMO2010N5

/-- A function `f : ℕ → ℕ` is called `c`-good if
  `(f(m) + n + c)(f(n) + m + c)` is a square for any `m, n : ℕ`. -/
def good (c : ℕ) (f : ℕ → ℕ) := ∀ m n, ∃ k, (f m + n + c) * (f n + m + c) = k ^ 2

/-- The function `n ↦ n + k` is `c`-good for any `c, k : ℕ`. -/
lemma add_right_is_good (c k) : good c (· + k) := by
  intro m n; refine ⟨m + n + k + c, ?_⟩
  rw [Nat.pow_two, Nat.add_right_comm m, Nat.add_right_comm n, Nat.add_comm n]


section

variable {p a b : ℕ} (hp : Nat.Prime p) (h : ∃ k : ℕ, a * b = k ^ 2)
include hp h

/-- Step 1: if `ab` is a square and `ν_p(a) = 2n + 1` for some `n : ℕ`, then `p ∣ b`. -/
lemma step1_general (ha : p ^ (2 * n + 1) ∣ a) (ha0 : ¬p ^ (2 * n + 2) ∣ a) : p ∣ b := by
  rcases h with ⟨k, hk⟩
  ---- Write `a = p^{2n + 1} u` for some `u`, and note that `p ∤ u`.
  rcases ha with ⟨u, rfl⟩
  replace ha0 : ¬p ∣ u := mt (Nat.mul_dvd_mul_iff_left (Nat.pow_pos hp.pos)).mpr ha0
  ---- Since `p^{2n + 1} ∣ k^2`, we have `p^{n + 1} ∣ k`, say `k = p^{n + 1} t`.
  replace hk : k ^ 2 = (p ^ n) ^ 2 * (p * (u * b)) := by
    rw [← hk, Nat.pow_succ, Nat.mul_assoc, Nat.mul_assoc, Nat.mul_comm 2, Nat.pow_mul]
  obtain ⟨m, rfl⟩ : p ^ n ∣ k := (Nat.pow_dvd_pow_iff (Nat.succ_ne_zero 1)).mp ⟨_, hk⟩
  replace hk : m ^ 2 = p * (u * b) := by
    rwa [Nat.mul_pow, ← Nat.pow_mul, Nat.mul_right_inj (Nat.pow_pos hp.pos).ne.symm] at hk
  obtain ⟨t, rfl⟩ : p ∣ m := hp.dvd_of_dvd_pow ⟨_, hk⟩
  ---- Then `p` divides `ub = pt^2`, and since `p ∤ u`, we get `p ∣ b`.
  replace hk : p ∣ u * b := by
    refine ⟨t ^ 2, ?_⟩
    rw [← Nat.mul_left_cancel_iff hp.pos, ← hk, Nat.mul_pow, Nat.pow_two, Nat.mul_assoc]
  exact (hp.dvd_mul.mp hk).resolve_left ha0

/-- A version of Step 1 with `a ≡ p^{2n + 1} (mod p^{2n + 2})`. -/
lemma step1_modeq (ha : a ≡ p ^ (2 * n + 1) [MOD p ^ (2 * n + 2)]) : p ∣ b := by
  refine step1_general hp h (n := n) ?_ ?_
  ---- Check `p^{2n + 1} ∣ a`.
  · exact (ha.dvd_iff ⟨p, rfl⟩).mpr (Nat.dvd_refl _)
  ---- Check `p^{2n + 2} ∤ a`.
  · rw [ha.dvd_iff (Nat.dvd_refl _), Nat.pow_dvd_pow_iff_le_right hp.one_lt]
    exact Nat.not_succ_le_self (2 * n + 1)

/-- A version of Step 1 with `a ≡ p (mod p^2)`. -/
lemma step1_pow_one (ha : a ≡ p [MOD p ^ 2]) : p ∣ b :=
  step1_modeq hp h (n := 0) (p.pow_one.symm ▸ ha)

end


/-- For any `b > 0` and for any `a, c : ℕ`,
  there exists `n : ℕ` such that `a + n ≡ c (mod b)`. -/
lemma exists_add_modeq (hb : 0 < b) (a c) : ∃ n, a + n ≡ c [MOD b] := by
  refine ⟨(b - 1) * a + c, ?_⟩
  rw [← Nat.add_assoc, Nat.add_modEq_right_iff,
    Nat.add_comm, ← Nat.add_one_mul, Nat.sub_add_cancel hb]
  exact Nat.dvd_mul_right b a

/-- If `f` is `c`-good and `f(k) ≡ f(l) (mod p)`, then `k ≡ l (mod p)`. -/
lemma map_modeq_prime_imp_modeq
    (hf : good c f) (hp : Nat.Prime p) (h : f k ≡ f l [MOD p]) : k ≡ l [MOD p] := by
  ---- It suffices to find `n` such that `p` divides `f(n) + k + c` and `f(n) + l + c`.
  suffices ∃ n, p ∣ f n + k + c ∧ p ∣ f n + l + c by
    rcases this with ⟨n, hn⟩
    replace hn : f n + k + c ≡ f n + l + c [MOD p] :=
      (Nat.mod_eq_zero_of_dvd hn.1).trans (Nat.mod_eq_zero_of_dvd hn.2).symm
    exact (hn.add_right_cancel' _).add_left_cancel' _
  ---- This `n` depends on whether `f(k) ≡ f(l) (mod p^2)` or not.
  by_cases h0 : f k ≡ f l [MOD p ^ 2]
  ---- If `f(k) ≡ f(l) (mod p^2)`, then we need `f(k) + n + c ≡ p (mod p^2)`.
  · obtain ⟨n, h1⟩ : ∃ n, f k + c + n ≡ p [MOD p ^ 2] :=
      exists_add_modeq (Nat.pow_pos hp.pos) _ _
    replace h0 : f l + c + n ≡ p [MOD p ^ 2] :=
      ((h0.add_right c).add_right n).symm.trans h1
    refine ⟨n, step1_pow_one hp (hf k n) ?_, step1_pow_one hp (hf l n) ?_⟩
    all_goals rwa [Nat.add_right_comm]
  ---- If `f(k) ≢ f(l) (mod p^2)`, then we need `f(k) + n + c ≡ p^3 (mod p^4)` instead.
  · obtain ⟨n, h1⟩ : ∃ n, f k + c + n ≡ p ^ 3 [MOD p ^ 4] :=
      exists_add_modeq (Nat.pow_pos hp.pos) _ _
    replace h1 : f k + n + c ≡ p ^ 3 [MOD p ^ 4] := by rwa [Nat.add_right_comm] at h1
    have h2 : f k + n + c ≡ 0 [MOD p ^ 2] :=
      (Nat.ModEq.of_dvd ⟨p ^ 2, Nat.pow_add p 2 2⟩ h1).trans (Nat.mul_mod_right _ p)
    replace h0 : ¬p ^ 2 ∣ f l + n + c := by
      intro h3; replace h3 : f k + n + c ≡ f l + n + c [MOD p ^ 2] :=
        h2.trans (Nat.right_modEq_add_iff.mpr h3)
      exact h0 ((h3.add_right_cancel' _).add_right_cancel' _)
    replace h2 : (f l + n + c) % p = p ^ 3 % p :=
      ((h.symm.add_right _).add_right _).trans (h1.symm.of_mul_left _).symm
    replace h2 : p ^ 1 ∣ f l + n + c := by
      rw [Nat.pow_one, Nat.dvd_iff_mod_eq_zero, h2, Nat.pow_succ, Nat.mul_mod_left]
    exact ⟨n, step1_modeq hp (hf k n) (n := 1) h1, step1_general hp (hf l n) (n := 0) h2 h0⟩

/-- If `k ≤ l` and `k ≢ l (mod p)` for every prime `p`, then `l = k + 1`. -/
lemma not_modeq_prime_imp₁
    (h : k ≤ l) (h0 : ∀ p : ℕ, Nat.Prime p → ¬k ≡ l [MOD p]) : l = k + 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, l = k + c := Nat.exists_eq_add_of_le h
  obtain rfl | hc : c = 1 ∨ c ≠ 1 := dec_em (c = 1)
  exacts [rfl, absurd (c.minFac_dvd.zero_modEq_nat.add_left k) (h0 _ (Nat.minFac_prime hc))]

/-- If `k ≢ l (mod p)` for every prime `p`, then either `l = k + 1` or `k = l + 1`. -/
lemma not_modeq_prime_imp₂ (h : ∀ p, Nat.Prime p → ¬k ≡ l [MOD p]) :
    l = k + 1 ∨ k = l + 1 := by
  obtain h0 | h0 : k ≤ l ∨ l ≤ k := Nat.le_total k l
  · left; exact not_modeq_prime_imp₁ h0 h
  · right; exact not_modeq_prime_imp₁ h0 λ p hp h1 ↦ h p hp h1.symm

/-- Let `f : ℕ → ℕ` be a function such that `f(k) ≡ f(l) (mod p)` implies `k ≡ l (mod p)`
  for any `k, l : ℕ` and for any prime `p`. Then `f = n ↦ n + k` for some `k : ℕ`. -/
lemma step3 {f : ℕ → ℕ} (hf : ∀ {p k l}, Nat.Prime p → f k ≡ f l [MOD p] → k ≡ l [MOD p]) :
    ∃ k, f = (· + k) := by
  ---- First show that `f` is injective.
  have hf0 : f.Injective := by
    -- If `f(k) = f(l)`, then `k ≡ l (mod p)` for any `p` large enough, implying `k = l`.
    intro k l h
    obtain ⟨p, hp0, hp⟩ : ∃ p > max k l, Nat.Prime p :=
      Nat.exists_infinite_primes (max k l).succ
    replace hp0 : k < p ∧ l < p := max_lt_iff.mp hp0
    calc k
      _ = k % p := (Nat.mod_eq_of_lt hp0.1).symm
      _ = l % p := hf hp (congrArg (· % p) h)
      _ = l := Nat.mod_eq_of_lt hp0.2
  ---- Now by `not_modeq_prime_imp₂`, we have `f(n + 1) - f(n) = ±1` for all `n`.
  have h (n) : f (n + 1) = f n + 1 ∨ f n = f (n + 1) + 1 := by
    refine not_modeq_prime_imp₂ λ p hp h ↦ Nat.zero_ne_one ?_
    replace h : 0 % p = 1 % p := (hf hp h).add_left_cancel'
    rwa [Nat.zero_mod, Nat.mod_eq_of_lt hp.one_lt] at h
  ---- If `f(n) = f(n + 1) + 1`, then we also get `f(n + 1) = f(n + 2) + 1`.
  have h0 {n} (hn : f n = f (n + 1) + 1) : f (n + 1) = f (n + 2) + 1 :=
    (h _).resolve_left λ h0 ↦ (hf0 (h0.trans hn.symm)).not_gt (n + 1).le_succ
  ---- Then `f` would be strictly antitone; contradiction, so `f(n + 1) = f(n) + 1`.
  replace h0 (n) : f (n + 1) = f n + 1 := by
    refine (h n).resolve_right λ hn ↦ ?_
    replace h0 (k) : f (n + k) = f (n + k + 1) + 1 := by
      induction k with | zero => exact hn | succ k k_ih => exact h0 k_ih
    replace h0 (k) : f n = f (n + k) + k := by
      induction k with | zero => rfl | succ k k_ih => ?_
      rw [k_ih, h0, Nat.add_right_comm, Nat.add_assoc, Nat.add_assoc]
    exact (h0 (f n + 1)).not_lt (Nat.le_add_left _ _)
  ---- The rest is easy.
  refine ⟨f 0, funext λ k ↦ ?_⟩
  induction k with | zero => rw [Nat.zero_add] | succ k k_ih => ?_
  rw [h0, k_ih, Nat.add_right_comm]

/-- A function `f : ℕ → ℕ` is `c`-good if and only if
  it is of the form `n ↦ n + k` for some fixed `k : ℕ`. -/
theorem good_iff : good c f ↔ ∃ k, f = (· + k) :=
  ⟨λ h ↦ step3 (map_modeq_prime_imp_modeq h), λ ⟨_, h⟩ ↦ h ▸ add_right_is_good _ _⟩





/-! ### The `ℕ+` version -/

/-- A positive integer is a square over `ℕ+` iff it is a square over `ℕ`. -/
theorem PNat_square_iff_Nat_square {m : ℕ+} : (∃ k, m = k ^ 2) ↔ (∃ k : ℕ, m = k ^ 2) := by
  ---- The `→` direction is easy.
  refine ⟨λ ⟨k, hk⟩ ↦ ⟨k, congrArg PNat.val hk⟩, ?_⟩
  ---- For the `←` direction, the missing piece is that the square root is positive.
  rintro ⟨k, hk⟩
  have hk0 : k > 0 := Nat.pos_of_mul_pos_left (m.pos.trans_eq hk)
  exact ⟨⟨k, hk0⟩, PNat.coe_injective hk⟩

/-- Given a property `P : ℕ → Prop`, `P(n)` holds for some `n : ℕ`
  iff either `P(0)` holds or `P(n)` holds for some `n : ℕ=`. -/
theorem exists_Nat_iff_zero_or_exists_PNat {P : ℕ → Prop} :
    (∃ n, P n) ↔ P 0 ∨ ∃ n : ℕ+, P n := by
  refine ⟨?_, ?_⟩
  ---- The `→` direction
  · rintro ⟨n, hn⟩
    obtain rfl | hn0 : n = 0 ∨ n > 0 := Nat.eq_zero_or_pos n
    · left; exact hn
    · right; exact ⟨⟨n, hn0⟩, hn⟩
  ---- The `←` direction
  · rintro (h | ⟨n, hn⟩)
    exacts [⟨0, h⟩, ⟨n, hn⟩]

/-- Final solution -/
theorem final_solution {f : ℕ+ → ℕ+} :
    (∀ m n : ℕ+, ∃ k, (f m + n) * (f n + m) = k ^ 2) ↔ f = id ∨ ∃ k : ℕ+, f = (· + k) := by
  let g (n : ℕ) : ℕ := (f n.succPNat).natPred
  let σ : ℕ+ ≃ ℕ := Equiv.pnatEquivNat
  ---- By transferring from `ℕ+` to `ℕ`, we reduce to two subtasks.
  calc ∀ m n : ℕ+, ∃ k, (f m + n) * (f n + m) = k ^ 2
    _ ↔ ∀ m n : ℕ+, ∃ k : ℕ, (f m + n) * (f n + m) = k ^ 2 :=
      forall₂_congr λ _ _ ↦ PNat_square_iff_Nat_square
    _ ↔ good 2 g := by
      refine σ.forall₂_congr σ (exists_congr λ k ↦ ?_)
      simp_rw [σ, g, Equiv.pnatEquivNat_apply, PNat.succPNat_natPred,
        Nat.add_add_add_comm _ _ 1 1, PNat.natPred_add_one]
    _ ↔ ∃ k : ℕ, g = (· + k) := good_iff
    _ ↔ g = id ∨ ∃ k : ℕ+, g = (· + k.val) := exists_Nat_iff_zero_or_exists_PNat
    _ ↔ f = id ∨ ∃ k : ℕ+, f = (· + k) := or_congr ?_ (exists_congr λ k ↦ ?_)
  ---- Subtask 1: show that `g = id` iff `f = id`.
  · calc g = id
    _ ↔ ∀ n : ℕ, (f n.succPNat).natPred = n := funext_iff
    _ ↔ ∀ n : ℕ, f n.succPNat = n.succPNat :=
      forall_congr' λ _ ↦ σ.apply_eq_iff_eq_symm_apply
    _ ↔ ∀ n : ℕ+, f n = n := σ.symm.forall_congr λ _ ↦ Iff.rfl
    _ ↔ f = id := funext_iff.symm
  ---- Subtask 2: show that `g = λ n ↦ n + k` iff `f = λ n ↦ n + k`.
  · calc g = (· + k.val)
      _ ↔ ∀ n : ℕ, (f n.succPNat).natPred = n + k := funext_iff
      _ ↔ ∀ n : ℕ, f n.succPNat = n.succPNat + k := by
        refine forall_congr' λ n ↦ ?_
        calc (f n.succPNat).natPred = n + ↑k
          _ ↔ f n.succPNat = (n + k).succPNat := σ.apply_eq_iff_eq_symm_apply
          _ ↔ f n.succPNat = n.succPNat + k := by
            refine Eq.congr_right (PNat.coe_injective ?_)
            rw [Nat.succPNat_coe, PNat.add_coe, Nat.succPNat_coe, Nat.succ_add]
      _ ↔ ∀ n : ℕ+, f n = n + k := σ.symm.forall_congr λ _ ↦ Iff.rfl
      _ ↔ f = (· + k) := funext_iff.symm
