/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Factors
import Mathlib.Data.PNat.Find
import Mathlib.FieldTheory.Finite.Basic

/-!
# IMO 2020 N5

Find all functions $f : ℕ⁺ → ℕ$ such that:
1. $f(n) = 0$ for some $n ∈ ℕ⁺$;
2. $f(xy) = f(x) + f(y)$ for all $x, y ∈ ℕ⁺$;
3. there are infinitely many $n ∈ ℕ⁺$ such that
  $f(a) = f(b)$ for any $a, b ∈ ℕ⁺$ with $a + b = n$.

### Answer

$n ↦ cν_p(n)$, where $c$ is a fixed positive integer and $p$ is a prime number.

### Solution

We follow Solution 1 of the official solution.
See [here](https://www.imo-official.org/problems/IMO2020SL.pdf).

### Generalization

It is possible to generalize $ℕ$ to any (additive) abelian monoid $M$.
The answer functions are (again) of the form $n ↦ ν_p(n) c$ if $M$ is torsion-free.
However, this is not the case if $M$ is not torsion-free.
See `Generalizations/IMO2020N5.lean` for more details.

### TODO

Implement the generalization.
-/

namespace IMOSL
namespace IMO2020N5

/-- Given `f : ℕ+ → α` and `n : ℕ`, we say that `n` is `f`-*nice*
  if `f(a) = f(b)` whenever `a + b = n`. -/
def nice (f : ℕ+ → α) (n : ℕ+) := ∀ a b, a + b = n → f a = f b

/-- The functional equation to be solved. -/
structure good (f : ℕ+ → ℕ) : Prop where
  nontrivial : ∃ n, 0 < f n
  map_mul (x y) : f (x * y) = f x + f y
  infinite_nice (N) : ∃ n ≥ N, nice f n



/-! ### Construction of good functions -/

/-- `p`-adic valuation of `n : ℕ+` is equal to `0` if and only if `p ∤ n`.
  TODO: This might be `mathlib`-worthy, so remove this lemma if it goes to `mathlib`. -/
lemma factorMultiset_count_eq_zero_iff {p : Nat.Primes} {n : ℕ+} :
    Multiset.count p n.factorMultiset = 0 ↔ ¬(p : ℕ+) ∣ n := by
  rw [← pow_one (p : ℕ+), PNat.count_factorMultiset, Nat.not_le, Nat.lt_one_iff]

/-- If `a, b : ℕ⁺` and `a + b` is a power of `p`, then `ν_p(a) = ν_p(b)`. -/
theorem padic_eq_of_add_eq_ppow {p : Nat.Primes} {N} {a b : ℕ+} (h : a + b = p ^ N) :
    a.factorMultiset.count p = b.factorMultiset.count p := by
  ---- Induction on `N`, but the base case `N = 0` is impossible, as `a + b > 1`.
  induction N generalizing a b with
  | zero => exact absurd (a.one_le.trans_lt (a.lt_add_right b)) h.not_gt
  | succ N N_ih => ?_
  ---- Auxiliary statement: `p ∣ a + b` over `ℕ`.
  have X : ((p : ℕ+) : ℕ) ∣ a + b := by
    rw [← PNat.add_coe, h, ← PNat.dvd_iff]
    exact dvd_pow_self _ N.succ_ne_zero
  ---- Divide into two cases: `p ∣ a` and `p ∤ a`.
  obtain ⟨a', rfl⟩ | ha : (p : ℕ+) ∣ a ∨ ¬(p : ℕ+) ∣ a := em _
  ---- Case 1: `p ∣ a`; then `p ∣ b` and apply induction hypothesis.
  · obtain ⟨b', rfl⟩ : (p : ℕ+) ∣ b :=
      PNat.dvd_iff.mpr ((Nat.dvd_add_right ⟨a', rfl⟩).mp X)
    rw [← mul_add, pow_succ', mul_right_inj] at h
    rw [PNat.factorMultiset_mul, PNat.factorMultiset_mul,
      Multiset.count_add, Multiset.count_add, N_ih h]
  ---- Case 2: `p ∤ a`; then `p ∤ b` and both sides are zero.
  · rw [factorMultiset_count_eq_zero_iff.mpr ha, eq_comm,
      factorMultiset_count_eq_zero_iff, PNat.dvd_iff]
    refine λ hb ↦ ha ?_
    rwa [PNat.dvd_iff, Nat.dvd_add_iff_left hb]

/-- Functions of the form `n ↦ c ν_p(n)` are good. -/
theorem padic_mul_is_good (c : ℕ+) (p : Nat.Primes) :
    good (λ n ↦ c * n.factorMultiset.count p) :=
  { nontrivial := ⟨p, Nat.mul_pos c.pos <| (PNat.count_factorMultiset _ _ _).mp (by simp)⟩
    map_mul x y := by rw [PNat.factorMultiset_mul, Multiset.count_add, Nat.mul_add]
    infinite_nice N := ⟨p ^ N.1, (Nat.lt_pow_self p.2.one_lt).le,
      λ a b h ↦ congrArg (c.1 * ·) (padic_eq_of_add_eq_ppow h)⟩ }



/-! ### Properties of good functions -/

namespace good

variable {f : ℕ+ → ℕ} (hf : good f)
include hf

/-- `f(1) = 0`. -/
theorem map_one : f 1 = 0 :=
  Nat.left_eq_add.mp (hf.map_mul 1 1)

/-- `f(n^k) = f(n) k`. -/
theorem map_pow (n k) : f (n ^ k) = f n * k := by
  induction k with | zero => exact hf.map_one | succ k hk => ?_
  rw [pow_succ, Nat.mul_succ, hf.map_mul, hk]

/-- If `n` is `f`-nice and `d ∣ n`, then `d` if `f`-nice. -/
theorem nice_of_dvd_nice (hn : nice f n) (hd : d ∣ n) : nice f d := by
  rcases hd with ⟨k, rfl⟩
  rintro a b rfl
  specialize hn (a * k) (b * k) (add_mul a b k).symm
  rwa [hf.map_mul, hf.map_mul, Nat.add_right_cancel_iff] at hn


/-- The smallest `p : ℕ+` such that `f(p) > 0`, named as such because it is prime. -/
def base_prime_PNat : ℕ+ := PNat.find hf.nontrivial

/-- Specification of `base_prime_PNat`. -/
theorem base_prime_PNat_spec : 0 < f hf.base_prime_PNat :=
  PNat.find_spec hf.nontrivial

/-- Minimality of `base_prime_PNat`. -/
theorem base_prime_PNat_min (h : a < hf.base_prime_PNat) : f a = 0 :=
  Nat.eq_zero_of_not_pos (PNat.find_min hf.nontrivial h)

/-- Minimality of `base_prime_PNat`. -/
theorem base_prime_PNat_min' (h : 0 < f a) : hf.base_prime_PNat ≤ a :=
  PNat.find_min' hf.nontrivial h

/-- `base_prime_PNat` is prime. -/
theorem base_prime_PNat_is_prime : hf.base_prime_PNat.Prime := by
  ---- Let `q` be a prime factor of `p = base_prime_PNat`.
  obtain ⟨q, hq, h⟩ : ∃ q : ℕ+, q.Prime ∧ q ∣ hf.base_prime_PNat :=
    PNat.exists_prime_and_dvd λ h ↦ hf.base_prime_PNat_spec.ne (by rw [h, hf.map_one])
  ---- It suffices to show that `q ≥ p`, since we know `q ≤ p`.
  suffices hf.base_prime_PNat ≤ q by rwa [this.antisymm (PNat.le_of_dvd h)]
  ---- Factorize `p = qr` and infer that `f(r) = 0` since `r < p`.
  rcases h with ⟨r, h⟩
  have h0 : f r = 0 :=
    hf.base_prime_PNat_min ((lt_mul_of_one_lt_left' r hq.one_lt).trans_eq h.symm)
  ---- Thus `f(q) = f(q) + f(r) = f(qr) = f(p) > 0`, so minimality yields `q ≥ p`.
  replace hq : 0 < f hf.base_prime_PNat := hf.base_prime_PNat_spec
  rw [h, hf.map_mul, h0] at hq
  exact hf.base_prime_PNat_min' hq

/-- The smallest `p : ℕ+` such that `f(p) > 0`, as a `Nat.Primes`.
  Use `base_prime_PNat` for actual computations instead. -/
def base_prime : Nat.Primes := ⟨hf.base_prime_PNat, hf.base_prime_PNat_is_prime⟩


/-- If `d` is `f`-nice and `p ≤ d`, then `p ∣ d`. -/
theorem base_prime_dvd_of_le_of_nice (hd : hf.base_prime_PNat ≤ d) (hd0 : nice f d) :
    hf.base_prime_PNat ∣ d := by
  set p : ℕ+ := hf.base_prime_PNat
  ---- If `d % p = 0`, we are done, so assume that `d % p > 0` (`%` over `ℕ`).
  obtain hd1 | hd1 : d.1 % p = 0 ∨ 0 < d.1 % p := Nat.eq_zero_or_pos _
  · rwa [PNat.dvd_iff, Nat.dvd_iff_mod_eq_zero]
  ---- Work out the equation `d = pq + r` over `ℕ+`, where `q = d / p` and `r = d % p`.
  lift d.val % p to ℕ+ using hd1 with r hr
  lift d.val / p to ℕ+ using Nat.div_pos hd p.pos with q hq
  have h : p * q + r = d := by
    rw [← PNat.coe_inj, PNat.add_coe, hr, PNat.mul_coe, hq, Nat.div_add_mod]
  ---- Since `d` is `f`-nice, we get `f(r) = f(pq) ≥ f(p) > 0`.
  clear hq; replace h : 0 < f r := by
    simpa only [← hd0 _ _ h, hf.map_mul] using Nat.add_pos_left (base_prime_PNat_spec hf) _
  ---- But `f(p) > 0`; contradiction.
  refine absurd (hf.base_prime_PNat_min ?_) h.ne.symm
  simpa only [← PNat.coe_lt_coe, hr] using Nat.mod_lt _ p.pos

/-- If `d` is `f`-nice and `p^k ≤ d`, then `p^k ∣ d`. -/
theorem base_prime_pow_dvd_of_le_of_nice
    (hd : hf.base_prime_PNat ^ k ≤ d) (hd0 : nice f d) :
    hf.base_prime_PNat ^ k ∣ d := by
  ---- Induction on `k`, but the base case is trivial.
  induction k generalizing d with | zero => exact one_dvd _ | succ k hk => ?_
  ---- Since `p ≤ p^{k + 1} ≤ d`, previous step gives `p ∣ d`. Write `d = pd'`.
  obtain ⟨d', rfl⟩ : hf.base_prime_PNat ∣ d :=
    hf.base_prime_dvd_of_le_of_nice
      ((PNat.le_of_dvd (dvd_pow_self _ k.succ_ne_zero)).trans hd) hd0
  ---- Now `d'` is `f`-nice and `p^k ≤ d'`.
  replace hd : hf.base_prime_PNat ^ k ≤ d' :=
    le_of_mul_le_mul_left' ((pow_succ' _ _).symm.trans_le hd)
  replace hd0 : nice f d' := hf.nice_of_dvd_nice hd0 (dvd_mul_left _ _)
  ---- By induction hypothesis, `p^k ∣ d'`; which gives `p^{k + 1} ∣ d`.
  simpa only [pow_succ'] using mul_dvd_mul_left _ (hk hd hd0)

/-- `p^k` is `f`-nice for any `k ≥ 0`. -/
theorem base_prime_pow_is_nice (k) : nice f (hf.base_prime_PNat ^ k) := by
  ---- Pick any `n ≥ p^k` that is `f`-nice. Then `p^k ∣ n`, so `p^k` is `f`-nice too.
  obtain ⟨n, hn, hn0⟩ : ∃ n ≥ hf.base_prime_PNat ^ k, nice f n := hf.infinite_nice _
  exact hf.nice_of_dvd_nice hn0 (hf.base_prime_pow_dvd_of_le_of_nice hn hn0)

/-- If `gcd(n, p) = 1`, then `f(n) = 0`. -/
theorem map_eq_zero_of_coprime_base_prime (hn : ¬hf.base_prime_PNat ∣ n) : f n = 0 := by
  ---- Assume `n > 1`; we are done otherwise.
  obtain rfl | hn0 : n = 1 ∨ 1 < n := n.one_le.eq_or_lt'
  · exact hf.map_one
  ---- Write `p^{φ(n)} = x + 1` for some `x ∈ ℕ+`.
  obtain ⟨x, hx⟩ : ∃ x : ℕ+, hf.base_prime_PNat ^ n.1.totient = x + 1 := by
    apply PNat.exists_eq_succ_of_ne_one
    rw [Ne, pow_eq_one_iff (n.1.totient_pos.mpr n.pos).ne.symm]
    exact hf.base_prime_PNat_is_prime.ne_one
  ---- Deduce `n ∣ x` and write `x = nq`, `p^{φ(n)} = nq + 1` for some `q ∈ ℕ+`.
  obtain ⟨q, rfl⟩ : n ∣ x := by
    rw [PNat.dvd_iff, ← Nat.modEq_zero_iff_dvd]
    apply Nat.ModEq.add_right_cancel' ((1 : ℕ+) : ℕ)
    rw [← PNat.add_coe, ← hx, PNat.pow_coe]
    apply Nat.ModEq.pow_totient
    rwa [hf.base_prime_PNat_is_prime.coprime_iff_not_dvd, ← PNat.dvd_iff]
  ---- Since `p^k` is `f`-good, we get `f(n) ≤ f(nq) = f(1) = 0`, so `f(n) = 0`.
  refine (Nat.eq_zero_of_add_eq_zero (m := f q) ?_).1
  rw [← hf.map_mul, hf.base_prime_pow_is_nice _ _ _ hx.symm, hf.map_one]

/-- The main result: `f(n) = f(p) ν_p(n)` for all `n : ℕ+`, where `p = base_prime`. -/
theorem eq_map_base_prime_mul_padic_base_prime (n : ℕ+) :
    f n = f hf.base_prime_PNat * n.factorMultiset.count hf.base_prime := by
  let p : Nat.Primes := hf.base_prime
  let ν : ℕ := n.factorMultiset.count p
  ---- Factorize `n` as `p^{ν_p(n)} k` for some `k : ℕ+`.
  obtain ⟨k, hk⟩ : (p : ℕ+) ^ ν ∣ n :=
    (n.count_factorMultiset _ _).mpr (Nat.le_refl _)
  ---- Get `p ∤ k` from the definition of `p`-adic valuation.
  have h : ¬(p : ℕ+) ∣ k := by
    intro h; replace h : (p : ℕ+) ^ (ν + 1) ∣ p ^ ν * k := mul_dvd_mul_left _ h
    rw [← hk, PNat.count_factorMultiset, ← Nat.not_lt, Nat.lt_add_right_iff_pos] at h
    exact h Nat.one_pos
  ---- Then `f(n) = f(p) ν_p(n) + f(k) = f(p) ν_p(n)`.
  simpa only [hf.map_mul, hf.map_pow, Nat.add_zero,
    hf.map_eq_zero_of_coprime_base_prime h] using congrArg f hk

end good



/-! ### Summary -/

/-- Final solution -/
theorem final_solution {f : ℕ+ → ℕ} :
    good f ↔ ∃ (c : ℕ+) (p : Nat.Primes), f = λ n : ℕ+ ↦ c * n.factorMultiset.count p :=
  ⟨λ hf ↦ ⟨⟨f hf.base_prime, hf.base_prime_PNat_spec⟩,
    hf.base_prime, funext hf.eq_map_base_prime_mul_padic_base_prime⟩,
  λ ⟨c, p, hf⟩ ↦ hf ▸ padic_mul_is_good c p⟩
