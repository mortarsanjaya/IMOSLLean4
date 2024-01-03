/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Factors

/-!
# p-adic Valuation and Complement in `ℕ+`

Let `n p : ℕ+` with `p` prime.
The *`p`-adic complement* of `n` is defined as `n/p^ν_p(n)`,
  where `ν_p(n)` is the `p`-adic valuation of `n`.
It is the largest factor of `n` that is coprime with `p`.

(This is an `ℕ+` version of `padicValNat` and `ord_compl`.)
-/

namespace IMOSL
namespace IMO2020N5

open PNat Multiset

variable (p : Nat.Primes)

/-- The `p`-adic valuation over `ℕ+` -/
def padicValPNat (n : ℕ+) : ℕ := n.factorMultiset.count p



namespace padicValPNat

lemma one : padicValPNat p 1 = 0 := rfl

lemma mul (x y : ℕ+) :
    padicValPNat p (x * y) = padicValPNat p x + padicValPNat p y := by
  rw [padicValPNat, padicValPNat, padicValPNat,
    factorMultiset_mul, count_add]

lemma pow (n : ℕ+) (k : ℕ) :
    padicValPNat p (Pow.pow n k) = k * padicValPNat p n := by
  rw [padicValPNat, padicValPNat, factorMultiset_pow, count_nsmul]

lemma self : padicValPNat p p = 1 := by
  rw [padicValPNat, factorMultiset_ofPrime,
    PrimeMultiset.ofPrime, count_singleton_self p]

lemma spec (n : ℕ+) (k : ℕ) :
    Pow.pow (p : ℕ+) k ∣ n ↔ k ≤ padicValPNat p n := by
  rw [count_factorMultiset, padicValPNat]

theorem replicate_add_factor_filter (n : ℕ+) :
    replicate (padicValPNat p n) p + n.factorMultiset.filter (Ne p)
      = n.factorMultiset := by
  rw [padicValPNat, ← filter_eq, filter_add_not]

end padicValPNat





/-- The `p`-adic complement over `ℕ+` -/
def padicComplPNat (n : ℕ+) : ℕ+ :=
  PrimeMultiset.prod (n.factorMultiset.filter (Ne p))



namespace padicComplPNat

lemma one : padicComplPNat p 1 = 1 := rfl

lemma mul (x y : ℕ+) :
    padicComplPNat p (x * y) = padicComplPNat p x * padicComplPNat p y := by
  rw [padicComplPNat, padicComplPNat, padicComplPNat,
    factorMultiset_mul, filter_add, PrimeMultiset.prod_add]

lemma pow (n : ℕ+) (k : ℕ) :
    padicComplPNat p (Pow.pow n k) = Pow.pow (padicComplPNat p n) k := by
  rw [padicComplPNat, padicComplPNat, factorMultiset_pow,
    filter_nsmul, PrimeMultiset.prod_smul]

lemma self : padicComplPNat p p = 1 := by
  rw [padicComplPNat, factorMultiset_ofPrime, PrimeMultiset.ofPrime,
    filter_singleton, if_neg (not_ne_iff.mpr rfl)]; rfl

lemma not_dvd (n : ℕ+) : ¬(p : ℕ+) ∣ padicComplPNat p n := by
  rw [padicComplPNat, ← factorMultiset_le_iff', factorMultiset_ofPrime,
    PrimeMultiset.ofPrime, singleton_le, mem_filter]
  intro h; exact h.2 rfl

lemma coprimeNat (n : ℕ+) :
    (padicComplPNat p n : ℕ).Coprime p := by
  rw [Nat.coprime_comm, p.2.coprime_iff_not_dvd, ← p.coe_pnat_nat, ← dvd_iff]
  exact not_dvd p n

theorem mul_p_pow_Val (n : ℕ+) :
    Pow.pow (p : ℕ+) (padicValPNat p n) * padicComplPNat p n = n := by
  rw [← PrimeMultiset.prod_ofPrime, ← PrimeMultiset.prod_smul,
    padicComplPNat, ← PrimeMultiset.prod_add, PrimeMultiset.ofPrime,
    nsmul_singleton, padicValPNat.replicate_add_factor_filter]
  exact prod_factorMultiset n

end padicComplPNat
