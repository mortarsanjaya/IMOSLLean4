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

/-- Extra lemma: given `n : ℕ+` such that `n > 1`, we have `n - 1 < n` -/
lemma PNat_pred_lt_self {n : ℕ+} (h : 1 < n) : n - 1 < n :=
  ((n - 1).lt_add_left 1).trans_eq (PNat.add_sub_of_lt h)

variable (p : Nat.Primes)

/-- The `p`-adic valuation over `ℕ+` -/
def padicValPNat (n : ℕ+) : ℕ := n.factorMultiset.count p



namespace padicValPNat

lemma one : padicValPNat p 1 = 0 := rfl

lemma mul (x y : ℕ+) :
    padicValPNat p (x * y) = padicValPNat p x + padicValPNat p y := by
  rw [padicValPNat, padicValPNat, padicValPNat, factorMultiset_mul, count_add]

lemma pow (n : ℕ+) (k : ℕ) :
    padicValPNat p (n ^ k) = k * padicValPNat p n := by
  rw [padicValPNat, padicValPNat, ← count_nsmul, ← factorMultiset_pow]; rfl

lemma self : padicValPNat p p = 1 := by
  rw [padicValPNat, factorMultiset_ofPrime,
    PrimeMultiset.ofPrime, count_singleton_self p]

lemma self_pow (k : ℕ) : padicValPNat p (p ^ k) = k := by
  rw [pow, self, mul_one]

lemma spec (n : ℕ+) (k : ℕ) : (p : ℕ+) ^ k ∣ n ↔ k ≤ padicValPNat p n := by
  rw [padicValPNat, ← count_factorMultiset]; rfl

theorem replicate_add_factor_filter (n : ℕ+) :
    replicate (padicValPNat p n) p + n.factorMultiset.filter (Ne p)
      = n.factorMultiset := by
  rw [padicValPNat, ← filter_eq, filter_add_not]

lemma pos_iff_dvd {n : ℕ+} : 0 < padicValPNat p n ↔ (p : ℕ+) ∣ n := by
  rw [← pow_one (p : ℕ+), spec]; rfl

lemma zero_iff_not_dvd {n : ℕ+} : padicValPNat p n = 0 ↔ ¬(p : ℕ+) ∣ n := by
  rw [← pos_iff_dvd, Nat.not_lt, Nat.le_zero]

lemma zero_of_not_dvd (h : ¬(p : ℕ+) ∣ n) : padicValPNat p n = 0 :=
  (zero_iff_not_dvd p).mpr h

theorem zero_of_lt (h : n < (p : ℕ+)) : padicValPNat p n = 0 :=
  zero_of_not_dvd p (mt le_of_dvd h.not_le)

theorem pred : padicValPNat p (p - 1) = 0 :=
  zero_of_lt p (PNat_pred_lt_self p.2.one_lt)

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
    padicComplPNat p (n ^ k) = padicComplPNat p n ^ k := by
  rw [padicComplPNat, padicComplPNat]
  change _ = Pow.pow _ _
  rw [← PrimeMultiset.prod_smul, ← filter_nsmul, ← factorMultiset_pow]
  rfl

lemma self : padicComplPNat p p = 1 := by
  rw [padicComplPNat, factorMultiset_ofPrime, PrimeMultiset.ofPrime,
    filter_singleton, if_neg (not_ne_iff.mpr rfl)]; rfl

lemma not_dvd (n : ℕ+) : ¬(p : ℕ+) ∣ padicComplPNat p n := by
  rw [padicComplPNat, ← factorMultiset_le_iff', factorMultiset_ofPrime,
    PrimeMultiset.ofPrime, singleton_le, mem_filter]
  intro h; exact h.2 rfl

lemma coprimeNat (n : ℕ+) : (padicComplPNat p n : ℕ).Coprime p := by
  rw [Nat.coprime_comm, p.2.coprime_iff_not_dvd, ← p.coe_pnat_nat, ← dvd_iff]
  exact not_dvd p n

theorem self_pow_Val_mul (n : ℕ+) :
    (p : ℕ+) ^ padicValPNat p n * padicComplPNat p n = n := by
  change Pow.pow _ _ * _ = n
  rw [← PrimeMultiset.prod_ofPrime, ← PrimeMultiset.prod_smul,
    padicComplPNat, ← PrimeMultiset.prod_add, PrimeMultiset.ofPrime,
    nsmul_singleton, padicValPNat.replicate_add_factor_filter]
  exact prod_factorMultiset n

theorem factorMultiset (n : ℕ+) :
    factorMultiset (padicComplPNat p n) = filter (Ne p) (factorMultiset n) :=
  PrimeMultiset.factorMultiset_prod _

theorem apply_eq_iff (n k : ℕ+) :
    padicComplPNat p n = k ↔ n.factorMultiset.filter (Ne p) = k.factorMultiset :=
  factorMultisetEquiv.symm_apply_eq (x := n.factorMultiset.filter (Ne p)) (y := k)

theorem fixedPt_iff_not_dvd : padicComplPNat p n = n ↔ ¬(p : ℕ+) ∣ n := by
  rw [← padicValPNat.zero_iff_not_dvd, padicValPNat,
    count_eq_zero, apply_eq_iff, filter_eq_self]
  -- Hack-ish, but the Multiset version does not exist
  exact List.forall_mem_ne

theorem fixedPt_of_lt (h : n < (p : ℕ+)) : padicComplPNat p n = n :=
  (fixedPt_iff_not_dvd p).mpr (mt le_of_dvd h.not_le)

theorem pred : padicComplPNat p (p - 1) = p - 1 :=
  fixedPt_of_lt p (PNat_pred_lt_self p.2.one_lt)

end padicComplPNat
