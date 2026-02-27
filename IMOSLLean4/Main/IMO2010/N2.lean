/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.NumberTheory.Multiplicity

/-!
# IMO 2010 N2

Find all pairs $(m, n) ∈ ℤ × ℕ$ such that
$$ m^2 + 2 \cdot 3^n = m(2^{n + 1} - 1). $$

### Answer

$(6, 3), (9, 3), (9, 5), (54, 5)$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2010SL.pdf).
While we allow $m$ to be negative, the given equation implies that $m$ is non-negative.
For lower bounding $\min\{p, q\}$, we use the LTE (lifting the exponent) lemma instead,
  giving us the stronger inequality $\min\{p, q\} ≤ \log_3(p + q + 1)$.
-/

namespace IMOSL
namespace IMO2010N2

/-- A pair `(m, n)` is called *good* if `m^2 + 2 3^n = m(2^{n + 1} - 1)`. -/
def good (m : ℤ) (n : ℕ) := m ^ 2 + 2 * 3 ^ n = m * (2 ^ (n + 1) - 1)

/-- A pair `(p, q)` is caled *nice* if `3^p + 2 3^q = 2^{p + q + 1} - 1`. -/
def nice (p q : ℕ) := (3 : ℤ) ^ p + 2 * 3 ^ q = 2 ^ (p + q + 1) - 1

/-- Given a nice pair `(p, q)`, the pair `(3^p, p + q)` is good. -/
theorem nice.good_three_pow_left (h : nice p q) : good (3 ^ p) (p + q) := by
  rw [good, ← h, sq, Int.pow_add, Int.mul_left_comm, Int.mul_add]

/-- Given a nice pair `(p, q)`, the pair `(2 3^q, p + q)` is good. -/
theorem nice.good_two_mul_three_pow_right (h : nice p q) : good (2 * 3 ^ q) (p + q) := by
  rw [good, ← h, sq, Int.pow_add, Int.mul_left_comm 2,
    Int.add_comm, ← Int.add_mul, Int.mul_comm]

/-- A pair `(m, n)` is good iff there exists a nice pair `(p, q)`
  such that `n = p + q` and either `m = 3^p` or `m = 2 3^q`. -/
theorem good_iff_nice :
    good m n ↔ ∃ p q, nice p q ∧ n = p + q ∧ (m = 3 ^ p ∨ m = 2 * 3 ^ q) := by
  ---- The `←` direction has been proved via two lemmas.
  refine Iff.symm ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · rcases h with ⟨p, q, h, rfl, rfl | rfl⟩
    exacts [h.good_three_pow_left, h.good_two_mul_three_pow_right]
  ---- For the `→` direction, first note that `m ≥ 0`.
  have h0 (n : ℕ) : 0 < (3 : ℤ) ^ n := Int.pow_pos three_pos
  have h1 (n : ℕ) : 0 < (2 : ℤ) * 3 ^ n := Int.mul_pos two_pos (h0 n)
  have hm : 0 < m * (2 ^ (n + 1) - 1) := calc
    _ < m ^ 2 + 2 * 3 ^ n := Int.add_pos_of_nonneg_of_pos (Int.sq_nonnneg m) (h1 n)
    _ = m * (2 ^ (n + 1) - 1) := h
  replace hm : 0 ≤ m := by
    have h0 : (1 : ℤ) < 2 ^ (n + 1) := one_lt_pow₀ one_lt_two (Nat.succ_ne_zero n)
    exact Int.le_of_lt (Int.pos_of_mul_pos_left hm (sub_pos_of_lt h0))
  lift m to ℕ using hm
  ---- Next, note that `m ∣ 2 3^n`.
  have h2 {m n : ℕ} (hmn : m ∣ 3 ^ n) : ∃ k ≤ n, m = 3 ^ k :=
    (Nat.dvd_prime_pow Nat.prime_three).mp hmn
  have hmn : (m : ℤ) ∣ 2 * 3 ^ n := by
    refine ⟨2 ^ (n + 1) - 1 - m, ?_⟩
    rw [eq_sub_of_add_eq' h, sq, ← mul_sub]
  replace hmn : m ∣ 2 * 3 ^ n := by
    rwa [← Int.natCast_dvd_natCast, Int.natCast_mul, Int.natCast_pow]
  ---- If `m` is even then `m = 2 3^q` for some `q ≤ n`; pick `p = n - q`.
  obtain ⟨k, rfl⟩ | hm : 2 ∣ m ∨ ¬2 ∣ m := dec_em _
  · replace hmn : ∃ q ≤ n, k = 3 ^ q := h2 (Nat.dvd_of_mul_dvd_mul_left Nat.two_pos hmn)
    rcases hmn with ⟨q, hq, rfl⟩
    replace hq : n = n - q + q := (Nat.sub_add_cancel hq).symm
    refine ⟨n - q, q, ?_, hq, Or.inr rfl⟩
    replace h :
        (2 : ℤ) * 3 ^ q * (3 ^ (n - q) + 2 * 3 ^ q)
          = 2 * 3 ^ q * (2 ^ (n - q + q + 1) - 1) :=
      calc (2 : ℤ) * 3 ^ q * (3 ^ (n - q) + 2 * 3 ^ q)
      _ = (2 * 3 ^ q) ^ 2 + 2 * 3 ^ n := by
        rw [Int.mul_add, sq, Int.mul_assoc, ← Int.pow_add, Nat.add_comm, ← hq, Int.add_comm]
      _ = 2 * 3 ^ q * (2 ^ (n + 1) - 1) := h
      _ = 2 * 3 ^ q * (2 ^ (n - q + q + 1) - 1) := by rw [← hq]
    exact Int.eq_of_mul_eq_mul_left (h := h) (h1 q).ne.symm
  ---- If `m` is odd then `m = 3^p` for some `p ≤ n`; pick `q = n - p`.
  · replace hmn : ∃ p ≤ n, m = 3 ^ p :=
      h2 (((Nat.prime_two.coprime_iff_not_dvd).mpr hm).symm.dvd_of_dvd_mul_left hmn)
    rcases hmn with ⟨p, hp, rfl⟩
    replace hp : n = p + (n - p) := (Nat.add_sub_of_le hp).symm
    refine ⟨p, n - p, ?_, hp, Or.inl rfl⟩
    replace h :
        (3 : ℤ) ^ p * (3 ^ p + 2 * 3 ^ (n - p)) = 3 ^ p * (2 ^ (p + (n - p) + 1) - 1) :=
      calc (3 : ℤ) ^ p * (3 ^ p + 2 * 3 ^ (n - p))
      _ = (3 ^ p) ^ 2 + 2 * 3 ^ n := by
        rw [Int.mul_add, ← sq, Int.mul_left_comm, ← Int.pow_add, ← hp]
      _ = 3 ^ p * (2 ^ (n + 1) - 1) := h
      _ = 3 ^ p * (2 ^ (p + (n - p) + 1) - 1) := by rw [← hp]
    exact Int.eq_of_mul_eq_mul_left (h0 p).ne.symm h

/-- If `(p, q)` is a nice pair, then `p + q ≤ 3 min{p, q} + 1`. -/
theorem nice.add_le_three_mul_min_add_one (h : nice p q) : p + q ≤ 3 * min p q + 1 := by
  ---- This is done via bounding over the real place.
  have X (n : ℕ) : 0 ≤ (3 : ℤ) ^ n := Int.pow_nonneg (Int.natCast_nonneg 3)
  have X0 : (0 : ℤ) < 8 := by decide
  ---- First we have the easy bound `3^{max{p, q}} ≤ 3^p + 2 3^q`.
  have h0 : (3 : ℤ) ^ max p q ≤ 3 ^ p + 2 * 3 ^ q := by
    obtain h0 | h0 : max p q = p ∨ max p q = q := Std.MaxEqOr.max_eq_or p q
    · rw [h0, le_add_iff_nonneg_right]
      exact Int.mul_nonneg (Int.natCast_nonneg 2) (X _)
    · rw [h0, Int.two_mul, ← Int.add_assoc, le_add_iff_nonneg_left]
      exact Int.add_nonneg (X _) (X _)
  ---- Combining with the fact that `(p, q)` is nice, we get `3^{max{p, q}} ≤ 2^{p + q + 1}`.
  replace h0 : (3 : ℤ) ^ max p q < 2 ^ (p + q + 1) :=
    calc (3 : ℤ) ^ max p q
    _ ≤ 3 ^ p + 2 * 3 ^ q := h0
    _ = 2 ^ (p + q + 1) - 1 := h
    _ < 2 ^ (p + q + 1) := Int.sub_one_lt_of_le (Int.le_refl _)
  ---- Since `2^3 = 8 < 9 = 3^2`, we have `8^{3 max{p, q}} < 8^{2(p + q + 1)}`.
  replace h0 : (8 : ℤ) ^ (3 * max p q) < (8 : ℤ) ^ (2 * (p + q) + 2) :=
    calc (8 : ℤ) ^ (3 * max p q)
    _ ≤ (3 ^ 2 : ℤ) ^ (3 * max p q) := pow_le_pow_left₀ X0.le (by decide) _
    _ = ((3 : ℤ) ^ max p q) ^ 6 := by
      rw [← Int.pow_mul, ← Nat.mul_assoc, Nat.mul_comm, Int.pow_mul]
    _ < (2 ^ (p + q + 1)) ^ 6 := pow_lt_pow_left₀ h0 (X _) (by decide)
    _ = (2 ^ 3 : ℤ) ^ (2 * (p + q + 1)) := by
      rw [← Int.pow_mul, Nat.mul_comm, Nat.mul_assoc 3 2, Int.pow_mul]
  ---- Thus `3 max{p, q} < 2(p + q + 1)` and the rest follows by rearrangement.
  replace X0 : (1 : ℤ) < 8 := by decide
  replace h0 : max p q ≤ 2 * min p q + 1 := by
    rwa [pow_lt_pow_iff_right₀ X0, ← max_add_min p q, Nat.mul_add, Nat.add_assoc,
      Nat.succ_mul, Nat.add_lt_add_iff_left, Nat.lt_succ_iff] at h0
  rwa [← max_add_min p q, Nat.succ_mul, Nat.add_right_comm, Nat.add_le_add_iff_right]

/-- If `(p, q)` is a nice pair, then `min{p, q} > 0`. -/
theorem nice.min_pos (h : nice p q) : min p q > 0 := by
  ---- If not, the previous bound gives `p + q ≤ 1`.
  refine Nat.pos_of_ne_zero λ h0 ↦ ?_
  replace h0 : p + q ≤ 1 := calc
    _ ≤ 3 * min p q + 1 := h.add_le_three_mul_min_add_one
    _ = 1 := congrArg (3 * · + 1) h0
  ---- Bashing yields contradiction.
  have h1 : q ∈ Finset.range 2 := Finset.mem_range_succ_iff.mpr (Nat.le_of_add_left_le h0)
  replace h0 : p ∈ Finset.range (2 - q) := by
    rwa [Finset.mem_range, Nat.lt_sub_iff_add_lt, Nat.lt_succ_iff]
  revert h; revert p; revert q
  unfold nice; decide

/-- If `3 ∣ 2^n - 1`, then `2 ∣ n`. -/
theorem two_dvd_of_three_dvd_pow_sub_one (h : (3 : ℤ) ∣ 2 ^ n - 1) : 2 ∣ n := by
  refine Decidable.by_contra λ h0 ↦ ?_
  replace h0 : n % 2 = 1 := Nat.two_dvd_ne_zero.mp h0
  replace h : 2 ≡ 1 [MOD 3] := calc
    _ = 1 ^ (n / 2) * 2 := congrArg (· * 2) (Nat.one_pow _).symm
    _ ≡ 4 ^ (n / 2) * 2 [MOD 3] :=
      have h1 : 1 ≡ 4 [MOD 3] := rfl
      (h1.pow _).mul_right 2
    _ = 2 ^ (2 * (n / 2) + n % 2) := by rw [h0, Nat.pow_succ, Nat.pow_mul]
    _ = 2 ^ n := congrArg (2 ^ ·) (Nat.div_add_mod n 2)
    _ ≡ 1 [MOD 3] := (Nat.modEq_of_dvd h).symm
  revert h; decide

/-- We have `ν_3(4^r - 1) = r + 1` for any `r : ℕ`. -/
theorem emultiplicity_three_four_pow_sub_one (r : ℕ) :
    emultiplicity (3 : ℤ) (4 ^ r - 1) = emultiplicity 3 r + 1 :=
  calc emultiplicity (3 : ℤ) (4 ^ r - 1)
  _ = emultiplicity (3 : ℤ) (4 ^ r - 1 ^ r) := by rw [Int.one_pow]
  _ = emultiplicity (3 : ℤ) (4 - 1) + emultiplicity 3 r :=
    Int.emultiplicity_pow_sub_pow Nat.prime_three ⟨1, rfl⟩ (dvd_refl 3) (by decide) _
  _ = 1 + emultiplicity 3 r :=
    congrArg (· + _) (FiniteMultiplicity.emultiplicity_self ⟨2, by decide⟩)
  _ = emultiplicity 3 r + 1 := add_comm _ _

/-- This lemma is `emultiplicity_three_four_pow_sub_one` with `multiplicity` version. -/
theorem multiplicity_three_four_pow_sub_one {r : ℕ} (hr : r ≠ 0) :
    multiplicity (3 : ℤ) (4 ^ r - 1) = multiplicity 3 r + 1 := by
  have h : 3 ≠ 1 := by decide
  have hr0 : (4 : ℤ) ^ r - 1 > 0 := sub_pos_of_lt (one_lt_pow₀ (by decide) hr)
  replace hr0 : FiniteMultiplicity (3 : ℤ) (4 ^ r - 1) :=
    Int.finiteMultiplicity_iff.mpr ⟨h, hr0.ne.symm⟩
  replace hr : FiniteMultiplicity 3 r := by
    refine Nat.finiteMultiplicity_iff.mpr ⟨h, Nat.pos_of_ne_zero hr⟩
  rw [← ENat.coe_inj, ← hr0.emultiplicity_eq_multiplicity, Nat.cast_succ,
    ← hr.emultiplicity_eq_multiplicity, emultiplicity_three_four_pow_sub_one]

/-- If `(p, q)` is a nice pair, then `p + q + 1 = 2r`
  for some `r : ℕ` and `min{p, q} ≤ ν_3(r) + 1`. -/
theorem nice.add_succ_even_and_min_le_multiplicity (h : nice p q) :
    ∃ r, p + q + 1 = 2 * r ∧ min p q ≤ multiplicity 3 r + 1 := by
  ---- The given equation yields `3^{min(p, q)} ∣ 2^{p + q + 1} - 1`.
  have h0 : (3 : ℤ) ^ min p q ∣ 3 ^ p := pow_dvd_pow _ (Nat.min_le_left _ _)
  have h1 : (3 : ℤ) ^ min p q ∣ 2 * 3 ^ q :=
    Int.dvd_mul_of_dvd_right (pow_dvd_pow _ (Nat.min_le_right _ _))
  replace h1 : (3 : ℤ) ^ min p q ∣ 2 ^ (p + q + 1) - 1 := calc
    _ ∣ 3 ^ p + 2 * 3 ^ q := Int.dvd_add h0 h1
    _ = 2 ^ (p + q + 1) - 1 := h
  ---- It also implies `min{p, q} > 0`, so `p + q + 1` must be even, say `= 2r`.
  obtain ⟨r, hr⟩ : 2 ∣ p + q + 1 :=
    two_dvd_of_three_dvd_pow_sub_one ((pow_dvd_pow _ h.min_pos).trans h1)
  refine ⟨r, hr, ?_⟩
  ---- Then by LTE we get `min(p, q) ≤ ν_3(2^{2r} - 1) = r + 1`.
  replace h0 : 0 < (2 : ℤ) ^ (p + q + 1) - 1 :=
    sub_pos_of_lt (one_lt_pow₀ one_lt_two (Nat.succ_ne_zero _))
  replace h0 : FiniteMultiplicity (3 : ℤ) (2 ^ (p + q + 1) - 1) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, h0.ne.symm⟩
  replace h1 : min p q ≤ multiplicity (3 : ℤ) (2 ^ (p + q + 1) - 1) :=
    h0.le_multiplicity_of_pow_dvd h1
  replace h0 : r ≠ 0 := by rintro rfl; exact Nat.succ_ne_zero _ hr
  calc min p q
    _ ≤ multiplicity (3 : ℤ) (2 ^ (p + q + 1) - 1) := h1
    _ = multiplicity (3 : ℤ) (4 ^ r - 1) := by rw [hr, Int.pow_mul]; rfl
    _ = multiplicity 3 r + 1 := multiplicity_three_four_pow_sub_one h0

/-- The only nice pairs are `(2, 1)` and `(2, 3)`. -/
theorem nice_iff : nice p q ↔ p = 2 ∧ (q = 1 ∨ q = 3) := by
  ---- The `←` direction can be checked directly.
  refine Iff.symm ⟨λ hpq ↦ ?_, λ hpq ↦ ?_⟩
  · rcases hpq with ⟨rfl, rfl | rfl⟩
    all_goals rfl
  ---- For `→`, recall that `p + q + 1 = 2r` for some `r` with `min{p, q} ≤ ν_3(r) + 1`.
  obtain ⟨r, hr, h⟩ : ∃ r, p + q + 1 = 2 * r ∧ min p q ≤ multiplicity 3 r + 1 :=
    hpq.add_succ_even_and_min_le_multiplicity
  ---- But we also have `p + q ≤ 3 min{p, q} + 1`, so `2r ≤ 3ν_3(r) + 5`.
  replace h : 2 * r ≤ 3 * multiplicity 3 r + 5 := calc
    _ = p + q + 1 := hr.symm
    _ ≤ 3 * min p q + 2 := Nat.add_le_add_right hpq.add_le_three_mul_min_add_one 1
    _ ≤ 3 * (multiplicity 3 r + 1) + 2 := Nat.add_le_add_right (Nat.mul_le_mul_left _ h) 2
  ---- For this inequality to be satisfied, we must have `r ≤ 3`.
  replace h : r ≤ 3 := by
    -- Assume `r > 3`, and divide into two cases: `3 ∤ r` and `3 ∣ r`.
    contrapose! h
    obtain h0 | h0 : ¬3 ∣ r ∨ 3 ∣ r := dec_em' _
    -- If `3 ∤ r` then `ν_3(r) = 0` and the inequality follows since `5 < 2r`.
    · calc 3 * multiplicity 3 r + 5
      _ = 5 := by rw [multiplicity_eq_zero.mpr h0]
      _ < 2 * r := Nat.mul_le_mul_left 2 h.le
    -- If `3 ∣ r` then `r ≥ 6` and the inequality follows from `3 ν_3(r) ≤ r`.
    · have h1 : r ≠ 0 := Nat.ne_zero_of_lt h
      replace h : 2 * 3 ≤ r :=
        Nat.mul_le_of_le_div 3 2 r ((Nat.lt_div_iff_mul_lt' h0 1).mpr h)
      replace h0 : multiplicity 3 r ≤ Nat.log 3 r := calc
        _ = padicValNat 3 r := (padicValNat_def h1).symm
        _ ≤ Nat.log 3 r := padicValNat_le_nat_log r
      replace h0 : 3 * multiplicity 3 r ≤ r := calc
        _ ≤ 3 * Nat.log 3 r := Nat.mul_le_mul_left 3 h0
        _ ≤ 3 ^ Nat.log 3 r := Nat.mul_le_pow Nat.add_one_add_one_ne_one _
        _ ≤ r := Nat.pow_log_le_self 3 h1
      calc 3 * multiplicity 3 r + 5
      _ ≤ r + 5 := Nat.add_le_add_right h0 5
      _ < r + r := Nat.add_lt_add_left h r
      _ = 2 * r := (Nat.two_mul r).symm
  ---- Now we can just brute force all the cases.
  replace h : r ∈ Finset.range 4 := Finset.mem_range_succ_iff.mpr h
  have hq : q < 2 * r := calc
    _ ≤ p + q := Nat.le_add_left q p
    _ < p + q + 1 := Nat.lt_succ_self _
    _ = 2 * r := hr
  replace hq : q ∈ Finset.range (2 * r) := Finset.mem_range.mpr hq
  obtain rfl : p = 2 * r - 1 - q := Nat.eq_sub_of_add_eq (Nat.eq_sub_of_add_eq hr)
  clear hr; revert q; revert r
  unfold nice; decide

/-- Final solution -/
theorem final_solution :
    good m n ↔ (n = 3 ∧ (m = 9 ∨ m = 6)) ∨ (n = 5 ∧ (m = 9 ∨ m = 54)) := by
  simp [good_iff_nice, nice_iff]
