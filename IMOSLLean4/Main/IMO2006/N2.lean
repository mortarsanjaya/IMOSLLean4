/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Fintype.Pigeonhole

/-!
# IMO 2006 N2

Let $b > 1$ be a positive integer.
For any real number $r$, its **$n$th digit after decimal point in base $b$**
  is defined to be the remainder of $⌊b^{n + 1} r⌋$ upon division by $b$.
In particular, the $0$th digit is right after (not before) the decimal point.
(This definition is different from the naive definition for negative real numbers.)

Let $x$ be a rational number.
Let $y$ be a real number whose $n$th digit after decimal point in base $b$
  is equal to the $2^n$th digit after decimal point of $x$ in base $b$.
Show that $y$ is rational.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2006SL.pdf).
We generalize the setting even more by working over archimedean ring with floor.
(See `FloorRing` for the formal definition.)
We use a custom definition of being rational, implemented as `IMOSL.IMO2006N2.isRational`:
  an element $r$ is "rational" if there exist integers $m > 0$ and $n$ with $mr = n$.
-/

namespace IMOSL
namespace IMO2006N2

open Finset

/-! ### Pigeonhole principle applied to integer powers -/

section

variable (k : ℕ) {m : ℕ} (hm : m > 0)
include hm

open Fin.NatCast in
/-- For any `k, m : ℕ` with `m > 0`, there exists `a < b` such that `k^a ≡ k^b (mod m)`. -/
theorem exists_lt_pow_mod_eq : ∃ a, ∃ b > a, k ^ a % m = k ^ b % m := by
  haveI : NeZero m := NeZero.of_pos hm
  obtain ⟨a, b, hab, h⟩ : ∃ a b, a ≠ b ∧ ((k ^ a : ℕ) : Fin m) = (k ^ b : ℕ) :=
    Finite.exists_ne_map_eq_of_infinite _
  obtain hab | hab : a < b ∨ b < a := Nat.lt_or_gt_of_ne hab
  exacts [⟨a, b, hab, congrArg Fin.val h⟩, ⟨b, a, hab, congrArg Fin.val h.symm⟩]

/-- For any `k, m : ℕ` with `m > 0`, there exists `a < b` such that `m ∣ k^a - k^b`. -/
theorem exists_lt_dvd_pow_sub_pow : ∃ a, ∃ b > a, (m : ℤ) ∣ k ^ b - k ^ a := by
  obtain ⟨a, b, hab, h⟩ : ∃ a, ∃ b > a, k ^ a % m = k ^ b % m := exists_lt_pow_mod_eq k hm
  refine ⟨a, b, hab, ?_⟩
  rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_eq_emod_iff_emod_sub_eq_zero,
    ← Int.natCast_pow, ← Int.natCast_emod, ← Int.natCast_pow, ← Int.natCast_emod, h]

/-- For any `k, m : ℕ` with `m > 0`, there exists
  `N` and `d > 0` with `m ∣ k^{N + d} - k^N`. -/
theorem exists_lt_dvd_pow_add_sub_pow : ∃ N, ∃ d > 0, (m : ℤ) ∣ k ^ (N + d) - k ^ N := by
  obtain ⟨a, b, hab, h⟩ : ∃ a, ∃ b > a, (m : ℤ) ∣ k ^ b - k ^ a :=
    exists_lt_dvd_pow_sub_pow k hm
  refine ⟨a, b - a, Nat.sub_pos_of_lt hab, ?_⟩
  rwa [Nat.add_sub_cancel' (Nat.le_of_lt hab)]

/-- For any `k, m : ℕ` with `m > 0`, there exists
  `N`, `d > 0`, and `t` with `k^{N + d} = mt + k^N`. -/
theorem exists_lt_pow_eq_pow_add_mul : ∃ N, ∃ d > 0, ∃ t, k ^ (N + d) = m * t + k ^ N := by
  obtain rfl | hk : k = 0 ∨ k > 0 := Nat.eq_zero_or_pos k
  · exact ⟨1, 1, Nat.one_pos, 0, rfl⟩
  obtain ⟨N, d, hd, t, ht⟩ : ∃ N, ∃ d > 0, (m : ℤ) ∣ k ^ (N + d) - k ^ N :=
    exists_lt_dvd_pow_add_sub_pow k hm
  refine ⟨N, d, hd, t.natAbs, ?_⟩
  replace hd : k ^ N ≤ k ^ (N + d) := Nat.pow_le_pow_right hk (Nat.le_add_right _ _)
  replace ht : ((k ^ (N + d) - k ^ N : ℕ) : ℤ) = m * t := by
    rwa [← Int.natCast_pow, ← Int.natCast_pow, ← Int.natCast_sub hd] at ht
  refine Nat.eq_add_of_sub_eq hd ?_
  have ht0 : t ≥ 0 :=
    Int.nonneg_of_mul_nonneg_right ((Nat.cast_nonneg _).trans_eq ht) (Int.natCast_pos.mpr hm)
  rw [← Int.natCast_inj, ht, Int.natCast_mul, Int.natCast_natAbs, abs_of_nonneg ht0]

end





/-! ### The `n`th decimal digit -/

variable [CommRing R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- The `n`th decimal digit of an element of a ring with floor in base `b`. -/
def nthDecimalDigit (b : ℕ) (r : R) (n : ℕ) : ℤ := ⌊b ^ (n + 1) * r⌋ % b

omit [IsStrictOrderedRing R] in
/-- The `(n + d)`th decimal digit of `r` in base `b` is the
  same as the `n`th decimal digit of `b^d r` in base `b`. -/
theorem nthDecimalDigit_add (b) (r : R) (n d) :
    nthDecimalDigit b r (n + d) = nthDecimalDigit b (b ^ d * r) n := by
  unfold nthDecimalDigit; rw [Nat.add_right_comm, pow_add, mul_assoc]

/-- An alternative formula for the `n`th decimal digit, `⌊b^{n + 1} r⌋ - b⌊b^n r⌋`. -/
theorem nthDecimalDigit_alt_formula (b : ℕ) (r : R) (n : ℕ) :
    nthDecimalDigit b r n = ⌊b ^ (n + 1) * r⌋ - b * ⌊b ^ n * r⌋ := by
  obtain rfl | hb : b = 0 ∨ b ≠ 0 := eq_or_ne _ _
  · rw [nthDecimalDigit, Int.natCast_zero, Int.zero_mul, Int.sub_zero, Int.emod_zero]
  · rw [nthDecimalDigit, Int.emod_def, sub_right_inj, pow_succ',
      mul_assoc, Int.natCast_mul_floor_div_cancel hb]

/-- A summation formula for `⌊b^n r⌋ - b^n⌊r⌋` in terms of base `b` decimal digits of `r`. -/
theorem nthDecimalDigit_floor_sum_formula (b : ℕ) (r : R) (n : ℕ) :
    ∑ i ∈ range n, b ^ (n - (i + 1)) * nthDecimalDigit b r i
      = ⌊b ^ n * r⌋ - b ^ n * ⌊r⌋ :=
  let f (i : ℕ) : ℤ := b ^ (n - i) * ⌊b ^ i * r⌋
  calc ∑ i ∈ range n, b ^ (n - (i + 1)) * nthDecimalDigit b r i
    _ = ∑ i ∈ range n, (f (i + 1) - f i) := by
      refine sum_congr rfl λ i hi ↦ ?_
      rw [nthDecimalDigit_alt_formula, Int.mul_sub, Int.sub_right_inj, ← Int.mul_assoc,
        ← Int.pow_succ, ← Nat.succ_sub (mem_range.mp hi), Nat.succ_sub_succ]
    _ = b ^ (n - n) * ⌊b ^ n * r⌋ - b ^ n * ⌊b ^ 0 * r⌋ := sum_range_sub _ _
    _ = ⌊b ^ n * r⌋ - b ^ n * ⌊r⌋ := by
      rw [Nat.sub_self, Int.pow_zero, Int.one_mul, pow_zero, one_mul]

/-- A summation formula for `b^n{r} - {b^n r}` in terms of base `b` decimal digits of `r`. -/
theorem nthDecimalDigit_fract_sum_formula (b : ℕ) (r : R) (n : ℕ) :
    ∑ i ∈ range n, b ^ (n - (i + 1)) * nthDecimalDigit b r i
      = b ^ n * Int.fract r - Int.fract (b ^ n * r) := by
  rw [Int.fract, mul_sub, Int.fract, ← sub_add, sub_sub_cancel_left,
    neg_add_eq_sub, nthDecimalDigit_floor_sum_formula, Int.cast_sub,
    Int.cast_mul, Int.cast_pow, Int.cast_natCast]

/-- A rearrangement of `nthDecimalDigit_fract_sum_formula`. -/
theorem nthDecimalDigit_fract_sum_formula2 (b : ℕ) (r : R) (n : ℕ) :
    b ^ n * Int.fract r = Int.fract (b ^ n * r)
      + ∑ i ∈ range n, b ^ (n - (i + 1)) * nthDecimalDigit b r i := by
  rw [nthDecimalDigit_fract_sum_formula, add_sub_cancel]

/-- If `r` and `s` has the same base `b` digits after decimal,
  then `|{r} - {s}|` is infinitesimal. -/
theorem infinitesimal_of_nthDecimalDigit_eq (hb : b > 1)
    {r s : R} (hrs : nthDecimalDigit b r = nthDecimalDigit b s) (n : ℕ) :
    n • |Int.fract r - Int.fract s| < 1 :=
  calc n • |Int.fract r - Int.fract s|
  _ ≤ b ^ n • |Int.fract r - Int.fract s| :=
    nsmul_le_nsmul_left (abs_nonneg _) (Nat.le_of_lt (Nat.lt_pow_self hb))
  _ = |b ^ n * Int.fract r - b ^ n * Int.fract s| := by
    rw [← mul_sub, abs_mul, abs_pow, Nat.abs_cast, nsmul_eq_mul, Nat.cast_pow]
  _ < 1 := by
    refine Int.abs_sub_lt_one_of_floor_eq_floor ?_
    iterate 2 rw [nthDecimalDigit_fract_sum_formula2,
      Int.floor_add_intCast, Int.floor_fract, Int.zero_add]
    rw [hrs]

/-- If `R` is archimedean and `r` and `s` has the same base `b` digits after decimal,
  then `r - s` is an integer. -/
theorem sub_eq_intCast_of_nthDecimalDigit_eq [Archimedean R] (hb : b > 1)
    {r s : R} (hrs : nthDecimalDigit b r = nthDecimalDigit b s) :
    ∃ z : ℤ, r - s = z := by
  obtain h | h : |Int.fract r - Int.fract s| = 0 ∨ 0 < |Int.fract r - Int.fract s| :=
    eq_or_lt_of_le' (abs_nonneg _)
  ---- If `|{r} - {s}| = 0`, then pick `z = ⌊r⌋ - ⌊s⌋`.
  · refine ⟨⌊r⌋ - ⌊s⌋, ?_⟩
    rw [Int.cast_sub, sub_eq_sub_iff_sub_eq_sub]
    exact eq_of_abs_sub_eq_zero h
  ---- If `|{r} - {s}| > 0`, then archimedean property implies contradiction.
  · obtain ⟨n, hn⟩ : ∃ n, 1 ≤ n • |Int.fract r - Int.fract s| := Archimedean.arch _ h
    exact absurd hn (infinitesimal_of_nthDecimalDigit_eq hb hrs n).not_ge





/-! ### Rational elements -/

/-- An element `r ∈ R` is called "rational" if `mr = T`
  for some `m : ℕ` and `T : ℤ` with `m > 0`. -/
def isRational (r : R) := ∃ m > 0, ∃ T : ℤ, m • r = T

/-- If an element is rational, then its decimal digit
  sequence base `b` is eventually periodic. -/
theorem isRational.nthDecimalDigit_eventually_periodic {r : R} (hr : isRational r) (b) :
    ∃ N, ∃ d > 0, ∀ n ≥ N, nthDecimalDigit b r (n + d) = nthDecimalDigit b r n := by
  ---- Write `mr = T` for some `m : ℕ` and `T : ℤ` with `m > 0`.
  rcases hr with ⟨m, hm, T, hr⟩
  ---- Find `N`, `d > 0`, and `z` such that `mz = b^{N + d} - b^N`.
  obtain ⟨N, d, hd, z, hz⟩ : ∃ N, ∃ d > 0, (m : ℤ) ∣ b ^ (N + d) - b ^ N :=
    exists_lt_dvd_pow_add_sub_pow b hm
  ---- Then we claim that the same `N` and `d` works.
  refine ⟨N, d, hd, λ n hn ↦ ?_⟩
  ---- From `mz = b^{N + d} - b^N` we first deduce `b^{N + d} r = Tz + b^N r`.
  replace hz : b ^ (N + d) * r = (T * z : ℤ) + b ^ N * r :=
    calc b ^ (N + d) * r
    _ = ((b ^ (N + d) : ℤ) : R) * r := by rw [Int.cast_pow, Int.cast_natCast]
    _ = (m * z + (b ^ N : ℤ)) * r := by
      rw [eq_add_of_sub_eq hz, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    _ = m * z * r + b ^ N * r := by rw [add_mul, Int.cast_pow, Int.cast_natCast]
    _ = (T * z : ℤ) + b ^ N * r := by rw [mul_right_comm, ← nsmul_eq_mul, hr, Int.cast_mul]
  ---- Now do the main calculations.
  obtain ⟨k, rfl⟩ : ∃ k, n = N + k := Nat.exists_eq_add_of_le hn
  calc ⌊b ^ (N + k + d + 1) * r⌋ % b
    _ = ⌊b ^ (N + d) * r * b ^ (k + 1)⌋ % b := by
      rw [Nat.add_assoc, Nat.add_add_add_comm, pow_add, mul_right_comm]
    _ = ⌊((T * z : ℤ) + b ^ N * r) * b ^ (k + 1)⌋ % b := by rw [hz]
    _ = ⌊(T * z : ℤ) * b ^ (k + 1) + b ^ (N + k + 1) * r⌋ % b := by
      rw [add_mul, Nat.add_assoc, mul_right_comm, ← pow_add]
    _ = ⌊(T * z * b ^ (k + 1) : ℤ) + b ^ (N + k + 1) * r⌋ % b := by
      rw [Int.cast_mul (T * z), Int.cast_pow, Int.cast_natCast]
    _ = (T * z * b ^ k * b + ⌊b ^ (N + k + 1) * r⌋) % b := by
      rw [Int.floor_intCast_add, Int.pow_succ, ← Int.mul_assoc]
    _ = ⌊b ^ (N + k + 1) * r⌋ % b := Int.mul_add_emod_self_right _ _ _

/-- If the decimal digit sequence base `b` of an element is eventually periodic,
  then that element is rational. -/
theorem isRational_of_nthDecimalDigit_eventually_periodic
    [Archimedean R] (hb : b > 1) {r : R}
    (hr : ∃ N, ∃ d > 0, ∀ n ≥ N, nthDecimalDigit b r (n + d) = nthDecimalDigit b r n) :
    isRational r := by
  /- Pick `N` and `d` such that `(n + d)`th decimal digit and
    `n`th decimal digit of `r` in base `b` are equal for all `n ≥ N`. -/
  rcases hr with ⟨N, d, hd, h⟩
  ---- In other words, `b^{N + d} r` and `b^N r` has the same digits base `b` past decimal.
  replace h : nthDecimalDigit b (b ^ (N + d) * r) = nthDecimalDigit b (b ^ N * r) := by
    funext n; rw [← nthDecimalDigit_add, ← nthDecimalDigit_add,
      ← Nat.add_assoc, h _ (Nat.le_add_left _ _)]
  ---- Thus `(b^{N + d} - b^N) r` is an integer, and note `b^{N + d} - b^N > 0`.
  obtain ⟨z, hz⟩ : ∃ z : ℤ, ↑b ^ (N + d) * r - ↑b ^ N * r = z :=
    sub_eq_intCast_of_nthDecimalDigit_eq hb h
  replace h : b ^ N < b ^ (N + d) := Nat.pow_lt_pow_right hb (Nat.lt_add_of_pos_right hd)
  replace hz : (b ^ (N + d) - b ^ N) • r = z := by
    rw [nsmul_eq_mul, Nat.cast_sub (Nat.le_of_lt h), Nat.cast_pow, Nat.cast_pow, sub_mul, hz]
  ---- We get everything now.
  exact ⟨_, Nat.zero_lt_sub_of_lt h, z, hz⟩





/-! ### The main statement -/

/-- Final solution -/
theorem final_solution [Archimedean R] (hb : b > 1) {x y : R} (hx : isRational x)
    (hyx : ∀ n, nthDecimalDigit b y n = nthDecimalDigit b x (2 ^ n)) :
    isRational y := by
  ---- Suppose that the digit sequence of `x` is `d`-periodic from index `N` onwards.
  obtain ⟨N, d, hd, hx0⟩ :
      ∃ N, ∃ d > 0, ∀ n ≥ N, nthDecimalDigit b x (n + d) = nthDecimalDigit b x n :=
    hx.nthDecimalDigit_eventually_periodic b
  replace hx0 {n : ℕ} (hn : n ≥ N) (t) :
      nthDecimalDigit b x (n + d * t) = nthDecimalDigit b x n := by
    induction t with | zero => rfl | succ t t_ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, hx0 _ (Nat.le_add_right_of_le hn), t_ih]
  ---- Find `M`, `c > 0`, and `t` such that `2^{M + c} = dt + 2^M`.
  obtain ⟨M, c, hc, t, ht⟩ : ∃ M, ∃ c > 0, ∃ t, 2 ^ (M + c) = d * t + 2 ^ M :=
    exists_lt_pow_eq_pow_add_mul 2 hd
  ----- Then the digit sequence of `y` is `c`-periodic from index `M + N` onwards.
  refine isRational_of_nthDecimalDigit_eventually_periodic hb ⟨M + N, c, hc, λ n hn ↦ ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, n = M + k := Nat.exists_eq_add_of_le (Nat.le_of_add_right_le hn)
  replace hn : N ≤ 2 ^ (M + k) := calc
    N ≤ k := Nat.add_le_add_iff_left.mp hn
    _ ≤ M + k := Nat.le_add_left k M
    _ ≤ 2 ^ (M + k) := Nat.le_of_lt Nat.lt_two_pow_self
  calc nthDecimalDigit b y (M + k + c)
    _ = nthDecimalDigit b x (2 ^ (M + c) * 2 ^ k) := by
      rw [hyx, Nat.add_right_comm, Nat.pow_add]
    _ = nthDecimalDigit b x (2 ^ (M + k) + d * (t * 2 ^ k)) := by
      rw [ht, Nat.add_mul, Nat.mul_assoc, Nat.pow_add, Nat.add_comm]
    _ = nthDecimalDigit b x (2 ^ (M + k)) := hx0 hn _
    _ = nthDecimalDigit b y (M + k) := (hyx _).symm
