/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.ModEq

/-!
# IMO 2009 N4

Find all positive integers $n$ such that there exists positive integers $a_1, …, a_n$
  such that $(a_{k - 1} + 1)(a_{k + 1} + 1) = a_k^2 + 1$ for all $k = 2, …, n - 1$.

### Answer

$n ≤ 4$.

### Solution

We modify the [solution](https://artofproblemsolving.com/community/c6h355798p15723361)
  in the AoPS thread post #5 by **TheUltimate123**.
The solutions in AoPS resemble Solution 1 of the official solution, but with a
  different proof that no even positive integers $m$ and $n$ satisfy
  $m + 1 ∣ n^2 + 1$ and $n + 1 ∣ m^2 + 1$, but still using infinite descent.
In our case, assuming $n < m$, we write $m^2 + 1 = (n + 1)(k + 1)$ and
  prove $m + 1 ∣ k^2 + 1$ by directly trying to prove $nk ≡ 1 \pmod{x + 1}$.
-/

namespace IMOSL
namespace IMO2009N4

/-! ### Extra lemmas -/

/-- For any `n ∈ ℕ`, `n^2 + 1` is never divisible by `4`. -/
theorem not_four_dvd_sq_add_one (n : ℕ) : ¬4 ∣ n ^ 2 + 1 := by
  suffices ¬((n % 4) ^ 2 % 4 + 1) % 4 = 0 by
    rwa [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.pow_mod]
  have h : n % 4 < 4 := Nat.mod_lt n (Nat.succ_pos 3)
  generalize n % 4 = k at h ⊢
  revert k; decide

/-- For any `x ∈ ℕ`, we have `x^2 + 1 ≡ 2 (mod x + 1)`. -/
theorem pow_two_add_one_modeq_two (x : ℕ) : x ^ 2 + 1 ≡ 2 [MOD x + 1] :=
  calc x ^ 2 + 1
  _ ≡ x ^ 2 + 1 + (x + 1) [MOD x + 1] := Nat.left_modEq_add_iff.mpr (Nat.dvd_refl _)
  _ = x * (x + 1) + 2 := by rw [Nat.add_add_add_comm, Nat.mul_succ, Nat.pow_two]
  _ ≡ 2 [MOD x + 1] := Nat.mul_modulus_add_modEq_iff.mpr rfl





/-! ### Start of the problem -/

open List

/-- A list `[a_1, …, a_n]` of positive integers is called *good* if
  `(a_{k - 1} + 1)(a_{k + 1} + 1) = a_k^2 + 1` for all `k = 2, …, n - 1`. -/
def good : List ℕ+ → Prop
  | [] => True
  | [_] => True
  | [_, _] => True
  | a :: b :: c :: l => good (b :: c :: l) ∧ (a + 1) * (c + 1) = b ^ 2 + 1

instance : DecidablePred good :=
  List.rec instDecidableTrue λ _ l _ ↦ match l with
  | [] => instDecidableTrue
  | [_] => instDecidableTrue
  | _ :: _ :: _ => instDecidableAnd

/-- The list `[4, 33, 217, 1384]` is good. -/
theorem std_list_is_good : good [4, 33, 217, 1384] := by
  decide

/-- `a :: b :: c :: l` is good iff `b :: c :: l` is good and `(a + 1)(c + 1) = b^2 + 1`. -/
theorem good_three_cons_iff :
    good (a :: b :: c :: l) ↔ good (b :: c :: l) ∧ (a + 1) * (c + 1) = b ^ 2 + 1 :=
  Iff.rfl

/-- If a list is good, then its tail (see `List.tail`) is good. -/
theorem good.tail (h : good l) : good l.tail :=
  match l with
  | [] => trivial
  | [_] => trivial
  | [_, _] => trivial
  | _ :: _ :: _ :: _ => h.1

/-- If there is a good list of length `n`, there is one of length `n - k` for any `k ≥ 0`. -/
theorem exists_good_length_sub (hn : ∃ l, good l ∧ l.length = n) (k) :
    ∃ l, good l ∧ l.length = n - k := by
  ---- Indeed, just keep taking the tails.
  induction k with | zero => exact hn | succ k k_ih => ?_
  rcases k_ih with ⟨l, hl, hl0⟩
  refine ⟨l.tail, hl.tail, ?_⟩
  rw [length_tail, hl0, Nat.sub_sub]

/-- If `m ≤ n` and there is a good list of length `n`, there is one of length `m`. -/
theorem exists_good_length_of_le (hn : ∃ l, good l ∧ l.length = n) (hmn : m ≤ n) :
    ∃ l, good l ∧ l.length = m :=
  Nat.sub_sub_self hmn ▸ exists_good_length_sub hn (n - m)


section

variable {a b c : ℕ} (h : (a + 1) * (c + 1) = b ^ 2 + 1)
include h

/-- If `(a + 1)(c + 1) = b^2 + 1` then one of `a` or `c` is even. -/
theorem even_or_even_of_add_one_mul_add_one_eq_sq_add_one : Even a ∨ Even c := by
  by_contra! h0
  ---- If not, then `4 ∣ b^2 + 1`, which is a contradiction.
  refine not_four_dvd_sq_add_one b ?_
  obtain ⟨⟨k, hk⟩, ⟨m, hm⟩⟩ : 2 ∣ a + 1 ∧ 2 ∣ c + 1 := by
    rwa [← Nat.even_add_one, even_iff_two_dvd, ← Nat.even_add_one, even_iff_two_dvd] at h0
  rw [← h, hk, hm, Nat.mul_mul_mul_comm]
  exact Nat.dvd_mul_right _ _

/-- If `(a + 1)(c + 1) = b^2 + 1` and `b` is even, then `a` is even. -/
theorem even_of_add_one_mul_add_one_eq_sq_add_one (hb : Even b) : Even a := by
  contrapose hb
  ---- If `a` is odd, then `b` is odd.
  replace h : Even (b ^ 2 + 1) := by
    rw [← h, Nat.even_mul, Nat.even_add_one]
    left; exact hb
  rwa [Nat.even_add_one, Nat.not_even_iff_odd,
    Nat.odd_pow_iff (Nat.succ_ne_zero 1), ← Nat.not_even_iff_odd] at h

end


/-- We call a pair `(x, y)` a bad pair if `x + 1 ∣ y^2 + 1` and `y + 1 ∣ x^2 + 1`. -/
def isBadPair (x y : ℕ) := x + 1 ∣ y ^ 2 + 1 ∧ y + 1 ∣ x ^ 2 + 1


namespace isBadPair

instance (x y) : Decidable (isBadPair x y) :=
  instDecidableAnd

/-- If `(x, y)` is a bad pair, then so is `(y, x)`. -/
theorem symm (h : isBadPair x y) : isBadPair y x :=
  And.symm h

/-- If `(0, y)` is a bad pair, then `y = 0`. -/
theorem zero_of_zero_left (h : isBadPair 0 y) : y = 0 := by
  replace h : y + 1 ∣ 1 := h.2
  rwa [Nat.dvd_one, Nat.succ_inj] at h

/-- If `(x, x)` is a bad pair, then `x = 0` or `x = 1`. -/
theorem zero_or_one_of_self (h : isBadPair x x) : x = 0 ∨ x = 1 := by
  rwa [isBadPair, and_self, (pow_two_add_one_modeq_two x).dvd_iff (Nat.dvd_refl _),
    Nat.dvd_prime Nat.prime_two, Nat.succ_inj, Nat.succ_inj] at h

/-- If `(x, y)` is a bad pair and `x` is even, then `y` is even. -/
theorem even_of_even (h : isBadPair x y) (hx : Even x) : Even y := by
  contrapose hx
  replace hx : Even (y + 1) := Nat.even_add_one.mpr hx
  replace h : Even (x ^ 2 + 1) := h.2.even hx
  rwa [Nat.even_add_one, Nat.even_pow' (Nat.succ_ne_zero 1)] at h

/-- If `(x, y)` is a bad pair with `x` even and `x < y`,
  then there exists `z < x` such that `z` is even and `(z, x)` is a bad pair. -/
theorem exists_lt_of_even (h : isBadPair x y) (hxy : x < y) (hx : Even x) :
    ∃ z < x, isBadPair z x ∧ Even z := by
  ---- First write `x^2 + 1 = (k + 1)(y + 1)`.
  rcases h with ⟨h, l, h0⟩
  obtain rfl | ⟨k, rfl⟩ : l = 0 ∨ ∃ k, l = k + 1 :=
    (Nat.eq_zero_or_eq_succ_pred l).imp_right λ hl ↦ ⟨l.pred, hl⟩
  · exact absurd h0 (Nat.succ_ne_zero _)
  ---- Now we claim that this `k` works, by first showing that `k < x`.
  refine ⟨k, Nat.lt_of_not_ge λ hkx ↦ ?_, ?_⟩
  · refine Nat.ne_of_lt ?_ h0
    calc x ^ 2 + 1
      _ ≤ (x + 1) ^ 2 := Nat.pow_lt_pow_left (Nat.lt_succ_self x) (Nat.succ_ne_zero 1)
      _ = (x + 1) * (x + 1) := Nat.pow_two _
      _ < (y + 1) * (k + 1) := Nat.mul_lt_mul_of_lt_of_le
        (Nat.succ_lt_succ hxy) (Nat.succ_le_succ hkx) (Nat.succ_pos k)
  ---- It suffices to show `x + 1 ∣ k^2 + 1` to show the rest.
  suffices x + 1 ∣ k ^ 2 + 1 by
    refine (and_iff_left_of_imp λ h1 ↦ h1.symm.even_of_even hx).mpr ⟨⟨y + 1, ?_⟩, this⟩
    rw [h0, Nat.mul_comm]
  ---- Note that `x + 1` is coprime with `2` and `y`.
  replace hx : Nat.Coprime (x + 1) 2 := by
    rwa [Nat.coprime_two_right, Nat.odd_add_one, Nat.not_odd_iff_even]
  replace hxy : Nat.Coprime (x + 1) y := by
    have h1 : Nat.Coprime (y ^ 2 + 1) y := by
      rw [Nat.Coprime, Nat.pow_two, Nat.gcd_mul_left_add_left, Nat.gcd_one_left]
    exact h1.coprime_dvd_left h
  ---- For the rest, get `yk ≡ 1 (mod x + 1)` and conclude.
  replace h0 : (y + 1) * (k + 1) ≡ 2 [MOD x + 1] :=
    h0 ▸ pow_two_add_one_modeq_two x
  have h1 : 2 * (y * (k + 1)) ≡ 2 * (y + 1) [MOD x + 1] := calc
    _ = 2 * y * (k + 1) := (Nat.mul_assoc _ _ _).symm
    _ ≡ (y ^ 2 + 1) * (k + 1) + 2 * y * (k + 1) [MOD x + 1] :=
      Nat.right_modEq_add_iff.mpr (Nat.dvd_mul_right_of_dvd h _)
    _ = (y + 1) * (k + 1) * (y + 1) := by
      rw [← Nat.add_mul, Nat.mul_right_comm,
        ← Nat.pow_two, add_sq', Nat.mul_one, Nat.one_pow]
    _ ≡ 2 * (y + 1) [MOD x + 1] := h0.mul_right _
  replace h1 : y * (k + 1) ≡ y + 1 [MOD x + 1] :=
    h1.cancel_left_of_coprime hx
  replace h1 : y * k ≡ 1 [MOD x + 1] := by
    rw [Nat.mul_succ, Nat.add_comm y] at h1
    exact h1.add_right_cancel' y
  suffices x + 1 ∣ y ^ 2 * (k ^ 2 + 1) from (hxy.pow_right 2).dvd_of_dvd_mul_left this
  rw [Nat.mul_succ, ← Nat.mul_pow, ← Nat.modEq_zero_iff_dvd, Nat.add_comm _ (y ^ 2)]
  calc y ^ 2 + (y * k) ^ 2
    _ ≡ y ^ 2 + 1 [MOD x + 1] := (h1.pow 2).add_left (y ^ 2)
    _ ≡ 0 [MOD x + 1] := Nat.modEq_zero_iff_dvd.mpr h

/-- If `(x, y)` is a bad pair with `x` even, then `x = 0`. -/
theorem even_imp_zero (h : isBadPair x y) (hx : Even x) : x = 0 := by
  ---- Strong induction on `x` to prove: if `x > 0` is even then `(x, y)` is not a bad pair.
  by_contra h0
  induction x using Nat.strong_induction_on generalizing y with | h x x_ih => ?_
  ---- First note that `y` is even, and so minimality yields `x ≤ y` (or `y = 0`; impossible).
  obtain rfl | hxy : y = x ∨ x < y := by
    refine Nat.eq_or_lt_of_not_lt λ hyx ↦ x_ih y hyx h.symm (h.even_of_even hx) ?_
    rintro rfl; exact hyx.ne.symm h.symm.zero_of_zero_left
  ---- If `x = y`, then `x = 0` or `x = 1`, but `x ≠ 0` is even; contradiction!
  · exact h.zero_or_one_of_self.elim h0 λ hy ↦ Nat.not_even_one (hy ▸ hx)
  ---- If `x < y`, pick some `z < x` even such that `(z, x)` is a bad pair; contradiction!
  · obtain ⟨z, hzx, hzx0, hz⟩ : ∃ z < x, isBadPair z x ∧ Even z :=
      h.exists_lt_of_even hxy hx
    obtain rfl | hz0 : z = 0 ∨ z ≠ 0 := eq_or_ne z 0
    exacts [h0 hzx0.zero_of_zero_left, x_ih z hzx hzx0 hz hz0]

end isBadPair


/-- A list of length `5` is not good (the list is given in an explicit manner). -/
theorem length_five_not_good (a b c d e) : ¬good [a, b, c, d, e] := by
  ---- Suppose that `[a, b, c, d, e]` is a good list.
  intro h
  replace h : ((c + 1 : ℕ) * (e + 1) = d ^ 2 + 1 ∧ (b + 1 : ℕ) * (d + 1) = c ^ 2 + 1)
      ∧ (a + 1 : ℕ) * (c + 1) = b ^ 2 + 1 := by
    simp_rw [good, ← PNat.coe_inj] at h; rwa [true_and] at h
  ---- First we prove that `b` is even.
  have hb : Even (b : ℕ) := by
    -- Since `(b + 1)(d + 1) = c^2 + 1`, one of `b` or `d` is even.
    obtain h0 | h0 : Even (b : ℕ) ∨ Even (d : ℕ) :=
      even_or_even_of_add_one_mul_add_one_eq_sq_add_one h.1.2
    · exact h0
    -- If `d` is even, then `c` is even and then `b` is even too.
    replace h0 : Even (c : ℕ) := even_of_add_one_mul_add_one_eq_sq_add_one h.1.1 h0
    exact even_of_add_one_mul_add_one_eq_sq_add_one h.1.2 h0
  ---- Now prove that `(b, c)` is a bad pair.
  replace h : isBadPair b c :=
    ⟨⟨d + 1, h.1.2.symm⟩, ⟨a + 1, h.2.symm.trans (Nat.mul_comm _ _)⟩⟩
  ---- But then we proved that these two imply `b = 0`; contradiction.
  replace hb : (b : ℕ) = 0 := h.even_imp_zero hb
  exact absurd hb b.ne_zero

/-- A good list has length at most `4`. -/
theorem good.length_le_four (hl : good l) : l.length ≤ 4 := by
  refine Nat.le_of_not_lt λ hl0 ↦ ?_
  obtain ⟨l', hl', hl'0⟩ : ∃ l, good l ∧ l.length = 5 :=
    exists_good_length_of_le (n := l.length) ⟨l, hl, rfl⟩ hl0
  cases l' with | nil => exact absurd hl'0 (Nat.zero_ne_add_one 4) | cons a l'' => ?_
  rw [length_cons, Nat.succ_inj, length_eq_four] at hl'0
  rcases hl'0 with ⟨b, c, d, e, rfl⟩
  exact length_five_not_good _ _ _ _ _ hl'

/-- Final solution -/
theorem final_solution : (∃ l, good l ∧ l.length = n) ↔ n ≤ 4 :=
  ⟨λ ⟨_, hl, hl0⟩ ↦ hl0.symm.trans_le hl.length_le_four,
  exists_good_length_of_le ⟨[4, 33, 217, 1384], std_list_is_good, rfl⟩⟩
