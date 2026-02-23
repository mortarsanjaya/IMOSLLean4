/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.FieldTheory.Finite.Basic

/-!
# IMO 2010 N4

An integer polynomial $P$ is called $n$-*good* if $P$ is injective modulo $n$.
We say that $P$ is *very good* if $P$ is $n$-good for infinitely many positive integers $n$.
1. Find a pair $(a, b) ∈ ℤ^2$ such that $P(X) = aX^3 + bX$ is $51$-good but not very good.
2. Prove that if $P(X) = aX^3 + bX$ is $2010$-good, where $a, b ∈ ℤ$, then $P$ is very good.

### Answer for part 1

$(a, b) = (1, -51^2)$.

### Solution

We follow the outline of the
  [official solution](https://www.imo-official.org/problems/IMO2010SL.pdf).
Note that for $n ≠ 0$, "injective" can be replaced by "surjective".
In implementation, we define $P$ to be $n$-*nice* if $P$ is surjective modulo $n$.
Note that being $n$-nice and being $n$-good are equivalent if $n ≠ 0$.
The $n$-nice predicate is more convenient to work with when the case $n = 0$ appears.

Claim 1 follows more generally due to Chinese remainder theorem, which implies that
  if $\gcd(k, m) = 1$, then a polynomial is $km$-nice iff it is $k$-nice and $m$-nice.
The right direction generalizes further: if $n ∣ m$, then an $m$-nice polynomial is $n$-nice.

Claim 2 follows by a more general result: if $p ≠ 3$ is prime, then for any
  $x ∈ 𝔽_p$ non-zero, there exists $a ≠ b ∈ 𝔽_p$ such that $a^2 + ab + b^2 = x$.
The requirement $a ≠ b$ is not very difficult: if $a = b$ works then $a = -2b ≠ b$ works.
This forces $p ∣ ab$ if $aX^3 + bX$ is $p$-good.
Then for $p ≡ 1 (mod 3)$, one can check that $p ∣ b$ is impossible, so $p ∣ a$.

Claim 3 follows by Hensel lifting: if $P$ is $p$-good and $P'$ has no root modulo $p$,
  then $P$ is $p^k$-good for all $k ≥ 0$, and therefore $P$ is very good.
-/

namespace IMOSL
namespace IMO2010N4

open Polynomial

/-- A polynomial `P : ℤ[X]` is called `n`-good if for any `k, m : ℤ`,
  `P(k) ≡ P(m) (mod n)` implies `k ≡ m (mod n)`. -/
def good (n : ℕ) (P : ℤ[X]) := ∀ k m, P.eval k ≡ P.eval m [ZMOD n] → k ≡ m [ZMOD n]

/-- A polynomial `P : ℤ[X]` is called `n`-nice if for any `y : ℤ`,
  there exists `x : ℤ` such that `P(x) ≡ y (mod n)`. -/
def nice (n : ℕ) (P : ℤ[X]) := ∀ y, ∃ x, P.eval x ≡ y [ZMOD n]

/-- A polynomial `P : ℤ[X]` is called *very good* if
  `P` is `n`-good for infinitely many `n : ℕ`. -/
def veryGood (P : ℤ[X]) := ∀ N, ∃ n > N, good n P

/-- A polynomial `P` is `n`-good iff it is injective modulo `n`. -/
theorem good_iff_ZMod : good n P ↔ (P.map (Int.castRingHom (ZMod n))).eval.Injective := by
  set φ : ℤ →+* ZMod n := Int.castRingHom (ZMod n)
  have hφ : Function.Surjective φ := ZMod.ringHom_surjective φ
  have hφ0 {k m : ℤ} : φ k = φ m ↔ k ≡ m [ZMOD n] := ZMod.intCast_eq_intCast_iff k m n
  rw [good, Function.Injective, hφ.forall₂]
  conv_rhs => ext k m; rw [eval_map_apply, eval_map_apply, hφ0, hφ0]

/-- A polynomial `P` is `n`-nice iff it is surjective modulo `n`. -/
theorem nice_iff_ZMod : nice n P ↔ (P.map (Int.castRingHom (ZMod n))).eval.Surjective := by
  set φ : ℤ →+* ZMod n := Int.castRingHom (ZMod n)
  have hφ : Function.Surjective φ := ZMod.ringHom_surjective φ
  have hφ0 {k m : ℤ} : φ k = φ m ↔ k ≡ m [ZMOD n] := ZMod.intCast_eq_intCast_iff k m n
  rw [nice, Function.Surjective, hφ.forall]
  simp_rw [hφ.exists, eval_map_apply, hφ0]

/-- If `n > 0`, a polynomial `P` is `n`-good iff it is `n`-nice. -/
theorem good_iff_nice [NeZero n] : good n P ↔ nice n P := by
  rw [good_iff_ZMod, nice_iff_ZMod, Finite.injective_iff_surjective]

/-- Any polynomial is `1`-good. -/
theorem good_one_left (P) : good 1 P :=
  λ _ _ _ ↦ Int.modEq_one

/-- If `P` is `m`-nice and `n ∣ m`, then `P` is `n`-nice. -/
theorem nice.of_dvd (hm : nice m P) (hnm : n ∣ m) : nice n P := by
  intro y
  obtain ⟨x, hx⟩ : ∃ x, P.eval x ≡ y [ZMOD m] := hm y
  exact ⟨x, hx.of_dvd (Int.ofNat_dvd.mpr hnm)⟩

/-- If `m > 0`, `n ∣ m`, and `P` is `m`-good, then `P` is `n`-good. -/
theorem good.of_dvd [NeZero m] (hm : good m P) (hnm : n ∣ m) : good n P :=
  have : NeZero n := ⟨ne_zero_of_dvd_ne_zero (NeZero.ne m) hnm⟩
  good_iff_nice.mpr ((good_iff_nice.mp hm).of_dvd hnm)

/-- Evaluation of a polynomial after mapping to a product of rings. -/
theorem eval_map_RingHom_prod [Semiring R] [Semiring S] [Semiring T]
    (φ : R →+* S) (ρ : R →+* T) (P : R[X]) (s : S) (t : T) :
    (P.map (φ.prod ρ)).eval (s, t) = ((P.map φ).eval s, (P.map ρ).eval t) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
      iterate 3 rw [Polynomial.map_add, eval_add]
      rw [hp, hq]; rfl
  | monomial n r =>
      iterate 3 rw [map_monomial, eval_monomial]
      rw [RingHom.prod_apply, Prod.pow_mk, Prod.mk_mul_mk]

/-- If `k` and `m` are coprime, then `P` is `km`-nice iff `P` is `k`-nice and `m`-nice. -/
theorem nice_iff_of_coprime (h : Nat.Coprime k m) :
    nice (k * m) P ↔ nice k P ∧ nice m P := by
  ---- It suffices to do the `→` direction.
  refine ⟨λ hP ↦ ⟨hP.of_dvd (Nat.dvd_mul_right k m), hP.of_dvd (Nat.dvd_mul_left m k)⟩,
    λ hP ↦ nice_iff_ZMod.mpr λ y ↦ ?_⟩
  ---- Let `φ : ℤ/(kmℤ) ≅ ℤ/kℤ × ℤ/mℤ` be the canonical map.
  let φ : ZMod (k * m) ≃+* ZMod k × ZMod m := ZMod.chineseRemainder h
  ---- Every element of `ℤ/kmℤ` takes the form `φ⁻¹(P(a, b))`.
  obtain ⟨a, ha⟩ : ∃ a, (P.map (Int.castRingHom _)).eval a = (φ y).1 :=
    nice_iff_ZMod.mp hP.1 _
  obtain ⟨b, hb⟩ : ∃ b, (P.map (Int.castRingHom _)).eval b = (φ y).2 :=
    nice_iff_ZMod.mp hP.2 _
  clear_value φ
  replace h : Int.castRingHom (ZMod k × ZMod m)
      = (Int.castRingHom (ZMod k)).prod (Int.castRingHom (ZMod m)) :=
    RingHom.ext_int _ _
  let p : ZMod k × ZMod m := (a, b)
  obtain rfl : φ.symm ((P.map (Int.castRingHom _)).eval p) = y := by
    rw [φ.symm_apply_eq, h, eval_map_RingHom_prod, ha, hb]
  ---- But `φ⁻¹(P(a, b)) = P(φ⁻¹(a, b))`, so we are done.
  clear_value p; clear a b ha hb
  let ρ : ZMod k × ZMod m →+* ZMod (k * m) := φ.symm
  refine ⟨ρ p, ?_⟩
  change eval (ρ p) (map (Int.castRingHom (ZMod (k * m))) P)
    = ρ (eval p (map (Int.castRingHom (ZMod k × ZMod m)) P))
  replace h : Int.castRingHom (ZMod (k * m)) = ρ.comp (Int.castRingHom _) :=
    RingHom.ext_int _ _
  rw [h, eval_map, ← hom_eval₂, eval_map]

/-- If `k, m > 0` are coprime, then `P` is `km`-good iff `P` is `k`-good and `m`-good. -/
theorem good_iff_of_coprime (h : Nat.Coprime k m) :
    good (k * m) P ↔ good k P ∧ good m P := by
  ---- If `k = 0` then `m = 1` and we are done.
  obtain rfl | this_k : k = 0 ∨ NeZero k := eq_zero_or_neZero k
  · obtain rfl : m = 1 := (Nat.coprime_zero_left _).mp h
    exact (and_iff_left (good_one_left _)).symm
  ---- If `m = 0` then `k = 1` and we are done.
  obtain rfl | this_m : m = 0 ∨ NeZero m := eq_zero_or_neZero m
  · obtain rfl : k = 1 := (Nat.coprime_zero_right _).mp h
    exact (and_iff_right (good_one_left _)).symm
  ---- If `k, m > 0` then the statement follows from the `nice` version.
  rw [good_iff_nice, good_iff_nice, good_iff_nice, nice_iff_of_coprime h]

/-- Let `p > 1` and let `P` be a `p^2`-good polynomial. Then `p ∤ P'(x)` for any `x : ℤ`. -/
theorem good.prime_not_dvd_derivative (hp : p > 1) (hP : good (p ^ 2) P) (x : ℤ) :
    ¬(p : ℤ) ∣ P.derivative.eval x := by
  ---- Suppose `p ∣ P'(k)` for some integer `k`.
  rintro ⟨t, hx⟩
  ---- Then `P(k + p) ≡ P(k) (mod p^2)`.
  have h : ((p : ℤ) : ZMod (p ^ 2)) ^ 2 = 0 := by
    rw [Int.cast_natCast, ← Nat.cast_pow, ZMod.natCast_self]
  replace hx : ((P.eval (x + p) : ℤ) : ZMod (p ^ 2)) = P.eval x :=
    calc ((P.eval (x + p) : ℤ) : ZMod (p ^ 2))
    _ = (P.map (Int.castRingHom _)).eval ((x + p : ℤ) : ZMod (p ^ 2)) :=
      (eval_map_apply (Int.castRingHom (ZMod (p ^ 2))) _).symm
    _ = (P.map (Int.castRingHom _)).eval (x : ZMod (p ^ 2))
        + (P.map (Int.castRingHom _)).derivative.eval (Int.castRingHom _ x) * (p : ℤ) := by
      rw [Int.cast_add, eval_add_of_sq_eq_zero _ _ _ h, eq_intCast]
    _ = (P.map (Int.castRingHom _)).eval (x : ZMod (p ^ 2)) + (p : ℤ) * t * (p : ℤ) := by
      rw [derivative_map, eval_map_apply, eq_intCast, hx, Int.cast_mul]
    _ = (P.map (Int.castRingHom _)).eval (x : ZMod (p ^ 2)) := by
      rw [mul_right_comm, ← sq, h, zero_mul, add_zero]
    _ = P.eval x := eval_map_apply (Int.castRingHom (ZMod (p ^ 2))) x
  ---- If `P` is `p^2`-good, then `k + p ≡ k (mod p^2)`; but `p^2 ∤ p`, contradiction.
  clear t h
  replace hx : x + p ≡ x [ZMOD p ^ 2] := hP _ _ ((ZMod.intCast_eq_intCast_iff _ _ _).mp hx)
  rw [Int.add_modEq_left_iff, ← Int.natCast_pow, Int.natCast_dvd_natCast] at hx
  exact Nat.not_dvd_of_pos_of_lt (Nat.zero_lt_of_lt hp) (lt_self_pow₀ hp Nat.one_lt_two) hx


section

variable [Fact (Nat.Prime p)] (hP : good p P) (hP0 : ∀ x, ¬(p : ℤ) ∣ P.derivative.eval x)
include hP hP0

/-- Let `p` be a prime and let `P` be a `p`-good polynomial such that
  `p ∤ P'(x)` for every integer `x`. Then `P` is `p^k`-good for all `k ≥ 0`. -/
theorem good.pow_lift_of_not_dvd_derivative (k) : good (p ^ k) P := by
  ---- The case `k = 0` is trivial.
  obtain rfl | hk : k = 0 ∨ k > 0 := Nat.eq_zero_or_pos k
  · exact good_one_left P
  ---- For `k ≥ 1`, we induct on `k` with the base case trivial as well.
  induction k, hk using Nat.le_induction with
  | base => rwa [Nat.pow_one]
  | succ k hk k_ih => ?_
  ---- Pick any integers `a` and `b` with `P(a) ≡ P(b) (mod p^{k + 1})`.
  intro a b hab
  ---- Since `P` is `p^k`-good, Twe have `a ≡ b (mod p^k)`; write `a = p^k x + b`.
  replace k_ih : a ≡ b [ZMOD (p ^ k : ℕ)] :=
    k_ih _ _ (hab.of_dvd (Int.natCast_dvd_natCast.mpr ⟨p, rfl⟩))
  replace k_ih : ((p ^ k : ℕ) : ℤ) ∣ a - b := k_ih.symm.dvd
  rcases k_ih with ⟨x, hx⟩
  replace hx : a = p ^ k * x + b := by rwa [Int.sub_eq_iff_eq_add, Int.natCast_pow] at hx
  subst hx
  ---- It suffices to show that `p ∣ x`.
  suffices (p : ℤ) ∣ x by
    rw [Int.add_modEq_right_iff, Int.natCast_pow, Int.pow_succ]
    exact Int.mul_dvd_mul_left _ this
  ---- Going back to `P(a) = P(p^k x + b) ≡ P(b) (mod p^{k + 1})` indeed yields `p ∣ x`.
  let φ : ℤ →+* ZMod (p ^ (k + 1)) := Int.castRingHom _
  replace hab : φ (P.eval (p ^ k * x + b)) = φ (P.eval b) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr hab
  have h : ((p ^ k : ℕ) : ZMod (p ^ (k + 1))) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff, ← Nat.pow_mul, Nat.mul_two]
    exact Nat.pow_dvd_pow p (Nat.add_le_add_left hk k)
  replace h : φ (p ^ k * x) ^ 2 = 0 := by
    rw [φ.map_mul, mul_pow, eq_intCast, ← Int.natCast_pow, Int.cast_natCast, h, zero_mul]
  replace h : φ (P.eval (p ^ k * x + b))
      = φ (P.eval b) + (P.derivative.eval b * (p ^ k * x) : ℤ) := by
    rw [← eval_map_apply, φ.map_add, add_comm _ (φ b), eval_add_of_sq_eq_zero _ _ _ h,
      derivative_map, eval_map_apply, eval_map_apply, ← φ.map_mul, eq_intCast, eq_intCast]
  replace hab : (p : ℤ) ^ k * p ∣ p ^ k * (eval b (derivative P) * x) := by
    rwa [h, add_eq_left, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Int.natCast_pow, Int.mul_left_comm, Int.pow_succ] at hab
  replace hab : (p : ℤ) ∣ P.derivative.eval b * x :=
    Int.dvd_of_mul_dvd_mul_left (h := hab) <|
      Int.pow_ne_zero (Int.natCast_ne_zero.mpr (NeZero.ne p))
  exact ((Nat.prime_iff_prime_int.mp Fact.out).dvd_or_dvd hab).resolve_left (hP0 b)

/-- Let `p` be a prime and let `P` be a `p`-good polynomial such that
  `P'` does not have a root mod `p`. Then `P` is very good. -/
theorem good.veryGood_of_not_dvd_derivative : veryGood P :=
  λ N ↦ ⟨p ^ N, Nat.lt_pow_self (Nat.Prime.one_lt Fact.out),
    hP.pow_lift_of_not_dvd_derivative hP0 N⟩

end





/-! ### Part 1 -/

/-- Evaluating `X^3 - bX` at a point. -/
theorem eval_X3_sub_mul_X [CommRing R] (b r : R) :
    (X ^ 3 - C b * X).eval r = r ^ 3 - b * r := by
  rw [eval_sub, eval_C_mul, eval_X_pow, eval_X]

/-- The polynomial `X^3 - n^2 X` is not `k`-good for any `k > n`. -/
theorem not_good_X3_sub_sq_mul_X_of_lt {n k : ℕ} (hn : n > 0) (hnk : n < k) :
    ¬good k (X ^ 3 - C (n ^ 2 : ℤ) * X) := by
  ---- This follows from `n^3 - n^2 n = 0^3 - n^2 0 = 0`.
  intro hk; specialize hk n 0
  rw [eval_X3_sub_mul_X, ← Int.pow_succ, Int.sub_self,
    eval_X3_sub_mul_X, Int.pow_succ, ← Int.sub_mul, Int.mul_zero] at hk
  replace hk : n ≡ 0 [ZMOD k] := hk (Int.ModEq.refl _)
  rw [Int.modEq_zero_iff_dvd, Int.natCast_dvd_natCast] at hk
  exact Nat.not_dvd_of_pos_of_lt hn hnk hk

/-- The polynomial `X^3 - n^2 X` is not very good for any `n : ℕ` with `n ≠ 0`. -/
theorem not_veryGood_X3_sub_sq_mul_X {n : ℕ} (hn : n > 0) :
    ¬veryGood (X ^ 3 - C (n ^ 2 : ℤ) * X) := by
  intro h
  obtain ⟨k, hkn, hk⟩ : ∃ k > n, good k (X ^ 3 - C (n ^ 2 : ℤ) * X) := h n
  exact not_good_X3_sub_sq_mul_X_of_lt hn hkn hk

/-- Let `p` be a prime with either `p = 3` or `p ≡ 2 (mod 3)`.
  Then for any `b : ℤ` with `p ∣ b`, `X^3 - bX` is `p`-good. -/
theorem good_prime_X3_sub_mul_X
    {p : ℕ} {b : ℤ} [Fact p.Prime] (hp : p = 3 ∨ p % 3 = 2) (hpb : (p : ℤ) ∣ b) :
    good p (X ^ 3 - C b * X) := by
  ---- We prove this via surjectivity; for any `x`, pick `x^{2(p + 1)/3 - 1}`.
  have hp0 : Nat.Prime p := Fact.out
  refine good_iff_nice.mpr λ x ↦ ⟨x ^ (2 * ((p + 1) / 3) - 1), ?_⟩
  ---- Since `p ∣ b`, we only need to check that `x^{(2(p + 1)/3 - 1) 3} ≡ x (mod p)`.
  suffices (x : ZMod p) ^ ((2 * ((p + 1) / 3) - 1) * 3) = x by
    calc eval (x ^ (2 * ((p + 1) / 3) - 1)) (X ^ 3 - C b * X)
    _ = (x ^ (2 * ((p + 1) / 3) - 1)) ^ 3 - b * (x ^ (2 * ((p + 1) / 3) - 1)) :=
      eval_X3_sub_mul_X _ _
    _ ≡ x ^ ((2 * ((p + 1) / 3) - 1) * 3) [ZMOD p] := by
      rw [Int.pow_mul, Int.sub_eq_add_neg, Int.add_modEq_left_iff, ← Int.mul_neg]
      exact Int.dvd_mul_of_dvd_left hpb
    _ ≡ x [ZMOD p] := by rw [← ZMod.intCast_eq_intCast_iff, Int.cast_pow, this]
  generalize (x : ZMod p) = x
  ---- If `p = 3`, then our goal is `x^3 ≡ x (mod 3)`.
  rcases hp with rfl | hp
  · exact ZMod.pow_card _
  ---- If `p ≡ 2 (mod 3)`, then our goal is `x^{2p - 1} ≡ x (mod p)`.
  replace hp : 3 ∣ p + 1 := by rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_add_mod, hp]
  replace hpb : x ^ p = x := ZMod.pow_card _
  have hp0 : p > 0 := (Fact.out : p.Prime).pos
  calc x ^ ((2 * ((p + 1) / 3) - 1) * 3)
    _ = x ^ (2 * (p + 1) - 3) := by
      rw [Nat.sub_one_mul, Nat.mul_assoc, Nat.div_mul_cancel hp]
    _ = x ^ (p + p - 1) := by rw [Nat.mul_succ, Nat.add_sub_add_right, Nat.two_mul]
    _ = x * x ^ (p - 1) := by rw [Nat.add_sub_assoc hp0, pow_add, hpb]
    _ = x := by rw [← pow_succ', Nat.sub_add_cancel hp0, hpb]

/-- Let `p` be a prime with `p % 3 = 2`. Then `X^3 - (3p)^2 X` is `3p`-good. -/
theorem good_three_mul_prime_X3_sub_sq_mul_X {p : ℕ} [Fact p.Prime] (hp : p % 3 = 2) :
    good (3 * p) (X ^ 3 - C ((3 * p) ^ 2 : ℤ) * X) := by
  have hp0 : Nat.Coprime 3 p := by
    rw [Nat.prime_three.coprime_iff_not_dvd, Nat.dvd_iff_mod_eq_zero, hp]; decide
  refine (good_iff_of_coprime hp0).mpr ⟨?_, ?_⟩
  · refine good_prime_X3_sub_mul_X (Or.inl rfl) ⟨3 * p ^ 2, ?_⟩
    rw [Int.mul_pow, sq, Int.mul_assoc]; rfl
  · refine good_prime_X3_sub_mul_X (Or.inr hp) ⟨3 ^ 2 * p, ?_⟩
    rw [Int.mul_pow, sq (p : ℤ), Int.mul_left_comm]

/-- Final solution, part 1 -/
theorem final_solution_part1 :
    let P : ℤ[X] := X ^ 3 - C (51 ^ 2) * X
    good 51 P ∧ ¬veryGood P :=
  haveI : Fact (Nat.Prime 17) := ⟨by decide⟩
  ⟨good_three_mul_prime_X3_sub_sq_mul_X (p := 17) rfl,
  not_veryGood_X3_sub_sq_mul_X (Nat.succ_pos 50)⟩



/-! ### Part 2 -/

/-- Mapping `aX^3 + bX` under a ring homomorphism from `ℤ` to a commutative ring. -/
theorem map_mul_X3_add_mul_X (R) [CommRing R] (a b : ℤ) :
    (C a * X ^ 3 + C b * X).map (Int.castRingHom R) = C (a : R) * X ^ 3 + C (b : R) * X := by
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    map_C, map_C, eq_intCast, eq_intCast, Polynomial.map_pow, map_X]

/-- If `P(X) = aX^3 + bX`, then `P'(X) = 3aX^2 + b`. -/
theorem derivative_mul_X3_add_mul_X (a b : ℤ) :
    (C a * X ^ 3 + C b * X).derivative = C (3 * a) * X ^ 2 + C b := by
  rw [derivative_add, derivative_C_mul_X_pow, Int.mul_comm, derivative_C_mul_X]; rfl


section

variable [Fintype F] [Field F] (hF3 : ringChar F ≠ 3)
include hF3

/-- Let `F` be a finite field of characteristic `≠ 3`.
  Then for any `x : F`, there exists `t, u : F` such that `t^2 + tu + u^2 = x`. -/
theorem exists_cyclotomic3_eq_of_char_ne3 (x : F) :
    ∃ t u : F, t ^ 2 + t * u + u ^ 2 = x := by
  ---- If `char(F) = 2`, then take `t = 0` and let `u` be the square root of `x`.
  obtain hF2 | hF2 : ringChar F = 2 ∨ ringChar F ≠ 2 := eq_or_ne _ _
  · obtain ⟨u, rfl⟩ : IsSquare x := FiniteField.isSquare_of_char_two hF2 x
    refine ⟨0, u, ?_⟩
    rw [sq, ← mul_add, zero_mul, zero_add, sq]
  ---- If `char(F) ≠ 2`, use `exists_root_sum_quadratic` and get `r^2 + (3s^2 - x) = 0`.
  obtain ⟨r, s, h⟩ : ∃ r s : F, (X ^ 2).eval r + (C 3 * X ^ 2 - C x).eval s = 0 := by
    have hF : (3 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F Nat.prime_three hF3
    have h : (C (3 : F) * X ^ 2).degree = 2 := degree_C_mul_X_pow 2 hF
    replace h : (C (3 : F) * X ^ 2 - C x).degree = 2 :=
      (degree_sub_C (h.trans_gt zero_lt_two)).trans h
    exact FiniteField.exists_root_sum_quadratic
      (degree_X_pow 2) h (FiniteField.odd_card_of_char_ne_two hF2)
  ---- Rearranging gives `r^2 + 3s^2 = x`.
  replace h : r ^ 2 + 3 * s ^ 2 = x := by
    rwa [eval_X_pow, eval_sub, eval_C, eval_mul_X_pow,
      eval_C, ← add_sub_assoc, sub_eq_zero] at h
  ---- Finally, set `t = r - 2s` and `u = s`.
  refine ⟨r - s, 2 * s, ?_⟩
  subst h; ring

/-- Let `F` be a finite field of characteristic `≠ 3`.
  Then for any `x : F` nonzero, there exists `t ≠ u : F` such that `t^2 + tu + u^2 = x`. -/
theorem exists_cyclotomic3_eq_of_char_ne3' {x : F} (hx : x ≠ 0) :
    ∃ t u : F, t ≠ u ∧ t ^ 2 + t * u + u ^ 2 = x := by
  obtain ⟨t, u, rfl⟩ : ∃ t u, t ^ 2 + t * u + u ^ 2 = x :=
    exists_cyclotomic3_eq_of_char_ne3 hF3 x
  obtain htu | rfl : t ≠ u ∨ t = u := ne_or_eq t u
  · exact ⟨t, u, htu, rfl⟩
  · refine ⟨t + t, -t, λ h ↦ hx ?_, by ring⟩
    rw [sq, ← add_mul, h, neg_mul, neg_add_cancel]

end


/-- Rewriting the condition that the polynomial `aX^3 + bX` is `n`-good. -/
theorem good_mul_X3_add_mul_X_iff {n : ℕ} {a b : ℤ} :
    good n (C a * X ^ 3 + C b * X) ↔ (λ x : ZMod n ↦ a * x ^ 3 + b * x).Injective := by
  rw [good_iff_ZMod, map_mul_X3_add_mul_X]
  simp_rw [eval_add, eval_C_mul, eval_X_pow, eval_X]


section

variable {p : ℕ} [Fact p.Prime] (h : good p (C a * X ^ 3 + C b * X))
include h

/-- If `aX^3 + bX` is `p`-good where `p ≠ 3` is prime, then either `p ∣ a` or `p ∣ b`. -/
theorem good.prime_dvd_X3_coeff_or_X_coeff (hp : p ≠ 3) : (p : ℤ) ∣ a ∨ (p : ℤ) ∣ b := by
  by_contra! h0
  ---- Pick `t ≠ u ∈ 𝔽_p` with `t^2 + tu + u^2 = -b/a`.
  replace h0 : (a : ZMod p) ≠ 0 ∧ (b : ZMod p) ≠ 0 := by
    simpa only [ZMod.intCast_zmod_eq_zero_iff_dvd, Ne] using h0
  obtain ⟨t, u, htu, h1⟩ : ∃ t u : ZMod p, t ≠ u ∧ t ^ 2 + t * u + u ^ 2 = -(b / a) :=
    exists_cyclotomic3_eq_of_char_ne3' ((ZMod.ringChar_zmod_n p).trans_ne hp)
      (neg_ne_zero.mpr (div_ne_zero h0.2 h0.1))
  ---- Since `t^2 + tu + u^2 = -b/a`, one can check that `at^3 + bt = au^3 + bu`.
  replace h1 : a * (t ^ 3 - u ^ 3) = b * (u - t) :=
    calc a * (t ^ 3 - u ^ 3)
    _ = a * -(t ^ 2 + t * u + u ^ 2) * (u - t) := by ring
    _ = b * (u - t) := by rw [h1, neg_neg, mul_div_cancel₀ _ h0.1]
  replace h1 : a * t ^ 3 + b * t = a * u ^ 3 + b * u := by
    rw [add_comm _ (b * u), ← sub_eq_sub_iff_add_eq_add, ← mul_sub, h1, mul_sub]
  ---- Thus `t = u`; contradiction.
  exact htu (good_mul_X3_add_mul_X_iff.mp h h1)

/-- If `aX^3 + bX` is `p`-good where `p` is prime and `p ≡ 1 (mod 3)`, then `p ∤ b`. -/
theorem good.prime_not_dvd_X_coeff (hp : p % 3 = 1) : ¬(p : ℤ) ∣ b := by
  ---- If `p ∣ b`, then the map `x ↦ ax^3` is injective.
  intro hb; replace hb : (b : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd b p).mpr hb
  replace h : Function.Injective (λ x : ZMod p ↦ a * x ^ 3) := by
    simp_rw [good_mul_X3_add_mul_X_iff, hb, zero_mul, add_zero] at h; exact h
  ---- Now pick a primitive third root of unity mod `p`, say `x : 𝔽_p`.
  obtain ⟨x, hx⟩ : ∃ x : (ZMod p)ˣ, orderOf x = 3 := by
    have h0 : 3 ∣ Fintype.card (ZMod p)ˣ := by
      rw [ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
      exact (Nat.modEq_iff_dvd' NeZero.one_le).mp hp.symm
    exact exists_prime_orderOf_dvd_card 3 h0
  ---- Then `ax^3 = a 1^3`, contradicting injectivity of the map `x ↦ ax^3`.
  replace h : x = 1 := by
    refine Units.val_eq_one.mp (h (?_ : (a : ZMod p) * _ = a * _))
    rw [one_pow, ← Units.val_pow_eq_pow_val, ← hx, pow_orderOf_eq_one, Units.val_one]
  rw [h, orderOf_one] at hx
  exact absurd hx.symm (Nat.succ_succ_ne_one 1)

/-- Let `p` be a prime with `p % 3 = 1`. If `aX^3 + bX` is `p`-good then it is very good. -/
theorem good.veryGood_cubic (hp : p % 3 = 1) : veryGood (C a * X ^ 3 + C b * X) := by
  refine h.veryGood_of_not_dvd_derivative λ x ↦ ?_
  have hb : ¬(p : ℤ) ∣ b := h.prime_not_dvd_X_coeff hp
  have hp0 : p ≠ 3 := λ hp1 ↦ absurd hp (hp1.symm ▸ Nat.zero_ne_one)
  have ha : (p : ℤ) ∣ a := (h.prime_dvd_X3_coeff_or_X_coeff hp0).resolve_right hb
  rwa [derivative_mul_X3_add_mul_X, eval_add, eval_C_mul, eval_C,
    Int.mul_right_comm, Int.dvd_add_right (Int.dvd_mul_of_dvd_right ha)]

end


/-- Final solution, part 2 -/
theorem final_solution_part2 {a b : ℤ} (h : good 2010 (C a * X ^ 3 + C b * X)) :
    veryGood (C a * X ^ 3 + C b * X) :=
  haveI : Fact (Nat.Prime 67) := ⟨by decide⟩
  (h.of_dvd ⟨30, rfl⟩).veryGood_cubic (p := 67) rfl
