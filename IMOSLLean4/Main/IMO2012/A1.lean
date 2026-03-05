/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Tactic.Ring
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# IMO 2012 A1

A triple $(a, b, c)$ of integers is called a *Heron triple* if
$$ a^2 + b^2 + c^2 = 2ab + 2bc + 2ca. $$
Find all functions $f : ℤ → ℤ$ such that $f(a), f(b), f(c))$ is
  a Heron triple for any $a, b, c ∈ ℤ$ satisfying $a + b + c = 0$.

### Answer

They are precisely the functions of the following form:
* $f(n) = cn^2$;
* $f(n) = \begin{cases} c & \text{if } 2 ∤ n, \\ 0 & \text{if } 2 ∣ n, \end{cases}$;
* $f(n) = \begin{cases} c & \text{if } 2 ∤ n, \\ 4c & \text{if } n ≡ 2 \pmod{4}, \\
    0 & \text{if } 2 ∣ n. \end{cases}$

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2012SL.pdf).
Our implementation is slightly more complicated at the final step in the case where
  $f(2) = 4f(1)$ and $f(3) = 9f(1)$, but it works even when the range of the function
  is generalized to any integral domain (of characteristic not equal to $3$).
The difference is that $k(n - 1)^2 ≠ k(n - 3)^2$ is not always true this time,
  but $k(n - 1)^2 = k(n - 3)^2$ would imply either $k = 0$, $R$ has characteristic $2$,
  or $n = 2$ in $R$, and in all cases we still get $f(n + 1) = k(n + 1)^2$.
-/

namespace IMOSL
namespace IMO2012A1


/-! ### Heron triples -/

/-- A triple `(a, b, c) ∈ R^3` is called a *Heron triple*
  if `a^2 + b^2 + c^2 = 2ab + 2bc + 2ca`. -/
def HeronTriple [CommSemiring R] (a b c : R) :=
  a ^ 2 + b ^ 2 + c ^ 2 = 2 * (a * b + b * c + c * a)


namespace HeronTriple

instance [CommSemiring R] [DecidableEq R] (a b c : R) : Decidable (HeronTriple a b c) :=
  decEq _ _


section

variable [CommSemiring R] {a b c : R} (h : HeronTriple a b c)
include h

/-- If `(a, b, c)` is a Heron triple, then `(b, c, a)` is a Heron triple. -/
theorem perm231 : HeronTriple b c a := by
  rw [HeronTriple, ← add_rotate, h, add_rotate]

/-- If `(a, b, c)` is a Heron triple, then `(c, a, b)` is a Heron triple. -/
theorem perm312 : HeronTriple c a b :=
  h.perm231.perm231

/-- If `(a, b, c)` is a Heron triple, then `(b, a, c)` is a Heron triple. -/
theorem perm213 : HeronTriple b a c := by
  rw [HeronTriple, add_comm (b ^ 2), h, add_right_comm, mul_comm a, mul_comm c, mul_comm b c]

/-- If `(a, b, c)` is a Heron triple, then `(c, b, a)` is a Heron triple. -/
theorem perm321 : HeronTriple c b a :=
  h.perm231.perm213

/-- If `(a, b, c)` is a Heron triple, then `(a, c, b)` is a Heron triple. -/
theorem perm132 : HeronTriple a c b :=
  h.perm213.perm231

/-- If `(a, b, c)` is a Heron triple, then `(ra, rb, rc)` is a Heron triple for any `r`. -/
theorem mul_left (r : R) : HeronTriple (r * a) (r * b) (r * c) := by
  unfold HeronTriple
  iterate 3 rw [mul_pow, mul_mul_mul_comm r _ r]
  iterate 4 rw [← mul_add]
  rw [h, mul_left_comm, sq]

end


variable [CommRing R]

/-- The main formula which inspires the name "Heron triple":
  `2(a^2 b^2 + b^2 c^2 + c^2 a^2) - (a^4 + b^4 + c^4)` is equal to
  `(a + b - c)(b + c - a)(c + a - b)(a + b + c)`. -/
theorem reference_formula (a b c : R) :
    2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)
        - ((a ^ 2) ^ 2 + (b ^ 2) ^ 2 + (c ^ 2) ^ 2)
      = (a + b - c) * (b + c - a) * (c + a - b) * (a + b + c) := by ring

/-- The triple `(a^2, b^2, c^2)` is a Heron triple if `a + b + c = 0`. -/
theorem squares_of_add_eq_zero {a b c : R} (h : a + b + c = 0) :
    HeronTriple (a ^ 2) (b ^ 2) (c ^ 2) := by
  rw [HeronTriple, eq_comm, ← sub_eq_zero, reference_formula, h, mul_zero]


section

variable [NoZeroDivisors R]

/-- If `char(R) ≠ 3` and `(x, x, x)` is a Heron triple, then `x = 0`. -/
theorem eq_zero_of_const (hR : (3 : R) ≠ 0) {c : R} (hc : HeronTriple c c c) : c = 0 := by
  rwa [HeronTriple, sq, two_mul, right_eq_add, ← two_mul, ← add_one_mul,
    mul_eq_zero, two_add_one_eq_three, or_iff_right hR, mul_self_eq_zero] at hc

/-- The triple `(x, y, 0)` is a Heron triple if and only if `x = y`. -/
theorem iff_eq_of_zero_right {x y : R} : HeronTriple x y 0 ↔ x = y := by
  rw [HeronTriple, sq 0, mul_zero, add_zero, mul_zero, add_zero, zero_mul,
    add_zero, ← mul_assoc, ← sub_eq_zero, ← sub_sq', sq_eq_zero_iff, sub_eq_zero]

/-- The triple `(rx^2, ry^2, z)` is a Heron triple if and only if
  either `z = r(x + y)^2` or `z = r(x - y)^2`. -/
theorem iff_eq_mul_add_or_sub_sq {r x y z : R} :
    HeronTriple (r * x ^ 2) (r * y ^ 2) z ↔ z = r * (x + y) ^ 2 ∨ z = r * (x - y) ^ 2 := by
  calc HeronTriple (r * x ^ 2) (r * y ^ 2) z
  _ ↔ (r * x ^ 2) ^ 2 + (r * y ^ 2) ^ 2 + z ^ 2
      - 2 * ((r * x ^ 2) * (r * y ^ 2) + (r * y ^ 2) * z + z * (r * x ^ 2)) = 0 :=
    sub_eq_zero.symm
  _ ↔ (z - r * (x + y) ^ 2) * (z - r * (x - y) ^ 2) = 0 := Eq.congr_left (by ring)
  _ ↔ z = r * (x + y) ^ 2 ∨ z = r * (x - y) ^ 2 := by
    rw [mul_eq_zero, sub_eq_zero, sub_eq_zero]

/-- The triple `(r, r, z)` is a Heron triple if and only if `z = 4r` or `z = 0`. -/
theorem iff_of_left_mid_eq {r z : R} : HeronTriple r r z ↔ z = r * 2 ^ 2 ∨ z = 0 := calc
  _ ↔ HeronTriple (r * 1 ^ 2) (r * 1 ^ 2) z := by rw [one_pow, mul_one]
  _ ↔ z = r * (1 + 1) ^ 2 ∨ z = r * (1 - 1) ^ 2 := iff_eq_mul_add_or_sub_sq
  _ ↔ z = r * 2 ^ 2 ∨ z = 0 := by
    rw [one_add_one_eq_two, sub_self, zero_pow (Nat.succ_ne_zero 1), mul_zero]

end

end HeronTriple





/-! ### Start of the problem -/

open HeronTriple

/-- A function `f : G → R` is called *good* if `(f(a), f(b), f(c))` is
  a Heron triple whenever `a, b, c ∈ G` satisfies `a + b + c = 0`. -/
def good [AddZero G] [CommSemiring R] (f : G → R) :=
  ∀ a b c : G, a + b + c = 0 → HeronTriple (f a) (f b) (f c)

instance [DecidableEq G] [Fintype G] [AddZero G] [CommSemiring R] [DecidableEq R]
    (f : G → R) : Decidable (good f) :=
  Fintype.decidableForallFintype

/-- The square function is good. -/
theorem sq_is_good [CommRing R] : good (λ r : R ↦ r ^ 2) :=
  λ _ _ _ ↦ squares_of_add_eq_zero

/-- The function `f : ZMod 2 → ℤ` defined by `f(0) = 0` and `f(1) = 1` is good. -/
theorem ZMod2_01_is_good : good (![0, 1] : ZMod 2 → ℤ) := by
  decide

/-- The function `f : ZMod 4 → ℤ` defined by `0 ↦ 0, 1 ↦ 1, 2 ↦ 4, 3 ↦ 1` is good. -/
theorem ZMod4_0141_is_good : good (![0, 1, 4, 1] : ZMod 4 → ℤ) := by
  decide


namespace good

/-- An alternative definition of `good` function when `G` is a group. -/
theorem alt_def [AddGroup G] [CommSemiring R] {f : G → R} (hf : good f) (a b : G) :
    HeronTriple (f a) (f b) (f (-(a + b))) :=
  hf a b (-(a + b)) (add_neg_cancel _)

/-- If `f : G → R` is good, then the function `rf : x ↦ rf(x)` is good for any `r : R`. -/
theorem smul_left [AddZero G] [CommSemiring R]
    {f : G → R} (hf : good f) (r : R) : good (r • f) :=
  λ a b c h ↦ (hf a b c h).mul_left r

/-- If `f : G → R` is good and `φ : G₀ → G` is a group homomorphism, `f ∘ φ` is good. -/
theorem comp_AddMonoidHom [AddZero G₀] [AddZero G] [CommSemiring R]
    {f : G → R} (hf : good f) (φ : G₀ →+ G) : good (f ∘ φ) :=
  λ a b c h ↦ hf _ _ _ (by rw [← φ.map_add, ← φ.map_add, h, φ.map_zero])


section

variable [AddGroup G] [CommRing R] [NoZeroDivisors R]

/-- Suppose that `char(R) ≠ 3`. If `f : G → R` is good then `f(0) = 0`. -/
theorem map_zero_of_three_ne_zero (hR : (3 : R) ≠ 0) {f : G → R} (hf : good f) : f 0 = 0 :=
  (hf 0 0 0 ((add_zero _).trans (add_zero _))).eq_zero_of_const hR


variable {f : G → R} (hf : good f) (hf0 : f 0 = 0)
include hf hf0

/-- If `f : G → R` is good with `f(0) = 0` then `f` is even. -/
theorem map_neg_of_map_zero (x) : f (-x) = f x := by
  have h : HeronTriple (f (-x)) (f x) (f 0) :=
    hf (-x) x 0 ((add_zero _).trans (neg_add_cancel x))
  rwa [hf0, iff_eq_of_zero_right] at h

/-- If `f : G → R` is good with `f(0) = 0` then
  `(f(x), f(y), f(x + y))` is a Heron triple for any `x, y : G`. -/
theorem def_of_map_zero (x y : G) : HeronTriple (f x) (f y) (f (x + y)) := by
  simpa only [hf.map_neg_of_map_zero hf0] using hf.alt_def x y

/-- If `f : G → R` is good with `f(0) = 0` and `c : G` satisfies `f(c) = 0`,
  then `f(x + c) = f(x)` for any `x : G`. -/
theorem map_add_of_map_eq_zero {c : G} (hc : f c = 0) (x) : f (x + c) = f x := by
  have h : HeronTriple (f (x + c)) (f x) (f c) := (hf.def_of_map_zero hf0 x c).perm312
  rwa [hc, iff_eq_of_zero_right] at h

/-- If `f : G → R` is good with `f(0) = 0` and `c : G` satisfies `f(c) = 0`,
  then `f(nc) = 0` for every integer `n`. -/
theorem map_nsmul_of_map_eq_zero {c : G} (hc : f c = 0) (n : ℤ) : f (n • c) = 0 := by
  induction n using Int.induction_on with
  | zero => rw [zero_zsmul, hf0]
  | succ n n_ih => rw [add_one_zsmul, hf.map_add_of_map_eq_zero hf0 hc, n_ih]
  | pred n n_ih =>
      replace hc : f (-c) = 0 := (hf.map_neg_of_map_zero hf0 c).trans hc
      rw [sub_one_zsmul, hf.map_add_of_map_eq_zero hf0 hc, n_ih]

end


section

variable [CommRing R] [NoZeroDivisors R] {f : ℤ → R} (hf : good f) (hf0 : f 0 = 0)
include hf hf0

/-- If `f(0) = 0` and `f(N) = 0` for some `N : ℕ` nonzero, then for any `n : ℕ`,
  we have `f(n) = f(x)` where `x` is the image of `n` in `Fin N`. -/
theorem Int_map_ZMod_of_map_eq_zero {N : ℕ} [NeZero N] (hN : f N = 0) (n : ℤ) :
    f (n : ZMod N).val = f n := by
  obtain ⟨k, hk⟩ : (N : ℤ) ∣ n - (n : ZMod N).val := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, ZMod.natCast_val,
      ZMod.intCast_cast, ZMod.cast_intCast (Nat.dvd_refl _), sub_self]
  calc f (n : ZMod N).val
    _ = f ((n : ZMod N).val + k * N) :=
      (hf.map_add_of_map_eq_zero hf0 (hf.map_nsmul_of_map_eq_zero hf0 hN k) _).symm
    _ = f n := by rw [Int.mul_comm, ← hk, add_sub_cancel]

/-- If `f(0) = 0`, then `f(2)` is equal to either `4 f(1)` or `0`. -/
theorem Int_map_two_eq : f 2 = f 1 * 2 ^ 2 ∨ f 2 = 0 :=
  iff_of_left_mid_eq.mp (hf.def_of_map_zero hf0 1 1)

/-- If `f(0) = f(2) = 0`, then `f(n) = f(1)` if `n` is odd and `f(n) = 0` if `n` is even. -/
theorem Int_eq_smul_ZMod2_01_of_map_two (hf1 : f 2 = 0) :
    f = λ n : ℤ ↦ f 1 * ![0, 1] (n : ZMod 2) := by
  have h : ∀ x : ZMod 2, f x.val = f 1 * ![0, 1] x
    | 0 => hf0.trans (mul_zero _).symm
    | 1 => (mul_one _).symm
  funext n; rw [← hf.Int_map_ZMod_of_map_eq_zero hf0 hf1 _, h]

/-- If `f(0) = 0 0` and `f(2) = 4 f(1)`, then `f(3)` is either `9 f(1)` or `f(1)`. -/
theorem Int_map_three_eq_of_map_two (hf1 : f 2 = f 1 * 2 ^ 2) :
    f 3 = f 1 * 3 ^ 2 ∨ f 3 = f 1 := by
  have h : HeronTriple (f 1 * 2 ^ 2) (f 1 * 1 ^ 2) (f 3) := by
    rw [one_pow, mul_one, ← hf1]; exact hf.def_of_map_zero hf0 2 1
  rwa [iff_eq_mul_add_or_sub_sq, two_add_one_eq_three,
    sub_eq_of_eq_add one_add_one_eq_two.symm, one_pow, mul_one] at h

/-- If `f(0) = 0`, `f(2) = 4 f(1)`, and `f(3) = 9 f(1)`,
  then `f(n) = f(1) n^2` for all integers `n`. -/
theorem Int_eq_smul_sq_of_map_three (hf1 : f 2 = f 1 * 2 ^ 2) (hf2 : f 3 = f 1 * 3 ^ 2) :
    f = λ n : ℤ ↦ f 1 * n ^ 2 := by
  ---- Since `f` is even, we only need to check `f(n) = f(1) n^2` for `n : ℕ`.
  suffices ∀ n : ℕ, f n = f 1 * n ^ 2 by
    funext n; have h : f n = f n.natAbs := by
      obtain hn | hn : n = n.natAbs ∨ n = -n.natAbs := n.natAbs_eq
      exacts [congrArg f hn, (congrArg f hn).trans (hf.map_neg_of_map_zero hf0 _)]
    rw [h, this, ← Int.cast_natCast, ← Int.cast_pow, Int.natAbs_sq, Int.cast_pow]
  ---- We proceed by strong induction on `n`, with the base cases `n ≤ 3` easy to check.
  intro n; induction n using Nat.strong_induction_on with | h n n_ih => ?_
  have hf3 : f 1 = f 1 * 1 ^ 2 := by rw [one_pow, mul_one]
  match n with
    | 0 => rw [Int.natCast_zero, hf0, Nat.cast_zero, zero_pow (Nat.succ_ne_zero 1), mul_zero]
    | 1 => rw [Int.natCast_one, Nat.cast_one, ← hf3]
    | 2 => exact hf1
    | 3 => exact hf2
    | n + 4 => ?_
  change f (n + 4) = _
  ---- First, `(a, b) = (n + 3, 1)` gives `f(n + 4) ∈ {f(1) (n + 4)^2, f(1) (n + 2)^2}`.
  obtain h | h :
      f (n + 4) = f 1 * ((n + 3 : ℕ) + 1) ^ 2 ∨ f (n + 4) = f 1 * ((n + 3 : ℕ) - 1) ^ 2 := by
    have h := hf.def_of_map_zero hf0 (n + 3 : ℕ) 1
    rwa [hf3, n_ih (n + 3) (Nat.lt_succ_self _), iff_eq_mul_add_or_sub_sq] at h
  · rw [Nat.cast_succ, h]
  ---- Second, `(a, b) = (n + 2, 2)` gives `f(n + 4) ∈ {f(1) (n + 4)^2, f(1) n^2}`.
  obtain h0 | h0 :
      f (n + 4) = f 1 * ((n + 2 : ℕ) + 2) ^ 2 ∨ f (n + 4) = f 1 * ((n + 2 : ℕ) - 2) ^ 2 := by
    have h0 := hf.def_of_map_zero hf0 (n + 2 : ℕ) 2
    rwa [hf1, n_ih _ (Nat.le_add_right _ 1), iff_eq_mul_add_or_sub_sq] at h0
  · rw [Nat.cast_add (n + 2) 2, Nat.cast_two, h0]
  ---- Now assume `f(n + 4) = f(1) (n + 2)^2 = f(1) n^2`.
  replace h0 : f (n + 4) = f 1 * n ^ 2 := by
    rwa [Nat.cast_add, Nat.cast_two, add_sub_cancel_right] at h0
  replace h : f (n + 4) = f 1 * (n + 2) ^ 2 := by
    rwa [Nat.cast_succ, add_sub_cancel_right, Nat.cast_add] at h
  ---- Then we have either `f(1) = 0` or `(n + 2)^2 = n^2` over `R`.
  replace h : f 1 = 0 ∨ (n + 2 : R) ^ 2 = n ^ 2 := by
    rwa [h0, eq_comm, mul_eq_mul_left_iff, or_comm] at h
  ---- The case `f(1) = 0` is trivial, so now assume `(n + 2)^2 = n^2` on `R`.
  rcases h with h | h
  · rw [h0, h, zero_mul, zero_mul]
  ---- Rearranging gives `4(n + 1) = 0`, so either `2 = 0` on `R` or `n + 1 = 0` on `R`.
  replace h : (2 : R) = 0 ∨ (n + 1 : R) = 0 := by
    rwa [add_sq, add_assoc, add_eq_left, mul_right_comm, ← sq, ← mul_add_one,
      mul_eq_zero, pow_eq_zero_iff (Nat.succ_ne_zero 1)] at h
  ---- If `2 = 0` on `R`, we have `f(n + 4) = f(1) n^2 = f(1) (n + 4)^2`.
  rcases h with h | h
  · rw [h0, Nat.cast_add _ 2, Nat.cast_add, Nat.cast_two, h, add_zero, add_zero]
  ---- Finally, if `n + 1 = 0` on `R`, then `f(n + 4) = f(3) = f(1) (n + 4)^2`.
  replace h0 : f (n + 1 : ℕ) = 0 := by
    rw [n_ih (n + 1) (Nat.le_add_right _ 2), Nat.cast_succ, h, sq, mul_zero, mul_zero]
  calc f (n + 4 : ℕ)
    _ = f (3 + (n + 1 : ℕ)) := by rw [Nat.cast_add _ 3, add_comm, Nat.cast_three]
    _ = f 3 := hf.map_add_of_map_eq_zero hf0 h0 3
    _ = f 1 * 3 ^ 2 := hf2
    _ = f 1 * (n + 4 : ℕ) ^ 2 := by rw [Nat.cast_add _ 3, Nat.cast_succ, h, zero_add]; rfl

end


/-- If `char(R) ≠ 3`, `f(2) = 4 f(1)`, and `f(3) = f(1)`, then `f(n) = f(1)` if `n` is odd,
  `f(n) = 4f(1)` if `n ≡ 2 (mod 4)`, and `f(n) = 0` if `4 ∣ n`. -/
theorem Int_eq_smul_ZMod4_0141_of_map_three
    [CommRing R] [NoZeroDivisors R] (hR : (3 : R) ≠ 0)
    {f : ℤ → R} (hf : good f) (hf0 : f 2 = f 1 * 2 ^ 2) (hf1 : f 3 = f 1) :
    f = λ n : ℤ ↦ f 1 * ![0, 1, 4, 1] (n : ZMod 4) := by
  have hR0 : (2 : R) ^ 2 = 4 := by rw [sq, mul_two, two_add_two_eq_four]
  have hf2 : f 0 = 0 := hf.map_zero_of_three_ne_zero hR
  ---- It suffices to prove `f(4) = 0` by periodicity.
  suffices f 4 = 0 by
    have h : ∀ x : ZMod 4, f x.val = f 1 * ![0, 1, 4, 1] x
      | 0 =>  hf2.trans (mul_zero _).symm
      | 1 =>  (mul_one _).symm
      | 2 =>  hf0.trans (congrArg (f 1 * ·) hR0)
      | 3 =>  hf1.trans (mul_one _).symm
    funext n; rw [← hf.Int_map_ZMod_of_map_eq_zero hf2 this _, h]
  ---- First, since `f(3) = f(1)`, we have `f(4) ∈ {0, 4f(1)}`; assume the latter.
  obtain hf3 | hf3 : f 4 = 0 ∨ f 4 = f 1 * 2 ^ 2 := by
    have h : HeronTriple (f 3) (f 1) (f 4) := hf.def_of_map_zero hf2 3 1
    rwa [hf1, iff_of_left_mid_eq, or_comm] at h
  · exact hf3
  ---- Next, we also have `f(4) ∈ {0, 4f(2)}`; assume the latter as well.
  obtain hf4 | hf4 : f 4 = 0 ∨ f 4 = f 2 * 2 ^ 2 :=
    (iff_of_left_mid_eq.mp (hf.def_of_map_zero hf2 2 2)).symm
  · exact hf4
  ---- Then `4f(1) = 4f(2) = 16f(1) ↔ 12f(1) = 0 → f(4) = 4f(1) = 0` since `3 ≠ 0` in `R`.
  rwa [hf0, ← hf3, eq_comm, ← sub_eq_zero, ← mul_sub_one, hR0, mul_eq_zero,
    sub_eq_of_eq_add three_add_one_eq_four.symm, or_iff_left hR] at hf4

end good


open Fin.IntCast in
/-- Final solution -/
theorem final_solution {f : ℤ → ℤ} :
    good f ↔ (∃ c, f = λ n : ℤ ↦ c * ![0, 1] n)
      ∨ (∃ c, f = λ n : ℤ ↦ c * ![0, 1, 4, 1] n) ∨ (∃ c, f = λ n ↦ c * n ^ 2) := by
  refine ⟨λ hf ↦ ?_, ?_⟩
  ---- The `→` direction.
  · have h : (3 : ℤ) ≠ 0 := by decide
    have hf0 : f 0 = 0 := hf.map_zero_of_three_ne_zero h
    exact (hf.Int_map_two_eq hf0).symm.imp
      (λ hf1 ↦ ⟨f 1, hf.Int_eq_smul_ZMod2_01_of_map_two hf0 hf1⟩)
      (λ hf1 ↦ (hf.Int_map_three_eq_of_map_two hf0 hf1).symm.imp
        (λ hf2 ↦ ⟨f 1, hf.Int_eq_smul_ZMod4_0141_of_map_three h hf1 hf2⟩)
        (λ hf2 ↦ ⟨f 1, hf.Int_eq_smul_sq_of_map_three hf0 hf1 hf2⟩))
  ---- The `←` direction.
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact (ZMod2_01_is_good.comp_AddMonoidHom (Int.castAddHom (ZMod 2))).smul_left _
    · exact (ZMod4_0141_is_good.comp_AddMonoidHom (Int.castAddHom (ZMod 4))).smul_left _
    · exact sq_is_good.smul_left c
