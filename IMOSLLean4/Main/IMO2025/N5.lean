/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

module
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Order.Bounds.Defs

/-!
# IMO 2025 N5

Define the function $f : ℕ^3 → ℕ^3$ by
$$ f(a, b, c) = (a + \gcd(b, c), b + \gcd(c, a), c + \gcd(a, b)). $$
Let $N ≥ 2$ be an integer.
Determine the smallest possible value of the first entry of $f^{3N}(a, b, c)$
  across all triples $(a, b, c)$ of positive integers.

### Answer

$3 · 2^N$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/2025/).
To obtain the bound on the first entry, we proceed by induction.
We prove more: the smallest possible value of the first entry of $f^N(a, b, c)$ is
  $(3 + N \% 3) 2^{⌊N/3⌋}$ for $N ≥ 6$, all attained by $(a, b, c) = (3, 5, 6)$.

### Notes

For $N ≤ 5$, the smallest possible value of the first entry of $f^N(a, b, c)$
  are indeed $1, 2, 3, 4, 6, 8$, attained by $(a, b, c) = (1, 1, 4)$.
-/

@[expose] public section

namespace IMOSL
namespace IMO2025N5

/-- The function `f(a, b, c) = (a + gcd(b, c), b + gcd(c, a), c + gcd(a, b))` -/
def f (x : ℕ × ℕ × ℕ) :=
  (x.1 + x.2.1.gcd x.2.2, x.2.1 + x.2.2.gcd x.1, x.2.2 + x.1.gcd x.2.1)

/-- This is a predicate for `(a, b, c)` saying that `a, b, c > 0`, just for convenience. -/
def triple_pos (x : ℕ × ℕ × ℕ) := x.1 > 0 ∧ x.2.1 > 0 ∧ x.2.2 > 0





/-! ### Basic lemmas -/

/-- If `a, b, c` are positive, then all entries of `f(a, b, c)` are also positive. -/
theorem f_triple_pos (hx : triple_pos x) : triple_pos (f x) :=
  hx.imp (Nat.add_pos_left · _) (And.imp (Nat.add_pos_left · _) (Nat.add_pos_left · _))

/-- If `a, b, c` are positive, then all entries of `f^N(a, b, c)` are also positive. -/
theorem triple_pos.f_iter (hx : triple_pos x) (N) : triple_pos (f^[N] x) :=
  Nat.recOn N hx λ _ ↦ f.iterate_succ_apply' _ _ ▸ f_triple_pos

/-- If `na, nb, nc > 0`, then `a, b, c > 0`. -/
theorem triple_pos.of_nsmul {n : ℕ} (h : triple_pos (n • x)) : triple_pos x :=
  h.imp Nat.pos_of_mul_pos_left (And.imp Nat.pos_of_mul_pos_left Nat.pos_of_mul_pos_left)

/-- If `f^N(a, b, c) = k(d, e, f)` and `a, b, c > 0`, then `d, e, f > 0`. -/
theorem triple_pos.of_f_iter_nsmul (h : triple_pos x) {k : ℕ} (h0 : f^[N] x = k • y) :
    triple_pos y :=
  (h0 ▸ h.f_iter N).of_nsmul

/-- We have `f(na, nb, nc) = n f(a, b, c)` for any `n, a, b, c : ℕ`. -/
theorem f_nsmul (n : ℕ) (x : ℕ × ℕ × ℕ) : f (n • x) = n • f x := by
  rcases x with ⟨a, b, c⟩
  have h (a b c : ℕ) : n • (a + b.gcd c) = n • a + (n • b).gcd (n • c) := by
    change n * (a + b.gcd c) = n * a + (n * b).gcd (n * c)
    rw [Nat.gcd_mul_left, Nat.mul_add]
  simp only [f, Prod.smul_mk, h]

/-- We have `f^N(na, nb, nc) = n f^N(a, b, c)` for any `N, n, a, b, c : ℕ`. -/
theorem f_iter_nsmul (N n : ℕ) (x : ℕ × ℕ × ℕ) : f^[N] (n • x) = n • f^[N] x := by
  induction N with | zero => rfl | succ N N_ih =>
    rw [f.iterate_succ_apply', N_ih, f_nsmul, f.iterate_succ_apply']





/-! ### The first entry of`f^N(3, 5, 6)` is `2 ^ (N / 3) * (3 + N % 3)` -/

/-- The entries of `(3, 5, 6)` are positive. -/
theorem triple_pos_356 : triple_pos (3, 5, 6) := by
  unfold triple_pos; decide

/-- We have `f^{3N}(3, 5, 6) = (2^N * 3, 2^N * 5, 2^N * 6)` for any `N`. -/
theorem f_iter3N_356 (N : ℕ) : f^[3 * N] (3, 5, 6) = 2 ^ N • (3, 5, 6) := by
  induction N with | zero => rfl | succ N N_ih => ?_
  calc f^[3 * (N + 1)] (3, 5, 6)
    _ = 2 • f^[3 * N] (3, 5, 6) := f_iter_nsmul (3 * N) 2 (3, 5, 6)
    _ = (2 * (2 ^ N * 3), 2 * (2 ^ N * 5), 2 * (2 ^ N * 6)) := congrArg (2 • ·) N_ih
    _ = (2 ^ (N + 1) * 3, 2 ^ (N + 1) * 5, 2 ^ (N + 1) * 6) :=
      have h (a) : 2 * (2 ^ N * a) = 2 ^ (N + 1) * a := by rw [Nat.pow_succ', Nat.mul_assoc]
      Prod.ext (h 3) (Prod.ext (h 5) (h 6))

/-- We have `f^N(3, 5, 6) = 2^{N / 3} f^{N % 3}(3, 5, 6)` for any `N`. -/
theorem f_iterN_356 (N : ℕ) : f^[N] (3, 5, 6) = 2 ^ (N / 3) • f^[N % 3] (3, 5, 6) := by
  rw [← f_iter_nsmul, ← f_iter3N_356, ← f.iterate_add_apply, Nat.mod_add_div]

/-- The first entry of `f^N(3, 5, 6)` is `3 + N` if `N < 3`. -/
theorem f_iterN_356_fst_of_lt_three (hN : N < 3) : (f^[N] (3, 5, 6)).1 = 3 + N := by
  match N with | 0 => rfl | 1 => rfl | 2 => rfl

/-- The first entry of `f^N(3, 5, 6)` is `2^{N / 3} (3 + N % 3)`. -/
theorem f_iterN_356_fst (N) : (f^[N] (3, 5, 6)).1 = 2 ^ (N / 3) * (3 + N % 3) :=
  (congrArg Prod.fst (f_iterN_356 N)).trans <| congrArg (2 ^ (N / 3) * ·) <|
    f_iterN_356_fst_of_lt_three (Nat.mod_lt N (Nat.succ_pos 2))





/-! ### The entries of `f^3(x)` are all even -/

section

open Fin.NatCast

/-- The function `g_1 : Fin 2 × Fin 2 × Fin 2 → Fin 2`, defined by
  `g_1(a, b, c) = a + d`, where `d = 0` if `b = c = 0` and `d = 1` otherwise. -/
def g_1 (a b c : Fin 2) : Fin 2 := a + if b = 0 ∧ c = 0 then 0 else 1

/-- The value of `gcd(b, c) % 2` purely in terms of `b % 2` and `c % 2`. -/
theorem gcd_mod_two (b c : ℕ) : b.gcd c % 2 = if b % 2 = 0 ∧ c % 2 = 0 then 0 else 1 := by
  by_cases h : b % 2 = 0 ∧ c % 2 = 0
  ---- Case 1: `b` and `c` are even.
  · rw [if_pos h, ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_gcd_iff]
    exact ⟨Nat.dvd_of_mod_eq_zero h.1, Nat.dvd_of_mod_eq_zero h.2⟩
  ---- Case 2: `b` or `c` is odd.
  · rw [if_neg h, ← Nat.mod_two_ne_zero, Ne, ← Nat.dvd_iff_mod_eq_zero, Nat.dvd_gcd_iff]
    exact λ h0 ↦ h (h0.imp Nat.mod_eq_zero_of_dvd Nat.mod_eq_zero_of_dvd)

/-- The reduction to `Fin 2` of `a + gcd(b, c)` is exactly `g_1((a, b, c) mod 2)`. -/
theorem add_gcd_Fin2_eq_g (a b c : ℕ) : ((a + b.gcd c : ℕ) : Fin 2) = g_1 a b c := by
  suffices (a + b.gcd c) % 2 = (g_1 a b c).val from Fin.val_inj.mp this
  calc (a + b.gcd c) % 2
    _ = (a % 2 + if b % 2 = 0 ∧ c % 2 = 0 then 0 else 1) % 2 := by
      rw [Nat.add_mod, gcd_mod_two]
    _ = ((a : Fin 2) + if (b : Fin 2) = 0 ∧ (c : Fin 2) = 0 then 0 else 1) % 2 := by
      simp only [← Fin.val_inj (b := 0)]; rfl
    _ = (g_1 a b c : ℕ) := by
      generalize (a : Fin 2) = x, (b : Fin 2) = y, (c : Fin 2) = z
      unfold g_1; revert x y z; decide

/-- The mod 2 reduction of a triple. -/
def triple_to_Fin2 (x : ℕ × ℕ × ℕ) : Fin 2 × Fin 2 × Fin 2 := (x.1, x.2.1, x.2.2)

/-- The function `g(a, b, c) = (g_1(a, b, c), g_1(b, c, a), g_1(c, a, b))`. -/
def g (x : Fin 2 × Fin 2 × Fin 2) : Fin 2 × Fin 2 × Fin 2 :=
  (g_1 x.1 x.2.1 x.2.2, g_1 x.2.1 x.2.2 x.1, g_1 x.2.2 x.1 x.2.1)

/-- Semiconjugation by `triple_to_Fin2` from `f` to `g`. -/
theorem triple_to_Fin2_semiconj_f_to_g : triple_to_Fin2.Semiconj f g :=
  λ _ ↦ Prod.ext (add_gcd_Fin2_eq_g _ _ _)
    (Prod.ext (add_gcd_Fin2_eq_g _ _ _) (add_gcd_Fin2_eq_g _ _ _))

/-- For any triple `x : Fin 2 × Fin 2 × Fin 2`, we have `g^3(x) = 0`. -/
theorem g_iter3_eq_zero (x) : g^[3] x = (0, 0, 0) := by
  rcases x with ⟨a, b, c⟩
  revert a b c; decide

/-- For any triple `x : ℕ × ℕ × ℕ`, the entries of `f^3(x)` modulo `2` are zeroes. -/
theorem triple_to_Fin2_f_iter3_eq_zero (x) : triple_to_Fin2 (f^[3] x) = (0, 0, 0) :=
  (triple_to_Fin2_semiconj_f_to_g.iterate_right 3 _).trans (g_iter3_eq_zero _)

/-- All entries of `f^3(a, b, c)` are even. -/
theorem f_iter3_exists_two_nsmul (x) : ∃ y, f^[3] x = 2 • y := by
  have h {a : ℕ} (ha : (a : Fin 2) = 0) : a = 2 * (a / 2) :=
    (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (congrArg Fin.val ha))).symm
  let p := f^[3] x
  obtain ⟨h0, h1, h2⟩ : (p.1 : Fin 2) = 0 ∧ (p.2.1 : Fin 2) = 0 ∧ (p.2.2 : Fin 2) = 0 := by
    simpa only [Prod.ext_iff, triple_to_Fin2] using triple_to_Fin2_f_iter3_eq_zero _
  exact ⟨(p.1 / 2, p.2.1 / 2, p.2.2 / 2), Prod.ext (h h0) (Prod.ext (h h1) (h h2))⟩

end


/-- All entries of `f^{3N}(a, b, c)` are multiples of `2^N`. -/
theorem f_iter3N_exists_two_pow_N_nsmul (x N) : ∃ y, f^[3 * N] x = 2 ^ N • y := by
  induction N with
  | zero =>
      refine ⟨x, (?_ : x = (1 * _, 1 * _, 1 * _))⟩
      simp only [Nat.one_mul]
  | succ N N_ih =>
      rcases N_ih with ⟨z, hz⟩
      obtain ⟨⟨a, b, c⟩, hy⟩ : ∃ y, f^[3] z = 2 • y := f_iter3_exists_two_nsmul z
      rw [Nat.mul_succ, Nat.add_comm, f.iterate_add_apply, hz, f_iter_nsmul, hy]
      have h (t) : 2 ^ N * (2 * t) = 2 ^ (N + 1) * t := (Nat.mul_assoc _ _ _).symm
      exact ⟨⟨a, b, c⟩, Prod.ext (h _) (Prod.ext (h _) (h _))⟩





/-! ### The first entry of `f^N(x)` is at least `2 ^ (N / 3) * (3 + N % 3)` -/

/-- If `a, b, c` are positive, then the first entry of `f(a, b, c)` is at least `a + 1`. -/
theorem f_fst_of_triple_pos (hx : triple_pos x) : x.1 + 1 ≤ (f x).1 :=
  Nat.lt_add_of_pos_right (Nat.gcd_pos_of_pos_left x.2.2 hx.2.1)

/-- If `a, b, c` are positive, then the first entry of `f^N(a, b, c)` is at least `a + N`. -/
theorem f_iter_fst_of_triple_pos (N : ℕ) (hx : triple_pos x) : x.1 + N ≤ (f^[N] x).1 :=
  Nat.recOn N (Nat.le_refl _)
    λ n hn ↦ f.iterate_succ_apply' _ _ ▸
      Nat.lt_of_le_of_lt hn (f_fst_of_triple_pos (hx.f_iter n))

/-- If `a, b, c` are positive, then the first entry of `f^3(a, b, c)` is at least `4`. -/
theorem four_le_f_iter3_fst_of_triple_pos (hx : triple_pos x) : 4 ≤ (f^[3] x).1 :=
  Nat.le_trans (Nat.add_le_add_right hx.1 3) (f_iter_fst_of_triple_pos 3 hx)

/-- If `a, b, c` are positive, then `f^6(a, b, c) = (4d, 4e, 4f)` with `d ≥ 3`. -/
theorem f_iter6_form_of_triple_pos (hx : triple_pos x) :
    ∃ z, f^[6] x = 4 • z ∧ 3 ≤ z.1 := by
  ---- First write `f^3(x) = 2y` for some triple `y` and show that `y.1 ≥ 2`.
  obtain ⟨y, hy⟩ : ∃ y, f^[3] x = 2 • y := f_iter3_exists_two_nsmul x
  have hy0 : triple_pos y := hx.of_f_iter_nsmul hy
  have hy1 : 2 ≤ y.1 :=
    Nat.le_of_mul_le_mul_left (hc := Nat.two_pos)
      (Nat.le_trans (four_le_f_iter3_fst_of_triple_pos hx) (hy ▸ Nat.le_refl _))
  ---- Now write `f^3(y) = 2z` for some triple `z`; then `z` works.
  obtain ⟨z, hz⟩ : ∃ z, f^[3] y = 2 • z := f_iter3_exists_two_nsmul y
  refine ⟨z, ?_, ?_⟩
  ---- Show that `f^6(x) = 4z`.
  · rw [f.iterate_add_apply 3 3, hy, f_iter_nsmul, hz]
    have h (a) : 2 * (2 * a) = 4 * a := (Nat.mul_assoc 2 2 a).symm
    exact Prod.ext (h _) (Prod.ext (h _) (h _))
  ---- Show that `z.1 ≥ 3`.
  · have hz0 : 5 ≤ 2 * z.1 := calc
      _ ≤ y.1 + 3 := Nat.add_le_add_right hy1 3
      _ ≤ (f^[3] y).1 := f_iter_fst_of_triple_pos 3 hy0
      _ = 2 * z.1 := congrArg Prod.fst hz
    exact Nat.lt_of_mul_lt_mul_left (a := 2) hz0

/-- If `a ≥ 3`, `b, c > 0`, and `f^{3N}(a, b, c) = 2^N (d, e, f)`, then `d ≥ 3`. -/
theorem f_iter3N_div_two_pow_N_fst
    (hx : triple_pos x) (hx0 : 3 ≤ x.1) (hy : f^[3 * N] x = 2 ^ N • y) : 3 ≤ y.1 := by
  induction N generalizing y with
    | zero => subst hy; exact Nat.one_mul y.1 ▸ hx0
    | succ N N_ih => ?_
  obtain ⟨z, hz⟩ : ∃ z, f^[3 * N] x = 2 ^ N • z := f_iter3N_exists_two_pow_N_nsmul x N
  have hz0 : triple_pos z := hx.of_f_iter_nsmul hz
  replace N_ih : 6 ≤ (f^[3] z).1 := calc
    _ ≤ z.1 + 3 := Nat.add_le_add_right (N_ih hz) 3
    _ ≤ (f^[3] z).1 := f_iter_fst_of_triple_pos 3 hz0
  replace hy : 2 ^ N * (f^[3] z).1 = 2 ^ (N + 1) * y.1 :=
    calc (2 ^ N • f^[3] z).1
    _ = (f^[3] (f^[3 * N] x)).1 := by rw [hz, f_iter_nsmul]
    _ = (f^[3 * (N + 1)] x).1 := by rw [Nat.mul_succ, Nat.add_comm, f.iterate_add_apply]
    _ = 2 ^ (N + 1) * y.1 := congrArg Prod.fst hy
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.two_pow_pos (N + 1))
  calc 2 ^ (N + 1) * 3
    _ = 2 ^ N * 6 := by rw [Nat.pow_succ, Nat.mul_assoc]
    _ ≤ 2 ^ N * (f^[3] z).1 := Nat.mul_le_mul_left _ N_ih
    _ = 2 ^ (N + 1) * y.1 := hy

/-- If `a ≥ 3` and `b, c > 0`, then the first entry
  of `f^N(a, b, c)` is at least `2^{N/3} * (3 + N % 3)`. -/
theorem f_iterN_of_three_le_fst {x} (hx : triple_pos x) (hx0 : 3 ≤ x.1) (N) :
    2 ^ (N / 3) * (3 + N % 3) ≤ (f^[N] x).1 := by
  obtain ⟨y, hy⟩ : ∃ y, f^[3 * (N / 3)] x = 2 ^ (N / 3) • y :=
    f_iter3N_exists_two_pow_N_nsmul _ _
  calc 2 ^ (N / 3) * (3 + N % 3)
    _ ≤ (2 ^ (N / 3) • f^[N % 3] y).1 :=
      Nat.mul_le_mul_left _ <| Nat.le_trans
        (Nat.add_le_add_right (f_iter3N_div_two_pow_N_fst hx hx0 hy) _)
        (f_iter_fst_of_triple_pos _ (hx.of_f_iter_nsmul hy))
    _ = (f^[N] x).1 := by
      rw [← f_iter_nsmul, ← hy, ← f.iterate_add_apply, Nat.mod_add_div]

/-- If `a, b, c > 0` and `N ≥ 6`, then `f^N(a, b, c) ≥ 2^{N/3} * (3 + N % 3)`. -/
theorem f_iterN_fst_of_ge_six (hN : N ≥ 6) (hx : triple_pos x) :
    2 ^ (N / 3) * (3 + N % 3) ≤ (f^[N] x).1 := by
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 6 := Nat.exists_eq_add_of_le' hN
  obtain ⟨z, hz0, hz⟩ : ∃ z, f^[6] x = 4 • z ∧ 3 ≤ z.1 := f_iter6_form_of_triple_pos hx
  rw [f.iterate_add_apply, hz0, f_iter_nsmul, Nat.add_mul_mod_self_left _ 3 2,
    Nat.add_mul_div_left K 2 (Nat.succ_pos 2), Nat.add_comm, Nat.pow_add, Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (f_iterN_of_three_le_fst (hx.of_f_iter_nsmul hz0) hz K)





/-! ### Summary -/

/-- The general result: the smallest possible value of the first entry of
  `f^N(a, b, c)` is `2^{N / 3} (3 + N % 3)` if `N ≥ 6`. -/
theorem general_result (hN : N ≥ 6) :
    IsLeast ((Set.ofPred triple_pos).image λ x ↦ (f^[N] x).1) (2 ^ (N / 3) * (3 + N % 3)) :=
  ⟨⟨(3, 5, 6), triple_pos_356, f_iterN_356_fst N⟩,
  λ _ ⟨_, hx, h⟩ ↦ h ▸ f_iterN_fst_of_ge_six hN hx⟩

/-- Final solution -/
theorem final_solution (hN : N ≥ 2) :
    IsLeast ((Set.ofPred triple_pos).image λ x ↦ (f^[3 * N] x).1) (2 ^ N * 3) := by
  simpa only [Nat.mul_div_right _ (Nat.succ_pos 2), Nat.mul_mod_right]
    using general_result (Nat.mul_le_mul_left 3 hN)
