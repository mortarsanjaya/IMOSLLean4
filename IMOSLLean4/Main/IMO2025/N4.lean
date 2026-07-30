/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Basic
import Mathlib.Data.Set.Finite.Basic

/-!
# IMO 2025 N4

Find all functions $f : ℕ⁺ → ℤ$ such that for every $d, n ∈ ℕ⁺$ with $d ∣ n$,
  there exists $e ∈ ℕ⁺$ such that $e ∣ n$ and $n ∣ d + f(e)$.

### Answer

$f(n) = -n$.

### Solution

We follow Solution 3 of the [official solution](https://www.imo-official.org/problems/2025/).
We modify the proof of the lemma and the finishing after that.

For the proof of the lemma, suppose that $f(m) ≠ 0$.
Consider an arbitrary $k > 2|f(m)|$.
Pick some $d ∣ km$ such that $km ∣ d + f(m)$.
Since $km ∤ f(m)$, we have $d < km$, so $2d ≤ km$ and $2 |f(m)| < km$.
This implies $|d + f(m)| < km$, and so $f(m) = -d$, where is a divisor of $km$.
Picking $k = 2|f(m)| + 1$ and $k = 2|f(m)| + 2$ gives us $f(m) = -e$ for some $e ∣ m$.

For the finishing, we go back to the original statement.
Pick an arbitrary positive integer $k > 1$.
Then for any $n ∈ ℕ+$, there exists $e_k ∣ kn$ such that $kn ∣ n + f(e_k)$.
Since $k > 1$, we know $f(e_k) ≠ 0$, so $f(e_k) = -c$ for some $c ∣ e_k$.
Since $c ∣ kn$, $n ∣ kn$, and $kn ∣ n - c$, we get $c = n$, so $f(e_k) = -n$.
By injectivity, all the $e_k$'s are equal to some positive integer $e$.
Then $e = e_2 = e_3$ divides both $2n$ and $3n$, which means $e ∣ n$.
But we also have $-f(e) = n ∣ e$, so $e = n$, proving $f(n) = -n$.
-/

namespace IMOSL
namespace IMO2025N4

/-! ### Extra lemmas -/

/-- Auxiliary lemma: if `a, b : ℕ+` are divisors of `n` and `a ≡ b (mod n)`, then `a = b`. -/
theorem eq_of_dvd_of_dvd_sub {a b n : ℕ+}
    (han : a ∣ n) (hbn : b ∣ n) (h : (n : ℤ) ∣ a - b) : a = b := by
  wlog hab : (b : ℤ) ≤ (a : ℤ)
  · refine (this hbn han ?_ (Int.le_of_not_le hab)).symm
    rwa [← Int.neg_sub, Int.dvd_neg]
  have h0 : (a : ℤ) - b < n :=
    Int.lt_of_lt_of_le (Int.sub_lt_self _ (Int.natCast_pos.mpr b.pos))
      (Int.ofNat_le.mpr (PNat.le_of_dvd han))
  replace h0 : (a : ℤ) - (b : ℤ) = 0 :=
    Int.eq_zero_of_dvd_of_nonneg_of_lt (Int.sub_nonneg_of_le hab) h0 h
  rwa [Int.sub_eq_zero, Int.natCast_inj, PNat.coe_inj] at h0

/-- Auxiliary lemma: `eq_of_dvd_of_dvd_sub'` but using subtypes. -/
theorem eq_of_dvd_of_dvd_sub' {n : ℕ+} (a b : {d | d ∣ n}) (h : (n : ℤ) ∣ a - b) : a = b :=
  Subtype.coe_injective (eq_of_dvd_of_dvd_sub a.2 b.2 h)





/-! ### Start of the problem -/

/-- A function `f : ℕ+ → ℤ` is called `good` if for every `d, n : ℕ+` with `d ∣ n`,
  there exists `e : ℕ+` such that `e ∣ n` and `n ∣ d + f(e)`. -/
def good (f : ℕ+ → ℤ) := ∀ n d : ℕ+, d ∣ n → ∃ e, e ∣ n ∧ (n : ℤ) ∣ d + f e

/-- The function `n ↦ -n` is good. -/
theorem neg_is_good : good (λ n ↦ -n) :=
  λ _ d h ↦ ⟨d, h, 0, (add_neg_cancel _).trans (Int.mul_zero _).symm⟩


namespace good

variable (hf : good f)
include hf

/-- For each `n`, there exists a permutation `g` on divisors on `n`.
  such that `n ∣ e + f(g(e))` for any `e ∣ n`. -/
theorem exists_divisor_perm (n : ℕ+) :
    ∃ g : Equiv.Perm {d | d ∣ n}, ∀ e, (n : ℤ) ∣ e + f (g e) := by
  ---- By axiom of choice, such `g` exists; we just need to show that `g` is bijective.
  let S := Set.Elem {d | d ∣ n}
  obtain ⟨g, hg⟩ : ∃ g : S → S, ∀ d : S, (n : ℤ) ∣ d + f (g d) :=
    Classical.axiom_of_choice (r := λ d e : S ↦ (n : ℤ) ∣ d + f e)
      (λ d ↦ (hf n d.1 d.2).elim λ e he ↦ ⟨⟨e, he.1⟩, he.2⟩)
  suffices g.Bijective from ⟨Equiv.ofBijective g this, hg⟩
  ---- Indeed, `g` is injective due to `eq_of_dvd_of_dvd_sub`.
  have hg0 : g.Injective :=
    λ a b h ↦ eq_of_dvd_of_dvd_sub' a b <| calc
        _ ∣ (a + f (g a)) - (b + f (g b)) := Int.dvd_sub (hg a) (hg b)
        _ = a - b := by rw [h, Int.add_sub_add_right]
  ---- But `S` is finite, so `g` is bijective.
  haveI : Finite S := by
    let T : Set ℕ := Finset.range (n + 1)
    have hT : T.Finite := Finset.finite_toSet _
    have hT0 : {d | d ∣ n}.InjOn PNat.val := Set.injOn_of_injective PNat.coe_injective
    have hT1 : {d | d ∣ n}.MapsTo PNat.val T :=
      λ d hd ↦ Finset.mem_range_succ_iff.mpr (PNat.le_of_dvd hd)
    exact Set.finite_coe_iff.mpr (hT.of_injOn hT1 hT0)
  exact hg0.bijective_of_finite

/-- `f` is injective. -/
theorem injective : f.Injective := by
  intro a b h
  ---- Let `c = ab`, and pick the corresponding permutation `g` on divisors of `c`.
  let c := a * b
  let S := Set.Elem {d | d ∣ c}
  obtain ⟨g, hg⟩ : ∃ g : S ≃ S, ∀ e, (c : ℤ) ∣ e + f (g e) := hf.exists_divisor_perm _
  replace hg (e : S) : (c : ℤ) ∣ g.symm e + f e := by
    simpa only [Equiv.apply_symm_apply] using hg (g.symm e)
  ---- Considering `c ∣ g⁻¹(a) + f(a)` and `c ∣ g⁻¹(b) + f(b)` gives `c ∣ g⁻¹(a) - g⁻¹(b)`.
  let a₀ : S := ⟨a, dvd_mul_right _ _⟩
  let b₀ : S := ⟨b, dvd_mul_left _ _⟩
  have h : (c : ℤ) ∣ g.symm a₀ - g.symm b₀ := calc
    _ ∣ (g.symm a₀ + f a) - (g.symm b₀ + f b) := Int.dvd_sub (hg a₀) (hg b₀)
    _ = g.symm a₀ - g.symm b₀ := by rw [h, Int.add_sub_add_right]
  ---- Then `g⁻¹(a) = g⁻¹(b)`, and so `a = b`.
  replace h : g.symm a₀ = g.symm b₀ := eq_of_dvd_of_dvd_sub' _ _ h
  rwa [EmbeddingLike.apply_eq_iff_eq, ← Subtype.coe_inj] at h

/-- A convenient specialization of `exists_divisor_perm`:
  for every `e, n : ℕ+` with `e ∣ n`, there exists `d ∣ n` such that `n ∣ d + f(e)`. -/
theorem forall_right_exists_left {n e : ℕ+} (he : e ∣ n) :
    ∃ d, d ∣ n ∧ (n : ℤ) ∣ d + f e := by
  let S := Set.Elem {d | d ∣ n}
  obtain ⟨g, hg⟩ : ∃ g : S ≃ S, ∀ e, (n : ℤ) ∣ e + f (g e) :=
    hf.exists_divisor_perm n
  let e₀ : S := ⟨e, he⟩
  let d₀ : S := g.symm e₀
  refine ⟨d₀.1, d₀.2, ?_⟩
  simpa only [Equiv.apply_symm_apply] using hg (g.symm e₀)

/-- For any `m` with `f(m) ≠ 0`, there exists `d ∣ m` such that `f(m) = -d`. -/
theorem map_eq_zero_or_neg_divisor {m} (hm : f m ≠ 0) : ∃ d, d ∣ m ∧ f m = -d := by
  ---- Reduce to: for all `k > 2|f(m)|`, there exists `d ∣ km` with `f(m) = -d`.
  suffices ∀ k : ℕ+, k > 2 * (f m).natAbs → ∃ d, d ∣ k * m ∧ f m = -d by
    -- Pick `d` for `k = 2|f(m)| + 1` and `k = 2|f(m) + 2`.
    set N : ℕ := 2 * (f m).natAbs
    obtain ⟨d, hd, hd0⟩ : ∃ d, d ∣ N.succPNat * m ∧ f m = -d := this _ N.lt_add_one
    obtain ⟨e, he, he0⟩ : ∃ e, e ∣ (N.succPNat + 1) * m ∧ f m = -e :=
      this _ (Nat.lt_add_of_pos_right Nat.two_pos)
    -- Then the two `d`'s are equal and the two `d ∣ km` relation yields `d ∣ m`.
    refine ⟨d, ?_, hd0⟩
    obtain rfl : d = e := by rwa [hd0, Int.neg_inj, Int.natCast_inj, PNat.coe_inj] at he0
    rw [PNat.dvd_iff] at hd he ⊢
    rwa [add_one_mul, PNat.add_coe, Nat.dvd_add_right hd] at he
  ---- Pick `d ∣ km` such that `km ∣ d + f(m)`; then the goal reduces to `|d + f(m)| < km`.
  rintro ⟨k, h⟩ (hk : k > 2 * (f m).natAbs)
  obtain ⟨d, hd, hd0⟩ : ∃ d, d ∣ ⟨k, h⟩ * m ∧ _ ∣ d + f m :=
    hf.forall_right_exists_left (dvd_mul_left m _)
  refine ⟨d, hd, Eq.symm <| Int.neg_eq_of_add_eq_zero <|
    Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd0 ?_⟩
  ---- Let `N = km`, and note that `2|f(m)| < N`.
  let N : ℕ := k * m
  change (N : ℤ) ∣ d + f m at hd0
  replace hk : 2 * (f m).natAbs < N := hk.trans_le (Nat.le_mul_of_pos_right _ m.pos)
  ---- Now we show that `2d ≤ N`.
  replace hd : 2 * d ≤ N := by
    -- Write `N = dt`; if `t > 1` then we are done, so now assume `t = 1` and `N = d`.
    rcases hd with ⟨t, ht⟩
    obtain ht0 | rfl : t > 1 ∨ t = 1 := (eq_one_or_one_lt t).symm
    · calc 2 * (d : ℕ)
        _ ≤ t * d := Nat.mul_le_mul_right _ ((PNat.coe_lt_coe _ _).mp ht0)
        _ = N := by rw [Nat.mul_comm, ← PNat.mul_coe, ← ht]; rfl
    -- Then `N ∣ f(m)`, contradicting `2|f(m)| < N`.
    replace ht : N = d := (congrArg PNat.val ht).trans d.1.mul_one
    replace hd0 : (N : ℤ) ∣ f m := by rwa [← ht, Int.dvd_add_right (Int.dvd_refl _)] at hd0
    replace hd0 : N ≤ (f m).natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr hm) (Int.ofNat_dvd_left.mp hd0)
    exact absurd (hd0.trans (Nat.le_mul_of_pos_left _ Nat.two_pos)) hk.not_ge
  ---- Finally, we get `2|d + f(m)| < 2d + 2|f(m)| ≤ 2N` and so `|d + f(m)| < N`.
  replace h : 2 * (d + (f m).natAbs) < 2 * N := by
    rw [Nat.mul_add, Nat.two_mul N]
    exact Nat.add_lt_add_of_le_of_lt hd hk
  exact (Int.natAbs_add_le _ _).trans_lt (Nat.lt_of_mul_lt_mul_left h)

/-- We have `f(n) = -n` for all `n : ℕ+`. -/
theorem map_eq_neg (n) : f n = -n := by
  ---- First show that for all `k > 1`, there exists `e ∣ kn` such that `f(e) = -n`.
  have h (k) (hk : k > 1) : ∃ e, e ∣ k * n ∧ f e = -n := by
    -- Pick `e ∣ kn` such that `kn ∣ n + f(e)`; this `e` works.
    obtain ⟨e, he, he0⟩ : ∃ e, e ∣ k * n ∧ ↑↑(k * n) ∣ n + f e :=
      hf (k * n) n (dvd_mul_left n k)
    refine ⟨e, he, ?_⟩
    -- Since `kn > n > 0`, we have `f(e) ≠ 0`, so `f(e) = -d` for some `d ∣ e`.
    obtain ⟨d, hd, hd0⟩ : ∃ d, d ∣ e ∧ f e = -d := by
      refine hf.map_eq_zero_or_neg_divisor λ he1 ↦ ?_
      rw [he1, Int.add_zero, Int.natCast_dvd_natCast, ← PNat.dvd_iff] at he0
      exact (PNat.le_of_dvd he0).not_gt (lt_mul_of_one_lt_left' n hk)
    -- Then `kn ∣ n - d`, where `n` and `d` divides `kn`; so `n = d` and we are done.
    rw [hd0, Int.add_neg_eq_sub] at he0
    rw [eq_of_dvd_of_dvd_sub (dvd_mul_left n k) (hd.trans he) he0, hd0]
  ---- Pick `e` for `k = 2` and `k = 3`; by injectivity they are the same.
  obtain ⟨e, he, he0⟩ : ∃ e, e ∣ 2 * n ∧ f e = -n := h 2 (by decide)
  obtain ⟨d, hd, hd0⟩ : ∃ d, d ∣ 3 * n ∧ f d = -n := h 3 (by decide)
  obtain rfl : e = d := hf.injective (he0.trans hd0.symm)
  clear hd0
  ---- Since `e` divides `2n` and `3n`, we have `e ∣ n`.
  replace hd : e ∣ n := by
    rw [PNat.dvd_iff, PNat.mul_coe, PNat.val_ofNat] at he hd
    rwa [Nat.succ_mul, Nat.dvd_add_right he, ← PNat.dvd_iff] at hd
  ---- On the other hand, by `map_eq_zero_or_neg_divisor`, we have `n ∣ e`.
  replace he : f e ≠ 0 := by
    rw [he0, Int.neg_ne_zero, Int.natCast_ne_zero]
    exact n.ne_zero
  replace he : n ∣ e := by
    obtain ⟨c, hc, hc0⟩ : ∃ c, c ∣ e ∧ f e = -c := hf.map_eq_zero_or_neg_divisor he
    rw [he0, Int.neg_inj, Int.natCast_inj, PNat.coe_inj] at hc0
    rwa [hc0]
  ---- Thus we get `n = e` and so `f(n) = -n`.
  rwa [PNat.dvd_antisymm hd he] at he0

end good


/-- Final solution -/
theorem final_solution : good f ↔ f = λ n : ℕ+ ↦ -(n : ℤ) :=
  ⟨λ hf ↦ funext hf.map_eq_neg, λ hf ↦ hf ▸ neg_is_good⟩
