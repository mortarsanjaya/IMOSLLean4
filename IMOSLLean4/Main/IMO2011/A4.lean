/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Basic

/-!
# IMO 2011 A4

Find all functions $f, g : ℕ⁺ → ℕ⁺$ such that for any $n ∈ ℕ$,
$$ f^{g(n) + 1}(n) + g^{f(n)}(n) + g(n + 1) = f(n + 1) + 1. $$

### Answer

$f(n) = n$, $g(n) = 1$.

### Solution

We follow the outline of the AoPS solution ♯8 by **yayups** in
  [this thread](https://artofproblemsolving.com/community/c6h488536p19655187),
  but we will greatly simplify the solution.
Thus we will write down the proof below.

It is easy to check that $f(n) = n$, $g(n) = 1$ works.
For the converse, first suppose that $f(n) = n$ for all $n ∈ ℕ⁺$.
Then plugging into the functional equation yields $g^n(n) + g(n + 1) = 2$.
Thus $g(1) = g^1(1) = 1$ and $g(n + 1) = 1$ for all $n ∈ ℕ⁺$.
This implies $g(n) = 1$ for all $n ∈ ℕ⁺$.

It now remains to show that $f(n) = n$ for all $n ∈ ℕ$.
For this part, we only need the following immediate consequence of the functional equation:
$$ f(n + 1) > f^{g(n) + 1}(n). $$

First we show that $f(n) ≥ k$ whenever $n ≥ k$.
We proceed by induction on $k$, with the base case $k = 1$ obvious.
Now, suppose that for some $k ∈ ℕ$, we have $f(n) ≥ k$ whenever $n ≥ k$.
Then for any $n ≥ k + 1$, we have $f^t(n - 1) ≥ k$ for any $t$ (by induction on $t$).
Thus we get $f(n) > f^{g(n - 1) + 1}(n - 1) ≥ k$, and so $f(n) ≥ k + 1$, as desired.

As a result, we immediately get $f(n) ≥ n$ for all $n ∈ ℕ$.
Then $f(n + 1) > f^{g(n) + 1}(n) ≥ f^2(n)$ for all $n ∈ ℕ$.
This implies $f(n + 1) > f(n)$ for all $n ∈ ℕ$, so $f$ is strictly increasing.
Then $f(n + 1) > f^2(n)$ also implies $n + 1 > f(n)$, so $f(n) ≤ n$ for all $n ∈ ℕ$.
Together with $f(n) ≥ n$, we get $f(n) = n$ for all $n ∈ ℕ$.
-/

namespace IMOSL
namespace IMO2011A4

/-! ### Extra lemmas -/

/-- For any `a, b ∈ ℕ+`, if `a + b = 2`, then `a = 1`. -/
theorem pnat_add_eq_two_imp_left_eq_one {a b : ℕ+} (h : a + b = 2) : a = 1 :=
  a.one_le.eq_or_lt'.resolve_right ((PNat.lt_add_right _ _).trans_eq h).not_ge

/-- Iteration formula but the function to be iterated is constant.
  TODO: Remove this once it gets into `mathlib`. -/
theorem fn_iterate_const {α : Type*} (hn : 0 < n) (a b : α) : (λ _ ↦ a)^[n] b = a :=
  match n with | 0 => absurd rfl hn.ne | n + 1 => Function.iterate_fixed rfl n

/-- If `f : ℕ+ → α` satisfies `f(n + 1) > f(n)` for all `n ∈ ℕ+`, where `α` is a preorder,
  then `f` is strictly increasing. The naming mimics `strictMono_nat_of_lt_succ`. -/
theorem strictMono_pnat_of_lt_succ [Preorder α] {f : ℕ+ → α} (hf : ∀ n, f n < f (n + 1)) :
    StrictMono f :=
  λ b c h ↦ calc f b
  _ = f b.natPred.succPNat := congrArg f b.succPNat_natPred.symm
  _ < f c.natPred.succPNat :=
    strictMono_nat_of_lt_succ (λ n ↦ hf n.succPNat) (PNat.natPred_lt_natPred.mpr h)
  _ = f c := congrArg f c.succPNat_natPred



/-! ### Start of the problem -/

/-- Given `f : ℕ+ → ℕ+` and `g : ℕ+ → ℕ`, if `g(n) ≥ 2` for all `n ∈ ℕ` and
  `f(n + 1) > f^{g(n)}(n)` for all `n ∈ ℕ`, then `f(n) = n` for all `n ∈ ℕ`. -/
theorem f_eq_id_of_map_iter_lt_map_succ {f : ℕ+ → ℕ+} {g : ℕ+ → ℕ}
    (hg : ∀ n, 2 ≤ g n) (hfg : ∀ n, f^[g n] n < f (n + 1)) :
    f = id := by
  ---- First show that `f(n) ≥ k` whenever `n ≥ k`.
  have h {k : ℕ+} : ∀ {n : ℕ+}, k ≤ n → k ≤ f n := by
    -- Induction on `k`, with the base case being obvious.
    induction k using PNat.recOn with
      | one => exact λ _ ↦ PNat.one_le _
      | succ k hk => ?_
    /- Now suppose `f(n) ≥ k` whenever `n ≥ k`.
      By induction on `t`, `n ≥ k` implies `f^t(n) ≥ k`. -/
    replace hk : ∀ t, ∀ {n : ℕ+}, k ≤ n → k ≤ f^[t] n :=
      Nat.rec id λ t ht n hn ↦ ht (hk hn)
    -- Now pick some `n ≥ k + 1`, and write `n` as `m + 1`.
    intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 :=
      PNat.exists_eq_succ_of_ne_one (PNat.one_lt_of_lt hn).ne.symm
    -- Deduce that `k ≤ f^{g(m)}(m) < f(m + 1) = f(n)`, so `k + 1 ≤ f(n)`.
    exact (hk (g m) (PNat.lt_add_one_iff.mp hn)).trans_lt (hfg m)
  ---- It follows that `f(n) ≥ n` for all `n`.
  replace h (n) : n ≤ f n := h (le_refl n)
  ---- By induction on `t`, we get `f^t(n)` for all `n`.
  replace h : ∀ t n, n ≤ f^[t] n :=
    Nat.rec le_refl λ t ht n ↦ (h n).trans (ht (f n))
  ---- For any `n`, we have `f(n + 1) > f^{g(n)}(n) ≥ f^2(n)`.
  replace hfg (n) : f^[2] n < f (n + 1) :=
    calc f^[2] n
    _ ≤ f^[g n - 2 + 2] n := h (g n - 2) (f^[2] n)
    _ = f^[g n] n := by rw [Nat.sub_add_cancel (hg n)]
    _ < f (n + 1) := hfg n
  ---- For any `n`, we have `f(n + 1) > f^2(n) ≥ f(n)`, so `f` is strictly increasing.
  replace hg : StrictMono f := strictMono_pnat_of_lt_succ λ n ↦ (h 1 (f n)).trans_lt (hfg n)
  ---- Then for any` n`, `f(n + 1) > f^2(n)` implies `n + 1 > f(n)` or `f(n) ≤ n`.
  replace hfg (n) : f n ≤ n := PNat.lt_add_one_iff.mp (hg.lt_iff_lt.mp (hfg n))
  ---- Since we showed that `f(n) ≥ n`, we are done.
  exact funext λ n ↦ (h 1 n).antisymm' (hfg n)

/-- Final solution -/
theorem final_solution {f g : ℕ+ → ℕ+} :
    (∀ n, f^[g n + 1] n + g^[f n] n + g (n + 1) = f (n + 1) + 1)
      ↔ f = id ∧ g = λ _ ↦ 1 := by
  ---- The `←` case is easy; just substitute and check.
  refine Iff.symm ⟨λ h n ↦ ?_, λ h ↦ ?_⟩
  · rcases h with ⟨rfl, rfl⟩
    rw [Function.iterate_id, id, fn_iterate_const n.pos 1 n]; rfl
  ---- For the `→` case, we first show that `f = id`.
  obtain rfl : f = id := by
    -- We still need to show that `f^{g(n) + 1}(n) < f(n + 1)` for all `n`.
    refine f_eq_id_of_map_iter_lt_map_succ (g := λ n ↦ g n + 1)
      (λ n ↦ Nat.succ_le_succ (g n).pos) (λ n ↦ ?_)
    -- We show `f^{g(n) + 1}(n) + 1 < f(n + 1) + 1` instead.
    apply lt_of_add_lt_add_right (a := 1)
    -- Now do the calc.
    calc f^[g n + 1] n + 1
      _ ≤ f^[g n + 1] n + g^[f n] n := add_le_add_right (PNat.one_le _) _
      _ < f^[g n + 1] n + g^[f n] n + g (n + 1) := PNat.lt_add_right _ _
      _ = f (n + 1) + 1 := h n
  ---- Thus it remains to show that `g(n) = 1` for all `n ∈ ℕ+`.
  refine ⟨rfl, funext λ n ↦ ?_⟩
  ---- Rewrite the original functional equation as `g^n(n) + g(n + 1) = 2`.
  replace h (n : ℕ+) : g^[n] n + g (n + 1) = 1 + 1 := by
    simpa only [Function.iterate_id, id, add_assoc, add_right_inj] using h n
  ---- If `n = 1`, then `g(1) + g(2) = 2` implies `g(1) = 1`.
  obtain rfl | h0 : n = 1 ∨ 1 < n := n.one_le.eq_or_lt'
  · exact pnat_add_eq_two_imp_left_eq_one (h 1)
  ---- If `n ≠ 1`, then `g^{n - 1}(n - 1) + g(n) = 2` implies `g(n) = 1`.
  calc g n
    _ = g (n - 1 + 1) := congrArg g (PNat.sub_add_of_lt h0).symm
    _ = 1 := pnat_add_eq_two_imp_left_eq_one ((add_comm _ _).trans (h _))
