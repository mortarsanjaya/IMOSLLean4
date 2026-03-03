/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Basic

/-!
# IMO 2007 A2

Consider all functions $f : ℕ⁺ → ℕ⁺$ such that for any $m, n ∈ ℕ⁺$,
$$ f(m + n) + 1 ≥ f(m) + f(f(n)). $$
For any $N ∈ ℕ⁺$, find all possible values of $f(N)$.

### Answer

* If $N = 1$ then the only possible value is $1$.
* If $N > 1$ then the possible values are positive integers less than or equal to $N + 1$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2007SL.pdf),
  except for the final step and the case $N = 1$.
However, the main arguments are done over $ℕ$ instead.
We say that a function $g : ℕ → ℕ$ is *good* if for any $m, n ∈ ℕ⁺$,
$$ g(m + n + 1) ≥ g(m) + g(g(n)). $$
Then it is easy to see that $f : ℕ⁺ → ℕ⁺$ satisfies the given condition
  if and only if the function $g(n) = f(n - 1) + 1$ is good.
We prove that any good function $g$ satisfies $g(0) = 0$, and we prove that
  the possible values of $g(N)$ for $N > 0$ across all good functions $g$ are
  non-negative integers less than or equal to $N + 1$.
Note that the official solution only considers the case $N = 2007$.
However, the proof works for all $N$ except $N = 1$,
  which requires the proof that all good functions $g$ satisfy $g(0) = 0$.

As in the official solution, we prove that $g$ is non-decreasing.
Now suppose for the sake of contradiction that $g(0) > 0$.
Then $g(1) ≥ g(0) + g(g(0)) > g(g(0))$, so $g(0) < 1$; contradiction.
It remains to show that $g(N) ≤ N + 1$ for all $N ∈ ℕ$.

First consider an arbitrary $m ∈ ℕ$ with $g(m) > 0$.
The original inequality implies $g(m + n + 1) > g(g(n))$ for any $n ∈ ℕ$.
Since $g$ is non-decreasing, we get $m + n + 1 > g(n)$ or $m ≥ g(n) - n$ for all $n ∈ ℕ$.

Now suppose for the sake of contradiction that $g(N) ≥ N + 2$.
Then $g(m + N + 1) ≥ g(m) + g(g(N)) ≥ g(m) + (N + 2)$ for any $m ∈ ℕ$.
By induction, we get $g((N + 1)m) ≥ (N + 2)m$ for any $m ∈ ℕ$.
But then $g((N + 1)^2) - (N + 1)^2 ≥ N + 1 > N$; contradiction.
-/

namespace IMOSL
namespace IMO2007A2

/-- A function `g : ℕ → ℕ` is called *good* if
  `g(m + n + 1) ≥ g(m) + g(g(n))` for all `m, n : ℕ`. -/
def good (g : ℕ → ℕ) := ∀ m n : ℕ, g m + g (g n) ≤ g (m + n + 1)

/-- For any `m, n, k : ℕ` we have `(m - k) + (n - k) ≤ m + n - k`. -/
theorem sub_add_sub_le_add_sub (m n k : ℕ) : (m - k) + (n - k) ≤ m + n - k := by
  obtain h | h : n ≤ k ∨ k ≤ n := Nat.le_total n k
  ---- Case 1: `n ≤ k`.
  · calc m - k + (n - k)
    _ = m - k := by rw [Nat.sub_eq_zero_of_le h, Nat.add_zero]
    _ ≤ m + n - k := Nat.sub_le_sub_right (Nat.le_add_right _ _) _
  ---- Case 2: `k ≤ n`.
  · calc m - k + (n - k)
    _ ≤ m + (n - k) := Nat.add_le_add_right (Nat.sub_le _ _) _
    _ = m + n - k := (Nat.add_sub_assoc h _).symm

/-- The function `n ↦ n - C` is good for any `C : ℕ`. -/
theorem sub_right_is_good (C : ℕ) : good (· - C) := by
  intro m n; calc m - C + (n - C - C)
    _ ≤ (m - C) + (n - C) := Nat.add_le_add_left (Nat.sub_le _ _) _
    _ ≤ m + n - C := sub_add_sub_le_add_sub _ _ _
    _ ≤ m + n + 1 - C := Nat.sub_le_sub_right (Nat.le_add_right _ _) _

/-- For any `K ≠ 1`, the function `g : ℕ → ℕ` defined by
  `g(n) = n` if `K ∤ n + 1` and `g(n) = n + 1` if `K ∣ n + 1` is good. -/
theorem ite_dvd_add_one_is_good (hK : K ≠ 1) :
    good (λ n ↦ if K ∣ n + 1 then n + 1 else n) := by
  intro m n; dsimp only
  by_cases hn : K ∣ n + 1
  ---- Case 1: `K ∣ n + 1`.
  · apply Nat.le_of_eq
    have hn0 : ¬K ∣ n + 1 + 1 := by rwa [Nat.dvd_add_right hn, Nat.dvd_one]
    calc (if K ∣ m + 1 then m + 1 else m) + _
      _ = (if K ∣ m + 1 then m + 1 else m) + (n + 1) := by rw [if_pos hn, if_neg hn0]
      _ = if K ∣ m + 1 then (m + 1) + (n + 1) else m + (n + 1) := ite_add _ _ _ _
      _ = if K ∣ (m + 1) + (n + 1) then (m + 1) + (n + 1) else m + (n + 1) :=
        if_congr (Nat.dvd_add_iff_left hn) rfl rfl
      _ = if K ∣ m + n + (1 + 1) then m + n + (1 + 1) else m + (n + 1) := by
        rw [Nat.add_add_add_comm]
  ---- Case 2: `K ∤ n + 1`.
  · calc (if K ∣ m + 1 then m + 1 else m) + _
    _ = (if K ∣ m + 1 then m + 1 else m) + n := by rw [if_neg hn, if_neg hn]
    _ ≤ max (m + 1) m + n := Nat.add_le_add_right (ite_le_sup _ _ _) _
    _ = m + 1 + n := congrArg (· + n) (max_eq_left_of_lt (Nat.lt_succ_self m))
    _ = m + n + 1 := Nat.add_right_comm _ _ _
    _ = min (m + n + 1 + 1) (m + n + 1) := (min_eq_right_of_lt (Nat.lt_succ_self _)).symm
    _ ≤ if K ∣ m + n + 1 + 1 then m + n + 1 + 1 else m + n + 1 := inf_le_ite _ _ _


namespace good

variable {g : ℕ → ℕ} (hg : good g)
include hg

/-- A good function is monotone. -/
theorem monotone : Monotone g := by
  refine monotone_iff_forall_lt.mpr λ x y h ↦ ?_
  calc g x
    _ ≤ g x + g (g (y - (x + 1))) := Nat.le_add_right _ _
    _ ≤ g (x + (y - (x + 1)) + 1) := hg x (y - (x + 1))
    _ = g y := by rw [Nat.add_right_comm, Nat.add_sub_of_le h]

/-- If `g` is a good function, then `g(0) = 0`. -/
theorem map_zero : g 0 = 0 :=
  Nat.eq_zero_of_not_pos λ h0 ↦
    (hg.monotone h0).not_gt ((Nat.lt_add_of_pos_left h0).trans_le (hg 0 0))

/-- If `g` is a good function and `g(m) > 0`, then `g(n) ≤ m + n` for any `n : ℕ`. -/
theorem map_le_add_of_map_pos (hm : g m > 0) (n) : g n ≤ m + n := by
  refine Nat.le_of_not_lt λ h ↦ Nat.not_lt_of_le (hg m n) ?_
  calc g (m + n + 1)
    _ ≤ g (g n) := hg.monotone h
    _ < g m + g (g n) := Nat.lt_add_of_pos_left hm

/-- If `g` is a good function, then `g(N) ≤ N + 1` for all `N : ℕ`. -/
theorem map_bound (N : ℕ) : g N ≤ N + 1 := by
  ---- Suppose for the sake of contradiction that `g(N) ≥ N + 2`.
  refine Nat.le_of_not_lt λ hN ↦ ?_
  ---- Then `g(m + N + 1) ≥ g(m) + (N + 2)` for all `m : ℕ`.
  have hN0 (m) : g m + (N + 2) ≤ g (m + (N + 1)) := calc
    _ ≤ g m + g N := Nat.add_le_add_left hN _
    _ ≤ g m + g (N + 2) := Nat.add_le_add_left (hg.monotone (Nat.le_add_right _ _)) _
    _ ≤ g m + g (g N) := Nat.add_le_add_left (hg.monotone hN) _
    _ ≤ g (m + (N + 1)) := hg _ _
  ---- By induction, we get `g((N + 1) m) ≥ (N + 2) m` for all `m : ℕ`.
  replace hN0 (m) : (N + 2) * m ≤ g ((N + 1) * m) := by
    induction m with | zero => exact Nat.zero_le _ | succ m m_ih => ?_
    calc (N + 2) * m + (N + 2)
      _ ≤ g ((N + 1) * m) + (N + 2) := Nat.add_le_add_right m_ih _
      _ ≤ g ((N + 1) * m + (N + 1)) := hN0 _
  ---- Then `g((N + 1)^2) > N + (N + 1)^2`; contradiction.
  have hN1 : g ((N + 1) * (N + 1)) ≤ N + (N + 1) * (N + 1) :=
    hg.map_le_add_of_map_pos (Nat.zero_lt_of_lt hN) _
  replace hN0 : N + (N + 1) * (N + 1) + 1 ≤ g ((N + 1) * (N + 1)) := calc
    _ = (N + 2) * (N + 1) := by rw [Nat.add_right_comm, Nat.add_comm, ← Nat.succ_mul]
    _ ≤ g ((N + 1) * (N + 1)) := hN0 _
  exact Nat.not_lt_of_le hN1 hN0

end good


/-- The possible values of `g(N)` across good functions `g` are `0` if `N = 0`
  and any non-negative integer less than or equal to `N + 1` if `N > 0`. -/
theorem eq_map_good_iff : (∃ g, good g ∧ g N = k) ↔ k ≤ N + 1 ∧ (N = 0 → k = 0) := by
  ---- The `→` direction has been done above directly.
  refine ⟨?_, ?_⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨hg.map_bound N, λ hN ↦ hN ▸ hg.map_zero⟩
  ---- For the `←` direction, the case `N = 0` is straightforward, so now assume `N ≠ 0`.
  rintro ⟨hkN, hkN0⟩
  obtain rfl | hN : N = 0 ∨ N ≠ 0 := eq_or_ne _ _
  · exact ⟨id, sub_right_is_good 0, (hkN0 rfl).symm⟩
  ---- If `k ≤ N`, then `g(n) = n - (N - k)` works.
  obtain hk0 | rfl : k ≤ N ∨ k = N + 1 := Nat.le_or_eq_of_le_succ hkN
  · exact ⟨(· - (N - k)), sub_right_is_good _, Nat.sub_sub_self hk0⟩
  ---- If `k = N + 1`, then take `g(n) = n` for `N + 1 ∤ n` and `g(n) = n + 1` otherwise.
  exact ⟨λ n ↦ if N + 1 ∣ n + 1 then n + 1 else n,
    ite_dvd_add_one_is_good (Nat.add_one_ne_add_one_iff.mpr hN), if_pos (Nat.dvd_refl _)⟩

/-- Final solution -/
theorem final_solution {N k : ℕ+} :
    (∃ f : ℕ+ → ℕ+, (∀ m n, f m + f (f n) ≤ f (m + n) + 1) ∧ f N = k)
      ↔ k ≤ N + 1 ∧ (N = 1 → k = 1) :=
  let σ : ℕ+ ≃ ℕ := Equiv.pnatEquivNat
  calc (∃ f : ℕ+ → ℕ+, (∀ m n, f m + f (f n) ≤ f (m + n) + 1) ∧ f N = k)
  _ ↔ (∃ g : ℕ → ℕ,
        (∀ m n : ℕ+, σ.symm.conj g m + σ.symm.conj g (σ.symm.conj g n)
          ≤ σ.symm.conj g (m + n) + 1) ∧ σ.symm.conj g N = k) :=
    σ.conj.exists_congr_left
  _ ↔ (∃ g, good g ∧ g N.natPred = k.natPred) := by
    refine exists_congr λ g ↦ and_congr (σ.forall₂_congr σ ?_) σ.symm_apply_eq
    intro x y; let a := σ x; let b := σ y
    calc σ.symm (g a) + σ.symm (g (σ (σ.symm (g b)))) ≤ σ.symm.conj g (x + y) + 1
      _ ↔ g a + 1 + (g (g b) + 1) ≤ g (x + y).natPred + 2 := by
        rw [σ.apply_symm_apply, ← PNat.coe_le_coe]; rfl
      _ ↔ g a + g (g b) ≤ g (x + y).natPred := by
        rw [Nat.add_add_add_comm, Nat.add_le_add_iff_right]
      _ ↔ g a + g (g b) ≤ g (a + b + 1) := by
        suffices (x + y).natPred = a + b + 1 by rw [this]
        change (x + y).natPred = x.natPred + y.natPred + 1
        rw [← Nat.add_left_inj (n := 1), PNat.natPred_add_one, Nat.add_assoc,
          Nat.add_add_add_comm, PNat.natPred_add_one, PNat.natPred_add_one]; rfl
  _ ↔ k.natPred ≤ N.natPred + 1 ∧ (σ N = 0 → σ k = 0) := eq_map_good_iff
  _ ↔ k ≤ N + 1 ∧ (N = 1 → k = 1) := by
    refine and_congr ?_ (imp_congr σ.apply_eq_iff_eq_symm_apply σ.apply_eq_iff_eq_symm_apply)
    rw [PNat.natPred_add_one, ← Nat.add_le_add_iff_right (n := 1), PNat.natPred_add_one]; rfl
