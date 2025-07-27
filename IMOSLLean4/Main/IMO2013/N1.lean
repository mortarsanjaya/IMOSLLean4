/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Basic

/-!
# IMO 2013 N1

Find all functions $f : ℕ^+ → ℕ^+$ such that, for any $m, n : ℕ^+$,
$$ m^2 + f(n) ∣ m f(m) + n. $$

### Answer

$f(n) = n$.

### Solution

We follow both Solution 1 and Solution 2 of the
  [official solution](https://www.imo-official.org/problems/IMO2013SL.pdf).
For the → direction, we use Solution 2 for $f(n) ≤ n$ and we use Solution 1 for $f(n) ≥ n$.
-/

namespace IMOSL
namespace IMO2013N1

/-- Final solution -/
theorem final_solution {f : ℕ+ → ℕ+} :
    (∀ m n : ℕ+, m * m + f n ∣ m * f m + n) ↔ f = id := by
  ---- The `←` direction is obvious, so now we just work on the `→` direction.
  refine ⟨λ h ↦ ?_, λ h m n ↦ h ▸ dvd_refl _⟩
  ---- Break the equality `f(n) = n` into `f(n) ≤ n` and `f(n) ≥ n`.
  refine funext λ n ↦ le_antisymm ?_ ?_
  ---- Prove `f(n) ≤ n` via substituting `m = f(n)`.
  · apply PNat.le_of_dvd
    replace h : (f n : ℕ) ∣ f n * f (f n) + n :=
      PNat.dvd_iff.mp <| (Dvd.intro (f n + 1) rfl).trans (h (f n) n)
    rwa [Nat.dvd_add_right ⟨_, rfl⟩, ← PNat.dvd_iff] at h
  ---- Prove `f(n) ≥ n` via substituting `m = n`.
  · -- First, either `n = 1` or `n = k + 1` for some `k : ℕ+`.
    obtain rfl | ⟨k, rfl⟩ : n = 1 ∨ ∃ k, n = k + 1 :=
      (eq_or_ne n 1).imp_right PNat.exists_eq_succ_of_ne_one
    -- The case `n = 1` is obvious.
    · exact (f 1).one_le
    -- For `n = k + 1`, do the substitution `m = k + 1`.
    · replace h := PNat.le_of_dvd (h (k + 1) (k + 1))
      rw [add_one_mul k, add_right_comm, add_assoc, add_one_mul k, add_assoc] at h
      exact le_of_mul_le_mul_left' (le_of_add_le_add_right h)
