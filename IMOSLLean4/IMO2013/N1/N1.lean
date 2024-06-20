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
-/

namespace IMOSL
namespace IMO2013N1

/-- Final solution -/
theorem final_solution {f : ℕ+ → ℕ+} :
    (∀ m n : ℕ+, m * m + f n ∣ m * f m + n) ↔ f = id := by
  ---- Only `→` needs to be done now
  refine ⟨λ h ↦ funext λ n ↦ le_antisymm ?_ ?_, λ h m n ↦ h.symm ▸ dvd_refl (m * m + n)⟩
  ---- `f(n) ≤ n`
  · specialize h (f n) n
    rw [← mul_add_one (f n)] at h
    apply (dvd_mul_right _ _).trans at h
    rw [PNat.dvd_iff, PNat.add_coe, PNat.mul_coe,
      Nat.dvd_add_right ⟨_, rfl⟩, ← PNat.dvd_iff] at h
    exact PNat.le_of_dvd h
  ---- `f(n) ≥ n`
  · rcases eq_or_ne n 1 with rfl | h0
    · exact (f 1).one_le
    · rcases PNat.exists_eq_succ_of_ne_one h0 with ⟨k, rfl⟩
      replace h := PNat.le_of_dvd (h (k + 1) (k + 1))
      rw [add_one_mul k, add_right_comm, add_assoc, add_one_mul k, add_assoc] at h
      exact le_of_mul_le_mul_left' (le_of_add_le_add_right h)
