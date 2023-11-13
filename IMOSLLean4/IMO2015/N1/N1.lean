import Mathlib.Data.Int.Parity

/-! # IMO 2015 N1 -/

namespace IMOSL
namespace IMO2015N1

def f (n : ℤ) := n * (n / 2)

theorem main_claim {c m : ℤ} (h : 2 * c ∣ m - 3) (h0 : 2 * c ∣ f m - 3) :
    2 * (2 * c) ∣ m - 3 := by
  by_cases h1 : c = 0
  · rwa [h1, mul_zero, ← h1]
  · rcases h with ⟨d, h⟩
    rw [h, mul_comm]
    apply mul_dvd_mul_left
    have X : (2 : ℤ) ≠ 0 := two_ne_zero
    have X0 : (3 / 2 : ℤ) = 1 := rfl
    rw [f, eq_add_of_sub_eq h, add_mul, add_sub_assoc, mul_assoc, ← mul_sub_one,
      dvd_add_right ⟨_, rfl⟩, mul_assoc, add_comm, Int.add_mul_ediv_left _ _ X,
      X0, add_sub_cancel', ← two_add_one_eq_three, add_one_mul, ← mul_assoc,
      dvd_add_right ⟨_, rfl⟩, mul_comm] at h0
    exact Int.dvd_of_mul_dvd_mul_left h1 h0

/-- Final solution -/
theorem final_solution {M : ℤ} : (∃ k : ℕ, 2 ∣ (f^[k]) M) ↔ M ≠ 3 := by
  rw [iff_not_comm, not_exists]
  refine ⟨λ h n ↦ ?_, λ h ↦ ?_⟩
  · have h0 : f 3 = 3 := rfl
    rw [h, Function.iterate_fixed h0, ← two_add_one_eq_three]
    exact Int.two_not_dvd_two_mul_add_one 1
  · suffices h0 : ∀ n k, 2 ^ (n + 1) ∣ f^[k] M - 3
    · let K := (M - 3).natAbs
      refine eq_of_sub_eq_zero <| Int.eq_zero_of_abs_lt_dvd (h0 K 0) <| ?_
      rw [← Int.coe_natAbs, ← Nat.cast_ofNat (n := 2), ← Int.coe_nat_pow]
      exact Int.ofNat_lt.mpr (K.lt_succ_self.trans K.succ.lt_two_pow)
    · refine Nat.rec (λ k ↦ ?_) (λ n h0 k ↦ ?_)
      · rw [Int.dvd_iff_emod_eq_zero, Nat.zero_add, pow_one,
          ← Int.even_iff, Int.even_sub', Int.odd_iff_not_even,
          Int.even_iff, ← Int.dvd_iff_emod_eq_zero]
        refine iff_of_true (h k) (Int.odd_iff.mpr rfl)
      · rw [pow_succ, pow_succ]
        refine main_claim ?_ ?_
        · rw [← pow_succ]; exact h0 k
        · rw [← pow_succ, ← f.iterate_succ_apply']; exact h0 (k + 1)
