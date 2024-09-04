/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.NatSequence.AntitoneConst
import IMOSLLean4.Extra.Infinitesimal.Archimedean
import Mathlib.Data.Fin.VecNotation

/-!
# IMO 2006 A1

Let $R$ be an archimedean ring with floor.
Define the function $f : R → R$ by $$ f(x) = ⌊x⌋ (x - ⌊x⌋). $$
Prove that for any $r ∈ R$, there exists $N ∈ ℕ$ such that for all $k ≥ N$,
$$ f^{k + 2}(r) = f^k(r). $$
-/

namespace IMOSL
namespace IMO2006A1

open Extra

variable [LinearOrderedRing R] [FloorRing R]

abbrev f (r : R) := ⌊r⌋ * Int.fract r

theorem floor_f_nonneg {r : R} (h : 0 ≤ ⌊r⌋) : 0 ≤ ⌊f r⌋ :=
  Int.floor_nonneg.mpr <| mul_nonneg (Int.cast_nonneg.mpr h) (Int.fract_nonneg r)

theorem floor_f_nonpos {r : R} (h : ⌊r⌋ ≤ 0) : ⌊f r⌋ ≤ 0 :=
  Int.cast_le.mp <| (Int.floor_le _).trans <| Int.cast_zero (R := R) ▸
    mul_nonpos_of_nonpos_of_nonneg (Int.cast_nonpos.mpr h) (Int.fract_nonneg r)

theorem floor_f_natAbs_le (r : R) : ⌊f r⌋.natAbs ≤ ⌊r⌋.natAbs := by
  rw [← Nat.cast_le (α := ℤ), Int.cast_natAbs, Int.cast_natAbs,
    Int.cast_abs, Int.cast_id, Int.cast_abs, Int.cast_id]
  rcases le_total 0 ⌊r⌋ with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg (floor_f_nonneg h), ← Int.cast_le (R := R)]
    exact (Int.floor_le _).trans <| mul_le_of_le_one_right
      (Int.cast_nonneg.mpr h) (Int.fract_lt_one r).le
  · rw [abs_of_nonpos (floor_f_nonpos h), abs_of_nonpos h, neg_le_neg_iff, Int.le_floor]
    exact le_mul_of_le_one_right (Int.cast_nonpos.mpr h) (Int.fract_lt_one r).le

theorem floor_f_iter_natAbs_le (r : R) : ∀ k, ⌊f^[k] r⌋.natAbs ≤ ⌊r⌋.natAbs
  | 0 => le_refl _
  | k + 1 => (floor_f_iter_natAbs_le _ k).trans (floor_f_natAbs_le r)

theorem floor_f_iter_natAbs_eventually_const (r : R) :
    ∃ C N, ∀ n, ⌊f^[n + N] r⌋.natAbs = C :=
  NatSeq_antitone_imp_const (a := λ k ↦ ⌊f^[k] r⌋.natAbs) λ k m h0 ↦ by
    rcases Nat.exists_eq_add_of_le h0 with ⟨c, rfl⟩
    simp only; rw [Nat.add_comm, f.iterate_add_apply]
    exact floor_f_iter_natAbs_le _ c

theorem floor_f_lt_of_floor_pos {r : R} (h : 0 < ⌊r⌋) : ⌊f r⌋ < ⌊r⌋ :=
  Int.floor_lt.mpr <| mul_lt_of_lt_one_right (Int.cast_pos.mpr h) (Int.fract_lt_one r)

theorem floor_f_iter_eventually_const (r : R) : ∃ (C N : ℕ), ∀ n, ⌊f^[n + N] r⌋ = -C := by
  rcases floor_f_iter_natAbs_eventually_const r with ⟨C, N, h⟩
  refine ⟨C, N, λ n ↦ (Int.natAbs_eq_iff.mp (h n)).elim (λ h0 ↦ h0.trans ?_) id⟩
  simp only at h h0 ⊢; rcases C.eq_zero_or_pos with rfl | h1; rfl
  specialize h (n + 1); rw [Nat.add_right_comm, f.iterate_succ_apply'] at h
  replace h1 : 0 < ⌊f^[n + N] r⌋ := by rwa [h0, Nat.cast_pos]
  rw [← h, Int.natCast_natAbs, abs_of_nonneg (floor_f_nonneg h1.le)] at h0
  exact absurd h0.symm (floor_f_lt_of_floor_pos h1).ne

theorem case_floor_neg_one {r : R} (h : ∀ n, ⌊f^[n] r⌋ = -1) :
    ∃ s : R, (0 < s ∧ s < 1) ∧ (∀ n, f^[n] r = ![-s, s - 1] n) := by
  have X : ((-1 : ℤ) : R) = -1 := by rw [Int.cast_neg, Int.cast_one]
  refine ⟨-r, ?_, ?_⟩
  ---- `0 < r < 1`
  · rw [neg_pos, neg_lt]
    have h0 := Int.floor_eq_iff.mp (h 0)
    rw [f.iterate_zero_apply, X, neg_add_self, and_comm] at h0
    revert h0; refine And.imp_right λ h0 ↦ h0.lt_of_ne λ h1 ↦ ?_
    replace h0 : Int.fract (-1 : R) = 0 := Int.fract_neg_eq_zero.mpr Int.fract_one
    specialize h 1; rw [f.iterate_one, ← h1, f, h0, mul_zero, Int.floor_zero] at h
    exact one_ne_zero (zero_eq_neg.mp h)
  ---- Formula for `f^n(r)`
  · rw [neg_neg]; refine Nat.rec rfl λ n h0 ↦ ?_
    have X0 : (n.succ : Fin 2) = n + 1 := by
      rw [Fin.ext_iff, Fin.val_add, Fin.val_natCast,
        Fin.val_natCast, Fin.val_one, Nat.mod_add_mod]
    rw [f.iterate_succ_apply', f, Int.fract, h, X, h0,
      neg_one_mul, sub_neg_eq_add, neg_add', X0]
    exact Fin.cases rfl (λ i ↦ by simp [Fin.fin_one_eq_zero i]) n

theorem case_floor_neg_of_one_lt {r : R} {C : ℕ} (hC : 1 < C) (h : ∀ n, ⌊f^[n] r⌋ = -C) :
    ∃ ε : R, Infinitesimal ε ∧ ∀ n, (C + 1) * f^[n] r = -C ^ 2 + (-C) ^ n * ε := by
  have h0 (k) : (C + 1) * f^[k + 1] r + C ^ 2 = -C * ((C + 1) * f^[k] r + C ^ 2) := by
    rw [f.iterate_succ_apply', f, Int.fract, h, Int.cast_neg, Int.cast_natCast]
    generalize (C : R) = C; generalize f^[k] r = T
    rw [sub_neg_eq_add, neg_mul, mul_neg, ← eq_sub_iff_add_eq, neg_mul, ← neg_add',
      neg_inj, mul_add, mul_add, mul_add, add_assoc, ← sq, ← add_one_mul C,
      add_left_inj, ← mul_assoc, ← mul_assoc, add_one_mul C, mul_add_one C]
  replace h0 : ∀ k, (C + 1) * f^[k] r + C ^ 2 = (-C) ^ k * ((C + 1) * r + C ^ 2) :=
    Nat.rec (by rw [pow_zero, one_mul]; rfl)
      (λ k h1 ↦ by rw [h0, h1, ← mul_assoc, ← pow_succ'])
  refine ⟨(C + 1) * r + C ^ 2, ?_, λ k ↦ eq_neg_add_of_add_eq ((add_comm _ _).trans (h0 k))⟩
  ---- Remains to check that `ε = (C + 1) f^N(r) + C^2` is infinitesimal
  generalize (C + 1) * r + C ^ 2 = ε at h0 ⊢
  replace h0 (k) : |(C + 1) * Int.fract (f^[k] r) - C| = C ^ k • |ε| := by
    rw [Int.fract, h, Int.cast_neg, Int.cast_natCast, sub_neg_eq_add, mul_add,
      add_one_mul (C : R) C, add_sub_assoc, add_sub_cancel_right, ← sq, h0,
      abs_mul, abs_pow, abs_neg, Nat.abs_cast, nsmul_eq_mul, Nat.cast_pow]
  replace h (s : R) : |(C + 1) * Int.fract s - C| < ((C + 1 + C : ℕ) : R) := by
    apply (abs_sub _ _).trans_lt
    rw [Nat.abs_cast, Nat.cast_add, add_lt_add_iff_right, ← Nat.cast_succ,
      abs_mul, Nat.abs_cast, abs_of_nonneg (Int.fract_nonneg s)]
    exact mul_lt_of_lt_one_right (Nat.cast_pos.mpr C.succ_pos) (Int.fract_lt_one _)
  refine Infinitesimal.iff_nsmul_Nat_bdd.mpr ⟨C + 1 + C, λ k ↦ ?_⟩
  apply (nsmul_le_nsmul_left (abs_nonneg ε) (Nat.lt_pow_self hC k).le).trans_lt
  exact (h0 _).symm.trans_lt (h (f^[k] r))





/-! ### Extra predicates -/

/-- Predicate for what the sequence `(f^[n](x))_{n ≥ 0}` looks like eventually. -/
inductive GeneralGood : (ℕ → R) → Prop
  | const_zero : GeneralGood λ _ ↦ 0
  | two_period (s : R) (_ : 0 < s) (_ : s < 1) : GeneralGood λ n ↦ ![-s, s - 1] n
  | const_nonzero_add_Infinitesimal (C : ℕ) (_ : 1 < C) (ε : R) (_ : Infinitesimal ε)
        (a : ℕ → R) (_ : ∀ n, (C + 1) * a n = -C ^ 2 + (-C) ^ n * ε) :
      GeneralGood a

/-- Predicate for what the sequence `(f^[n](x))_{n ≥ 0}` looks like eventually,
  in the archimedean case. -/
inductive ArchimedeanGood : (ℕ → R) → Prop
  | const_zero : ArchimedeanGood λ _ ↦ 0
  | two_period (s : R) (_ : 0 < s) (_ : s < 1) : ArchimedeanGood λ n ↦ ![-s, s - 1] n
  | const_nonzero (C : ℕ) (_ : 1 < C) (a : ℕ → R) (_ : ∀ n, (C + 1) * a n = -C ^ 2) :
      ArchimedeanGood a

theorem GeneralGood.toArchimedeanGood [Archimedean R] {a : ℕ → R} (h : GeneralGood a) :
    ArchimedeanGood a := by
  refine h.recOn ArchimedeanGood.const_zero ArchimedeanGood.two_period ?_
  ---- Case `const_nonzero_add_Infinitesimal` remaining
  refine λ C h ε h0 a h1 ↦ ArchimedeanGood.const_nonzero C h a λ n ↦ ?_
  rw [h1, h0.zero_of_Archimedean, mul_zero, add_zero]

theorem ArchimedeanGood.two_periodic {a : ℕ → R} (h : ArchimedeanGood a) (n) :
    a (n + 2) = a n := by
  refine h.recOn rfl ?_ ?_
  ---- Case `two_period`
  · rintro s - -; apply congrArg
    rw [Fin.ext_iff, Fin.val_natCast, Fin.val_natCast, Nat.add_mod_right]
  ---- Case `const_nonzero`
  · rintro C - a ha
    have hC : 0 < (C : R) + 1 := (Nat.cast_pos.mpr C.succ_pos).trans_eq C.cast_succ
    rw [← mul_left_cancel_iff_of_pos hC, ha, ha]





/-! ### Summary -/

/-- Main result, general (non-archimedean) version -/
theorem eventually_GeneralGood (r : R) : ∃ N, GeneralGood (f^[· + N] r) := by
  rcases floor_f_iter_eventually_const r with ⟨_ | _ | C, N, h⟩
  ---- Case 1: `C = 0`
  · suffices ∀ n, f^[n + (N + 1)] r = 0
      from ⟨N + 1, funext this ▸ GeneralGood.const_zero⟩
    intro n; rw [← Nat.add_assoc, f.iterate_succ_apply', f, h,
      Int.cast_neg, Nat.cast_zero, Int.cast_zero, neg_zero, zero_mul]
  ---- Case 2: `C = 1`
  · simp only [f.iterate_add_apply] at h ⊢
    obtain ⟨s, h0, h1⟩ := case_floor_neg_one h
    exact ⟨N, funext h1 ▸ GeneralGood.two_period s h0.1 h0.2⟩
  ---- Case 3: `C > 1`
  · simp only [f.iterate_add_apply] at h ⊢
    have h0 := Nat.one_lt_succ_succ C
    obtain ⟨ε, hε, h1⟩ := case_floor_neg_of_one_lt h0 h
    exact ⟨N, GeneralGood.const_nonzero_add_Infinitesimal _ h0 ε hε _ h1⟩

/-- Main result, archimedean version -/
theorem eventually_ArchimedeanGood [Archimedean R] (r : R) :
    ∃ N, ArchimedeanGood (f^[· + N] r) :=
  (eventually_GeneralGood r).imp λ _ ↦ GeneralGood.toArchimedeanGood

/-- Final solution -/
theorem final_solution [Archimedean R] (r : R) : ∃ N, ∀ n ≥ N, f^[n + 2] r = f^[n] r := by
  refine (eventually_ArchimedeanGood r).imp λ N hN n hn ↦ ?_
  have h := hN.two_periodic (n - N)
  rwa [Nat.add_right_comm, Nat.sub_add_cancel hn] at h
