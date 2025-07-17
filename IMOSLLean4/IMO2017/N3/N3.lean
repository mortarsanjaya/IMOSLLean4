/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.Group.Units.Equiv

/-!
# IMO 2017 N3

Let $n > 1$ be an integer.
A *special $n$-tuple* is an $n$-tuple $\mathbf{a} = (a_0, a_1, …, a_{n - 1})$ of integers
  such that there exists an indexing function $f : [n] → [n]$ such that for all $i$,
$$ n ∣ a_i + a_{i + 1} + … + a_{i + f(i)}. $$
Determine all $n > 1$ such that any special $n$-tuple $\mathbf{a}$ satisfies
$$ n ∣ a_1 + a_2 + … + a_n. $$
-/

namespace IMOSL
namespace IMO2017N3

open Finset

/-! ### Extra lemmas -/

lemma mod_succ_eq_iff : k % n.succ = n ↔ n.succ ∣ k + 1 := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_add_mod, h, Nat.mod_self]
  · obtain ⟨k', rfl⟩ : ∃ k', k = n + k' :=
      Nat.exists_eq_add_of_le (Nat.le_of_succ_le_succ (Nat.le_of_dvd k.succ_pos h))
    rw [Nat.add_right_comm, Nat.dvd_add_self_left] at h
    rcases h with ⟨j, rfl⟩
    rw [Nat.add_mul_mod_self_left, Nat.mod_succ]

theorem Nat_exists_iterate_mod_eq (hp : 0 < p) (f : ℕ → ℕ) (i : ℕ) :
    ∃ k m, m > 0 ∧ m ≤ p ∧ f^[k + m] i % p = f^[k] i % p := by
  ---- Reduce to the true pigeonhole principle with pigenhole indexed by `[p + 1]`
  suffices ∃ m ∈ range p.succ, ∃ n ∈ range p.succ, m ≠ n ∧ f^[m] i % p = f^[n] i % p by
    rcases this with ⟨m, hm, n, hn, h, h0⟩
    wlog h1 : m < n
    · exact this hp f i n hn m hm h.symm h0.symm
        (Nat.lt_of_le_of_ne (Nat.le_of_not_lt h1) h.symm)
    refine ⟨m, n - m, Nat.sub_pos_of_lt h1, ?_, ?_⟩
    · exact (Nat.sub_le _ _).trans (Nat.le_of_lt_succ (mem_range.mp hn))
    · rw [Nat.add_sub_cancel' h1.le, h0]
  ---- Deduce the pigeonhole principle on `k ↦ f^[k] i % p`
  apply exists_ne_map_eq_of_card_lt_of_maps_to (t := range p)
  · rw [card_range, card_range]; exact p.lt_succ_self
  · rintro a -; exact mem_range.mpr (Nat.mod_lt _ hp)



/-! ##### Extra lemmas on sums over `Fin` vs. sums over `Nat` -/

section

open Fin.NatCast

variable [AddCommMonoid M]

lemma sum_Ico_fin_boole_last (a : M) (n k m : ℕ) :
    ∑ i ∈ Ico k m, (if (i : Fin n.succ) = Fin.last n then a else 0)
      = (m / n.succ - k / n.succ) • a := by
  obtain h | ⟨j, rfl⟩ : m ≤ k ∨ ∃ j, m = k + j :=
    (Nat.le_total m k).imp_right Nat.exists_eq_add_of_le
  ---- Case `m ≤ k` follows by definition of `Ico` and subtraction on `Nat`
  · have h0 : m / n.succ ≤ k / n.succ := Nat.div_le_div_right h
    rw [Ico_eq_empty h.not_gt, Nat.sub_eq_zero_of_le h0, zero_nsmul, sum_empty]
  ---- Case `m ≥ k` follows by induction on `k - m`
  induction' j with j j_ih
  · rw [Nat.add_zero, Ico_self, Nat.sub_self, zero_nsmul, sum_empty]
  · have h : k ≤ k + j := k.le_add_right j
    have h0 : k / n.succ ≤ (k + j) / n.succ := Nat.div_le_div_right h
    rw [← Nat.add_assoc, sum_Ico_succ_top h, j_ih, Nat.succ_div,
      (_ / n.succ).add_comm, Nat.add_sub_assoc h0, add_comm, add_nsmul, ite_smul]
    refine congrArg₂ _ (if_congr ?_ (one_nsmul a).symm (zero_nsmul a).symm) rfl
    rw [Fin.ext_iff, Fin.val_natCast, Fin.val_last, mod_succ_eq_iff]

lemma sum_Ico_fin_add {n : ℕ} (f : Fin n.succ → M) (i : ℕ) :
    ∑ j ∈ Ico i (i + n.succ), f j = ∑ j : Fin n.succ, f j := by
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, ← Fin.sum_univ_eq_sum_range]
  simp only [Nat.cast_add, Fin.cast_val_eq_self]
  exact Equiv.sum_comp (Equiv.addLeft (i : Fin n.succ)) f

lemma sum_Ico_fin_add_mul {n : ℕ} (f : Fin n.succ → M) (i : ℕ) :
    ∀ k, ∑ j ∈ Ico i (i + n.succ * k), f j = k • ∑ j : Fin n.succ, f j := by
  refine Nat.rec ?_ λ k hk ↦ ?_
  · rw [Nat.mul_zero, i.add_zero, Ico_self, zero_nsmul, sum_empty]
  · rw [Nat.mul_succ, ← i.add_assoc, succ_nsmul, ← hk, ← sum_Ico_fin_add f (i + n.succ * k)]
    exact (sum_Ico_consecutive _ (i.le_add_right _) (Nat.le_add_right _ n.succ)).symm

end





/-! ### Start of the problem -/

open Fin.NatCast in
structure SpecialTuple (n : ℕ) where
  toFun : Fin n.pred.succ → ℤ
  jump_shift : Fin n.pred.succ → Fin n.pred.succ
  jump_shift_spec : ∀ i, (n : ℤ) ∣ ∑ j ∈ Ico i.1 (i.1 + ((jump_shift i).1 + 1)), toFun j


namespace SpecialTuple

section

open Function

variable (X : SpecialTuple n)

def sum : ℤ := ∑ i, X.toFun i

lemma sum_def : X.sum = ∑ i : Fin n.pred.succ, X.toFun i := rfl

/-- `g(i) = i + f(i) + 1`, where `f` is `jump_shift` -/
def jump_index (i : ℕ) : ℕ := open Fin.NatCast in i + ((X.jump_shift i).1 + 1)

lemma lt_jump_index (i : ℕ) : i < X.jump_index i :=
  Nat.lt_add_of_pos_right (Nat.succ_pos _)

lemma le_jump_index (i : ℕ) : i ≤ X.jump_index i :=
  (X.lt_jump_index i).le

lemma le_jump_index_iterate (i) : ∀ k, i ≤ X.jump_index^[k] i := by
  refine Nat.rec i.le_refl λ k hk ↦ hk.trans ?_
  rw [iterate_succ_apply']; exact X.le_jump_index _

lemma lt_jump_index_iterate_of_pos (i) (hk : 0 < k) : i < X.jump_index^[k] i :=
  Nat.succ_pred_eq_of_pos hk ▸ (X.lt_jump_index _).trans_le (X.le_jump_index_iterate _ _)

lemma jump_index_le_add (i : ℕ) : X.jump_index i ≤ i + n.pred.succ :=
  Nat.add_le_add_left (Fin.isLt _) i

end



/-! ##### The composite case -/

section

open Fin.NatCast

variable (ha : 1 < a) (hb : 0 < b)

def ofComposite : SpecialTuple (a * b) where
  toFun := λ i ↦ a - if i = Fin.last _ then a else 0
  jump_shift := λ i ↦ if i.1 + b < a * b then b.pred else b
  jump_shift_spec := λ i ↦ by
    have h : (a * b).pred.succ = a * b :=
      Nat.succ_pred_eq_of_pos (Nat.mul_pos (Nat.zero_lt_of_lt ha) hb)
    have hi : i.1 < a * b := i.2.trans_eq h
    generalize i.1 = i at hi ⊢
    rw [sum_sub_distrib, sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, ← Nat.cast_sum,
      sum_Ico_fin_boole_last, nsmul_eq_mul, smul_eq_mul, Nat.cast_mul, Nat.cast_mul]
    simp only [Nat.div_eq_of_lt hi, h]
    rw [Nat.sub_zero, ← sub_mul, mul_comm]
    have h0 : b < a * b := (Nat.lt_mul_iff_one_lt_left hb).mpr ha
    refine dvd_of_eq (congrArg₂ _ ?_ rfl); split_ifs with h1
    · rw [Fin.val_natCast, h, Nat.mod_eq_of_lt (b.pred_le.trans_lt h0), ← Nat.succ_eq_add_one,
        Nat.succ_pred_eq_of_pos hb, Nat.div_eq_of_lt h1, Nat.cast_zero, sub_zero]
    · rw [Fin.val_natCast, h, Nat.mod_eq_of_lt h0, Nat.cast_succ, eq_sub_iff_add_eq]
      refine congrArg₂ _ rfl (congrArg Nat.cast (Nat.div_eq_of_lt_le ?_ ?_))
      exacts [Nat.le_succ_of_le ((a * b).one_mul.trans_le (Nat.le_of_not_lt h1)),
        (Nat.add_lt_add_of_lt_of_le hi h0).trans_eq (a * b).two_mul.symm]

lemma ofComposite_toFun_apply (i) :
  (ofComposite ha hb).toFun i = a - if i = Fin.last _ then a else 0 := rfl

theorem ofComposite_sum : (ofComposite ha hb).sum = a * (a * b - 1) := by
  simp only [sum_def, ofComposite_toFun_apply, Nat.cast_ite]
  rw [sum_sub_distrib, Fin.sum_const, Nat.cast_zero, Fintype.sum_ite_eq',
    Nat.succ_pred_eq_of_pos (Nat.mul_pos (Nat.zero_lt_of_lt ha) hb),
    nsmul_eq_mul, Nat.cast_mul, Int.mul_comm, mul_sub_one]

end



/-! ##### The prime case -/

section

open Fin.NatCast

open Function

variable (X : SpecialTuple n)

lemma dvd_sum_range_jump_shift_succ (i : Fin n.pred.succ) :
    (n : ℤ) ∣ ∑ j ∈ range (X.jump_shift i + 1), X.toFun (i + j) := by
  have h := X.jump_shift_spec i
  simp only [sum_Ico_eq_sum_range, Nat.cast_add] at h
  rwa [Nat.add_sub_cancel_left, Fin.cast_val_eq_self] at h

lemma dvd_sum_Ico_jump_index (i : ℕ) :
    (n : ℤ) ∣ ∑ j ∈ Ico i (X.jump_index i), X.toFun j := by
  rw [jump_index, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  simp only [Nat.cast_add]; exact X.dvd_sum_range_jump_shift_succ _

lemma dvd_sum_Ico_jump_index_iterate (i : ℕ) :
    ∀ k, (n : ℤ) ∣ ∑ j ∈ Ico i (X.jump_index^[k] i), X.toFun j := by
  refine Nat.rec ⟨0, ?_⟩ λ k hk ↦ ?_
  · rw [iterate_zero, id, Ico_self, mul_zero, sum_empty]
  · replace hk := dvd_add hk (X.dvd_sum_Ico_jump_index (X.jump_index^[k] i))
    rw [sum_Ico_consecutive _ (X.le_jump_index_iterate i k) (X.le_jump_index _)] at hk
    rwa [iterate_succ_apply']

lemma exists_dvd_pos_lt_nsmul_sum (hn : 0 < n) (X : SpecialTuple n.succ) :
    ∃ m > 0, m < n.succ ∧ (n.succ : ℤ) ∣ m • X.sum := by
  have hn0 : 1 < n.succ := Nat.succ_lt_succ hn
  ---- If `g(i) = i + f(i) = i + n + 1` for some `i`, we are done
  obtain ⟨i, hi⟩ | hX :
      (∃ i, X.jump_index i = i + n.succ) ∨ (∀ i, X.jump_index i < i + n.succ) := by
    refine (em' _).imp_left λ h ↦ ?_
    rcases not_forall.mp h with ⟨i, hi⟩
    exact ⟨i, Nat.le_antisymm (jump_index_le_add X i) (Nat.le_of_not_lt hi)⟩
  · refine ⟨1, Nat.one_pos, hn0, ?_⟩
    have h := X.dvd_sum_Ico_jump_index_iterate i 1
    rwa [iterate_one, hi, sum_Ico_fin_add, ← one_nsmul (∑ _, _)] at h
  ---- Now assume that `g(i) ≤ i + n` for all `i`. First get an inequality for `g^k(i)`
  replace hX (i) : ∀ k, X.jump_index^[k] i ≤ i + n * k := by
    refine Nat.rec (Nat.le_add_right _ _) λ k hk ↦ ?_
    rw [iterate_succ_apply', Nat.mul_succ, ← Nat.add_assoc]
    exact (Nat.le_of_lt_succ (hX _)).trans (Nat.add_le_add_right hk _)
  ---- Get `g^{k + m}(0) = g^k(0) + (n + 1)t` for some `k` and `0 < t ≤ n`
  obtain ⟨k, m, t, ht, ht0, h⟩ : ∃ k m t, 0 < t ∧ t ≤ n ∧
      X.jump_index^[k + m] 0 = X.jump_index^[k] 0 + (n + 1) * t := by
    obtain ⟨k, m, hm, hm0, h⟩ := Nat_exists_iterate_mod_eq n.succ_pos X.jump_index 0
    refine ⟨k, m, ?_⟩
    let i₀ := X.jump_index^[k] 0
    obtain ⟨u, hu⟩ : ∃ u, X.jump_index^[m] i₀ = i₀ + u :=
      Nat.exists_eq_add_of_le (X.le_jump_index_iterate i₀ m)
    apply Nat.sub_mod_eq_zero_of_mod_eq at h
    rw [Nat.add_comm, iterate_add_apply, hu] at h ⊢
    rw [Nat.add_sub_cancel_left, ← Nat.dvd_iff_mod_eq_zero] at h
    rcases h with ⟨t, rfl⟩; refine ⟨t, ?_, ?_, rfl⟩
    · have h : i₀ < X.jump_index^[m] i₀ := X.lt_jump_index_iterate_of_pos i₀ hm
      rw [hu, Nat.lt_add_right_iff_pos] at h
      exact Nat.pos_of_mul_pos_left h
    · have h := (hX i₀ m).trans_lt (Nat.lt_add_of_pos_right hm)
      rw [hu, Nat.add_assoc, Nat.add_lt_add_iff_left, ← Nat.succ_mul] at h
      exact Nat.le_of_lt_succ ((Nat.lt_of_mul_lt_mul_left h).trans_le hm0)
  ---- The same `t` picked above works
  refine ⟨t, ht, Nat.lt_succ_of_le ht0, ?_⟩
  have h0 := X.dvd_sum_Ico_jump_index_iterate (X.jump_index^[k] 0) m
  rwa [← iterate_add_apply, Nat.add_comm, h, sum_Ico_fin_add_mul] at h0

end

end SpecialTuple





/-! ### Final solution -/

/-- Final solution -/
theorem final_solution (hn : 1 < n) : (∀ X : SpecialTuple n, (n : ℤ) ∣ X.sum) ↔ n.Prime := by
  refine ⟨λ h ↦ ?_, λ h X ↦ ?_⟩
  ---- `→` direction
  · by_contra h0; obtain ⟨a, ha, b, hb, rfl⟩ : ∃ a > 1, ∃ b > 1, a * b = n := by
      obtain ⟨p, hp, k, rfl⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ n :=
        Nat.exists_prime_and_dvd hn.ne.symm
      refine ⟨p, hp.one_lt, k, Nat.lt_of_not_le ?_, rfl⟩
      rw [Nat.le_one_iff_eq_zero_or_eq_one]; rintro (rfl | rfl)
      · rw [p.mul_zero] at hn; exact hn.not_gt Nat.one_pos
      · exact h0 (p.mul_one.symm ▸ hp)
    clear h0 hn; specialize h (SpecialTuple.ofComposite ha (Nat.zero_lt_of_lt hb))
    rw [SpecialTuple.ofComposite_sum, ← Int.natCast_mul, mul_sub_one,
      Int.dvd_iff_emod_eq_zero, sub_eq_add_neg, add_comm, Int.add_mul_emod_self_right,
      ← Int.dvd_iff_emod_eq_zero, Int.dvd_neg, Int.ofNat_dvd] at h
    have ha0 : 0 < a := Nat.zero_lt_of_lt ha
    exact Nat.not_dvd_of_pos_of_lt ha0 ((Nat.lt_mul_iff_one_lt_right ha0).mpr hb) h
  ---- `←` direction
  · obtain ⟨n, rfl⟩ : ∃ n' : ℕ, n = n'.succ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.zero_lt_of_lt hn).ne.symm
    obtain ⟨m, hm, hm0, h0⟩ := X.exists_dvd_pos_lt_nsmul_sum (Nat.lt_of_succ_lt_succ hn)
    have h1 : n.succ.Coprime m := h.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt hm hm0)
    rwa [Int.natCast_dvd, nsmul_eq_mul, Int.natAbs_mul,
      Int.natAbs_natCast, h1.dvd_mul_left, ← Int.natCast_dvd] at h0
