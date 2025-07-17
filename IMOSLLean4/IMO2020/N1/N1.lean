/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.NatSequence.SeqMax
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Cast.Defs

/-!
# IMO 2020 N1

Prove that, for any positive integer $k$, there exists a prime $p$ and
  distinct elements $x_1, x_2, …, x_{k + 3} \in 𝔽_p^×$ such that for all $i ≤ k$,
$$ x_i x_{i + 1} x_{i + 2} x_{i + 3} = i. $$
-/

namespace IMOSL
namespace IMO2020N1

/-! ### `ℚ` version of the "problem" -/

abbrev ratSeq : ℕ → ℚ
  | 0 => 2
  | 1 => 2⁻¹
  | 2 => -4
  | 3 => -4⁻¹
  | n + 4 => (1 + (n.succ : ℚ)⁻¹) * ratSeq n



/-! ##### Some basic properties -/

lemma ratSeq_zero : ratSeq 0 = 2 := rfl
lemma ratSeq_one : ratSeq 1 = 2⁻¹ := rfl
lemma ratSeq_two : ratSeq 2 = -4 := rfl
lemma ratSeq_three : ratSeq 3 = -4⁻¹ := rfl
lemma ratSeq_add_four (n) : ratSeq (n + 4) = (1 + (n.succ : ℚ)⁻¹) * ratSeq n := rfl

lemma one_add_inv_pos (n : ℕ) : 0 < 1 + (n : ℚ)⁻¹ :=
  add_pos_of_pos_of_nonneg one_pos (inv_nonneg_of_nonneg n.cast_nonneg)

lemma one_add_inv_ne_zero (n : ℕ) : 1 + (n : ℚ)⁻¹ ≠ 0 :=
  (one_add_inv_pos n).ne.symm

lemma ratSeq_ne_zero : ∀ n, ratSeq n ≠ 0
  | 0 => two_ne_zero
  | 1 => inv_ne_zero two_ne_zero
  | 2 => neg_ne_zero.mpr four_ne_zero
  | 3 => neg_ne_zero.mpr (inv_ne_zero four_ne_zero)
  | n + 4 => mul_ne_zero (one_add_inv_ne_zero _) (ratSeq_ne_zero n)

lemma ratSeq_formula :
    ∀ n, ratSeq n * ratSeq (n + 1) * ratSeq (n + 2) * ratSeq (n + 3) = n.succ := by
  refine Nat.rec (by simp) λ n h ↦ ?_
  rw [ratSeq_add_four, Rat.mul_comm, Rat.mul_assoc, ← (ratSeq n).mul_assoc,
    ← (ratSeq n).mul_assoc, h, one_add_mul, n.succ.cast_succ,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr n.succ_ne_zero)]



/-! ##### Sign of `ratSeq` -/

lemma ratSeq_add_four_pos_iff : 0 < ratSeq (n + 4) ↔ 0 < ratSeq n := by
  rw [ratSeq, mul_pos_iff_of_pos_left (one_add_inv_pos _)]

lemma ratSeq_add_four_mul_pos_iff : ∀ {k}, 0 < ratSeq (n + 4 * k) ↔ 0 < ratSeq n
  | 0 => Iff.rfl
  | _ + 1 => ratSeq_add_four_pos_iff.trans ratSeq_add_four_mul_pos_iff

lemma ratSeq_pos_iff_mod_four : 0 < ratSeq n ↔ 0 < ratSeq (n % 4) := by
  rw [← ratSeq_add_four_mul_pos_iff (n := n % 4), Nat.mod_add_div]

lemma ratSeq_pos_iff_of_lt_four (h : n < 4) : 0 < ratSeq n ↔ n = 0 ∨ n = 1 := by
  simp only [Nat.lt_succ_iff_lt_or_eq, Nat.not_lt_zero, false_or] at h
  rcases h with ((rfl | rfl) | rfl) | rfl
  all_goals simp

lemma ratSeq_pos_iff : 0 < ratSeq n ↔ n % 4 = 0 ∨ n % 4 = 1 := by
  rw [ratSeq_pos_iff_mod_four, ratSeq_pos_iff_of_lt_four (n.mod_lt (Nat.succ_pos 3))]

lemma ratSeq_pos_iff' : 0 < ratSeq n ↔ n % 4 < 2 := by
  rw [ratSeq_pos_iff, Nat.lt_succ_iff_lt_or_eq, Nat.lt_one_iff]



/-! ##### Magnitude of `ratSeq` -/

lemma ratSeq_add_four_abs_gt (n) : |ratSeq n| < |ratSeq (n + 4)| := by
  rw [ratSeq_add_four, abs_mul, abs_eq_self.mpr (one_add_inv_pos _).le]
  apply lt_mul_left (abs_pos.mpr (ratSeq_ne_zero n))
  rw [lt_add_iff_pos_right, inv_pos, Nat.cast_pos]
  exact n.succ_pos

lemma ratSeq_add_four_mul_succ_abs_gt (n) : ∀ k, |ratSeq n| < |ratSeq (n + 4 * (k + 1))|
  | 0 => ratSeq_add_four_abs_gt n
  | k + 1 => (ratSeq_add_four_mul_succ_abs_gt n k).trans (ratSeq_add_four_abs_gt _)

lemma ratSeq_add_four_mul_abs_gt (hk : 0 < k) (n) : |ratSeq n| < |ratSeq (n + 4 * k)| :=
  Nat.succ_pred_eq_of_pos hk ▸ ratSeq_add_four_mul_succ_abs_gt n _

lemma ratSeq_abs_lt_of_mod_four (h : k % 4 = m % 4) (h0 : k < m) :
    |ratSeq k| < |ratSeq m| := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h0.le
  obtain ⟨n, rfl⟩ : 4 ∣ n := by
    replace h := Nat.sub_mod_eq_zero_of_mod_eq h.symm
    rwa [Nat.add_sub_cancel_left, ← Nat.dvd_iff_mod_eq_zero] at h
  refine ratSeq_add_four_mul_abs_gt ?_ k
  rwa [Nat.lt_add_right_iff_pos, Nat.mul_pos_iff_of_pos_left (Nat.succ_pos 3)] at h0

lemma ratSeq_abs_ne_of_mod_four (h : k % 4 = m % 4) (h0 : k ≠ m) :
    |ratSeq k| ≠ |ratSeq m| :=
  h0.lt_or_gt.elim (λ h1 ↦ (ratSeq_abs_lt_of_mod_four h h1).ne)
    (λ h1 ↦ (ratSeq_abs_lt_of_mod_four h.symm h1).ne.symm)



/-! ##### Parity of denominator -/

lemma ratSeq_two_mul_den (n) : ¬2 ∣ (ratSeq (2 * n)).den := by
  match n with
    | 0 => exact Nat.two_dvd_ne_zero.mpr rfl
    | 1 => exact Nat.two_dvd_ne_zero.mpr rfl
    | n + 2 => ?_
  intro h; rw [Nat.mul_add, ratSeq_add_four] at h
  replace h := h.trans (Rat.mul_den_dvd _ _)
  rw [Nat.prime_two.dvd_mul, or_iff_left (ratSeq_two_mul_den n)] at h
  replace h := h.trans (Rat.add_den_dvd _ _)
  rw [Rat.den_ofNat, Nat.one_mul, Rat.inv_natCast_den, if_neg (Nat.succ_ne_zero _)] at h
  revert h; exact Nat.two_dvd_ne_zero.mpr (Nat.mul_add_mod 2 n 1)

lemma num_odd_of_den_even {q : ℚ} (h : 2 ∣ q.den) : ¬2 ∣ q.num.natAbs :=
  λ h0 ↦ absurd (Nat.eq_one_of_dvd_coprimes q.reduced h0 h) (Nat.succ_ne_self 1)

lemma ratSeq_two_mul_add_one_den (n) : 2 ∣ (ratSeq (2 * n + 1)).den := by
  match n with
    | 0 => exact ⟨1, by rw [ratSeq, Rat.inv_ofNat_den]⟩
    | 1 => exact ⟨2, by rw [ratSeq, Rat.neg_den, Rat.inv_ofNat_den]⟩
    | n + 2 => ?_
  rw [Nat.mul_add, ratSeq_add_four, Rat.mul_den, Int.natAbs_mul]
  set q := 1 + ((2 * n + 1).succ : ℚ)⁻¹
  set r := ratSeq (2 * n + 1)
  have h : ¬2 ∣ q.num.natAbs := by
    have h := Rat.add_den_dvd (-1) q
    rw [Rat.neg_den, Rat.den_ofNat, one_mul, neg_add_cancel_left,
      Rat.inv_natCast_den, if_neg (Nat.succ_ne_zero _)] at h
    exact num_odd_of_den_even (dvd_trans ⟨n + 1, rfl⟩ h)
  have h0 : 2 ∣ r.den := ratSeq_two_mul_add_one_den n
  replace h : ¬2 ∣ q.num.natAbs * r.num.natAbs :=
    Nat.prime_two.not_dvd_mul h (num_odd_of_den_even h0)
  replace h0 : 2 ∣ q.den * r.den := h0.mul_left q.den
  set s := q.num.natAbs * r.num.natAbs
  set t := q.den * r.den
  rw [← Nat.mul_div_eq_iff_dvd.mpr (s.gcd_dvd_right t), Nat.prime_two.dvd_mul] at h0
  exact h0.resolve_left λ h1 ↦ h (h1.trans (s.gcd_dvd_left _))

lemma ratSeq_den_odd_iff : ¬2 ∣ (ratSeq n).den ↔ 2 ∣ n := by
  refine ⟨λ h ↦ ?_, λ ⟨n, h⟩ ↦ h ▸ ratSeq_two_mul_den n⟩
  rw [Nat.dvd_iff_mod_eq_zero, ← Nat.mod_two_ne_one]
  intro h0; apply h
  rw [← Nat.div_add_mod n 2, h0]
  exact ratSeq_two_mul_add_one_den (n / 2)



/-! ##### `ratSeq` is injective -/

lemma mod_two_eq_iff : i % 2 = j % 2 ↔ (2 ∣ i ↔ 2 ∣ j) := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero]
  obtain h | h : i % 2 = 0 ∨ i % 2 = 1 := i.mod_two_eq_zero_or_one
  all_goals rw [h, eq_comm]; simp

theorem ratSeq_injective : ratSeq.Injective := λ i j h ↦ by
  have h0 : (i % 4) % 2 = (j % 4) % 2 := by
    have h0 (n) : n % 4 % 2 = n % 2 := Nat.mod_mod_of_dvd n ⟨2, rfl⟩
    rw [h0, h0, mod_two_eq_iff, ← ratSeq_den_odd_iff, h, ratSeq_den_odd_iff]
  replace h0 : i % 4 = j % 4 := by
    have h1 : i % 4 < 2 ↔ j % 4 < 2 := by rw [← ratSeq_pos_iff', h, ratSeq_pos_iff']
    obtain h2 | h2 : i % 4 < 2 ∨ 2 ≤ i % 4 := lt_or_ge (i % 4) 2
    · rwa [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (h1.mp h2)] at h0
    · replace h1 : 2 ≤ j % 4 := by rwa [← Nat.not_lt, ← h1, Nat.not_lt]
      obtain ⟨c, hc⟩ : ∃ c, i % 4 = c + 2 := Nat.exists_eq_add_of_le' h2
      obtain ⟨d, hd⟩ : ∃ d, j % 4 = d + 2 := Nat.exists_eq_add_of_le' h1
      replace h2 : c < 2 := by
        rw [← Nat.add_lt_add_iff_right (k := 2), ← hc]
        exact Nat.mod_lt i (Nat.succ_pos 3)
      replace h1 : d < 2 := by
        rw [← Nat.add_lt_add_iff_right (k := 2), ← hd]
        exact Nat.mod_lt j (Nat.succ_pos 3)
      rw [hc, Nat.add_mod_right, hd, Nat.add_mod_right] at h0
      rw [hc, hd, Nat.add_left_inj, ← Nat.mod_eq_of_lt h2, h0, Nat.mod_eq_of_lt h1]
  by_contra h1; exact absurd (congrArg abs h) (ratSeq_abs_ne_of_mod_four h0 h1)





/-! ### Final solution -/

open Fin.NatCast in
/-- Final solution -/
theorem final_solution (k : ℕ) :
    ∃ (p : ℕ) (_ : p.Prime) (a : Fin (k + 4) → ZMod p), a.Injective ∧ (∀ i, a i ≠ 0) ∧
        (∀ i ≤ k, a i * a (i + 1) * a (i + 2) * a (i + 3) = i.succ) := by
  obtain ⟨M, hM, hM0⟩ : ∃ M, (∀ n : Fin (k + 4), (ratSeq n).num.natAbs < M) ∧
      (∀ n : Fin (k + 4), (ratSeq n).den < M) :=
    let f := λ n ↦ max (ratSeq n).num.natAbs (ratSeq n).den
    let X (n : Fin (k + 4)) := Extra.le_seqMax_of_le f (Nat.le_of_lt_succ n.2)
    ⟨Extra.seqMax f (k + 3) + 1, λ n ↦ Nat.lt_succ_of_le (le_of_max_le_left (X n)),
      λ n ↦ Nat.lt_succ_of_le (le_of_max_le_right (X n))⟩
  obtain ⟨p, h, hp⟩ : ∃ p, 2 * (M * M) < p ∧ p.Prime := Nat.exists_infinite_primes _
  haveI : Fact p.Prime := ⟨hp⟩
  have h' : M < p :=
    M.le_mul_self.trans_lt (h.trans_le' (Nat.le_mul_of_pos_left _ Nat.two_pos))
  ---- The denominators of `ratSeq` are non-zero mod `p` up to `k + 3`
  have h0 (i : Fin (k + 4)) : ((ratSeq i).den : ZMod p) ≠ 0 := by
    intro h1; rw [ZMod.natCast_eq_zero_iff] at h1
    exact (Nat.le_of_dvd (Rat.den_pos _) h1).not_gt ((hM0 i).trans h')
  refine ⟨p, hp, λ i ↦ (ratSeq i : ZMod p), ?_, ?_, ?_⟩
  ---- `ratSeq` is injective mod `p` up to `k + 3`
  · intro i j h1; simp only [Rat.cast_def] at h1
    rw [div_eq_div_iff (h0 _) (h0 _), ← AddGroupWithOne.intCast_ofNat, ← Int.cast_mul,
      ← AddGroupWithOne.intCast_ofNat (ratSeq i).den, ← Int.cast_mul, ← sub_eq_zero,
      ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd] at h1
    replace h1 : (ratSeq i).num * (ratSeq j).den = (ratSeq j).num * ↑(ratSeq i).den := by
      rw [← sub_eq_zero, ← Int.natAbs_eq_zero]
      refine Nat.eq_zero_of_dvd_of_lt h1 ((Int.natAbs_sub_le _ _).trans_lt (h.trans' ?_))
      simp only [Int.natAbs_natCast, Int.natAbs_mul]
      replace h1 (x y : Fin (k + 4)) : (ratSeq x).num.natAbs * (ratSeq y).den < M * M :=
        Nat.mul_lt_mul'' (hM _) (hM0 _)
      exact (Nat.add_lt_add (h1 _ _) (h1 _ _)).trans_eq (M * M).two_mul.symm
    exact Fin.eq_of_val_eq (ratSeq_injective (Rat.eq_iff_mul_eq_mul.mpr h1))
  ---- `ratSeq` only takes non-zero values mod `p` up to `k + 3`
  · intro i; simp only [Rat.cast_def, div_ne_zero_iff]
    refine ⟨λ h1 ↦ ?_, h0 i⟩
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd] at h1
    refine (Nat.le_of_dvd ?_ h1).not_gt ((hM i).trans h')
    rw [Int.natAbs_pos, Rat.num_ne_zero]; exact ratSeq_ne_zero _
  ---- The main content: `a_i a_{i + 1} a_{i + 2} a_{i + 3} = i + 1` mod `p`
  · intro i hi; have h1 {x y : Fin (k + 4)} := (Rat.cast_mul_of_ne_zero (h0 x) (h0 y)).symm
    rw [h1, mul_assoc, h1]
    replace h1 (x y : Fin (k + 4)) : ((ratSeq x * ratSeq y).den : ZMod p) ≠ 0 := by
      intro h2; rw [ZMod.natCast_eq_zero_iff] at h2
      obtain h2 | h2 := hp.dvd_mul.mp (h2.trans (Rat.mul_den_dvd _ _))
      all_goals exact h0 _ ((ZMod.natCast_eq_zero_iff _ _).mpr h2)
    rw [← Rat.cast_mul_of_ne_zero (h1 _ _) (h1 _ _)]
    simp only [Fin.val_add, Fin.val_natCast, Nat.mod_add_mod]
    replace h1 {m} (hm : m < 4) : (i + m) % (k + 4) = i + m :=
      Nat.mod_eq_of_lt (Nat.add_lt_add_of_le_of_lt hi hm)
    replace hi : i % (k + 4) = i := h1 (Nat.succ_pos 3)
    rw [hi, Fin.val_one, Fin.val_two, ← Nat.cast_ofNat (n := 3), Fin.val_natCast,
      Nat.add_mod_mod, h1 (by decide), h1 (by decide), h1 (Nat.lt_succ_self 3),
      ← mul_assoc, ratSeq_formula, Rat.cast_natCast]
