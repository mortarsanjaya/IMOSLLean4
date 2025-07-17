/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Set.Operations
import Mathlib.Data.Nat.Init

/-!
# IMO 2023 N6

A sequence $(a_n)_{n ≥ 0}$ is called *kawaii* if $a_0 = 0$, $a_1 = 1$, and for any $n ∈ ℕ$,
$$ a_{n + 2} + 2 a_n = 3 a_{n + 1} \text{ or } a_{n + 2} + 3 a_n = 4 a_{n + 1}. $$
A non-negative integer $m$ is said to be *kawaii* if it belongs to some kawaii sequence.

Let $m ∈ ℕ$ such that both $m$ and $m + 1$ are kawaii.
Prove that $3 ∣ m$ and $m/3$ belongs to a kawaii sequence.
-/

namespace IMOSL
namespace IMO2023N6

/-! ### Generalized kawaii sequence -/

@[ext] structure KawaiiSequence (S : Set ℕ) where
  a : ℕ → ℕ
  a_zero : a 0 = 0
  a_one : a 1 = 1
  a_step : ∀ n, ∃ c : S, a (n + 2) + c * a n = (c + 1) * a (n + 1)


namespace KawaiiSequence

variable (X : KawaiiSequence S)
include X

lemma a_le_succ : ∀ n, X.a n ≤ X.a (n + 1) := by
  refine Nat.rec ?_ λ n hn ↦ ?_
  · rw [X.a_zero, X.a_one]; exact Nat.zero_le 1
  · obtain ⟨c, h⟩ := X.a_step n
    rw [← Nat.add_le_add_iff_right (n := c * X.a n), h, Nat.succ_mul, Nat.add_comm]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hn) _

lemma a_monotone {m} : ∀ {n}, m ≤ n → X.a m ≤ X.a n :=
  Nat.le_induction (Nat.le_refl _) (λ n _ hn ↦ Nat.le_trans hn (X.a_le_succ n)) _

lemma a_succ_pos (n) : 0 < X.a (n + 1) := by
  have h := X.a_monotone n.succ_pos; rwa [X.a_one] at h

lemma one_le_a_succ (n) : 1 ≤ X.a (n + 1) :=
  X.a_succ_pos n

lemma a_sub_one_step (n) :
    ∃ c : S, (X.a (n + 3) - 1) + c.1 * (X.a (n + 1) - 1)
      = (c.1 + 1) * (X.a (n + 2) - 1) := by
  obtain ⟨c, hc⟩ := X.a_step (n + 1)
  refine ⟨c, (c.1 + 1).mul_sub_one _ ▸ Nat.eq_sub_of_add_eq ?_⟩
  rw [c.1.add_comm, Nat.add_add_add_comm, Nat.sub_add_cancel (X.one_le_a_succ _),
    ← Nat.mul_add_one, Nat.sub_add_cancel (X.one_le_a_succ _), hc, Nat.add_comm 1]

lemma a_two_pred_mem : X.a 2 - 1 ∈ S := by
  obtain ⟨c, h⟩ : ∃ c : S, X.a 2 + c * X.a 0 = (c + 1) * X.a 1 := X.a_step 0
  rw [X.a_zero, X.a_one, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at h
  rw [h, Nat.add_sub_cancel]; exact c.2



/-! ##### Kawaii sequence from a member -/

def of_mem (c : S) : KawaiiSequence S where
  a := Nat.rec 0 λ _ x ↦ c * x + 1
  a_zero := rfl
  a_one := rfl
  a_step := λ n ↦ ⟨c, by rw [Nat.add_right_comm, ← Nat.mul_add, Nat.add_right_comm,
    ← Nat.succ_mul, Nat.mul_succ, Nat.mul_left_comm, Nat.add_assoc, ← Nat.mul_succ]⟩

omit X in
lemma of_mem_a_succ (c : S) (n) : (of_mem c).a (n + 1) = c * (of_mem c).a n + 1 := rfl



/-! ##### Tail of a kawaii sequence; the number `a_2 - 1` -/

def tail_coeff : S := ⟨X.a 2 - 1, X.a_two_pred_mem⟩

lemma a_two : X.a 2 = X.tail_coeff + 1 :=
  (Nat.sub_add_cancel (X.one_le_a_succ 1)).symm

lemma tail_coeff_dvd_a_sub_one : ∀ n, X.tail_coeff.1 ∣ X.a n - 1
  | 0 => X.a_zero.symm ▸ Nat.dvd_zero _
  | 1 => X.a_one.symm ▸ Nat.dvd_zero _
  | 2 => Nat.dvd_refl _
  | n + 3 => by
      obtain ⟨c, hc⟩ := X.a_sub_one_step n
      have h : X.tail_coeff.1 ∣ c.1 * (X.a (n + 1) - 1) :=
        Nat.dvd_trans (tail_coeff_dvd_a_sub_one (n + 1)) (Nat.dvd_mul_left _ _)
      have h0 : X.tail_coeff.1 ∣ (c.1 + 1) * (X.a (n + 2) - 1) :=
        Nat.dvd_trans (tail_coeff_dvd_a_sub_one (n + 2)) (Nat.dvd_mul_left _ _)
      rwa [← hc, ← Nat.dvd_add_iff_left h] at h0

lemma a_succ_of_tail_coeff_eq_zero (h : X.tail_coeff.1 = 0) (n) : X.a (n + 1) = 1 :=
  Nat.eq_add_of_sub_eq (X.one_le_a_succ n)
    (Nat.zero_dvd.mp (h ▸ X.tail_coeff_dvd_a_sub_one _))



/-! ##### Dropping and appending tail on a kawaii sequence -/

def drop_tail_of_pos (h : 0 < X.tail_coeff.1) : KawaiiSequence S where
  a := λ n ↦ (X.a (n + 1) - 1) / X.tail_coeff
  a_zero := by simp only [X.a_one]; exact Nat.zero_div _
  a_one := by simp only [X.a_two]; exact Nat.div_self h
  a_step := λ n ↦ by
    obtain ⟨c, hc⟩ := X.a_sub_one_step n
    refine ⟨c, ?_⟩
    obtain ⟨k, hk⟩ := X.tail_coeff_dvd_a_sub_one (n + 1)
    obtain ⟨l, hl⟩ := X.tail_coeff_dvd_a_sub_one (n + 2)
    obtain ⟨m, hm⟩ := X.tail_coeff_dvd_a_sub_one (n + 3)
    rw [hk, hl, hm]; simp only [Nat.mul_div_cancel_left _ h]
    rw [hk, hl, hm, Nat.mul_left_comm, ← Nat.mul_add, Nat.mul_left_comm] at hc
    exact Nat.eq_of_mul_eq_mul_left h hc

lemma a_succ_drop_tail_formula_of_pos (h : 0 < X.tail_coeff.1) (n) :
    X.a (n + 1) = X.tail_coeff * (X.drop_tail_of_pos h).a n + 1 :=
  (Nat.sub_add_cancel (X.one_le_a_succ n)).symm.trans
    (congrArg Nat.succ (Nat.mul_div_cancel' (X.tail_coeff_dvd_a_sub_one _)).symm)

def drop_tail : KawaiiSequence S :=
  dite (0 < X.tail_coeff.1) X.drop_tail_of_pos
    λ h ↦ of_mem ⟨0, Nat.eq_zero_of_not_pos h ▸ X.tail_coeff.2⟩

lemma drop_tail_eq_of_pos (h : 0 < X.tail_coeff.1) : X.drop_tail = X.drop_tail_of_pos h :=
  dif_pos h

lemma drop_tail_eq_of_zero (h : X.tail_coeff.1 = 0) :
    X.drop_tail = of_mem ⟨0, h ▸ X.tail_coeff.2⟩ :=
  dif_neg (Nat.not_lt_of_le (Nat.le_zero.mpr h))

lemma a_succ_drop_tail_formula (n) : X.a (n + 1) = X.tail_coeff * X.drop_tail.a n + 1 := by
  obtain h | h : X.tail_coeff.1 = 0 ∨ 0 < X.tail_coeff.1 := X.tail_coeff.1.eq_zero_or_pos
  · rw [h, Nat.zero_mul, X.a_succ_of_tail_coeff_eq_zero h]
  · rw [X.drop_tail_eq_of_pos h, X.a_succ_drop_tail_formula_of_pos h]

def append_tail (c : S) : KawaiiSequence S where
  a := λ n ↦ match n with | 0 => 0 | n + 1 => c * X.a n + 1
  a_zero := rfl
  a_one := by show _ * X.a 0 + 1 = 1; rw [X.a_zero, Nat.mul_zero]
  a_step := λ n ↦ match n with
    | 0 => ⟨c, by simp only; rw [X.a_one, X.a_zero, c.1.mul_zero]; rfl⟩
    | n + 1 => by
        obtain ⟨d, hd⟩ := X.a_step n
        refine ⟨d, ?_⟩; simp only
        rw [Nat.mul_succ, Nat.add_add_add_comm, ← Nat.mul_left_comm,
          ← Nat.mul_add, hd, Nat.add_comm 1, Nat.mul_left_comm, Nat.mul_succ]

lemma tail_coeff_append_tail (c : S) : (X.append_tail c).tail_coeff = c :=
  Subtype.ext ((congrArg (c.1 * ·) X.a_one).trans c.1.mul_one)

lemma append_tail_a_succ (c : S) (n) : (X.append_tail c).a (n + 1) = c * X.a n + 1 := rfl

end KawaiiSequence





/-! ### Generalized kawaii integers (inductive) -/

inductive isKawaii : Set ℕ → ℕ → Prop
  | zero (S) : isKawaii S 0
  | rec_mul_succ {S : Set ℕ} (c : S) (n) (h : isKawaii S n) : isKawaii S (c * n).succ

protected theorem isKawaii.induction {S : Set ℕ} {P : ℕ → Prop}
    (h : P 0) (h0 : ∀ (c : S) (n : ℕ), P n → P (c * n).succ) :
    ∀ n, isKawaii S n → P n :=
  λ _ h1 ↦ h1.recOn h λ c n _ ↦ h0 c n

theorem isKawaii.one {S : Set ℕ} (hS : S.Nonempty) : isKawaii S 1 := by
  rcases hS with ⟨c, hc⟩
  have h := (isKawaii.zero S).rec_mul_succ ⟨c, hc⟩
  rwa [Nat.mul_zero] at h

theorem isKawaii.eq_zero_or_rec_mul_succ :
    ∀ k, isKawaii S k → k = 0 ∨ ∃ (c : S) (n : ℕ), isKawaii S n ∧ k = c * n + 1 := by
  refine isKawaii.induction (Or.inl rfl) λ c k h ↦ Or.inr ?_
  rcases h with rfl | ⟨d, m, hm, rfl⟩
  exacts [⟨c, 0, isKawaii.zero S, rfl⟩, ⟨c, d * m + 1, hm.rec_mul_succ d, rfl⟩]

theorem isKawaii.succ_imp (h : isKawaii S (k + 1)) :
    ∃ (c : S) (n : ℕ), isKawaii S n ∧ k = c * n := by
  obtain ⟨c, n, h0, h1⟩ := (h.eq_zero_or_rec_mul_succ _).resolve_left k.succ_ne_zero
  exact ⟨c, n, h0, Nat.succ_inj.mp h1⟩

theorem KawaiiSequence.a_isKawaii : ∀ (k : ℕ) (X : KawaiiSequence S), isKawaii S (X.a k) :=
  Nat.rec (λ X ↦ X.a_zero.symm ▸ isKawaii.zero S)
    λ n hn X ↦ X.a_succ_drop_tail_formula n ▸ (hn X.drop_tail).rec_mul_succ _ _

theorem isKawaii.exists_mem_KawaiiSequence (hS : S.Nonempty) :
    ∀ n, isKawaii S n → ∃ (X : KawaiiSequence S) (k : ℕ), n = X.a k := by
  refine isKawaii.induction ?_ ?_
  · rcases hS with ⟨c, hc⟩; exact ⟨KawaiiSequence.of_mem ⟨c, hc⟩, 0, rfl⟩
  · rintro d _ ⟨X, k, rfl⟩; exact ⟨X.append_tail d, k + 1, rfl⟩

theorem isKawaii_iff_mem_KawaiiSequence (hS : S.Nonempty) :
    isKawaii S n ↔ ∃ (X : KawaiiSequence S) (k : ℕ), n = X.a k := by
  refine ⟨isKawaii.exists_mem_KawaiiSequence hS _, ?_⟩
  rintro ⟨X, k, rfl⟩; exact X.a_isKawaii k





/-! ### Kawaii integers, `S = {2, 3}` version -/

theorem isKawaii23_mod_three : ∀ m, isKawaii {2, 3} m → 3 ∣ m ∨ m % 3 = 1 := by
  refine isKawaii.induction (Or.inl ⟨0, rfl⟩) λ c n hn ↦ ?_
  rcases c with ⟨c, rfl | rfl⟩
  ---- Case 1: `c = 2`
  · refine (hn.imp ?_ ?_).symm
    · rintro ⟨k, rfl⟩; rw [Nat.mul_left_comm, Nat.succ_eq_add_one, Nat.mul_add_mod]
    · intro hn0; refine ⟨2 * (n / 3) + 1, ?_⟩
      rw [Nat.mul_succ, Nat.succ_inj, Nat.mul_left_comm,
        ← Nat.mul_add_one, ← hn0, n.div_add_mod]
  ---- Case 2: `c = 3`
  · right; rw [Nat.succ_eq_add_one, Nat.mul_add_mod, Nat.one_mod]

theorem isKawaii23_self_and_succ (hm : isKawaii {2, 3} m) (hm0 : isKawaii {2, 3} (m + 1)) :
    ∃ k, isKawaii {2, 3} k ∧ m = 3 * k := by
  ---- First show that `m = 3k` for some `k : ℕ`, and reduce to showing that `k` is kawaii
  obtain ⟨k, rfl⟩ : 3 ∣ m := by
    refine (isKawaii23_mod_three _ hm).resolve_right λ h ↦ ?_
    replace h0 : (m + 1) % 3 = 2 := by rw [← Nat.mod_add_mod, h]
    apply absurd (isKawaii23_mod_three _ hm0)
    rw [Nat.dvd_iff_mod_eq_zero, h0]; decide
  refine ⟨k, ?_, rfl⟩
  ---- Next, resolve the case `k = 0`, and show that otherwise, `3k = 2n + 1` for some `n`
  have three_ne_zero : 3 ≠ 0 := Nat.succ_ne_zero 2
  obtain h | h : 3 * k = 0 ∨ _ := hm.eq_zero_or_rec_mul_succ _
  · exact (Nat.mul_eq_zero.mp h).resolve_left three_ne_zero ▸ isKawaii.zero _
  rcases h with ⟨⟨c, hc⟩, n, -, h⟩
  obtain rfl : c = 2 := by
    refine hc.resolve_right λ (hc : c = 3) ↦ absurd (congrArg (· % 3) h) ?_
    simp only [hc, Nat.mul_mod_right, Nat.mul_add_mod]; exact Nat.zero_ne_one
  ---- Next, `3k + 1` is of form `2m + 1` or `3m + 1` for some `m` kawaii
  simp only at h; clear hc
  obtain ⟨⟨_, rfl | rfl⟩, m, hm, h0⟩ := hm0.succ_imp
  ---- Case `3k + 1 = 2m + 1`
  · apply absurd (congrArg (· % 2) (h.symm.trans h0))
    simp only [Nat.mul_mod_right, Nat.mul_add_mod]; exact Nat.one_ne_zero
  ---- Case `3k + 1 = 3m + 1`
  · rwa [(Nat.mul_right_inj three_ne_zero).mp h0]





/-! ### Final solution -/

/-- Final solution -/
theorem final_solution (hn : ∃ (X : KawaiiSequence {2, 3}) (k : ℕ), n = X.a k)
    (hn0 : ∃ (X : KawaiiSequence {2, 3}) (k : ℕ), n + 1 = X.a k) :
    ∃ m, (∃ (X : KawaiiSequence {2, 3}) (k : ℕ), m = X.a k) ∧ n = 3 * m := by
  have h : ({2, 3} : Set ℕ).Nonempty := ⟨2, Or.inl rfl⟩
  simp only [← isKawaii_iff_mem_KawaiiSequence h] at hn hn0 ⊢
  exact isKawaii23_self_and_succ hn hn0
