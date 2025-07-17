/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-!
# IMO 2009 C2

For each $n ∈ ℕ$, find the largest integer $k$ such that the following holds:
  there exists injective functions $a_1, a_2, a_3 : [k] → ℕ$ such that
  $a_1(i) + a_2(i) + a_3(i) = n$ for all $i ∈ [k]$.
-/

namespace IMOSL
namespace IMO2009C2

open Finset

/-! ### Extra lemmas -/

theorem choose_two_right_mul_two (n : ℕ) : n.choose 2 * 2 = n * (n - 1) := by
  match n with | 0 => rfl | n + 1 => ?_
  rw [Nat.choose_two_right, Nat.add_sub_cancel, (n + 1).mul_comm]
  exact Nat.div_mul_cancel (even_iff_two_dvd.mp n.even_mul_succ_self)

theorem exists_mem_ge_of_card {S : Finset ℕ} (hS : n + 1 ≤ S.card) : ∃ k ∈ S, n ≤ k := by
  contrapose! hS; calc
    _ ≤ (range n).card := card_le_card λ k hk ↦ mem_range.mpr (hS k hk)
    _ = n := card_range n
    _ < n + 1 := n.lt_succ_self

theorem card_choose_le_nat_sum (S : Finset ℕ) : S.card.choose 2 ≤ S.sum id := by
  ---- Induction on `|S|`, with the base case trivial
  generalize hn : S.card = n; induction' n with n n_ih generalizing S
  · exact Nat.zero_le _
  ---- Start by writing `S = {m} ∪ T` for some `m ≥ n`
  obtain ⟨m, T, rfl, hm, hm0⟩ : ∃ m T, insert m T = S ∧ n ≤ m ∧ m ∉ T := by
    obtain ⟨m, hm, hm0⟩ := exists_mem_ge_of_card hn.ge
    exact ⟨m, S.erase m, insert_erase hm, hm0, notMem_erase m S⟩
  ---- Now `C(n, 2) ≤ T.sum id` by IH and `n ≤ m` gives the desired inequality
  rw [sum_insert hm0]; refine Nat.add_le_add (n.choose_one_right.trans_le hm) (n_ih T ?_)
  rwa [card_insert_of_notMem hm0, Nat.succ_inj] at hn

theorem card_choose_le_sum_of_inj {f : ι → ℕ} (hf : f.Injective) (I : Finset ι) :
    I.card.choose 2 ≤ I.sum f := calc
  _ = (I.image f).card.choose 2 := by rw [card_image_of_injective I hf]
  _ ≤ (I.image f).sum id := card_choose_le_nat_sum (I.image f)
  _ = I.sum f := sum_image λ _ _ _ _ h ↦ hf h

/-- Consider putting this lemma into mathlib -/
theorem sum_elim_injective {f : α → γ} {g : β → γ}
    (hf : f.Injective) (hg : g.Injective) (h : ∀ a b, f a ≠ g b) :
    (Sum.elim f g).Injective
  | Sum.inl _, Sum.inl _ => λ h0 ↦ congrArg Sum.inl (hf h0)
  | Sum.inl _, Sum.inr _ => λ h0 ↦ absurd h0 (h _ _)
  | Sum.inr _, Sum.inl _ => λ h0 ↦ absurd h0.symm (h _ _)
  | Sum.inr _, Sum.inr _ => λ h0 ↦ congrArg Sum.inr (hg h0)

theorem fin_cast_sub_two_mul_injective (k) :
    (λ i : Fin k ↦ 2 * (k - 1 - i.1)).Injective := by
  match k with | 0 => exact λ x _ ↦ x.elim0 | k + 1 => ?_
  intro a b h; rw [Nat.add_sub_cancel, Nat.mul_right_inj (Nat.succ_ne_zero 1)] at h
  rw [Fin.ext_iff, ← Nat.add_right_inj (n := k - a.1),
    Nat.sub_add_cancel a.is_le, h, Nat.sub_add_cancel b.is_le]





/-! ### Start of the problem -/

structure GoodTripleFn (n : ℕ) (ι : Type*) where
  toFun : Fin 3 → ι → ℕ
  toFun_inj : ∀ j, (toFun j).Injective
  toFun_sum : ∀ i, ∑ j : Fin 3, toFun j i = n


namespace GoodTripleFn

/-- The sequence of triplets satisfying given condition -/
def ofEmbedding (f : κ ↪ ι) (X : GoodTripleFn n ι) : GoodTripleFn n κ where
  toFun := λ j k ↦ X.toFun j (f k)
  toFun_inj := λ j ↦ (X.toFun_inj j).comp f.injective
  toFun_sum := λ k ↦ X.toFun_sum (f k)

theorem nonempty_of_card_le [Fintype ι] [Fintype κ]
    (hι : Nonempty (GoodTripleFn n ι)) (h : Fintype.card κ ≤ Fintype.card ι) :
    Nonempty (GoodTripleFn n κ) :=
  (Function.Embedding.nonempty_of_card_le h).elim λ f ↦ hι.elim λ X ↦ ⟨ofEmbedding f X⟩

/-- The bound `k := |ι| ≤ 2n/3 + 1` -/
theorem card_bound [Fintype ι] (X : GoodTripleFn n ι) : Fintype.card ι ≤ 2 * n / 3 + 1 := by
  ---- Do some counting to prove that `3 k(k - 1)/2 ≤ kn`
  have h : 3 * (Fintype.card ι).choose 2 ≤ Fintype.card ι * n := calc
    _ = ∑ _ : Fin 3, (univ : Finset ι).card.choose 2 := (sum_const _).symm
    _ ≤ ∑ j : Fin 3, ∑ i : ι, X.toFun j i :=
      sum_le_sum λ j _ ↦ card_choose_le_sum_of_inj (X.toFun_inj j) _
    _ = ∑ i : ι, ∑ j : Fin 3, X.toFun j i := sum_comm
    _ = ∑ _ : ι, n := Fintype.sum_congr _ _ X.toFun_sum
    _ = Fintype.card ι * n := sum_const _
  ---- Replace the above bound by another bound
  replace h : Fintype.card ι * ((Fintype.card ι - 1) * 3) ≤ Fintype.card ι * (2 * n) := calc
    _ = 3 * (Fintype.card ι).choose 2 * 2 := by
      rw [Nat.mul_assoc, choose_two_right_mul_two, ← mul_rotate']
    _ ≤ Fintype.card ι * n * 2 := Nat.mul_le_mul_right 2 h
    _ = Fintype.card ι * (2 * n) := by rw [Nat.mul_assoc, n.mul_comm]
  ---- Solve the case `k = 0`, then solve the case `k > 0`
  obtain h0 | h0 : Fintype.card ι = 0 ∨ 0 < Fintype.card ι := Nat.eq_zero_or_pos _
  · exact h0.trans_le (Nat.zero_le _)
  · refine Nat.le_add_of_sub_le ((Nat.le_div_iff_mul_le (Nat.succ_pos 2)).mpr ?_)
    exact Nat.le_of_mul_le_mul_left h h0

def add_val (X : GoodTripleFn n ι) (j₀ : Fin 3) (v : ℕ) : GoodTripleFn (n + v) ι where
  toFun := λ j i ↦ X.toFun j i + if j = j₀ then v else 0
  toFun_inj := λ j a b h ↦ X.toFun_inj j (Nat.add_right_cancel h)
  toFun_sum := λ j ↦ by rw [sum_add_distrib, X.toFun_sum, Fintype.sum_ite_eq']

/-- Default construction for `n = 3k` -/
def default_of_0mod3 (k) : GoodTripleFn (3 * k) (Fin (k + 1) ⊕ Fin k) where
  toFun := λ j ↦ match j with
    | 0 => Sum.elim (λ i ↦ i) (λ i ↦ k + 1 + i)
    | 1 => Sum.elim (λ i ↦ k + i) (λ i ↦ i)
    | 2 => Sum.elim (λ i ↦ 2 * (k - i)) (λ i ↦ 2 * (k - 1 - i) + 1)
  toFun_inj := λ j ↦ match j with
    | 0 => sum_elim_injective Fin.val_injective
        (λ _ _ h ↦ Fin.val_injective (Nat.add_left_cancel h))
        (λ a b ↦ (Nat.lt_add_right _ a.2).ne)
    | 1 => sum_elim_injective (λ _ _ h ↦ Fin.val_injective (Nat.add_left_cancel h))
        Fin.val_injective (λ a b ↦ (Nat.lt_add_right _ b.2).ne.symm)
    | 2 => sum_elim_injective (fin_cast_sub_two_mul_injective (k + 1))
        (λ _ _ h0 ↦ fin_cast_sub_two_mul_injective k (Nat.add_right_cancel h0))
        (λ _ _ ↦ Nat.two_mul_ne_two_mul_add_one)
  toFun_sum := by
    refine Sum.rec (λ i ↦ ?_) (λ i ↦ ?_)
    ---- Case `Sum.inl`
    · rw [Fin.sum_univ_three]; simp only [Sum.elim]
      rw [Nat.add_left_comm, ← Nat.two_mul, k.add_assoc, ← Nat.mul_add,
        Nat.add_sub_cancel' i.is_le, Nat.add_comm, ← Nat.succ_mul]
    ---- Case `Sum.inr`
    · rw [Fin.sum_univ_three]; simp only [Sum.elim]
      match k with | 0 => exact i.elim0 | k + 1 => ?_
      rw [k.add_sub_cancel, Nat.mul_succ, ← Nat.add_assoc, Nat.succ_inj,
        (k + 2).add_assoc, ← Nat.two_mul, Nat.add_assoc, ← Nat.mul_add,
        Nat.add_sub_cancel' i.is_le, Nat.add_right_comm, k.add_comm, ← Nat.succ_mul]

/-- Default construction for `n = 3k + 1` -/
def default_of_1mod3 (k) : GoodTripleFn (3 * k + 1) (Fin (k + 1) ⊕ Fin k) :=
  (default_of_0mod3 k).add_val 2 1

/-- Default construction for `n = 3k + 2` -/
def default_of_2mod3 (k) : GoodTripleFn (3 * k + 2) (Fin (k + 1) ⊕ Fin (k + 1)) where
  toFun := λ j ↦ match j with
    | 0 => Sum.elim (λ i ↦ i) (λ i ↦ k + 1 + i)
    | 1 => Sum.elim (λ i ↦ k + 2 + i) (λ i ↦ i)
    | 2 => Sum.elim (λ i ↦ 2 * (k - i)) (λ i ↦ 2 * (k - i) + 1)
  toFun_inj := λ j ↦ match j with
    | 0 => sum_elim_injective Fin.val_injective
        (λ _ _ h ↦ Fin.val_injective (Nat.add_left_cancel h))
        (λ a b ↦ (Nat.lt_add_right _ a.2).ne)
    | 1 => sum_elim_injective (λ _ _ h ↦ Fin.val_injective (Nat.add_left_cancel h))
        Fin.val_injective (λ a b ↦ (Nat.lt_add_right a.1 (Nat.lt_succ_of_lt b.2)).ne.symm)
    | 2 =>
        let h := fin_cast_sub_two_mul_injective (k + 1)
        sum_elim_injective h (λ _ _ h0 ↦ h (Nat.add_right_cancel h0))
          (λ _ _ ↦ Nat.two_mul_ne_two_mul_add_one)
  toFun_sum := by
    refine Sum.rec (λ i ↦ ?_) (λ i ↦ ?_)
    ---- Case `Sum.inl`
    · rw [Fin.sum_univ_three]; simp only [Sum.elim]
      rw [i.1.add_left_comm, ← Nat.two_mul, Nat.add_assoc, ← Nat.mul_add,
        Nat.add_sub_cancel' i.is_le, Nat.add_right_comm, k.add_comm, ← Nat.succ_mul]
    ---- Case `Sum.inr`
    · rw [Fin.sum_univ_three]; simp only [Sum.elim]
      rw [← Nat.add_assoc, Nat.succ_inj, (k + 1).add_assoc, ← Nat.two_mul,
        Nat.add_assoc, ← Nat.mul_add, Nat.add_sub_cancel' i.is_le,
        Nat.add_right_comm, k.add_comm, ← Nat.succ_mul]

theorem nonempty_of_le_bound [Fintype ι] (h : Fintype.card ι ≤ 2 * n / 3 + 1) :
    Nonempty (GoodTripleFn n ι) := by
  have three_pos : 0 < 3 := Nat.succ_pos 2
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 3 ∧ n = 3 * k + r :=
    ⟨n / 3, n % 3, Nat.mod_lt n three_pos, (n.div_add_mod 3).symm⟩
  rw [Nat.lt_succ_iff, Nat.le_succ_iff, Nat.le_one_iff_eq_zero_or_eq_one] at hr
  have fin_sum_fin_card (a b) : Fintype.card (Fin a ⊕ Fin b) = a + b := by
    rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  rcases hr with (rfl | rfl) | rfl
  ---- Case 1: `n = 3k`
  · refine nonempty_of_card_le ⟨default_of_0mod3 k⟩ (h.trans_eq ?_)
    rw [fin_sum_fin_card, k.add_right_comm, ← k.two_mul, (3 * k).add_zero,
      Nat.mul_left_comm, Nat.mul_div_cancel_left _ three_pos]
  ---- Case 2: `n = 3k + 1`
  · refine nonempty_of_card_le ⟨default_of_1mod3 k⟩ (h.trans_eq ?_)
    rw [fin_sum_fin_card, k.add_right_comm, ← k.two_mul,
      Nat.mul_succ, Nat.mul_left_comm, Nat.mul_add_div three_pos]
  ---- Case 3: `n = 3k + 2`
  · refine nonempty_of_card_le ⟨default_of_2mod3 k⟩ (h.trans_eq ?_)
    rw [fin_sum_fin_card, ← Nat.two_mul, Nat.mul_add, Nat.mul_left_comm,
      Nat.mul_add_div three_pos, Nat.add_assoc, Nat.mul_succ 2 k]

end GoodTripleFn





/-! ### Final solution -/

/-- Final solution -/
theorem final_solution [Fintype ι] :
    Nonempty (GoodTripleFn n ι) ↔ Fintype.card ι ≤ 2 * n / 3 + 1 :=
  ⟨λ h ↦ h.elim λ X ↦ X.card_bound, GoodTripleFn.nonempty_of_le_bound⟩
