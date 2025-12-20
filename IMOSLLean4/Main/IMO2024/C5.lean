/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Data.Int.SuccPred
import Mathlib.Algebra.Order.Interval.Finset.Basic

/-!
# IMO 2024 C5

Let $S$ be a finite set of integers.
Initially, each element of $S$ is written on the board, once.
Two players take a turn, where the current player choose a pair of integers $(k, n)$,
  where $k ≥ 0$ and $n$ is one of the integers remaining on the board, and then
  erases every integer $s$ on the board such that $s ≡ n (mod 2^k)$.
The player who cannot make a move **wins**.

Determine all positive integers $N$ such that the first player wins if $S = \{1, 2, …, N\}$.

### Answer

The first player wins if and only if $N = t 4^k$ where either
  $t = 2$ or $t$ is an odd number greater than $1$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2024SL.pdf).
The merging operation uses $2S ∪ (2T + 1)$ instead of $(2S - 1) ∪ 2T$.
Throughout the file, we use $[N]$ to denote $\{0, 1, …, N - 1\}$.
-/

namespace IMOSL
namespace IMO2024C5

open Finset

/-! ### Extra lemmas -/

/-- We have `a + d ≡ b + d (mod c) ↔ a ≡ b (mod c)`. -/
theorem Int_add_modeq_right_iff : a + d ≡ b + d [ZMOD c] ↔ a ≡ b [ZMOD c] :=
  ⟨λ h ↦ h.add_right_cancel', λ h ↦ h.add_right d⟩


section

variable (S : Finset ℤ) (m D)

/-- Removing elements `≡ 2m + c (mod 2D)` to `2S + c` yields `2T + c`,
  where `T` is obtained by removing elements `≡ m (mod D)` from `S`. -/
theorem filter_image_two_mul_translate (c) :
    {s ∈ S.image (2 * · + c) | ¬s ≡ 2 * m + c [ZMOD D * 2]}
      = {s ∈ S | ¬s ≡ m [ZMOD D]}.image (2 * · + c) := by
  suffices ∀ x, 2 * x + c ≡ 2 * m + c [ZMOD D * 2] ↔ x ≡ m [ZMOD D]
    by simp_rw [filter_image, this]
  intro x; rw [Int_add_modeq_right_iff, Int.mul_comm D,
    Int.ModEq.mul_left_cancel_iff' (by decide : (2 : ℤ) ≠ 0)]

/-- If `a ≢ b (mod 2)`, then removing elements `≡ 2m + b (mod 2D)`
  does nothing to `2S + a`. -/
theorem filter_image_two_mul_translate_of_mod_two_ne {a b : ℤ} (hab : a % 2 ≠ b % 2) :
    {s ∈ S.image (2 * · + a) | ¬s ≡ 2 * m + b [ZMOD D * 2]} = S.image (2 * · + a) := by
  rw [filter_eq_self, forall_mem_image]
  rintro x - h
  replace h : (2 * x + a) % 2 = (2 * m + b) % 2 := h.of_mul_left D
  iterate 2 rw [Int.mul_add_emod_self_left] at h
  exact hab h

end





/-! ### Start of the problem -/

/-- A finite subset `S ⊆ ℤ` is called *winning* if the first player would win the game
  when the board starts with `S`. -/
@[irreducible] def isWinning : Finset ℤ → Prop :=
  Finset.strongInduction λ S hS ↦ S = ∅ ∨ ∃ n, ∃ (hnS : n ∈ S), ∃ k : ℕ,
    ¬hS {s ∈ S | ¬s ≡ n [ZMOD 2 ^ k]} (filter_ssubset.mpr ⟨n, hnS, not_not.mpr rfl⟩)


namespace isWinning

/-- The empty set is winning. -/
theorem empty : isWinning ∅ := by
  rw [isWinning, strongInduction_eq]
  exact Or.inl rfl

/-- An inductive criterion for a non-empty set to be winning. -/
theorem iff_of_nonempty {S : Finset ℤ} (hS : S.Nonempty) :
    isWinning S ↔ ∃ n ∈ S, ∃ k : ℕ, ¬isWinning {s ∈ S | ¬s ≡ n [ZMOD 2 ^ k]} := by
  rw [isWinning, strongInduction_eq, or_iff_right (nonempty_iff_ne_empty.mp hS)]
  simp only [exists_prop]

/-- If there is a move transforming `S` into a losing set, then `S` is winning. -/
theorem of_move (hnS : n ∈ S) (hnS0 : ¬isWinning {s ∈ S | ¬s ≡ n [ZMOD 2 ^ k]}) :
    isWinning S :=
  (iff_of_nonempty ⟨n, hnS⟩).mpr ⟨n, hnS, k, hnS0⟩

/-- A singleton always loses. -/
theorem not_singleton (n) : ¬isWinning {n} := by
  simp_rw [iff_of_nonempty (singleton_nonempty n), mem_singleton]
  rintro ⟨n, rfl, k, h⟩
  have h0 : {s ∈ ({n} : Finset ℤ) | ¬s ≡ n [ZMOD 2 ^ k]} = ∅ :=
    filter_eq_empty_iff.mpr λ m hm ↦ by rw [not_not, mem_singleton.mp hm]
  exact h (h0 ▸ empty)

/-- Adding one element to a losing set creates a winning set. -/
theorem insert_of_not_isWinning (hS : ¬isWinning S) (hnS : n ∉ S) :
    isWinning (insert n S) := by
  ---- Find `e` such that `n` and all elements of `S` are less than `2^e`.
  obtain ⟨e, hen, heS⟩ : ∃ e, n.natAbs < 2 ^ e ∧ ∀ x ∈ S, x.natAbs < 2 ^ e := by
    let e := (insert n S).sup' (S.insert_nonempty n) Int.natAbs
    exact ⟨e, (forall_mem_insert n S (λ x ↦ x.natAbs < 2 ^ e)).mp
      λ x hx ↦ (le_sup' Int.natAbs hx).trans_lt Nat.lt_two_pow_self⟩
  ---- Then pick the move `(k = e + 1, n)`.
  refine of_move (mem_insert_self n S) (k := e + 1) ?_
  suffices {s ∈ insert n S | ¬s ≡ n [ZMOD 2 ^ (e + 1)]} = S from this.symm ▸ hS
  ---- It remains to show that we deleted `n` and nothing else.
  rw [filter_insert, if_neg (not_not.mpr (Int.ModEq.refl _)), filter_eq_self]
  ---- That is, it remains to show that `x ≢ n (mod 2^k)` for all `x ∈ S`.
  intro x hxS h0
  replace h0 : ((2 : ℤ) ^ (e + 1)).natAbs ≤ (x - n).natAbs :=
    Int.natAbs_le_of_dvd_ne_zero h0.symm.dvd (sub_ne_zero_of_ne λ h1 ↦ hnS (h1 ▸ hxS))
  have h1 : (x - n).natAbs < ((2 : ℤ) ^ (e + 1)).natAbs := calc
    _ ≤ x.natAbs + n.natAbs := Int.natAbs_sub_le x n
    _ < 2 ^ e + 2 ^ e := Nat.add_lt_add (heS x hxS) hen
    _ = ((2 : ℤ) ^ (e + 1)).natAbs := by rw [Int.natAbs_pow, ← Nat.mul_two]; rfl
  exact h0.not_gt h1

/-- `2S + d` is winning if and only if `S` is winning. -/
theorem two_mul_translate_iff : isWinning (S.image (2 * · + d)) ↔ isWinning S := by
  ---- Strong induction on `S`, where the empty case is trivial.
  induction S using Finset.strongInduction with | H S hS => ?_
  obtain rfl | hS0 : S = ∅ ∨ S.Nonempty := S.eq_empty_or_nonempty
  · exact ⟨λ _ ↦ isWinning.empty, λ _ ↦ empty⟩
  /- For induction step, the move `(k, 2n + d)` wins for `2S + d`
    if and only if `(max{k - 1, 0}, n)` wins for `S`. -/
  rw [iff_of_nonempty (hS0.image _), iff_of_nonempty hS0, exists_mem_image]
  refine exists_congr λ n ↦ and_congr_right λ hnS ↦ ?_
  conv_lhs =>
    congr; ext k; rw [filter_image, hS _ (filter_ssubset.mpr ⟨n, hnS, not_not.mpr rfl⟩)]
    simp only [Int_add_modeq_right_iff]
  ---- The LHS has been manipulated: choosing `n` in code ↔ choosing `2n` as a move.
  have X : (2 : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr (Nat.succ_ne_zero 1)
  refine ⟨?_, ?_⟩
  ---- If `(k, 2n + d)` wins for `2S + d`, then `(max{k - 1, 0}, n)` wins for `S`.
  · rintro ⟨k, h⟩
    refine ⟨k - 1, ?_⟩
    cases k with
    | zero => simpa only [Nat.zero_sub, Int.pow_zero, Int.modEq_one] using h
    | succ k => simpa only [Nat.add_sub_cancel, Int.pow_succ',
        Int.ModEq.mul_left_cancel_iff' X] using h
  --- If `(k, n)` wins for `S`, then `(k + 1, 2n + d)` wins for `2S + d`.
  · rintro ⟨k, h⟩
    refine ⟨k + 1, ?_⟩
    simpa only [Int.pow_succ', Int.ModEq.mul_left_cancel_iff' X]

/-- `2S` is winning if and only if `S` is winning. -/
theorem two_mul_iff : isWinning (S.image (2 * ·)) ↔ isWinning S := by
  simpa only [add_zero] using two_mul_translate_iff (d := 0)

/-- `S + d` is winning if and only if `S` is winning. -/
theorem translate_iff : isWinning (S.image (· + d)) ↔ isWinning S := by
  have h : (2 * ·) ∘ (· + d) = λ x ↦ 2 * x + 2 * d := funext λ x ↦ Int.mul_add 2 x d
  rw [← two_mul_iff, image_image, h, two_mul_translate_iff]


section

variable {a b : ℤ} (hab : a % 2 ≠ b % 2) {S T : Finset ℤ}
include hab

/-- If `a ≢ b (mod 2)`, `S` is losing, and `T ≠ ∅`, then `(2S + a) ∪ (2T + b)` is winning. -/
theorem binary_merge_of_left_not_isWinning (hS : ¬isWinning S) (hT : T.Nonempty) :
    isWinning (S.image (2 * · + a) ∪ T.image (2 * · + b)) := by
  ---- If `t ∈ T`, choose `(1, 2t + b)`, reducing `(2S + a) ∪ (2T + b)` to `2S + a`.
  rcases hT with ⟨t, ht⟩
  refine of_move (n := 2 * t + b) (k := 1) (mem_union_right _ (mem_image_of_mem _ ht)) ?_
  simp_rw [filter_union, filter_image, Int.ModEq,
    Int.pow_one, Int.mul_add_emod_self_left, filter_const]
  rwa [if_pos hab, if_neg (not_not.mpr trivial),
    image_empty, union_empty, two_mul_translate_iff]

/-- If `a ≢ b (mod 2)`, `S ≠ ∅`, and `T` is losing, then `(2S + a) ∪ (2T + b)` is winning. -/
theorem binary_merge_of_right_not_isWinning (hS : S.Nonempty) (hT : ¬isWinning T) :
    isWinning (S.image (2 * · + a) ∪ T.image (2 * · + b)) := by
  rw [union_comm]; exact binary_merge_of_left_not_isWinning hab.symm hT hS


set_option trace.profiler true
set_option trace.profiler.threshold 100

/-- If `a ≢ b (mod 2)` and `S ≠ ∅` is winning, then `(2S + a) ∪ (2S + b)` is losing. -/
theorem binary_merge_self_not_isWinning (hS : isWinning S) (hS0 : S.Nonempty) :
    ¬isWinning (S.image (2 * · + a) ∪ S.image (2 * · + b)) := by
  ---- Strong induction on `S`.
  induction S using Finset.strongInduction with | H S S_ih => ?_
  ---- Pick any move `(k, n)`, and WLOG assume `n = 2m + a` for some `m ∈ S`.
  rw [iff_of_nonempty (union_nonempty.mpr (Or.inl (hS0.image _))), not_exists]
  intro n; rw [not_and, mem_union, mem_image, mem_image, ← not_forall, not_not]
  intro hn k; wlog hn' : ∃ s ∈ S, 2 * s + a = n generalizing a b
  · have h (T : Finset ℤ) : T.image (2 * · + a) ∪ T.image (2 * · + b)
        = T.image (2 * · + b) ∪ T.image (2 * · + a) := union_comm _ _
    exact h S ▸ this hab.symm (λ t ↦ h t ▸ S_ih t) hn.symm (hn.resolve_left hn')
  clear hn; rcases hn' with ⟨m, hmS, rfl⟩
  ---- If `k = 0`, then we are done, so assume `k = j + 1 > 0`.
  obtain rfl | ⟨j, rfl⟩ : k = 0 ∨ ∃ j, k = j + 1 :=
    (Nat.eq_zero_or_eq_succ_pred k).imp_right λ h ↦ ⟨k.pred, h⟩
  · rw [Int.pow_zero, filter_eq_empty_iff.mpr λ x _ ↦ not_not.mpr Int.modEq_one]
    exact empty
  ---- Let `T = {s ∈ S | s ≢ m (mod 2^j)}`. Then the filtered set is `(2T + a) ∪ (2S + b)`.
  rw [filter_union, Int.pow_succ, filter_image_two_mul_translate,
    filter_image_two_mul_translate_of_mod_two_ne _ _ _ hab.symm]
  ---- If `T = ∅` then we are done; `2S + b` is winning.
  set T : Finset ℤ := {s ∈ S | ¬s ≡ m [ZMOD 2 ^ j]}
  obtain hT | hT : T = ∅ ∨ T.Nonempty := eq_empty_or_nonempty _
  · rwa [hT, image_empty, empty_union, two_mul_translate_iff]
  ---- If `T ≠ ∅` is losing, then `(1, 2m + b)` steals the game.
  have hmS0 : 2 * m + b ∈ T.image (2 * · + a) ∪ S.image (2 * · + b) :=
    mem_union_right _ (mem_image_of_mem _ hmS)
  obtain hT0 | hT0 : ¬isWinning T ∨ isWinning T := em' _
  · refine of_move (n := 2 * m + b) hmS0 (k := 1) ?_
    rwa [filter_union, Int.pow_succ, filter_image_two_mul_translate,
      filter_image_two_mul_translate_of_mod_two_ne _ _ _ hab, Int.pow_zero,
      filter_eq_empty_iff.mpr λ _ _ ↦ not_not.mpr Int.modEq_one,
      image_empty, union_empty, two_mul_translate_iff]
  ---- If `T ≠ ∅` is winning then `(j + 1, 2m + b)` wins the game.
  · refine of_move (n := 2 * m + b) hmS0 (k := j + 1) ?_
    rw [filter_union, Int.pow_succ, filter_image_two_mul_translate,
      filter_image_two_mul_translate_of_mod_two_ne _ _ _ hab]
    exact S_ih _ (filter_ssubset.mpr ⟨m, hmS, not_not.mpr rfl⟩) hT0 hT

/-- If `a ≢ b (mod 2)` and `S ≠ ∅`, then `2S ∪ (2S + 1)` is losing iff `S` is winning. -/
theorem binary_merge_self_not_isWinning_iff (hS : S.Nonempty) :
    ¬isWinning (S.image (2 * · + a) ∪ S.image (2 * · + b)) ↔ isWinning S :=
  ⟨λ hS0 ↦ by_contra λ hS1 ↦ hS0 (binary_merge_of_left_not_isWinning hab hS1 hS),
  λ hS0 ↦ binary_merge_self_not_isWinning hab hS0 hS⟩

end

end isWinning





/-! ### Specialization to the case `S = [N]` -/

/-- The binary decomposition `[2N] = 2[N] ∪ (2[N] + 1)`. -/
theorem binary_merge_Ico_zero_two_mul (N : ℕ) :
    Ico 0 ((2 * N : ℕ) : ℤ) =
      (Ico 0 (N : ℤ)).image (2 * · + 0) ∪ (Ico 0 (N : ℤ)).image (2 * · + 1) := by
  ext n; rw [mem_Ico, mem_union, mem_image, mem_image, ← exists_or]
  conv_rhs => congr; ext a; rw [← and_or_left, mem_Ico]
  have X : (2 : ℤ) > 0 := by decide
  refine ⟨?_, ?_⟩
  ---- If `0 ≤ n < 2N`, then there exists `0 ≤ a < N` such that `2a = n` or `2a + 1 = n`.
  · rintro ⟨hn, hnN⟩
    refine ⟨n / 2, ⟨Int.ediv_nonneg hn X.le,
      Int.ediv_lt_of_lt_mul X (Int.mul_comm _ _ ▸ hnN)⟩, ?_⟩
    rw [← eq_sub_iff_add_eq', ← eq_sub_iff_add_eq', ← Int.emod_def]
    exact (Int.emod_two_eq n).imp Eq.symm Eq.symm
  ---- If `n` equals `2a` or `2a + 1` for some `0 ≤ a < N`, then `0 ≤ n < 2N`.
  · rintro ⟨a, ⟨ha, haN⟩, h⟩
    have h2a : 0 ≤ 2 * a := Int.mul_nonneg X.le ha
    rcases h with rfl | rfl
    · rw [Int.add_zero]; exact ⟨h2a, Int.mul_lt_mul_of_pos_left haN X⟩
    · refine ⟨Int.add_nonneg h2a Int.one_nonneg, ?_⟩
      calc 2 * a + 1
        _ < 2 * a + 1 + 1 := Int.lt_add_of_pos_right _ Int.one_pos
        _ = 2 * (a + 1) := by rw [Int.mul_add, Int.add_assoc, Int.two_mul 1]
        _ ≤ 2 * N := Int.mul_le_mul_of_nonneg_left (Int.add_one_le_of_lt haN) X.le

/-- The binary decomposition `[2N + 1]` as `2[N + 1] ∪ (2[N] + 1)`. -/
theorem binary_merge_Ico_zero_two_mul_add_one (N : ℕ) :
    Ico 0 ((2 * N + 1 : ℕ) : ℤ) =
      (Ico 0 ((N + 1 : ℕ) : ℤ)).image (2 * · + 0) ∪ (Ico 0 (N : ℤ)).image (2 * · + 1) := by
  iterate 2 rw [Int.natCast_succ, ← insert_Ico_right_eq_Ico_add_one (Int.natCast_nonneg _)]
  rw [image_insert, insert_union, binary_merge_Ico_zero_two_mul]; rfl

/-- If `N > 0`, then `[2N]` is losing if and only if `[N]` is winning. -/
theorem Ico_zero_two_mul_not_isWinning_iff {N : ℕ} (hN : N > 0) :
    ¬isWinning (Ico 0 (2 * N : ℕ)) ↔ isWinning (Ico 0 N) := by
  rw [binary_merge_Ico_zero_two_mul]
  refine isWinning.binary_merge_self_not_isWinning_iff (by decide) ⟨0, ?_⟩
  rwa [left_mem_Ico, Int.natCast_pos]

/-- The set`[4N]` is winning if and only if `[N]` is winning. -/
theorem Ico_zero_four_mul_isWinning_iff {N : ℕ} :
    isWinning (Ico 0 (4 * N : ℕ)) ↔ isWinning (Ico 0 N) := by
  obtain rfl | hN : N = 0 ∨ N > 0 := Nat.eq_zero_or_pos N
  ---- The case `N = 0` is obvious.
  · rfl
  ---- The case `N > 0` follows by `Ico_zero_two_mul_not_isWinning_iff`.
  · rw [Nat.mul_assoc 2 2 N, ← Ico_zero_two_mul_not_isWinning_iff hN,
      ← Ico_zero_two_mul_not_isWinning_iff (Nat.mul_pos Nat.two_pos hN), not_not]

/-- The set `[1]` is losing (because it is a singleton!). -/
theorem Ico_zero_one_not_isWinning : ¬isWinning (Ico 0 1) :=
  isWinning.not_singleton 0

/-- If `N > 0`, then `[2N + 1]` is winning. -/
theorem Ico_zero_two_mul_add_one_isWinning {N : ℕ} (hN : N > 0) :
    isWinning (Ico 0 (2 * N + 1 : ℕ)) := by
  by_cases hN0 : isWinning (Ico 0 N)
  ---- If `[N]` is winning, then use the fact that `[2N]` losing.
  · rw [Int.natCast_succ, ← insert_Ico_right_eq_Ico_add_one (Int.natCast_nonneg _)]
    exact isWinning.insert_of_not_isWinning ((Ico_zero_two_mul_not_isWinning_iff hN).mpr hN0)
      right_notMem_Ico
  ---- If `[N]` is losing, then use  `[2N + 1] = 2[N + 1] ∪ (2[N] + 1)`.
  · rw [binary_merge_Ico_zero_two_mul_add_one]
    refine isWinning.binary_merge_of_right_not_isWinning (by decide) ⟨0, ?_⟩ hN0
    rw [left_mem_Ico, Int.natCast_pos]
    exact Nat.succ_pos N

/-- If `N` is odd, then `[N]` is winning if and only if `N > 1`. -/
theorem Ico_zero_isWinning_iff_of_odd {N : ℕ} (hN : Odd N) :
    isWinning (Ico 0 N) ↔ N ≠ 1 := by
  rcases hN with ⟨n, rfl⟩
  obtain rfl | hn : n = 0 ∨ n > 0 := Nat.eq_zero_or_pos n
  exacts [iff_of_false Ico_zero_one_not_isWinning (not_not.mpr rfl),
    iff_of_true (Ico_zero_two_mul_add_one_isWinning hn)
      (Nat.succ_ne_succ_iff.mpr (Nat.mul_ne_zero (Nat.succ_ne_zero 1) hn.ne.symm))]

/-- If `4 ∤ N`, then `[N]` is winning if and only if `N = 2` or `N ≠ 1` is odd. -/
theorem Ico_zero_isWinning_iff_of_not_four_dvd {N : ℕ} (hN : ¬4 ∣ N) :
    isWinning (Ico 0 N) ↔ N = 2 ∨ (N ≠ 1 ∧ Odd N) := by
  obtain hN0 | hN0 : Odd N ∨ Even N := (Nat.even_or_odd N).symm
  ---- Case 1: `N` is odd.
  · rw [and_iff_left hN0, or_iff_right_of_imp λ h ↦ h ▸ by decide]
    exact Ico_zero_isWinning_iff_of_odd hN0
  ---- Case 2: `N` is even.
  · obtain ⟨n, rfl⟩ : 2 ∣ N := even_iff_two_dvd.mp hN0
    replace hN : ¬2 ∣ n := by rwa [← Nat.mul_dvd_mul_iff_left Nat.two_pos]
    have hn : Odd n := by rwa [← Nat.not_even_iff_odd, even_iff_two_dvd]
    have hn0 : n > 0 := Nat.pos_of_ne_zero λ h ↦ Nat.not_odd_zero (h ▸ hn)
    rw [or_iff_left λ h ↦ Nat.not_even_iff_odd.mpr h.2 hN0, ← not_iff_not,
      Ico_zero_two_mul_not_isWinning_iff hn0, Ico_zero_isWinning_iff_of_odd hn,
      Ne, ← Nat.mul_right_inj (Nat.succ_ne_zero 1)]; rfl

/-- Criterion for `[N]` to be winning. -/
theorem Ico_zero_isWinning_iff {N : ℕ} (hN : N > 0) :
    isWinning (Ico 0 N) ↔ ∃ t, (t = 2 ∨ (t ≠ 1 ∧ Odd t)) ∧ ∃ k, N = t * 4 ^ k := by
  ---- Strong induction on `N`.
  induction N using Nat.strong_induction_on with | h N N_ih => ?_
  obtain hN0 | ⟨n, rfl⟩ : ¬4 ∣ N ∨ 4 ∣ N := dec_em' _
  ---- Case 1: `4 ∤ N`; then `t = N` and `k = 0` works.
  · refine (Ico_zero_isWinning_iff_of_not_four_dvd hN0).trans
      ⟨λ hN1 ↦ ⟨N, hN1, 0, (Nat.mul_one N).symm⟩, ?_⟩
    rintro ⟨t, ht, k, rfl⟩
    obtain rfl : k = 0 := by
      refine (Nat.eq_zero_or_pos k).resolve_right λ hk ↦ hN0 ⟨t * 4 ^ (k - 1), ?_⟩
      rw [Nat.mul_left_comm, ← Nat.pow_add_one', Nat.sub_one_add_one_eq_of_pos hk]
    rwa [Nat.pow_zero, Nat.mul_one]
  ---- Case 2: `4 ∣ N`, say `N = 4n`; then apply induction hypothesis on `n`.
  · replace hN : n > 0 := Nat.pos_of_mul_pos_left hN
    have hn : n < 4 * n := (Nat.lt_mul_iff_one_lt_left hN).mpr (by decide : 1 < 4)
    rw [Ico_zero_four_mul_isWinning_iff, N_ih _ hn hN]
    refine exists_congr λ t ↦ and_congr_right λ ht ↦ ⟨?_, ?_⟩
    -- If `n` takes the form `t 4^k` for some `k`, then so does `4n`.
    · rintro ⟨k, rfl⟩
      refine ⟨k + 1, ?_⟩
      rw [Nat.mul_left_comm, Nat.pow_add_one']
    -- If `4n` takes the form `t 4^k` for some `k`, then so does `n`, since `4 ∤ t`.
    · rintro ⟨k, hk⟩
      replace ht : ¬4 ∣ t := by
        rcases ht with rfl | ⟨-, ht⟩
        · decide
        · have h0 : 2 ∣ 4 := by decide
          exact λ h1 ↦ ht.not_two_dvd_nat (h0.trans h1)
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
        rw [Nat.exists_eq_add_one, Nat.pos_iff_ne_zero]
        rintro rfl; rw [Nat.pow_zero, Nat.mul_one] at hk
        exact ht ⟨n, hk.symm⟩
      have X : 4 ≠ 0 := by decide
      rw [Nat.pow_add_one', Nat.mul_left_comm, Nat.mul_right_inj X] at hk
      exact ⟨k', hk⟩

/-- Final solution -/
theorem final_solution {N : ℕ} (hN : N > 0) :
    isWinning (Icc 1 N) ↔ ∃ t, (t = 2 ∨ (t ≠ 1 ∧ Odd t)) ∧ ∃ k, N = t * 4 ^ k := by
  have h : Icc (1 : ℤ) N = (Ico (0 : ℤ) N).image (· + 1) := by
    rw [image_add_right_Ico, Ico_add_one_right_eq_Icc]; rfl
  rw [h, isWinning.translate_iff, Ico_zero_isWinning_iff hN]
