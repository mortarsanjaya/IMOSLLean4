/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Nat.Factors
import Mathlib.Order.Bounds.Defs

/-!
# IMO 2022 C6

Consider a single-player game on a board played with pebbles stacked on piles.
At any time, one can perform the following operation: choose two piles, take an equal
  number of pebbles from the two piles, and put these pebbles in one new pile.

Let $n$ be a nonnegative integer.
Suppose that we start with $n$ piles consisting of one pebble each.
Find, in terms of $n$, the minimum possible number of piles that
  one can attain after several operations.

### Answer

$0$ if $n = 0$, $1$ if $n$ is a power of $2$, and $2$ otherwise.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2022SL.pdf).
We represent a pile as a nonnegative integer and the board state as a multiset.
We define `canReach X Y` to denote that we can transform the state `X` to `Y`
  after several moves; in addition, we allow adding and removing empty piles.
-/

namespace IMOSL
namespace IMO2022C6

open Multiset

/-- `canReach X Y` means we can transform `X` to `Y` after several moves.
  We also allow adding and removing empty piles, for convenience. -/
inductive canReach : Multiset ℕ → Multiset ℕ → Prop
  | refl' (X) : canReach X X
  | trans' (X Y Z) : canReach X Y → canReach Y Z → canReach X Z
  /-- We can add or delete empty piles. -/
  | cons_zero (X) : canReach X (0 ::ₘ X)
  | delete_zero (X) : canReach (0 ::ₘ X) X
  /-- The actual operation. -/
  | op (a b c X) : canReach ((a + c) ::ₘ (b + c) ::ₘ X) (2 * c ::ₘ a ::ₘ b ::ₘ X)


namespace canReach

instance : Trans canReach canReach canReach := ⟨trans' _ _ _⟩

/-- `canReach X Y` means we can transform `X` to `Y` after several moves.
  We also allow adding and removing empty piles, for convenience. -/
infix : 50 " ==> " => canReach



/-! ### Basic statements -/

@[refl] protected lemma refl (X) : X ==> X :=
  canReach.refl' X

@[trans] protected lemma trans (h : X ==> Y) (h0 : Y ==> Z) : X ==> Z :=
  trans' X Y Z h h0

/-- If `X` can reach `Y`, then `X + Z` can reach `Y + Z`. -/
theorem add_right (h : X ==> Y) (Z) : X + Z ==> Y + Z := by
  induction h with
  | refl' X => rfl
  | trans' _ _ _ _ _ h h0 => exact h.trans h0
  | cons_zero X => rw [X.cons_add]; exact canReach.cons_zero (X + Z)
  | delete_zero X => rw [X.cons_add]; exact canReach.delete_zero (X + Z)
  | op a b c X => simpa [X.cons_add] using canReach.op a b c (X + Z)

/-- If `Y` can reach `Z`, then `X + Y` can reach `X + Z`. -/
theorem add_left (X) (h : Y ==> Z) : X + Y ==> X + Z := by
  rw [X.add_comm, X.add_comm]
  exact h.add_right X

/-- If `X` can reach `Y`, then `n ::ₘ X` can reach `n ::ₘ Y`.
  Here `n ::ₘ X` means the state obtained by adding a pile of size `n` to `X`. -/
theorem cons (h : X ==> Y) (n) : n ::ₘ X ==> n ::ₘ Y :=
  h.add_left {n}

/-- From a state `X`, we can reach the state by adding empty piles to `X`. -/
theorem add_zeroes (X n) : X ==> X + replicate n 0 := by
  induction n with
  | zero => rw [replicate_zero, add_zero]
  | succ n hn => rw [replicate_succ, add_cons]; exact hn.trans (cons_zero _)

/-- From a state `X`, we can reach a new state by removing some empty piles from `X`. -/
theorem delete_zeroes (X n) : X + replicate n 0 ==> X := by
  induction n with
  | zero => rw [replicate_zero, add_zero]
  | succ n hn => rw [replicate_succ, add_cons]; exact (delete_zero _).trans hn

/-- From a state `X`, we can reach a new state by removing all empty piles from `X`. -/
theorem self_to_filter_ne_zero (X) : X ==> X.filter (· ≠ 0) := calc
  X = X.filter (· ≠ 0) + replicate (X.count 0) 0 := by
    rw [← filter_eq', add_comm, filter_add_not]
  _ ==> X.filter (· ≠ 0) := delete_zeroes _ _

/-- If `X` can reach `Y`, the state `X'` obtained by multiplying the size of
  all piles in `X` by `n` can reach the state `Y'`, defined analogously. -/
theorem map_mul_left (h : X ==> Y) (n) : X.map (n * ·) ==> Y.map (n * ·) := by
  induction h with
  | refl' X => rfl
  | trans' _ _ _ _ _ h h0 => exact h.trans h0
  | cons_zero X => rw [map_cons, Nat.mul_zero]; exact cons_zero _
  | delete_zero X => rw [map_cons, Nat.mul_zero]; exact delete_zero _
  | op a b c X =>
      simp only [map_cons]
      rw [Nat.mul_left_comm, Nat.mul_add, Nat.mul_add]
      exact op _ _ _ _

/-- `{2, a + b} + X ==> {2, a, 1, 1, …, 1} + X`.
  That is, a pile of size `2` can be used to pull out singletons. -/
theorem add_replicate_ones_from_two (a b X) :
    2 ::ₘ (a + b) ::ₘ X ==> 2 ::ₘ a ::ₘ (replicate b 1 + X) := by
  induction b generalizing X with
  | zero => rw [replicate_zero, zero_add, Nat.add_zero]
  | succ b hb =>
      calc 2 ::ₘ (a + b + 1) ::ₘ X
        _ ==> 2 ::ₘ 1 ::ₘ (a + b) ::ₘ X := op _ _ _ _
        _ = 2 ::ₘ (a + b) ::ₘ 1 ::ₘ X := by rw [cons_swap (a + b)]
        _ ==> 2 ::ₘ a ::ₘ (replicate b 1 + (1 ::ₘ X)) := hb _
        _ = 2 ::ₘ a ::ₘ (replicate (b + 1) 1 + X) := by
          rw [replicate_succ, add_cons, cons_add]



/-! ### Invariance properties -/

/-- The number of pebbles in the board is invariant under operations. -/
theorem sum_eq (h : X ==> Y) : X.sum = Y.sum := by
  induction h with
  | refl' X => rfl
  | trans' _ _ _ _ _ h h0 => exact h.trans h0
  | cons_zero X => rw [X.sum_cons, Nat.zero_add]
  | delete_zero X => rw [X.sum_cons, Nat.zero_add]
  | op a b c X =>
      repeat rw [sum_cons]
      rw [← Nat.add_assoc, Nat.add_add_add_comm, ← Nat.two_mul,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_assoc]

/-- If `X` contains a pile of size not divisible by `n`, where `n` is odd, then for
  any state `Y` reachable from `X`, `Y` contains a pile of size not divisible by `n`. -/
theorem odd_not_dvd (hn : Odd n) (h : X ==> Y) (hX : ∃ a ∈ X, ¬n ∣ a) :
    ∃ a ∈ Y, ¬n ∣ a := by
  induction h with
  | refl' X => exact hX
  | trans' X Y Z h h0 hXY hYZ => exact hYZ (hXY hX)
  | cons_zero X =>
      rcases hX with ⟨t, htX, hnt⟩
      exact ⟨t, mem_cons_of_mem htX, hnt⟩
  | delete_zero X =>
      rcases hX with ⟨t, htX, hnt⟩
      exact ⟨t, (mem_cons.mp htX).resolve_left λ h ↦ hnt (h ▸ n.dvd_zero), hnt⟩
  | op a b c X =>
      ---- Suppose `t ∈ {a + c, b + c} + X` and `n ∤ t`.
      rcases hX with ⟨t, htX, hnt⟩
      ---- If `n ∤ c`, then we are done since `n ∤ 2c`.
      obtain hnc | hnc : ¬n ∣ c ∨ n ∣ c := dec_em' _
      · refine ⟨2 * c, mem_cons_self _ _, λ hnc0 ↦ hnc ?_⟩
        exact (Nat.coprime_two_right.mpr hn).dvd_of_dvd_mul_left hnc0
      ---- If `n ∣ c`, then split into three cases: `t = a + c, t = b + c, t ∈ X`.
      rw [mem_cons, mem_cons] at htX
      rcases htX with rfl | rfl | htX
      ---- Case 1: `t = a + c`; then `n ∤ a ∈ X`.
      · refine ⟨a, mem_cons_of_mem (mem_cons_self a _), ?_⟩
        rwa [Nat.dvd_add_left hnc] at hnt
      ---- Case 2: `t = b + c`; then `n ∤ b ∈ X`.
      · refine ⟨b, mem_cons_of_mem (mem_cons_of_mem (X.mem_cons_self b)), ?_⟩
        rwa [Nat.dvd_add_left hnc] at hnt
      ---- Case 3: `t ∈ X`; then pick `t`.
      · exact ⟨t, mem_cons_of_mem (mem_cons_of_mem (mem_cons_of_mem htX)), hnt⟩



/-! ### The main problem -/

/-- Given a state `X`, the state `2X` obtained by making two copies for each pile in `X`
  can reach the state `X'` obtained by doubling the size of each pile in `X`. -/
theorem two_nsmul_to_map_two_mul (X) : 2 • X ==> X.map (2 * ·) := by
  ---- Induction on `X`; the base case `X = 0` is trivial.
  induction X using Multiset.induction with | empty => rfl | cons a X hX => ?_
  ---- Induction step follows from `{a, a} ==> {2a}`.
  calc 2 • (a ::ₘ X)
    _ = 2 • {a} + 2 • X := nsmul_cons _ _
    _ = (0 + a) ::ₘ (0 + a) ::ₘ 2 • X := by
      rw [Nat.zero_add, two_nsmul, singleton_add, cons_add, singleton_add]
    _ ==> 2 * a ::ₘ 0 ::ₘ 0 ::ₘ 2 • X := op 0 0 a _
    _ = 0 ::ₘ 0 ::ₘ 2 * a ::ₘ 2 • X := by rw [cons_swap (2 * a), cons_swap (2 * a)]
    _ ==> 0 ::ₘ 2 * a ::ₘ 2 • X := delete_zero _
    _ ==> 2 * a ::ₘ 2 • X := delete_zero _
    _ ==> 2 * a ::ₘ X.map (2 * ·) := hX.cons _
    _ = (a ::ₘ X).map (2 * ·) := (X.map_cons _ _).symm

/-- The state with `2n` piles of size `a` reaches one with `n` piles of size `2a`. -/
theorem replicate_two_mul_left_to_right (n a) :
    replicate (2 * n) a ==> replicate n (2 * a) :=
  calc replicate (2 * n) a
    _ = 2 • replicate n a := (nsmul_replicate 2 _).symm
    _ ==> (replicate n a).map (2 * ·) := two_nsmul_to_map_two_mul _
    _ = replicate n (2 * a) := map_replicate _ _ _

/-- The state with `2^k n` piles of size `a` reaches one with `n` piles of size `2^k a`. -/
theorem replicate_two_pow_mul_left_to_right (k n a) :
    replicate (2 ^ k * n) a ==> replicate n (2 ^ k * a) := by
  induction k generalizing a with
  | zero => rw [Nat.pow_zero, Nat.one_mul, Nat.one_mul]
  | succ k hk =>
      calc replicate (2 ^ (k + 1) * n) a
        _ = replicate (2 * (2 ^ k * n)) a := by rw [Nat.pow_succ', Nat.mul_assoc]
        _ ==> replicate (2 ^ k * n) (2 * a) := replicate_two_mul_left_to_right _ _
        _ ==> replicate n (2 ^k * (2 * a)) := hk _
        _ = replicate n (2 ^ (k + 1) * a) := by rw [Nat.pow_succ, Nat.mul_assoc]

/-- The state with `2^k` piles of size `1` reaches one with a single pile of size `2^k`. -/
theorem replicate_two_pow_of_one_to_singleton (k) : replicate (2 ^ k) 1 ==> {2 ^ k} :=
  calc replicate (2 ^ k) 1
    _ = replicate (2 ^ k * 1) 1 := by rw [Nat.mul_one]
    _ ==> replicate 1 (2 ^ k * 1) := replicate_two_pow_mul_left_to_right _ _ _
    _ = {2 ^ k} := by rw [Nat.mul_one, replicate_one]

/-- If `m ≤ 2^k`, then the state with `2^k + m` piles of size `1` reaches
  the state with a single pile of size `2^k` and a single pile of size `m`. -/
theorem replicate_two_pow_add_of_one_to_doubleton (h : m ≤ 2 ^ k) :
    replicate (2 ^ k + m) 1 ==> {m, 2 ^ k} := by
  have h0 : replicate (2 ^ k) 1 ==> {2 ^ k} := replicate_two_pow_of_one_to_singleton k
  ---- If `m ∈ {0, 1}`, trivial.
  cases m with | zero => exact h0.trans (cons_zero _) | succ m' => ?_
  cases m' with | zero => exact h0.cons 1 | succ m'' => ?_
  ---- For `m = m'' + 2`, first write `k = k' + 1`; note that `k > 0`.
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    apply Nat.exists_eq_succ_of_ne_zero
    rintro rfl; exact h.not_gt (Nat.lt_of_sub_eq_succ rfl)
  ---- Also, write `2^k = m + r` for some `r`.
  let k := k' + 1
  let m := m'' + 2
  obtain ⟨r, hr⟩ : ∃ r, m + r = 2 ^ k := Nat.le.dest h
  ---- Now note that `LHS ==> {2^k, 2, 1, 1, ...} ==> {m, 2, 1, 1, ...} ==> RHS`.
  calc 1 ::ₘ 1 ::ₘ replicate (2 ^ k + m'') 1
    _ ==> 2 ::ₘ (replicate 2 0 + replicate (2 ^ k + m'') 1) := op 0 0 1 _
    _ = 2 ::ₘ (replicate (2 ^ k) 1 + replicate m'' 1) + replicate 2 0 := by
      rw [add_comm, replicate_add, cons_add]
    _ ==> 2 ::ₘ (replicate (2 ^ k) 1 + replicate m'' 1) := delete_zeroes _ _
    _ ==> 2 ::ₘ 2 ^ k ::ₘ replicate m'' 1 := (h0.add_right _).cons 2
    _ = 2 ::ₘ (m + r) ::ₘ replicate m'' 1 := by rw [hr]
    _ ==> 2 ::ₘ m ::ₘ (replicate r 1 + replicate m'' 1) :=
      add_replicate_ones_from_two m r _
    _ = m ::ₘ 2 ::ₘ replicate (2 * (2 ^ k' - 1)) 1 := by
      rw [cons_swap, ← replicate_add, Nat.add_comm, Nat.mul_sub_one,
        ← Nat.pow_succ', ← hr, Nat.add_right_comm, Nat.add_sub_cancel]
    _ ==> m ::ₘ 2 ::ₘ replicate (2 ^ k' - 1) 2 :=
      ((replicate_two_mul_left_to_right _ 1).cons 2).cons m
    _ = m ::ₘ replicate (2 ^ k' * 1) 2 := by
      rw [← replicate_succ, Nat.sub_add_cancel Nat.one_le_two_pow, Nat.mul_one]
    _ ==> {m, 2 ^ k' * 2} := (replicate_two_pow_mul_left_to_right _ _ _).cons m
    _ = {m, 2 ^ k} := by rw [← Nat.pow_succ]

/-- If `n ≠ 0`, then the state with `n` piles of size `1` reaches the state with
  two piles, one of size `n - 2^k` and one of size `2^k`, where `k = ⌊log_2 n⌋`.  -/
theorem replicate_ones_to_doubleton (hn : n ≠ 0) :
    replicate n 1 ==> {n - 2 ^ n.log2, 2 ^ n.log2} :=
  calc replicate n 1
    _ = replicate (2 ^ n.log2 + (n - 2 ^ n.log2)) 1 := by
      rw [Nat.add_sub_cancel' (Nat.log2_self_le hn)]
    _ ==> {n - 2 ^ n.log2, 2 ^ n.log2} := by
      refine replicate_two_pow_add_of_one_to_doubleton (Nat.sub_le_of_le_add ?_)
      rw [← Nat.mul_two, ← Nat.pow_succ]
      exact Nat.lt_log2_self.le

end canReach






/-! ### Summary -/

/-- `n` is a power of `2` if and only if `2^{⌊log_2 n⌋} = n`. -/
lemma isPowerOfTwo_iff_two_pow_log2_eq (n) : (∃ k, n = 2 ^ k) ↔ n = 2 ^ (Nat.log2 n) := by
  refine ⟨λ ⟨k, hk⟩ ↦ ?_, λ h ↦ ⟨n.log2, h⟩⟩
  rw [hk, Nat.log2_two_pow]

instance (n : ℕ) : Decidable (∃ k, n = 2 ^ k) :=
  decidable_of_iff' _ (isPowerOfTwo_iff_two_pow_log2_eq n)

open canReach in
/-- Final solution -/
theorem final_solution (n) :
    IsLeast (card '' {X | replicate n 1 ==> X})
      (if n = 0 then 0 else if ∃ k, n = 2 ^ k then 1 else 2) := by
  split_ifs with hn0 hn2
  ---- Case 1: `n = 0`.
  · exact ⟨⟨0, hn0 ▸ canReach.refl _, rfl⟩, λ s _ ↦ s.zero_le⟩
  ---- Case 2: `n` is a power of `2`.
  · rcases hn2 with ⟨k, rfl⟩
    refine ⟨⟨{2 ^ k}, replicate_two_pow_of_one_to_singleton k, rfl⟩, ?_⟩
    -- It remains to show that if `replicate (2 ^ k) 1 ==> X` then `X` is nonempty.
    rintro s ⟨X, hX : replicate (2 ^ k) 1 ==> X, rfl⟩
    replace hX : X.sum ≠ 0 := calc
      X.sum = (replicate (2 ^ k) 1).sum := hX.sum_eq.symm
      _ = 2 ^ k * 1 := sum_replicate _ _
      _ = 2 ^ k := Nat.mul_one _
      _ ≠ 0 := hn0
    rw [Nat.succ_le, card_pos]
    rintro rfl; exact hX rfl
  ---- Case 3: `n ≠ 0` is not a power of `2`.
  · refine ⟨⟨{n - 2 ^ n.log2, 2 ^ n.log2}, replicate_ones_to_doubleton hn0, rfl⟩, ?_⟩
    -- Let `X` be a pile reachable from the state of `n` piles of size `1`.
    rintro s ⟨X, hX : replicate _ 1 ==> X, rfl⟩
    -- If `X` consists of at most one pile, then it has one pile, of size `n`.
    refine le_of_not_gt λ hX0 ↦ ?_
    obtain rfl : X = {n} := by
      -- First note that `X` consists of `n` pebbles.
      have hX1 : X.sum = n := calc
        X.sum = (replicate n 1).sum := hX.sum_eq.symm
        _ = n * 1 := sum_replicate _ _
        _ = n := Nat.mul_one n
      -- Now do the casework.
      rw [Nat.lt_succ, Nat.le_one_iff_eq_zero_or_eq_one, card_eq_zero, card_eq_one] at hX0
      rcases hX0 with rfl | ⟨a, rfl⟩
      exacts [absurd hX1.symm hn0, congrArg _ hX1]
    -- Now pick any **odd** prime divisor `p` of `n`.
    obtain ⟨p, hp, hpn, hp0⟩ : ∃ p, p.Prime ∧ p ∣ n ∧ Odd p :=
      (Nat.eq_two_pow_or_exists_odd_prime_and_dvd n).resolve_left hn2
    -- Using divisibility by `p`, `{1, 1, …} ==> {n}` yields a contradiction.
    obtain ⟨N, hNX, hpN⟩ : ∃ N ∈ ({n} : Multiset ℕ), ¬p ∣ N :=
      hX.odd_not_dvd hp0 ⟨1, mem_replicate.mpr ⟨hn0, rfl⟩, hp.not_dvd_one⟩
    exact hpN (mem_singleton.mp hNX ▸ hpn)
