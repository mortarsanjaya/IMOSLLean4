/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
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
  /-- We can add and delete empty piles as we want. (This implies reflexivity to)-/
  | manip_zeroes (X m n) : canReach (X + replicate m 0) (X + replicate n 0)
  /-- Transitivity. -/
  | trans' (X Y Z) : canReach X Y → canReach Y Z → canReach X Z
  /-- The actual operation. -/
  | op (a b c X) : canReach ((a + c) ::ₘ (b + c) ::ₘ X) (2 * c ::ₘ a ::ₘ b ::ₘ X)


namespace canReach

instance : Trans canReach canReach canReach := ⟨trans' _ _ _⟩

@[inherit_doc canReach]
scoped infix : 50 " ==> " => canReach



/-! ### Basic statements -/

@[refl] protected lemma refl (X) : X ==> X := by
  simpa only [replicate_zero, Multiset.add_zero] using manip_zeroes X 0 0

@[trans] protected lemma trans (h : X ==> Y) (h0 : Y ==> Z) : X ==> Z :=
  trans' X Y Z h h0

/-- If `X` can reach `Y`, then `X + Z` can reach `Y + Z`. -/
theorem add_right (h : X ==> Y) (Z) : X + Z ==> Y + Z := by
  induction h with
  | manip_zeroes X m n => simpa only [add_right_comm X _ Z] using manip_zeroes (X + Z) m n
  | trans' _ _ _ _ _ h h0 => exact h.trans h0
  | op a b c X => simpa only [cons_add] using canReach.op a b c (X + Z)

/-- If `Y` can reach `Z`, then `X + Y` can reach `X + Z`. -/
theorem add_left (X) (h : Y ==> Z) : X + Y ==> X + Z := by
  rw [X.add_comm, X.add_comm]
  exact h.add_right X

/-- If `X` can reach `Y`, then `n ::ₘ X` can reach `n ::ₘ Y`.
  Here `n ::ₘ X` means the state obtained by adding a pile of size `n` to `X`. -/
theorem cons (h : X ==> Y) (n) : n ::ₘ X ==> n ::ₘ Y :=
  h.add_left {n}

/-- Adding empty piles to a state. -/
theorem add_zeroes (X n) : X ==> X + replicate n 0 := by
  simpa only [replicate_zero, Multiset.add_zero] using manip_zeroes X 0 n

/-- Removing empty piles from a state. -/
theorem delete_zeroes (X n) : X + replicate n 0 ==> X := by
  simpa only [replicate_zero, Multiset.add_zero] using manip_zeroes X n 0

/-- Adding one empty pile from a state. -/
theorem cons_zero (X) : X ==> 0 ::ₘ X :=
  calc X
  _ ==> X + replicate 1 0 := add_zeroes X 1
  _ = 0 ::ₘ X := by rw [replicate_one, add_comm, singleton_add]

/-- Removing one empty pile from a state. -/
theorem delete_zero (X) : 0 ::ₘ X ==> X :=
  calc 0 ::ₘ X
  _ = X + replicate 1 0 := by rw [replicate_one, add_comm, singleton_add]
  _ ==> X := delete_zeroes X 1

/-- Doubling a pile by depleting another pile. -/
theorem pile_doubling (X a b) : (a + b) ::ₘ b ::ₘ X ==> a ::ₘ (2 * b) ::ₘ X :=
  calc (a + b) ::ₘ b ::ₘ X
  _ = (a + b) ::ₘ (0 + b) ::ₘ X := by rw [Nat.zero_add]
  _ ==> 2 * b ::ₘ a ::ₘ 0 ::ₘ X := op a 0 b X
  _ = 0 ::ₘ a ::ₘ (2 * b) ::ₘ X := by rw [cons_swap, cons_swap (2 * b), cons_swap]
  _ ==> a ::ₘ (2 * b) ::ₘ X := delete_zero _

/-- Combining two piles of equal size into one pile. -/
theorem pile_merge (X a) : a ::ₘ a ::ₘ X ==> 2 * a ::ₘ X :=
  calc a ::ₘ a ::ₘ X
  _ = (0 + a) ::ₘ a ::ₘ X := by rw [Nat.zero_add]
  _ ==> 0 ::ₘ (2 * a) ::ₘ X := pile_doubling X 0 a
  _ ==> (2 * a) ::ₘ X := delete_zero _



/-! ### Invariance properties -/

/-- The number of pebbles in the board is invariant under operations. -/
theorem sum_eq (h : X ==> Y) : X.sum = Y.sum := by
  induction h with
  | manip_zeroes X m n => simp only [sum_add, sum_replicate, nsmul_zero]
  | trans' _ _ _ _ _ h h0 => exact h.trans h0
  | op a b c X =>
      repeat rw [sum_cons]
      rw [← Nat.add_assoc, Nat.add_add_add_comm, ← Nat.two_mul,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_assoc]

/-- If `X` contains a pile of size not divisible by `t`, where `t` is odd, then for
  any state `Y` reachable from `X`, `Y` contains a pile of size not divisible by `t`. -/
theorem odd_not_dvd (ht : Odd t) (h : X ==> Y) (hX : ∃ a ∈ X, ¬t ∣ a) : ∃ a ∈ Y, ¬t ∣ a := by
  induction h with
  | manip_zeroes X m n =>
      rcases hX with ⟨a, haX, hta⟩
      refine ⟨a, ?_, hta⟩
      rw [mem_add, mem_replicate] at haX ⊢
      left; exact haX.resolve_right λ ⟨h, h0⟩ ↦ hta ⟨0, h0⟩
  | trans' X Y Z h h0 hXY hYZ => exact hYZ (hXY hX)
  | op a b c X =>
      ---- Suppose `x ∈ {a + c, b + c} + X` and `t ∤ x`.
      rcases hX with ⟨x, hxX, htx⟩
      ---- If `t ∤ c`, then we are done since `t ∤ 2c`.
      obtain htc | htc : ¬t ∣ c ∨ t ∣ c := dec_em' _
      · refine ⟨2 * c, mem_cons_self _ _, λ hnc0 ↦ htc ?_⟩
        exact (Nat.coprime_two_right.mpr ht).dvd_of_dvd_mul_left hnc0
      ---- If `t ∣ c`, then split into three cases: `x = a + c, x = b + c, x ∈ X`.
      rw [mem_cons, mem_cons] at hxX
      rcases hxX with rfl | rfl | hxX
      ---- Case 1: `x = a + c`; then `t ∤ a ∈ X`.
      · refine ⟨a, mem_cons_of_mem (mem_cons_self a _), ?_⟩
        rwa [Nat.dvd_add_left htc] at htx
      ---- Case 2: `x = b + c`; then `t ∤ b ∈ X`.
      · refine ⟨b, mem_cons_of_mem (mem_cons_of_mem (X.mem_cons_self b)), ?_⟩
        rwa [Nat.dvd_add_left htc] at htx
      ---- Case 3: `x ∈ X`; then `t ∤ x ∈ x`.
      · exact ⟨x, mem_cons_of_mem (mem_cons_of_mem (mem_cons_of_mem hxX)), htx⟩



/-! ### Deconstruction algorithm using a pile of size two -/

/-- `{2, a + 1} + X ==> {2, a, 1} + X`; pulling out singletons with a pile of size `2`. -/
theorem deconstruct_succ (a X) : 2 ::ₘ (a + 1) ::ₘ X ==> 2 ::ₘ a ::ₘ 1 ::ₘ X :=
  calc 2 ::ₘ (a + 1) ::ₘ X
  _ ==> 2 ::ₘ 1 ::ₘ a ::ₘ X := op 1 a 1 X
  _ = 2 ::ₘ a ::ₘ 1 ::ₘ X := by rw [cons_swap 1 a]

/-- `{2, a + b} + X ==> {2, a, 1, 1, …, 1} + X`, with `1` appearing `b` times. -/
theorem deconstruct_add (a b X) :
    2 ::ₘ (a + b) ::ₘ X ==> 2 ::ₘ a ::ₘ (replicate b 1 + X) := by
  induction b generalizing X with
  | zero => rw [replicate_zero, zero_add, Nat.add_zero]
  | succ b hb =>
      calc 2 ::ₘ (a + b + 1) ::ₘ X
        _ ==> 2 ::ₘ (a + b) ::ₘ 1 ::ₘ X := deconstruct_succ (a + b) X
        _ ==> 2 ::ₘ a ::ₘ (replicate b 1 + (1 ::ₘ X)) := hb _
        _ = 2 ::ₘ a ::ₘ (replicate (b + 1) 1 + X) := by
          rw [replicate_succ, add_cons, cons_add]



/-! ### The main problem -/

/-- Given a state `X`, the state `2X` obtained by making two copies for each pile in `X`
  can reach the state `X'` obtained by doubling the size of each pile in `X`. -/
theorem two_nsmul_to_map_two_mul (X) : 2 • X ==> X.map (2 * ·) := by
  ---- Induction on `X`; the base case `X = 0` is trivial.
  induction X using Multiset.induction with | empty => rfl | cons a X hX => ?_
  ---- Induction step follows from `{a, a} ==> {2a}`.
  calc 2 • (a ::ₘ X)
    _ = a ::ₘ a ::ₘ 2 • X := by
      rw [nsmul_cons, two_nsmul, singleton_add, cons_add, singleton_add]
    _ ==> 2 * a ::ₘ 2 • X := pile_merge _ _
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
    _ ==> 2 ::ₘ (replicate (2 ^ k + m'') 1) := pile_merge _ _
    _ = 2 ::ₘ (replicate (2 ^ k) 1 + replicate m'' 1) := by rw [replicate_add]
    _ ==> 2 ::ₘ 2 ^ k ::ₘ replicate m'' 1 := (h0.add_right _).cons 2
    _ = 2 ::ₘ (m + r) ::ₘ replicate m'' 1 := by rw [hr]
    _ ==> 2 ::ₘ m ::ₘ (replicate r 1 + replicate m'' 1) := deconstruct_add m r _
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
