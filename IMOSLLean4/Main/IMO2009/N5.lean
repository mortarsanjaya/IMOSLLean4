/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Int.ModEq
import Mathlib.NumberTheory.Divisors

/-!
# IMO 2009 N5

Let $S$ be a set and $T : S → S$ be a function.
Prove that there does not exist a non-constant polynomial $P ∈ ℤ[X]$ such that
  for every positive integer $n$,
$$ #\\{x ∈ ℤ : T^n(x) = x\\} = P(n). $$

### Solution

We follow a variant of Solution 2 of the
  [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
Namely, $p$ does not have to be prime; we have $P(0) ≡ P(n) \pmod{q}$ for any $n > 0$.

We say that a function $T : S → S$ is *nice* if $T^n$ has
  finitely many fixed points for every positive integer $n$.
-/

namespace IMOSL
namespace IMO2009N5

open Polynomial Function Finset

/-! ### Extra lemma -/

/-- If `a₀` is `T`-periodic, then `a` has the same `T`-orbit as `a₀`
  if and only if `a` is in the `T`-orbit of `a₀`. -/
lemma periodicOrbit_eq_iff_mem_periodicOrbit (ha₀ : a₀ ∈ periodicPts T) :
    periodicOrbit T a = periodicOrbit T a₀ ↔ a ∈ periodicOrbit T a₀ := by
  refine ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  ---- If `a` and `a₀` has the same `T`-orbit, then `a` is in the `T`-orbit of `a₀`.
  · suffices a ∈ periodicPts T from h ▸ self_mem_periodicOrbit this
    simpa only [← minimalPeriod_pos_iff_mem_periodicPts,
      ← periodicOrbit_length, h] using ha₀
  ---- If `a` is in the `T`-orbit of `a₀`, then `a` and `a₀` has the same `T`-orbit.
  · rw [mem_periodicOrbit_iff ha₀] at h
    rcases h with ⟨n, rfl⟩
    exact periodicOrbit_apply_iterate_eq ha₀ n





/-! ### Start of the problem -/

/-- We say that a function `T : α → α` is nice if `T^n` has
  finitely many fixed points for every positive integer `n`. -/
structure NiceFun (α : Type*) where
  toFun : α → α
  /-- Fixed points of $T^n$, except we set the set to be empty at $0$ for convenience. -/
  nth_fixed_pts (n : ℕ) : Finset α
  nth_fixed_pts_zero : nth_fixed_pts 0 = ∅
  nth_fixed_pts_spec' (n) (hn : n > 0) (a) : a ∈ nth_fixed_pts n ↔ IsPeriodicPt toFun n a



namespace NiceFun

instance : FunLike (NiceFun α) α α where
  coe := NiceFun.toFun
  coe_injective' := λ f g h ↦ by
    rw [mk.injEq]
    refine ⟨h, funext λ n ↦ Finset.ext λ a ↦ ?_⟩
    obtain rfl | hn : n = 0 ∨ n > 0 := n.eq_zero_or_pos
    · rw [f.nth_fixed_pts_zero, g.nth_fixed_pts_zero]
    · rw [f.nth_fixed_pts_spec' _ hn, g.nth_fixed_pts_spec' _ hn, h]


section

variable (T : NiceFun α)

/-- `nth_fixed_pts n` consists of points `a` such that `T^n(a) = a`. -/
theorem nth_fixed_pts_spec (hn : n > 0) : a ∈ T.nth_fixed_pts n ↔ IsPeriodicPt T n a :=
  T.nth_fixed_pts_spec' n hn a

/-- The finite set of points of `T`-period exactly `n`. -/
noncomputable def period_n_pts (n : ℕ) : Finset α :=
  {a ∈ T.nth_fixed_pts n | minimalPeriod T a = n}

/-- `period_n_pts 0 = ∅`. -/
lemma period_zero_pts : T.period_n_pts 0 = ∅ := by
  rw [period_n_pts, T.nth_fixed_pts_zero, filter_empty]

/-- The finite set `period_n_pts` is indeed the set of `T`-period `n` points if `n > 0`. -/
lemma period_n_pts_spec (hn : n > 0) :
    a ∈ T.period_n_pts n ↔ minimalPeriod T a = n := by
  rw [period_n_pts, mem_filter, T.nth_fixed_pts_spec hn]
  exact and_iff_right_iff_imp.mpr λ h ↦ h ▸ iterate_minimalPeriod

/-- An alternate version of `period_n_pts_spec` that, in addition,
  says that there are no "`T`-period `0` points". -/
lemma period_n_pts_spec2 : a ∈ T.period_n_pts n ↔ n > 0 ∧ minimalPeriod T a = n := by
  obtain rfl | hn : n = 0 ∨ n > 0 := n.eq_zero_or_pos
  · rw [T.period_zero_pts, gt_iff_lt, lt_self_iff_false, false_and, iff_false]
    exact notMem_empty a
  · rw [and_iff_right hn, T.period_n_pts_spec hn]

/-- Any member of `period_n_pts` is a member of `periodicPts T`. -/
theorem mem_periodicPts_of_mem_period_n_pts (ha : a ∈ T.period_n_pts n) :
    a ∈ periodicPts T := by
  obtain rfl | hn : n = 0 ∨ n > 0 := Nat.eq_zero_or_pos n
  · exact absurd (T.period_zero_pts ▸ ha) (notMem_empty a)
  · rwa [← minimalPeriod_pos_iff_mem_periodicPts, (T.period_n_pts_spec hn).mp ha]

/-- If `T.period_n_pts n` has an element, then `n > 0`. -/
lemma pos_of_mem_period_n_pts (ha : a ∈ T.period_n_pts n) : n > 0 :=
  (T.period_n_pts_spec2.mp ha).1

/-- If `a` has `T`-period `n`, then `T^k(a)` has `T`-period `n`. -/
lemma iterate_apply_mem_period_n_pts (ha : a ∈ T.period_n_pts n) (k) :
    T^[k] a ∈ T.period_n_pts n := by
  obtain rfl | hn : n = 0 ∨ n > 0 := Nat.eq_zero_or_pos n
  · exact absurd (T.period_zero_pts ▸ ha) (notMem_empty a)
  · have h : minimalPeriod T (T^[k] a) = minimalPeriod T a :=
      minimalPeriod_apply_iterate (mem_periodicPts_of_mem_period_n_pts T ha) k
    simpa only [T.period_n_pts_spec hn, h] using ha



/-! ### Summation formula for the number of fixed points -/

/-- `T^n(a) = a` if and only if `a` has `T`-period dividing `n`.
  Note: Due to the formulation of `nth_fixed_pts` and `Nat.divisors`,
    the implemented formulation works even if `n = 0`. -/
theorem mem_nth_fixed_pts_iff_mem_period_n_pts_divisors (n) :
    a ∈ T.nth_fixed_pts n ↔ ∃ d ∈ n.divisors, a ∈ T.period_n_pts d := by
  obtain rfl | hn : n = 0 ∨ n > 0 := n.eq_zero_or_pos
  ---- Case 1: `n = 0`; both sides are empty.
  · rw [T.nth_fixed_pts_zero, Nat.divisors_zero, exists_mem_empty_iff, iff_false]
    exact notMem_empty a
  ---- Case 2: `n > 0`; then this is the usual expected statement.
  · rw [T.nth_fixed_pts_spec hn, isPeriodicPt_iff_minimalPeriod_dvd]
    conv => right; congr; ext d; rw [T.period_n_pts_spec2, ← and_assoc, Nat.mem_divisors,
      and_iff_left hn.ne.symm, and_iff_left_of_imp (λ h ↦ Nat.pos_of_dvd_of_pos h hn)]
    exact Iff.symm exists_eq_right'

/-- The sets of points with `T`-period `n` are pairwise disjoint across all `n`. -/
theorem period_n_pts_PairwiseDisjoint (S : Set ℕ) : S.PairwiseDisjoint T.period_n_pts := by
  rintro k - m - h
  refine disjoint_left.mpr λ a hak ham ↦ ?_
  rw [T.period_n_pts_spec2] at hak ham
  exact h (hak.2.symm.trans ham.2)

/-- The set of `n`th fixed points is the union, over all `d ∣ n`,
  of the set of elements of `T`-period `d`. -/
theorem nth_fixed_pts_eq_disjiUnion_divisors_period_n_pts (n) :
    T.nth_fixed_pts n = n.divisors.disjiUnion T.period_n_pts
      (T.period_n_pts_PairwiseDisjoint _) := by
  refine Finset.ext λ a ↦ ?_
  rw [T.mem_nth_fixed_pts_iff_mem_period_n_pts_divisors, mem_disjiUnion]

/-- Summation formula for the number of points `a` such that `T^n(a) = a`.
  Note: This is one of the key observations used in the solution. -/
theorem card_nth_fixed_pts_eq_sum_card_period_n_pts (n : ℕ) :
    #(T.nth_fixed_pts n) = ∑ d ∈ n.divisors, #(T.period_n_pts d) := calc
  _ = #(n.divisors.disjiUnion T.period_n_pts
      (T.period_n_pts_PairwiseDisjoint _)) :=
    congrArg card (T.nth_fixed_pts_eq_disjiUnion_divisors_period_n_pts n)
  _ = ∑ d ∈ n.divisors, #(T.period_n_pts d) :=
    card_disjiUnion _ _ _

end



/-! ### The number of points of period `n` is divisible by `n`. -/

/-- The "periodic orbit" of the points of `T`-period `n` has size `n`. -/
theorem periodicOrbit_length_of_mem_period_n_pts
    (T : NiceFun α) (ha : a ∈ T.period_n_pts n) :
    (periodicOrbit T a).length = n := by
  rwa [periodicOrbit_length, ← T.period_n_pts_spec (T.pos_of_mem_period_n_pts ha)]


section

variable [DecidableEq α] (T : NiceFun α) (n : ℕ)

/-- The size of `period_n_pts` is `n` times the number of corresponding orbits. -/
theorem card_period_n_pts_eq_n_mul_card_periodicOrbits (n) :
    #(T.period_n_pts n) = n * #((T.period_n_pts n).image (periodicOrbit T)) := by
  ---- Let `Bn` be the set of points of periodic `n` and `f` be the projection to cycle.
  let Bn : Finset α := T.period_n_pts n
  let f : α → Cycle α := periodicOrbit T
  ---- It suffices to show that the  preimage of every cycle in `f(Bn)` has size `n`.
  suffices ∀ C : Cycle α, C ∈ Bn.image f → #({a ∈ Bn | f a = C}) = n by
    calc #Bn
    _ = ∑ C ∈ Bn.image f, #{a ∈ Bn | f a = C} := card_eq_sum_card_image f Bn
    _ = n * #(Bn.image f) := by rw [sum_const_nat this, Nat.mul_comm]
  ---- First write `C` as the cycle `[a₀, f(a₀), …]` for some `a₀ ∈ Bn`.
  intro C hC
  rw [mem_image] at hC; rcases hC with ⟨a₀, ha₀, rfl⟩
  ---- It suffices to show that `f(a) = f(a₀)` if and only if `a ∈ C`.
  suffices {a ∈ Bn | f a = f a₀} = (f a₀).toFinset by
    calc #({a ∈ Bn | f a = f a₀})
    _ = (f a₀).toMultiset.dedup.card := congrArg card this
    _ = (f a₀).toMultiset.card :=
      Multiset.dedup_card_eq_card_iff_nodup.mpr nodup_periodicOrbit
    _ = n := T.periodicOrbit_length_of_mem_period_n_pts ha₀
  ---- Now show that `f(a) = f(a₀)` if and only if `a ∈ C`.
  have ha₀0 : a₀ ∈ periodicPts T := mem_periodicPts_of_mem_period_n_pts T ha₀
  ext a; rw [mem_filter, ← Cycle.toFinset_toMultiset, Multiset.mem_toFinset,
    periodicOrbit_eq_iff_mem_periodicOrbit ha₀0]
  refine and_iff_right_iff_imp.mpr λ h ↦ ?_
  ---- Remaining step: show that if `a` is in the `T`-orbit of `a₀`, then `a ∈ Bn`.
  rw [mem_periodicOrbit_iff ha₀0] at h
  rcases h with ⟨k, rfl⟩
  exact iterate_apply_mem_period_n_pts T ha₀ k

/-- The set of points with `T`-period `n` has size divisible by `n`.
  Note: This is one of the key observations used in the solution. -/
theorem n_dvd_card_period_n_pts (n) : n ∣ #(T.period_n_pts n) :=
  ⟨_, T.card_period_n_pts_eq_n_mul_card_periodicOrbits n⟩

/-- For any `n` and for any prime `q`, the number of fixed points
  of `T^n` and `T^{nq}` are congruent modulo `q`. -/
theorem card_nth_fixed_pts_modeq_prime (hq : Nat.Prime q) (n : ℕ) :
    #(T.nth_fixed_pts (n * q)) ≡ #(T.nth_fixed_pts n) [MOD q] := by
  /- It suffices to show the following claim: for each `d` dividing `nq` but not `n`,
    the number of `T`-period `d` points is divisible by `q`. -/
  calc #(T.nth_fixed_pts (n * q)) % q
    _ = (∑ d ∈ (n * q).divisors, #(T.period_n_pts d) % q) % q := by
      rw [card_nth_fixed_pts_eq_sum_card_period_n_pts, sum_nat_mod]
    _ = (∑ d ∈ n.divisors, #(T.period_n_pts d) % q) % q :=
      congrArg (· % q) (sum_congr_of_eq_on_inter ?_ ?_ λ _ _ _ ↦ rfl)
    _ = #(T.nth_fixed_pts n) % q := by
      rw [← sum_nat_mod, ← card_nth_fixed_pts_eq_sum_card_period_n_pts]
  ---- Show the claim by showing that `q ∣ d`.
  · intro d hdnq hdn
    rw [Nat.mem_divisors] at hdn hdnq
    refine Nat.dvd_iff_mod_eq_zero.mp (Nat.dvd_trans ?_ (T.n_dvd_card_period_n_pts d))
    -- We now show `q ∣ d` by contradiction.
    by_contra h
    refine hdn ⟨?_, Nat.ne_zero_of_mul_ne_zero_left hdnq.2⟩
    replace hdn : q.Coprime d := hq.coprime_iff_not_dvd.mpr h
    exact hdn.symm.dvd_of_dvd_mul_right hdnq.1
  /- Another claim we need to show is that similar statement holds
    if `d ∣ n` but `d ∤ nq`... which is trivially true. -/
  · intro d hdn hdnq
    rw [Nat.mem_divisors] at hdn hdnq
    refine absurd ?_ hdnq
    exact ⟨Nat.dvd_mul_right_of_dvd hdn.1 q, Nat.mul_ne_zero hdn.2 hq.ne_zero⟩

end

end NiceFun





/-- Final solution -/
theorem final_solution [DecidableEq α] {T : NiceFun α}
    (h : ∃ P : ℤ[X], ∀ n > 0, (#(T.nth_fixed_pts n) : ℤ) = P.eval ↑n) :
    ∃ N, ∀ n > 0, #(T.nth_fixed_pts n) = N := by
  rcases h with ⟨P, hP⟩
  ---- We show that `P(n) = P(0)` for any `n > 0`.
  have h (n : ℕ) (hn : n > 0) : P.eval ↑n = P.eval 0 := by
    -- Pick a large prime `q > |P(n) - P(0)|`.
    obtain ⟨q, hq, hq0⟩ : ∃ q > (P.eval ↑n - P.eval 0).natAbs, Nat.Prime q :=
      Nat.exists_infinite_primes _
    -- It clearly suffices to show that `P(n) ≡ P(0) (mod q)`.
    suffices P.eval ↑n ≡ P.eval 0 [ZMOD q]
      from Int.eq_of_sub_eq_zero (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs this.symm.dvd hq)
    -- Indeed, we have `P(n) ≡ P(nq) ≡ P(0) (mod q)`.
    calc P.eval ↑n % q
      _ = ↑(#(T.nth_fixed_pts n) % q) := congrArg (· % _) (hP n hn).symm
      _ = ↑(#(T.nth_fixed_pts (n * q)) % q) := by
        rw [T.card_nth_fixed_pts_modeq_prime hq0 n]
      _ = (P.eval ((n * q : ℕ) : ℤ)) % q := by
        rw [Int.natCast_emod, ← hP _ (Nat.mul_pos hn hq.pos)]
      _ = P.eval 0 % q := by
        rw [← Int.ModEq, Int.modEq_comm, Int.modEq_iff_dvd]
        refine dvd_trans ?_ (sub_dvd_eval_sub _ _ P)
        rw [sub_zero, Int.natCast_mul]
        exact Int.dvd_mul_left _ _
  ---- Since the required `N` is of type `ℕ`, we need to lift `P(0)` to `ℕ`.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, P.eval 0 = ↑N := by
    refine Int.eq_ofNat_of_zero_le (?_ : P.eval 0 ≥ 0)
    rw [← h 1 Nat.one_pos, ← hP 1 Nat.one_pos]
    exact Nat.cast_nonneg _
  ---- Now use the `N` we obtained.
  refine ⟨N, λ n hn ↦ ?_⟩
  rw [← Int.natCast_inj, ← hN, hP n hn, h n hn]
