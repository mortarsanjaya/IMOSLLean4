/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset

/-!
# IMO 2008 C4 (P5)

Let $n$ and $d$ be positive integers.
Consider $2n$ lamps labelled with a pair $(b, m)$ where
  $b \in \{0, 1\}$ and $m \in [n] = \{0, 1, \ldots, n - 1\}$.
Initially, all the lamps are off.

Consider sequences of $k = 2d + n$ steps, where at each step,
  one of the lamps is switched (off to on and vice versa).
Let $S_N$ be the set of $k$-step sequences ending in a stat
   where the lamps labelled $(b, m)$ are on iff $b = 0$.
Let $S_M ⊆ S_N$ consist of the sequences that do not
  touch the lamps labelled $(0, m)$ at all.
Find $|S_N|/|S_M|$.

### Some implementation details

In this implementation, `Λ` denote the type of half-lamps (those coded with `(0, m)`).
The set of all lamps is `Fin 2 × Λ`.
The type of index used for the sequence is `I`.
Thus, a sequence of toFun is `I → Λ`.

The set `S_N` is implemented as a structure of `I → Fin 2 × Λ` with extra conditions.
However, `S_M` will be implemented as `I → Λ` instead of `I → Fin 2 × Λ`.
-/

namespace IMOSL
namespace IMO2008C4

open Finset

/-! ### Extra lemmas -/

theorem Fin2_eq_zero_or_one : ∀ a : Fin 2, a = 0 ∨ a = 1
  | 0 => Or.inl rfl | 1 => Or.inr rfl

theorem Fin2_add_add_cancel_right : ∀ a b : Fin 2, a + b + b = a := by decide

theorem Fin2_zero_add : ∀ a : Fin 2, 0 + a = a
  | 0 => rfl | 1 => rfl





/-! ### General structure of functions with finite fiber -/

/-- General structure of functions with finite fiber -/
structure FiniteFiberFn (α β) where
  toFun : α → β
  fiber : β → Finset α
  fiber_spec : ∀ a b, a ∈ fiber b ↔ toFun a = b

namespace FiniteFiberFn

@[ext] lemma ext {X Y : FiniteFiberFn α β} (h : X.toFun = Y.toFun) : X = Y := by
  refine (mk.injEq _ _ _ _ _ _).mpr ⟨h, funext λ p ↦ Finset.ext λ i ↦ ?_⟩
  rw [fiber_spec, fiber_spec, h]

variable (X : FiniteFiberFn α β)

lemma fiber_disjoint_of_ne (h : p ≠ q) : Disjoint (X.fiber p) (X.fiber q) := by
  refine disjoint_iff_ne.mpr λ lp hlp lq hlq h0 ↦ h ?_
  rw [← (X.fiber_spec _ _).mp hlp, ← (X.fiber_spec _ _).mp hlq, h0]

end FiniteFiberFn





/-! ### N-sequences and basic properties -/

/-- Sequences in `S_N` -/
structure NSequence (I Λ) extends FiniteFiberFn I (Fin 2 × Λ) where
  fiber_card_Fin2 : ∀ p, open Fin.NatCast in ((fiber p).card : Fin 2) = p.1


namespace NSequence

variable (s : NSequence I Λ)

abbrev steps : I → Fin 2 × Λ := s.toFun

@[ext] lemma ext {s₁ s₂ : NSequence I Λ} (h : s₁.steps = s₂.steps) : s₁ = s₂ :=
  (mk.injEq _ _ _ _).mpr (FiniteFiberFn.ext h)

lemma fiber_card_mod2 (p) : (s.fiber p).card % 2 = p.1 :=
  congrArg Fin.val (s.fiber_card_Fin2 p)

lemma fiber_card0_mod2 (l) : (s.fiber (0, l)).card % 2 = 0 :=
  s.fiber_card_mod2 (0, l)

lemma fiber_card1_mod2 (l) : (s.fiber (1, l)).card % 2 = 1 :=
  s.fiber_card_mod2 (1, l)

lemma exists_mem_fiber_one (l) : ∃ a, a ∈ s.fiber (1, l) :=
  Multiset.card_pos_iff_exists_mem.mp <|
    Nat.one_pos.trans_le ((s.fiber_card1_mod2 l).symm.trans_le (Nat.mod_le _ _))

lemma card_lamp_le_step [Fintype I] [Fintype Λ] (s : NSequence I Λ) :
    Fintype.card Λ ≤ Fintype.card I := by
  apply Fintype.card_le_of_surjective (λ i ↦ (s.steps i).2) λ l ↦ ?_
  obtain ⟨a, ha⟩ := s.exists_mem_fiber_one l
  exact ⟨a, congrArg Prod.snd ((s.fiber_spec _ _).mp ha)⟩



variable [DecidableEq I] [Fintype I] [Fintype Λ]

noncomputable instance : Fintype (NSequence I Λ) :=
  Fintype.ofInjective steps λ _ _ ↦ ext

instance isEmpty (h : Fintype.card I < Fintype.card Λ) : IsEmpty (NSequence I Λ) :=
  ⟨λ s ↦ h.not_ge s.card_lamp_le_step⟩

end NSequence





/-! ### M-sequences and basic properties -/

/-- Sequences in `S_M` -/
structure MSequence (I Λ) extends FiniteFiberFn I Λ where
  fiber_card_mod2 : ∀ l, (fiber l).card % 2 = 1


namespace MSequence

abbrev steps (s : MSequence I Λ) : I → Λ := s.toFun

@[ext] lemma ext {s₁ s₂ : MSequence I Λ} (h : s₁.steps = s₂.steps) : s₁ = s₂ :=
  (mk.injEq _ _ _ _).mpr (FiniteFiberFn.ext h)

lemma exists_mem_fiber_one (s : MSequence I Λ) (l) : ∃ a, a ∈ s.fiber l :=
  Multiset.card_pos_iff_exists_mem.mp <|
    Nat.one_pos.trans_le ((s.fiber_card_mod2 l).symm.trans_le (Nat.mod_le _ _))

lemma card_lamp_le_step [Fintype I] [Fintype Λ] (s : MSequence I Λ) :
    Fintype.card Λ ≤ Fintype.card I := by
  apply Fintype.card_le_of_surjective s.steps λ l ↦ ?_
  obtain ⟨a, ha⟩ := s.exists_mem_fiber_one l
  exact ⟨a, (s.fiber_spec _ _).mp ha⟩


variable [DecidableEq I] [Fintype I] [Fintype Λ]

noncomputable instance : Fintype (MSequence I Λ) :=
  Fintype.ofInjective steps λ _ _ ↦ ext

instance isEmpty (h : Fintype.card I < Fintype.card Λ) : IsEmpty (MSequence I Λ) :=
  ⟨λ s ↦ h.not_ge s.card_lamp_le_step⟩

end MSequence





/-! ### K-sequences and basic properties -/

/-- Sequences in `S_K` -/
structure KSequence (I Λ) extends FiniteFiberFn I (Fin 2 × Λ) where
  fiber_card_add_mod2 : ∀ l, ((fiber (0, l)).card + (fiber (1, l)).card) % 2 = 1


namespace KSequence

abbrev steps (s : KSequence I Λ) : I → Fin 2 × Λ := s.toFun

@[ext] lemma ext {s₁ s₂ : KSequence I Λ} (h : s₁.steps = s₂.steps) : s₁ = s₂ :=
  (mk.injEq _ _ _ _).mpr (FiniteFiberFn.ext h)

open Fin.NatCast in
lemma fiber_card_add_Fin2 (s : KSequence I Λ)  (l) :
    ((s.fiber (0, l)).card + (s.fiber (1, l)).card : Fin 2) = 1 :=
  Fin.ext ((Nat.add_mod _ _ _).symm.trans (s.fiber_card_add_mod2 l))

open Fin.NatCast in
lemma fiber_card_Fin2 (s : KSequence I Λ) (b l) :
    ((s.fiber (b, l)).card : Fin 2) = (s.fiber (0, l)).card + b := match b with
  | 0 => match ((s.fiber (0, l)).card : Fin 2) with | 0 => rfl | 1 => rfl
  | 1 => by nth_rw 2 [← s.fiber_card_add_Fin2 l]
            generalize ((s.fiber (0, l)).card : Fin 2) = x
            generalize ((s.fiber (1, l)).card : Fin 2) = y
            revert x y; decide


variable [DecidableEq I] [Fintype I] [Fintype Λ]

noncomputable instance : Fintype (KSequence I Λ) :=
  Fintype.ofInjective steps λ _ _ ↦ ext





/-! ### K-sequences and M-sequences -/

def to_MSeq (s : KSequence I Λ) : MSequence I Λ where
  toFun := λ i ↦ (s.steps i).2
  fiber := λ l ↦ s.fiber (0, l) ∪ s.fiber (1, l)
  fiber_spec := λ i l ↦ by
    rw [mem_union, s.fiber_spec, s.fiber_spec, Prod.ext_iff, Prod.ext_iff, ← or_and_right]
    exact and_iff_right (Fin2_eq_zero_or_one _)
  fiber_card_mod2 := λ l ↦ by
    have h : Disjoint (s.fiber (0, l)) (s.fiber (1, l)) :=
      s.fiber_disjoint_of_ne λ h ↦ Fin.zero_ne_one (congrArg Prod.fst h)
    rw [card_union_of_disjoint h, s.fiber_card_add_mod2]

def to_PairMSeqFinset (s : KSequence I Λ) : MSequence I Λ × Finset I :=
  (s.to_MSeq, (univ : Finset Λ).biUnion (λ l ↦ s.fiber (0, l)))

def of_PairMSeqFinset (p : MSequence I Λ × Finset I) : KSequence I Λ where
  toFun := λ i ↦ (if i ∈ p.2 then 0 else 1, p.1.toFun i)
  fiber := λ (b, l) ↦ match b with
    | 0 => p.1.fiber l ∩ p.2
    | 1 => p.1.fiber l \ p.2
  fiber_spec := λ i (b, l) ↦ match b with
    | 0 => by rw [mem_inter, p.1.fiber_spec, and_comm]; simp
    | 1 => by rw [mem_sdiff, p.1.fiber_spec, and_comm]; simp
  fiber_card_add_mod2 := λ l ↦ by
    rw [add_comm, card_sdiff_add_card_inter, p.1.fiber_card_mod2]

def EquivPairMSeqFinset : KSequence I Λ ≃ MSequence I Λ × Finset I where
  toFun := to_PairMSeqFinset
  invFun := of_PairMSeqFinset
  left_inv := λ s ↦ by
    refine ext (funext λ i ↦ Prod.ext ?_ rfl)
    show (if i ∈ univ.biUnion λ l ↦ s.fiber (0, l) then 0 else 1) = (s.steps i).1
    simp only [mem_biUnion, mem_univ, true_and]; split_ifs with h
    · rcases h with ⟨l, h⟩; rw [s.fiber_spec] at h
      exact congrArg Prod.fst h.symm
    · replace h : (s.steps i).1 ≠ 0 := λ h0 ↦ h ⟨(s.steps i).2, by rw [← h0, s.fiber_spec]⟩
      exact (Fin.eq_one_of_ne_zero _ h).symm
  right_inv := λ (s, P) ↦ by
    unfold to_PairMSeqFinset of_PairMSeqFinset
    refine Prod.ext ?_ ?_
    · ext i; rfl
    · show (univ.biUnion λ l ↦ s.fiber l ∩ P) = P
      ext i; simp [s.fiber_spec]

theorem card_wrt_MSeq :
    Fintype.card (KSequence I Λ) = 2 ^ Fintype.card I * Fintype.card (MSequence I Λ) := calc
  _ = Fintype.card (MSequence I Λ × Finset I) := Fintype.card_congr EquivPairMSeqFinset
  _ = _ := by rw [Fintype.card_prod, Nat.mul_comm, Fintype.card_finset]





/-! ### K-sequences and N-sequences -/

open Fin.NatCast in
def to_Fin2 (s : KSequence I Λ) (l : Λ) : Fin 2 := (s.fiber (0, l)).card

open Fin.NatCast in
def to_NSeq (s : KSequence I Λ) : NSequence I Λ where
  toFun := λ i ↦ ((s.toFun i).1 + s.to_Fin2 (s.toFun i).2, (s.toFun i).2)
  fiber := λ (b, l) ↦ s.fiber (b + s.to_Fin2 l, l)
  fiber_spec := λ i (b, l) ↦ by
    simp only [s.fiber_spec, to_Fin2, Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · rintro ⟨h0, rfl⟩; exact ⟨h0 ▸ Fin2_add_add_cancel_right _ _, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨(Fin2_add_add_cancel_right _ _).symm, rfl⟩
  fiber_card_Fin2 := λ (b, l) ↦ by
    rw [s.fiber_card_Fin2, to_Fin2]
    generalize ((s.fiber (0, l)).card : Fin 2) = x
    revert b x; simp only; decide

def to_PairNSeqPi (s : KSequence I Λ) : NSequence I Λ × (Λ → Fin 2) :=
  (s.to_NSeq, s.to_Fin2)

def of_PairNSeqPi (p : NSequence I Λ × (Λ → Fin 2)) : KSequence I Λ where
  toFun := λ i ↦ ((p.1.steps i).1 + p.2 (p.1.steps i).2, (p.1.steps i).2)
  fiber := λ (b, l) ↦ p.1.fiber (b + p.2 l, l)
  fiber_spec := λ i (b, l) ↦ by
    rw [Prod.mk.injEq, p.1.fiber_spec, Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rintro ⟨h0, rfl⟩; exact ⟨h0 ▸ Fin2_add_add_cancel_right _ _, rfl⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨(Fin2_add_add_cancel_right _ _).symm, rfl⟩
  fiber_card_add_mod2 := λ l ↦ by
    simp only; rw [Nat.add_mod, p.1.fiber_card_mod2, p.1.fiber_card_mod2]
    match p.2 l with | 0 => rfl | 1 => rfl

open Fin.NatCast in
def EquivPairNSeqPi : KSequence I Λ ≃ NSequence I Λ × (Λ → Fin 2) where
  toFun := to_PairNSeqPi
  invFun := of_PairNSeqPi
  left_inv := λ s ↦ ext (funext λ i ↦ Prod.ext (Fin2_add_add_cancel_right _ _) rfl)
  right_inv := λ (s, f) ↦ by
    refine Prod.ext (NSequence.ext (funext λ i ↦ Prod.ext ?_ rfl)) (funext λ l ↦ ?_)
    · show (s.toFun i).1 + f (s.toFun i).2 +
        (s.fiber (0 + f (s.toFun i).2, (s.toFun i).2)).card = (s.steps i).1
      rw [Fin2_zero_add, s.fiber_card_Fin2, Fin2_add_add_cancel_right]
    · show ↑(s.fiber (0 + f l, l)).card = f l
      rw [Fin2_zero_add, s.fiber_card_Fin2]

theorem card_wrt_NSeq [DecidableEq Λ] :
    Fintype.card (KSequence I Λ) = 2 ^ Fintype.card Λ * Fintype.card (NSequence I Λ) := calc
  _ = Fintype.card (NSequence I Λ × (Λ → Fin 2)) := Fintype.card_congr EquivPairNSeqPi
  _ = _ := by rw [Fintype.card_prod, Nat.mul_comm, Fintype.card_fun, Fintype.card_fin]

end KSequence





/-! ### Summary -/

variable (I Λ) [DecidableEq I] [Fintype I] [DecidableEq Λ] [Fintype Λ]

theorem card_NSeq_vs_MSeq :
    2 ^ Fintype.card Λ * Fintype.card (NSequence I Λ)
      = 2 ^ Fintype.card I * Fintype.card (MSequence I Λ) := by
  rw [← KSequence.card_wrt_MSeq, ← KSequence.card_wrt_NSeq]

/-- Final solution -/
theorem final_solution :
    Fintype.card (NSequence I Λ) =
      2 ^ (Fintype.card I - Fintype.card Λ) * Fintype.card (MSequence I Λ) := by
  obtain h | h := lt_or_ge (Fintype.card I) (Fintype.card Λ)
  · have h0 := NSequence.isEmpty h
    have h1 := MSequence.isEmpty h
    rw [Fintype.card_of_isEmpty, Fintype.card_of_isEmpty (α := MSequence I Λ), Nat.mul_zero]
  · rw [← Nat.mul_right_inj (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos (Fintype.card Λ))),
      card_NSeq_vs_MSeq, ← Nat.mul_assoc, ← Nat.pow_add, Nat.add_sub_cancel' h]
