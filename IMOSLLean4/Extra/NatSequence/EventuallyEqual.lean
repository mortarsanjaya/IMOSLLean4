/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

/-!
# Eventually equal sequence

Let `(a_n)`, `(b_n)` be two `ℕ`-indexed sequences.
We say that they are *eventually equal* if there exists `N_a, N_b : ℕ`
  such that `a_{N_a + k} = b_{N_b + k}` for all `k : ℕ`.
We show that this relation is an equivalence class.
-/

namespace IMOSL
namespace Extra

def EventuallyEqual (a b : Nat → α) := ∃ N_a N_b, ∀ k, a (k + N_a) = b (k + N_b)


namespace EventuallyEqual

theorem refl (a : Nat → α) : EventuallyEqual a a := ⟨0, 0, λ _ ↦ rfl⟩

theorem symm (h : EventuallyEqual a b) : EventuallyEqual b a := by
  rcases h with ⟨N_a, N_b, h⟩; exact ⟨N_b, N_a, λ k ↦ (h k).symm⟩

theorem trans (h : EventuallyEqual a b) (h0 : EventuallyEqual b c) :
    EventuallyEqual a c := by
  rcases h with ⟨N_a, N_b, h⟩
  rcases h0 with ⟨K_b, K_c, h0⟩
  refine ⟨K_b + N_a, K_c + N_b, λ k ↦ ?_⟩
  rw [← Nat.add_assoc, h, Nat.add_right_comm, h0, Nat.add_right_comm, Nat.add_assoc]

theorem isEquivalence {α : Type _} : Equivalence (EventuallyEqual (α := α)) :=
  ⟨refl, symm, trans⟩

theorem of_shift (a : Nat → α) (N : Nat) : EventuallyEqual a (λ k ↦ a (k + N)) :=
  ⟨N, 0, λ _ ↦ rfl⟩

theorem const_right_iff {a : Nat → α} (c : α) :
    EventuallyEqual a (λ _ ↦ c) ↔ ∃ N, ∀ k, a (k + N) = c :=
  ⟨λ ⟨N, _, h⟩ ↦ ⟨N, h⟩, λ ⟨N, h⟩ ↦ ⟨N, 0, h⟩⟩
