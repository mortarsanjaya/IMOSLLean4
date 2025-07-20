/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Prod.Lex

/-!
# IMO 2008 A3

Let $α$ be a totally ordered type.
A Spanish couple on $α$ is a pair of strictly increasing functions $(f, g)$
  from $α$ to itself such that $f ∘ g ∘ g < g ∘ f$.
Determine whether there exists a Spanish couple on:
1. $ℕ$; and
2. $ℕ × ℕ$ (with the lexicographical order).

### Further directions

We are still interested in classifying for which types $α$
  there exists at least one Spanish couple on $α$.
For example, given $f : α → α$ strictly increasing, then
  $(f, f)$ is a Spanish couple if $f < \text{id}_α$.
-/

namespace IMOSL
namespace IMO2008A3

structure SpanishCouple [Preorder α] (f g : α → α) : Prop where
  f_mono : StrictMono f
  g_mono : StrictMono g
  spec : ∀ x, f (g (g x)) < g (f x)





/-! ### Part 1 -/

theorem f_id_not_spanishCouple [Preorder α] [h : Nonempty α] (f : α → α) :
    ¬SpanishCouple f id :=
  λ h0 ↦ h.elim λ x ↦ lt_irrefl (f x) (h0.spec x)

theorem g_iter_lt_f_of_spanishCouple [LinearOrder α]
    (h : ∀ f : α → α, StrictMono f → ∀ x, x ≤ f x) (h0 : SpanishCouple f g) :
    ∀ (k : ℕ) (x : α), (g^[k]) x < f x
  | 0, x => (h f h0.f_mono x).lt_of_ne λ h1 ↦ (h0.spec x).not_ge <|
      (congrArg g h1.symm).trans_le <| (h g h0.g_mono _).trans (h f h0.f_mono _)
  | k + 1, x => h0.g_mono.lt_iff_lt.mp <| (h0.spec x).trans' <|
      (g_iter_lt_f_of_spanishCouple h h0 k _).trans_eq' <|
      (g.iterate_succ_apply' _ _).symm

theorem add_iterate_le_of_strictMono_id_lt (h : StrictMono f) (h0 : x < f x) :
    ∀ k : ℕ, x + k ≤ (f^[k]) x
  | 0 => x.le_refl
  | k + 1 => (Nat.add_succ x k).trans_le <| Nat.succ_le_of_lt <|
      (add_iterate_le_of_strictMono_id_lt h h0 k).trans_lt <| h.iterate k h0

/-- Final solution, part 1 -/
theorem final_solution_part1 (f g : ℕ → ℕ) : ¬SpanishCouple f g :=
  (eq_or_ne g id).elim
  -- Case 1: `g = id`
  (λ h0 ↦ h0.symm ▸ f_id_not_spanishCouple f)
  -- Case 2: `g ≠ id`
  (λ h0 h ↦ (Function.ne_iff.mp h0).elim λ x h0 ↦
    (g_iter_lt_f_of_spanishCouple (λ _ ↦ StrictMono.id_le) h (f x) x).not_ge <|
      ((f x).le_add_left x).trans <| add_iterate_le_of_strictMono_id_lt
        h.g_mono ((h.g_mono.id_le x).lt_of_ne h0.symm) (f x))





/-! ### Part 2 -/

theorem prod_lex_lt_iff [Preorder α] [Preorder β] {p q : α ×ₗ β} :
    p < q ↔ p.1 < q.1 ∨ p.1 = q.1 ∧ p.2 < q.2 :=
  Prod.Lex.lt_iff

/-- Final solution, part 2 (general version) -/
theorem final_solution_part2_general [Preorder β]
    (h : StrictMono φ) (h0 : ∀ x, x < φ x) :
    SpanishCouple (λ p : ℕ ×ₗ β ↦ (p.1.succ, p.2))
      (λ p : ℕ ×ₗ β ↦ (p.1, (φ^[3 ^ p.1]) p.2)) :=
  { f_mono := λ p q h2 ↦ by
      rwa [prod_lex_lt_iff, Nat.succ_lt_succ_iff, Nat.succ_inj, ← prod_lex_lt_iff]
    g_mono := λ p q h2 ↦ by
      rw [prod_lex_lt_iff] at h2 ⊢
      refine h2.imp_right λ h3 ↦ ⟨h3.1, (h.iterate _ h3.2).trans_eq ?_⟩
      simp only; rw [← h3.1]
    spec := λ p ↦ by
      refine prod_lex_lt_iff.mpr <| Or.inr ⟨rfl, ?_⟩
      rw [← Function.iterate_add_apply, ← two_mul, pow_succ']
      exact h.strictMono_iterate_of_lt_map (h0 p.2)
        (Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self 2)
          (Nat.pow_pos (Nat.succ_pos 2))) }

/-- Final solution, part 2 -/
theorem final_solution_part2 :
    SpanishCouple (λ p : ℕ ×ₗ ℕ ↦ (p.1.succ, p.2))
      (λ p : ℕ ×ₗ ℕ ↦ (p.1, p.2 + 3 ^ p.1)) :=
  have h (p : ℕ ×ₗ ℕ) : (p.1, (Nat.succ^[3 ^ p.1]) p.2) = (p.1, p.2 + 3 ^ p.1) :=
    Prod.ext rfl (Nat.succ_iterate _ _)
  (funext h).symm ▸ final_solution_part2_general
    (λ _ _ ↦ Nat.succ_lt_succ) Nat.lt_succ_self
