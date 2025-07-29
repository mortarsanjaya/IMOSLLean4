/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Prod.Lex
import Mathlib.Order.Hom.Basic
import Mathlib.Order.Iterate
import Mathlib.Order.WellFounded

/-!
# IMO 2008 A3

Let $S$ be a totally ordered set.
A *Spanish couple* on $S$ is a pair of strictly increasing functions $(f, g)$
  from $S$ to itself such that for any $x ∈ S$,
$$ f(g(g(x))) < g(f(x)). $$
Determine whether there exists a Spanish couple on:
1. $ℕ$; and
2. $ℕ × ℕ$, where $(a, b) < (c, d)$ if and only if either $a < c$ or $a = c$ and $b < d$.
(This is the lexicographical order, denoted `ℕ ×ₗ ℕ` in implementation.)

### Answer

1. No.
2. Yes.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2008SL.pdf).

In the original problem, part 2 asks for a Spanish couple on the set of real numbers of
  the form $a - 1/b$ for some $a, b ∈ ℕ$, rather than the lexicographic $ℕ × ℕ$.
However, they are order isomorphic, and in fact the isomorphism is obvious,
  since $a - 1/b < c - 1/d$ if and only if either $a < c$ or $a = c$ and $b < d$.
We will not bother with the set $\{a - 1/b : a, b ∈ ℕ\}$.
The construction in the official solution corresponds to constructing a
  Spanish couple on $ℕ × T$ using a strictly increasing function $φ : T → T$
  such that $φ(x) > x$ for all $x ∈ T$.

We define strictly increasing functions using the more general `OrderEmbedding`.

### Generalization

If $S$ is a well-ordered set, then it is possible to determine whether there exists a
  Spanish couple on $S$: this is true if and only if $S$ is order-isomorphic to
  $T × ℕ × ℕ$ for some well-ordered set, with lexicographical order prioritizing $T$.
In terms of ordinals, this is just saying that $S = ℕ^2 T$.

See `IMOSLLean4/Generalization/IMO2008A3/IM2008A3.lean` for the implementation.
We also prove some other interesting properties.

### TODO

Implement the generalization.
Other than that, look for code improvements for Part 2, if possible.
-/

namespace IMOSL
namespace IMO2008A3

/-- A *Spanish couple* on `α` is a pair `(f, g)` of order embeddings `α ↪o α`
  such that `f(g(g(x))) < g(f(x))` for any `x : α`. -/
structure SpanishCouple (α) [Preorder α] where
  f : α ↪o α
  g : α ↪o α
  spec : ∀ x, f (g (g x)) < g (f x)





/-! ### Part 1 -/

namespace SpanishCouple

/-- Given a Spanish couple `(f, g)`, `g` can't be the identity. -/
theorem g_ne_id [hα : Nonempty α] [Preorder α] (X : SpanishCouple α) :
    X.g ≠ RelEmbedding.refl _ :=
  hα.elim λ x h ↦ (X.spec x).ne (h ▸ rfl)

/-- If `α` is well-ordered, then `g^k(x) ≤ f(x)` for any `k ∈ ℕ` and `x : α`. -/
theorem g_iter_le_f [LinearOrder α] [WellFoundedLT α] (X : SpanishCouple α) (k x) :
    X.g^[k] x ≤ X.f x := by
  ---- Induction on `k`, but the base case is obvious.
  induction k generalizing x with | zero => exact X.f.strictMono.id_le x | succ k hk => ?_
  /- For induction step, notice that `g^k(x) < f(x)` for all `x` implies
    `g^{k + 2}(x) ≤ f(g^2(x)) < g(f(x))` for all `x`. -/
  have h : X.g (X.g^[k + 1] x) < X.g (X.f x) := calc
    _ = X.g^[k] (X.g (X.g x)) := (X.g.toFun.iterate_succ_apply' _ _).symm
    _ ≤ X.f (X.g (X.g x)) := hk _
    _ < X.g (X.f x) := X.spec _
  exact (X.g.lt_iff_lt.mp h).le

end SpanishCouple


/-- Final solution, part 1 -/
theorem final_solution_part1 : IsEmpty (SpanishCouple ℕ) := by
  ---- Suppose that there is a Spanish couple `(f, g)` on `ℕ`.
  refine ⟨λ X ↦ ?_⟩
  ---- As we see above, `g ≠ id`, so there exists `n` such that `g(n) > n`.
  obtain ⟨n, hn⟩ : ∃ n, n < X.g n := by
    by_contra! h
    exact X.g_ne_id (RelEmbedding.ext λ n ↦ (h n).antisymm (X.g.strictMono.id_le n))
  ---- By induction, for any `k ∈ ℕ`, we have `n + k ≤ g^k(n)`.
  replace hn : ∀ k, n + k ≤ X.g^[k] n :=
    Nat.rec n.le_refl λ k hk ↦ hk.trans_lt (X.g.strictMono.iterate k hn)
  ---- But `g^k(n) ≤ f(n)` for all `k`; contradiction.
  exact (X.g_iter_le_f (X.f n + 1) n).not_gt (Nat.le_of_add_left_le (hn _))





/-! ### Part 2 -/

/-- The successor function on `ℕ` as an order embedding.
  TODO: Remove this once you see this in `mathlib`. -/
def NatSuccOrderEmbedding : OrderEmbedding ℕ ℕ where
  toFun := Nat.succ
  inj' := Nat.succ_injective
  map_rel_iff' := Nat.succ_le_succ_iff

/-- Create an order embedding from `α ×ₗ β` to itself using order embedding `α ↪o α`
  and collections of order embeddings `β ↪o β` indexed by `α`.
  TODO: Remove this once you see this in `mathlib`; see`RelEmbedding.prodLexMap` too. -/
def OrderEmbedding_prodLex [Preorder α] [Preorder β] (φ : α ↪o α) (ψ : α → (β ↪o β)) :
    (α ×ₗ β) ↪o (α ×ₗ β) where
  toFun x := match ofLex x with | (a, b) => toLex (φ a, ψ a b)
  inj' := λ a b h ↦
    have h0 : φ a.1 = φ b.1 ∧ ψ a.1 a.2 = ψ b.1 b.2 := Prod.ext_iff.mp h
    have h1 : a.1 = b.1 := φ.inj.mp h0.1
    Prod.ext_iff.mpr ⟨h1, (ψ _).inj.mp (h1 ▸ h0.2)⟩
  map_rel_iff' := by
    intro a₁ a₂
    simp only [Prod.Lex.le_iff, Function.Embedding.coeFn_mk]
    refine or_congr φ.lt_iff_lt ?_
    simp only [φ.inj, ofLex_toLex]
    exact and_congr_right λ h ↦ h ▸ (ψ _).le_iff_le

/-- Iteration of a `RelEmbedding`. TODO: Remove this once you see this in `mathlib`.
  Quite likely, it will be in `Mathlib.Algebra.Order.Group.End`. -/
@[simps apply]
def RelEmbedding_iterate {α} {r : α → α → Prop} (φ : r ↪r r) (k : ℕ) : r ↪r r where
  toFun := φ^[k]
  inj' := φ.inj'.iterate k
  map_rel_iff' := by revert k; exact Nat.rec Iff.rfl (λ k hk _ _ ↦ hk.trans φ.map_rel_iff)

/-- Constructing a `SpanishCouple` on `ℕ ×ₗ α` from `φ : α ↪o α` with `φ(x) > x` for all `x`.
  It is defined by `f(n, a) = (n + 1, a)` and `g(n, a) = (n, φ^{3^n}(a))`. -/
def SpanishCouple_NatLex_of_OrderEmbedding_id_lt
    [Preorder α] (φ : α ↪o α) (hφ : ∀ x, x < φ x) :
    SpanishCouple (ℕ ×ₗ α) where
  f := OrderEmbedding_prodLex NatSuccOrderEmbedding (λ _ ↦ RelEmbedding.refl _)
  g := OrderEmbedding_prodLex (RelEmbedding.refl _) (λ n ↦ RelEmbedding_iterate φ (3 ^ n))
  spec := by
    rintro ⟨k, x⟩
    refine Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, ?_⟩)
    calc φ^[3 ^ k] (φ^[3 ^ k] x)
      _ = φ^[3 ^ k * 2] x := by rw [Nat.mul_two, Function.iterate_add_apply]
      _ < φ^[3 ^ (k + 1)] x := φ.strictMono.strictMono_iterate_of_lt_map (hφ x)
        (Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self 2) (Nat.pow_pos (Nat.succ_pos 2)))

/-- Final solution, part 2 -/
def final_solution_part2 : SpanishCouple (ℕ ×ₗ ℕ) :=
  SpanishCouple_NatLex_of_OrderEmbedding_id_lt NatSuccOrderEmbedding Nat.lt_succ_self
