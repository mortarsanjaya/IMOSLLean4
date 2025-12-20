/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Prod.Lex
import Mathlib.Order.WellFounded

/-!
# IMO 2008 A3

A *Spanish couple* on an ordered set $S$ is a pair of strictly increasing functions
  $(f, g)$ from $S$ to itself such that for any $x ∈ S$,
$$ f(g(g(x))) < g(f(x)). $$
Determine whether there exists a Spanish couple on:
1. $ℕ$, with the usual ordering; and
2. $ℕ × ℕ$, where $(a, b) < (c, d)$ if and only if either $a < c$ or $a = c$ and $b < d$.
(This is the lexicographical order, denoted `ℕ ×ₗ ℕ` in implementation.)

### Answer

1. No.
2. Yes.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2008SL.pdf)
  only for part 1, and we do our own construction for part 2.

In the original problem, part 2 asks for a Spanish couple on the set of real numbers of
  the form $a - 1/b$ for some $a, b ∈ ℕ$, rather than the lexicographic $ℕ × ℕ$.
However, they are order isomorphic, and in fact the isomorphism is obvious,
  since $a - 1/b < c - 1/d$ if and only if either $a < c$ or $a = c$ and $b < d$.
We will not bother with the set $\{a - 1/b : a, b ∈ ℕ\}$.

The construction in the official solution corresponds to constructing a Spanish couple on
  $ℕ × T$ using a strictly increasing function $φ : T → T$ with $φ(x) > x$ for all $x ∈ T$.
It is defined by $f(n, x) = (n + 1, x)$ and $g(n, x) = (n, φ^{3^n}(x))$.
We instead choose $f(n, x) = (2n + 1, x)$ and $g(n, x) = (n, φ^n(x))$.
It is easy to check that this also works.

### Generalization

We can actually determine the existence of Spanish couple on any well-ordered set.
If $S$ is a well-ordered set, then there exists a Spanish couple on $S$ if and only if
  $S$ is order-isomorphic to the lexicographic $T × ℕ × ℕ$ for some well-ordered set.
In terms of ordinals, this is just saying that the ordinal number $o_S$ of $S$
  takes theform $ω^2 o$ for some ordinal $o$, where $ω$ is the ordinal number of $ℕ$.

See `IMOSLLean4/Generalization/IMO2008A3/IM2008A3.lean` for the implementation.
-/

namespace IMOSL
namespace IMO2008A3

/-- A *Spanish couple* on `α` is a pair `(f, g)` of strictly increasing
  functions `α → α` such that `f(g(g(x))) < g(f(x))` for any `x : α`. -/
structure SpanishCouple (α) [Preorder α] where
  f : α → α
  f_strictMono : StrictMono f
  g : α → α
  g_strictMono : StrictMono g
  spec : ∀ x, f (g (g x)) < g (f x)





/-! ### Part 1 -/

namespace SpanishCouple

/-- Given a Spanish couple `(f, g)`, `g` can't be the identity. -/
theorem g_ne_id [hα : Nonempty α] [Preorder α] (X : SpanishCouple α) : X.g ≠ id :=
  hα.elim λ x h ↦ (X.spec x).ne (h ▸ rfl)

/-- If `α` is well-ordered, then `g^k(x) ≤ f(x)` for any `k ∈ ℕ` and `x : α`. -/
theorem g_iter_le_f [LinearOrder α] [WellFoundedLT α] (X : SpanishCouple α) (k x) :
    X.g^[k] x ≤ X.f x := by
  ---- Induction on `k`, but the base case is obvious.
  induction k generalizing x with | zero => exact X.f_strictMono.id_le x | succ k hk => ?_
  /- For induction step, notice that `g^k(x) < f(x)` for all `x` implies
    `g^{k + 2}(x) ≤ f(g^2(x)) < g(f(x))` for all `x`. -/
  have h : X.g (X.g^[k + 1] x) < X.g (X.f x) := calc
    _ = X.g^[k] (X.g (X.g x)) := (X.g.iterate_succ_apply' _ _).symm
    _ ≤ X.f (X.g (X.g x)) := hk _
    _ < X.g (X.f x) := X.spec _
  exact (X.g_strictMono.lt_iff_lt.mp h).le

end SpanishCouple


/-- Final solution, part 1 -/
theorem final_solution_part1 : IsEmpty (SpanishCouple ℕ) := by
  ---- Suppose that there is a Spanish couple `(f, g)` on `ℕ`.
  refine ⟨λ X ↦ ?_⟩
  ---- As we see above, `g ≠ id`, so there exists `n` such that `g(n) > n`.
  obtain ⟨n, hn⟩ : ∃ n, n < X.g n := by
    by_contra! h; exact X.g_ne_id (funext λ n ↦ (h n).antisymm (X.g_strictMono.id_le n))
  ---- By induction, for any `k ∈ ℕ`, we have `n + k ≤ g^k(n)`.
  replace hn : ∀ k, n + k ≤ X.g^[k] n :=
    Nat.rec n.le_refl λ k hk ↦ hk.trans_lt (X.g_strictMono.iterate k hn)
  ---- But `g^k(n) ≤ f(n)` for all `k`; contradiction.
  exact (X.g_iter_le_f (X.f n + 1) n).not_gt (Nat.le_of_add_left_le (hn _))





/-! ### Part 2 -/

/-- Construct a function on `α × β` from a function on `α` and an `α`-indexed
  collection of function son `β`. For naming reasons, compare to `Equiv.prodShear`. -/
def ProdShear (f : α → α) (g : α → β → β) (p : α × β) : α × β :=
  (f p.1, g p.1 p.2)

/-- Construct a strictly increasing function on `α ×ₗ β` from a strictly increasing
  function on `α` and an `α`-indexed collection of strictly increasing functions on `β`. -/
theorem ProdShearLex_strictMono [Preorder α] [Preorder β]
    {f : α → α} (hf : StrictMono f) {g : α → β → β} (hg : ∀ a : α, StrictMono (g a)) :
    StrictMono (toLex.conj (ProdShear f g)) := by
  refine Lex.rec λ (a₁, b₁) ↦ Lex.rec λ (a₂, b₂) ↦ ?_
  rw [Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  change (a₁ < a₂ ∨ a₁ = a₂ ∧ b₁ < b₂) → (f a₁ < f a₂ ∨ f a₁ = f a₂ ∧ g a₁ b₁ < g a₂ b₂)
  exact Or.imp (λ h ↦ hf h) (λ h ↦ h.1 ▸ ⟨rfl, hg _ h.2⟩)

/-- Construct a strictly increasing function on `α ×ₗ β` from a
  strictly increasing function on `α`, using identity on `β`. -/
theorem ProdMapLex_strictMono [Preorder α] [Preorder β]
    {f : α → α} {g : β → β} (hf : StrictMono f) (hg : StrictMono g) :
    StrictMono (toLex.conj (Prod.map f g)) :=
  ProdShearLex_strictMono hf λ _ ↦ hg

/-- Constructing a Spanish Couple `(f, g)` on `ℕ ×ₗ α` from a
  strictly increasing function `φ : α → α` with `φ(x) > x` for all `x`.
  It is defined by `f(n, a) = (2n + 1, a)` and `g(n, a) = (n, φ^n(a))`. -/
def SpanishCouple_NatLex_of_strictMono_id_lt
    [Preorder α] {φ : α → α} (hφ : StrictMono φ) (hφ0 : ∀ x, x < φ x) :
    SpanishCouple (ℕ ×ₗ α) where
  f := toLex.conj (Prod.map (2 * · + 1) id)
  f_strictMono :=
    ProdMapLex_strictMono
      (λ k m h ↦ Nat.succ_lt_succ (Nat.mul_lt_mul_of_pos_left h Nat.two_pos))
      strictMono_id
  g := toLex.conj (ProdShear id (φ^[·]))
  g_strictMono := ProdShearLex_strictMono strictMono_id hφ.iterate
  spec := by
    ---- We only need to prove that `φ^{2n}(x) < φ^{2n + 1}(x)` for any `n` and `x`.
    refine Lex.rec λ (n, x) ↦ Prod.Lex.lt_iff.mpr (Or.inr ⟨rfl, ?_⟩)
    calc φ^[n] (φ^[n] x)
    _ = φ^[2 * n] x := by rw [Nat.two_mul, φ.iterate_add_apply]
    _ < φ^[2 * n + 1] x := hφ.iterate (2 * n) (hφ0 x)

/-- Final solution, part 2 -/
def final_solution_part2 : SpanishCouple (ℕ ×ₗ ℕ) :=
  SpanishCouple_NatLex_of_strictMono_id_lt (λ _ _ ↦ Nat.succ_lt_succ) Nat.lt_succ_self
