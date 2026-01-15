/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

/-!
# IMO 2009 C3

Let $\{0, 1\}^*$ denote the set of finite-length binary words with letters $0$ and $1$.
Let $ε$ denote the empty word.

Define the function $f : \{0, 1\}^* → ℕ$ recursively by $f(ε) = 1$, $f(0) = f(1) = 7$, and
$$ f(wa0) = 2 f(wa) + 3 f(w) ∧ f(wa1) = 3 f(wa) + f(w). $$
Prove that for any word $w ∈ \{0, 1\}^*$, we have $f(\overline{w}) = f(w)$,
  where $\overline{w}$ denotes the reversal of $w$.

### Generalized problem

Let $Γ$ be a set of alphabets.
For each $i ∈ Γ$, let $k_i$ and $m_i$ be non-negative integers.
Let $X, Y, Z$ be non-negative integers such that $k_i X + m_i Y = Z$ for each $i ∈ Γ$.

Let $Γ^*$ denote the set of finite-length words with letter set $Γ$.
Define the functions $g_1, g_2 : Γ → ℕ$ by $(g_1(ε), g_2(ε)) = (X, Y)$ and
$$ (g_1(wi), g_2(wi)) = (g_2(w), k_i g_1(w) + m_i g_2(w)) $$
  for each $w ∈ Γ^*$ and $i ∈ Γ$.
Prove that $g_2(\overline{w}) = g_2(w)$ for each $w ∈ Γ^*$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
The original statement follows from the general statement by picking $Γ = \{0, 1\}$
  and $(k_0, k_1, m_0, m_1, X, Y, Z) = (2, 3, 3, 1, 2, 1, 7)$.
-/

namespace IMOSL
namespace IMO2009C3

open List

/-! ### Generalized problem -/

/-- The function `g = (g_1, g_2)`. -/
def g (k m : Γ → Nat) : Nat × Nat → List Γ → Nat × Nat :=
  foldr (λ i (x, y) ↦ (y, k i * x + m i * y))

/-- The formula `g_2(wi) = k_i g_1(w) + m_i g_2(w)`. -/
theorem g_cons₂ (k m : Γ → Nat) (p i l) :
    (g k m p (i :: l)).2 = k i * (g k m p l).1 + m i * (g k m p l).2 := rfl

/-- The function `g` with starting point `(x + y, z + w)` is the sum of
  the two functions `g` with starting point `(x, z)` and `(y, w)`. -/
theorem g_add (k m : Γ → Nat) (x y z w) :
    ∀ l, (g k m (x + y, z + w) l).1 = (g k m (x, z) l).1 + (g k m (y, w) l).1 ∧
      (g k m (x + y, z + w) l).2 = (g k m (x, z) l).2 + (g k m (y, w) l).2 := by
  refine List.rec ⟨rfl, rfl⟩ λ a l h ↦ ⟨h.2, ?_⟩
  rw [g_cons₂, g_cons₂, g_cons₂, Nat.add_add_add_comm,
    ← Nat.mul_add, ← Nat.mul_add, h.1, h.2]

/-- The second coordinate of `g_add`. -/
theorem g_add₂ (k m : Γ → Nat) (x y z w l) :
    (g k m (x + y, z + w) l).2 = (g k m (x, z) l).2 + (g k m (y, w) l).2 :=
  (g_add k m x y z w l).2

/-- The function `g` with starting point `(cx, cy)` is
  `c` times the function `g` with starting point `(x, y)`. -/
theorem g_mul (k m : Γ → Nat) (c x y) :
    ∀ l, (g k m (c * x, c * y) l).1 = c * (g k m (x, y) l).1 ∧
      (g k m (c * x, c * y) l).2 = c * (g k m (x, y) l).2 := by
  refine List.rec ⟨rfl, rfl⟩ λ a l h ↦ ⟨h.2, ?_⟩
  rw [g_cons₂, g_cons₂, h.1, h.2, c.mul_add, c.mul_left_comm, c.mul_left_comm]

/-- The second coordinate of `g_mul`. -/
theorem g_mul₂ (k m : Γ → Nat) (c x y l) :
    (g k m (c * x, c * y) l).2 = c * (g k m (x, y) l).2 :=
  (g_mul k m c x y l).2

/-- A formula for `g(iw)`. -/
theorem g_append_singleton (k m : Γ → Nat) (p i l) :
    g k m p (l ++ [i]) = g k m (p.2, k i * p.1 + m i * p.2) l :=
  foldr_append

/-- The main theorem on `g`. -/
theorem g_reverse {k m : Γ → Nat} (h : ∀ i, k i * X + m i * Y = Z) :
    ∀ l : List Γ, (g k m (Y, Z) l.reverse).2 = (g k m (Y, Z) l).2
  | [] => rfl
  | [i] => rfl
  | j :: i :: l => calc
      _ = (g k m (k j * X + m j * Y, k j * Y + m j * Z) (i :: l).reverse).2 := by
        rw [reverse_cons, g_append_singleton, ← h j]
      _ = k j * (g k m (Y, Z) l.reverse).2 + m j * (g k m (Y, Z) (i :: l).reverse).2 := by
        rw [g_add₂, g_mul₂, g_mul₂, reverse_cons, g_append_singleton, h]
      _ = k j * (g k m (Y, Z) l).2 + m j * (g k m (Y, Z) (i :: l)).2 := by
        rw [g_reverse h l, g_reverse h (i :: l)]





/-! ### The original problem -/

/-- The function `f`. -/
def f : List Bool → Nat × Nat :=
  foldr (λ i (x, y) ↦ (y, match i with | false => 2 * x + 3 * y | true => 3 * x + y)) (1, 7)

/-- Expressing `f` as `g` with `(k_0, k_1, m_0, m_1, X, Y, Z) = (2, 3, 3, 1, 2, 1, 7)`. -/
theorem f_eq_g : f = g (Bool.rec 2 3) (Bool.rec 3 1) (1, 7) :=
  congrArg (foldr · (1, 7)) (funext (Bool.rec rfl (by simp only [Nat.one_mul])))

/-- Final solution -/
theorem final_solution : ∀ l, (f l.reverse).2 = (f l).2 :=
  f_eq_g ▸ g_reverse (X := 2) (Bool.rec rfl rfl)
