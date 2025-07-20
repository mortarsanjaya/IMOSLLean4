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
Fix a word $w ∈ L$, and let $w'$ denote the reversal of $w$.
Prove that $f(w') = f(w)$.
-/

namespace IMOSL
namespace IMO2009C3

open List

/-! ### Over-generalization -/

def g (k m : α → Nat) : Nat × Nat → List α → Nat × Nat :=
  foldr (λ a (x, y) ↦ (y, k a * x + m a * y))

theorem g_nil (k m : α → Nat) (p) : g k m p [] = p := rfl

theorem g_cons (k m : α → Nat) (p a l) :
    g k m p (a :: l) = ((g k m p l).2, k a * (g k m p l).1 + m a * (g k m p l).2) := rfl

theorem g_singleton (k m : α → Nat) (p a) :
    g k m p [a] = (p.2, k a * p.1 + m a * p.2) := rfl

theorem g_cons₁ (k m : α → Nat) (p a l) : (g k m p (a :: l)).1 = (g k m p l).2 := rfl

theorem g_cons₂ (k m : α → Nat) (p a l) :
    (g k m p (a :: l)).2 = k a * (g k m p l).1 + m a * (g k m p l).2 := rfl

theorem g_add (k m : α → Nat) (x y z w) :
    ∀ l, (g k m (x + y, z + w) l).1 = (g k m (x, z) l).1 + (g k m (y, w) l).1 ∧
      (g k m (x + y, z + w) l).2 = (g k m (x, z) l).2 + (g k m (y, w) l).2 := by
  refine List.rec ⟨rfl, rfl⟩ λ a l h ↦ ⟨h.2, ?_⟩
  rw [g_cons₂, g_cons₂, g_cons₂, Nat.add_add_add_comm,
    ← Nat.mul_add, ← Nat.mul_add, h.1, h.2]

theorem g_add₁ (k m : α → Nat) (x y z w l) :
    (g k m (x + y, z + w) l).1 = (g k m (x, z) l).1 + (g k m (y, w) l).1 :=
  (g_add k m x y z w l).1

theorem g_add₂ (k m : α → Nat) (x y z w l) :
    (g k m (x + y, z + w) l).2 = (g k m (x, z) l).2 + (g k m (y, w) l).2 :=
  (g_add k m x y z w l).2

theorem g_mul (k m : α → Nat) (c x y) :
    ∀ l, (g k m (c * x, c * y) l).1 = c * (g k m (x, y) l).1 ∧
      (g k m (c * x, c * y) l).2 = c * (g k m (x, y) l).2 := by
  refine List.rec ⟨rfl, rfl⟩ λ a l h ↦ ⟨h.2, ?_⟩
  rw [g_cons₂, g_cons₂, h.1, h.2, c.mul_add, c.mul_left_comm, c.mul_left_comm]

theorem g_mul₁ (k m : α → Nat) (c x y l) :
    (g k m (c * x, c * y) l).1 = c * (g k m (x, y) l).1 :=
  (g_mul k m c x y l).1

theorem g_mul₂ (k m : α → Nat) (c x y l) :
    (g k m (c * x, c * y) l).2 = c * (g k m (x, y) l).2 :=
  (g_mul k m c x y l).2

theorem g_append (k m : α → Nat) (p l₁ l₂) :
    g k m p (l₁ ++ l₂) = g k m (g k m p l₂) l₁ :=
  foldr_append

theorem g_append_singleton (k m : α → Nat) (p a l) :
    g k m p (l ++ [a]) = g k m (p.2, k a * p.1 + m a * p.2) l :=
  foldr_append

/-- The main theorem on `g` -/
theorem g_reverse {k m : α → Nat} (h : ∀ a, k a * X + m a * Y = Z) :
    ∀ l : List α, (g k m (Y, Z) l.reverse).2 = (g k m (Y, Z) l).2
  | [] => rfl
  | [a] => rfl
  | b :: a :: l => calc
      _ = (g k m (k b * X + m b * Y, k b * Y + m b * Z) (a :: l).reverse).2 := by
        rw [reverse_cons, g_append_singleton, ← h b]
      _ = k b * (g k m (Y, Z) l.reverse).2 + m b * (g k m (Y, Z) (a :: l).reverse).2 := by
        rw [g_add₂, g_mul₂, g_mul₂, reverse_cons, g_append_singleton, h]
      _ = k b * (g k m (Y, Z) l).2 + m b * (g k m (Y, Z) (a :: l)).2 := by
        rw [g_reverse h l, g_reverse h (a :: l)]






/-! ### The original problem -/

def f : List Bool → Nat × Nat :=
  foldr (λ a (x, y) ↦ (y, match a with | false => 2 * x + 3 * y | true => 3 * x + y)) (1, 7)

theorem f_eq_g : f = g (Bool.rec 2 3) (Bool.rec 3 1) (1, 7) :=
  congrArg (foldr · (1, 7)) (funext (Bool.rec rfl (by simp only [Nat.one_mul])))

/-- Final solution -/
theorem final_solution : ∀ l, (f l.reverse).2 = (f l).2 :=
  f_eq_g ▸ g_reverse (X := 2) (Bool.rec rfl rfl)
