import Mathlib.Data.Nat.Basic
import Mathlib.Order.Monotone.Basic

/-!
# Maximum element in a sequence

Let `α` be a linear ordered type and `f : ℕ → α` be a sequence.
We construct the sequence `g : ℕ → α` defined by
  `g(n) = max{f(0), f(1), ..., f(n)}` for each `n : ℕ`.
We also prove some of its properties.
-/

namespace IMOSL
namespace Extra

variable [LinearOrder α] (f : ℕ → α)

def seqMax : ℕ → α
  | 0 => f 0
  | n + 1 => max (seqMax n) (f n.succ)

theorem le_seqMax_self : ∀ n, f n ≤ seqMax f n
  | 0 => le_refl (f 0)
  | n + 1 => le_max_right (seqMax f n) (f n.succ)

theorem seqMax_mono : Monotone (seqMax f) :=
  monotone_nat_of_le_succ λ n ↦ le_max_left (seqMax f n) (f n.succ)

theorem le_seqMax_of_le {m n : ℕ} (h : m ≤ n) : f m ≤ seqMax f n :=
  (le_seqMax_self f m).trans (seqMax_mono f h)

theorem map_zero_le_seqMax (n : ℕ) : f 0 ≤ seqMax f n :=
  le_seqMax_of_le f n.zero_le

theorem exists_map_eq_seqMax : ∀ n : ℕ, ∃ k : ℕ, k ≤ n ∧ f k = seqMax f n
  | 0 => ⟨0, le_refl 0, rfl⟩
  | n + 1 => by
      rcases le_total (seqMax f n) (f n.succ) with h | h
      · exact ⟨n + 1, le_refl (n + 1), (max_eq_right h).symm⟩
      · rcases exists_map_eq_seqMax n with ⟨k, h0, h1⟩
        exact ⟨k, n.le_succ.trans' h0, h1.trans (max_eq_left h).symm⟩
