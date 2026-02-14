/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Positive.Ring

/-!
# IMO 2007 A4

Let $G$ be a totally ordered abelian group, and denote $G_{>0} = \{x ∈ G : x > 0\}$.
Find all functions $f : G_{>0} → G_{>0}$ such that for any $x, y ∈ G_{>0}$,
$$ f(x + f(y)) = f(x + y) + f(y). $$

### Answer

$f(x) = 2x$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2007SL.pdf).
-/

namespace IMOSL
namespace IMO2007A4

variable {G} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
local notation "G>0" => {x : G // 0 < x}

/-- If `x < y`, then there exists `t` such that `t + x = y`. -/
theorem exists_add_of_lt {x y : G>0} (h : x < y) : ∃ t, t + x = y :=
  ⟨⟨y.1 - x.1, sub_pos_of_lt h⟩, Subtype.ext (sub_add_cancel _ _)⟩

/-- Final solution -/
theorem final_solution {f : G>0 → G>0} :
    (∀ x y, f (x + f y) = f (x + y) + f y) ↔ ∀ x, f x = x + x := by
  ---- The `←` direction is straightforward.
  refine Iff.symm ⟨λ hf ↦ ?_, λ hf ↦ ?_⟩
  · intro x y; rw [hf, hf, hf, add_add_add_comm, add_add_add_comm x y, ← add_assoc]
  ---- For `→`, first write `f(x) = g(x) + x` for some `g : G_{>0} → G_{>0}`.
  obtain ⟨g, rfl⟩ : ∃ g : G>0 → G>0, g + id = f := by
    -- It reduces to showing `f(y) > y` for all `y : G_{>0}`.
    suffices ∀ y, y < f y
      from ⟨λ x ↦ ⟨f x - x, sub_pos_of_lt (this x)⟩,
        funext λ x ↦ Subtype.ext (sub_add_cancel _ _)⟩
    -- Now split into three cases.
    intro y
    obtain hy | hy | hy : y < f y ∨ y = f y ∨ f y < y := lt_trichotomy _ _
    -- Case 1: `y < f(y)`.
    · exact hy
    -- Case 2: `f(y) = y`.
    · absurd lt_irrefl (f (y + y))
      calc f (y + y)
        _ < f (y + y) + f y := lt_add_of_pos_right _ (f y).2
        _ = f (y + y) := by rw [← hf, ← hy]
    -- Case 3: `f(y) < y`.
    · let x : {x : G // 0 < x} := ⟨y - f y, sub_pos.mpr hy⟩
      have h : f y < f (x + f y) := calc
        _ < f (x + y) + f y := lt_add_of_pos_left _ (f _).2
        _ = f (x + f y) := (hf x y).symm
      exact absurd (congrArg f (Subtype.ext (sub_add_cancel _ _))) h.ne.symm
  ---- Now the original FE reads as `g(t + g(y)) = g(t) + y` whwnever `t > y`.
  replace hf {t y : G>0} (h : y < t) : g (t + g y) = g t + y := by
    obtain ⟨u, rfl⟩ : ∃ u, u + y = t := exists_add_of_lt h
    replace hf : g (u + (g y + y)) + (u + (g y + y))
        = g (u + y) + (u + y) + (g y + y) := hf u y
    rwa [← add_assoc, add_left_inj, add_comm _ y, ← add_assoc,
      ← add_assoc, add_right_comm _ u, add_left_inj] at hf
  rename ∀ {t y}, y < t → g (t + g y) = g t + y => hg
  ---- Next, show that `g` is injective.
  have hg0 : g.Injective := by
    intro x y h
    -- First find `t > max{x, y}`.
    obtain ⟨t, htx, hty⟩ : ∃ t > x, t > y :=
      ⟨x + y, lt_add_of_pos_right _ y.2, lt_add_of_pos_left _ x.2⟩
    -- Now prove `x = y` via `g(t) + x = g(t) + y`.
    rw [← add_right_inj (g t), ← hg htx, h, hg hty]
  ---- Now show that `g` is additive.
  have hg1 (x y) : g (x + y) = g x + g y := by
    -- First find `t > x + y`.
    obtain ⟨t, ht⟩ : ∃ t, t > x + y := ⟨x + y + x, lt_add_of_pos_right _ x.2⟩
    -- Then obtain `g(t + g(x + y)) = g(t + g(x) + g(y))`.
    have h : g (t + g (x + y)) = g (t + (g x + g y)) := by
      have htx : x < t := ht.trans' (lt_add_of_pos_right _ y.2)
      have hty : y < t + g x := calc
        y < x + y := lt_add_of_pos_left _ x.2
        _ < t := ht
        _ < t + g x := lt_add_of_pos_right _ (g x).2
      rw [hg ht, ← add_assoc, ← hg htx, ← hg hty, add_assoc]
    -- By injectivity of `g`, we are done.
    exact add_right_injective t (hg0 h)
  ---- Then the original FE simplifies to `g(g(t)) = t`.
  replace hg (t) : g (g t) = t := by
    rw [← add_right_inj (g (t + t)), ← hg1]
    exact hg (lt_add_of_pos_right _ t.2)
  ---- Additivity implies that `g` is (strictly) monotone.
  replace hg1 : StrictMono g := by
    intro x y h
    obtain ⟨t, rfl⟩ : ∃ t, t + x = y := exists_add_of_lt h
    calc g x
      _ < g t + g x := lt_add_of_pos_left _ (g t).2
      _ = g (t + x) := (hg1 t x).symm
  ---- Now split using trichotomy and do each cases one by one.
  intro x; obtain hx | hx | hx : g x < x ∨ g x = x ∨ x < g x := lt_trichotomy _ _
  exacts [absurd (hg x) ((hg1 hx).trans hx).ne, congrArg (· + x) hx,
    absurd (hg x) (hx.trans (hg1 hx)).ne.symm]
