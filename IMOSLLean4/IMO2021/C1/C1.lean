/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Fintype.Pigeonhole

/-!
# IMO 2021 C1

Consider a complete graph with an infinite vertex set $V$.
Each edge $xy$ is coloured such that for each vertex $v$, there exists only
  finitely many colours assigned to an edge incident with $v$.
Prove that if some of the edges has distinct colours, then there exists
  $x, y, z ∈ V$, pairwise distinct, such that $c_{xy} = c_{xz} ≠ c_{yz}$.
-/

namespace IMOSL
namespace IMO2021C1

/-- Structure for colouring with "finite incidence colours". -/
structure FiniteIncidenceColouring (V α : Type*) where
  colour : V → V → α
  colour_symm (x y : V) : colour x y = colour y x
  incidence_finite (v : V) : Finite (Set.range (colour v))

variable [Infinite V] (C : FiniteIncidenceColouring V α)

theorem monochromatic_of_triangle
    (h : ∀ {x y z}, y ≠ z → C.colour x y = C.colour x z → C.colour y z = C.colour x z) :
    ∃ c : α, ∀ x y : V, x ≠ y → C.colour x y = c := by
  obtain ⟨v₀⟩ : Nonempty V := Infinite.nonempty V
  ---- First find `c : α` such that infinitely many edges incident with `v₀` has colour `c`.
  obtain ⟨c, hc⟩ : ∃ c : α, Infinite { x // C.colour v₀ x = c } := by
    have hv₀ := C.incidence_finite v₀
    let f (v : V) : Set.range (C.colour v₀) := ⟨C.colour v₀ v, v, rfl⟩
    obtain ⟨⟨c, _⟩, hc⟩ := Finite.exists_infinite_fiber f
    exact ⟨c, by simpa [f, Set.preimage] using hc⟩
  ---- Reduce to showing that edges incident with `v₀` has colour `c`.
  suffices ∀ v ≠ v₀, C.colour v₀ v = c by
    refine ⟨c, λ x y h0 ↦ ?_⟩
    obtain rfl | hx : x = v₀ ∨ x ≠ v₀ := eq_or_ne x v₀
    · exact this y h0.symm
    obtain rfl | hy : y = v₀ ∨ y ≠ v₀ := eq_or_ne y v₀
    · exact (C.colour_symm x y).trans (this x hx)
    . let h2 := this y hy; exact (h h0 ((this x hx).trans h2.symm)).trans h2
  ---- Now show that all edges incident with `v₀` has colour `c`.
  intro v hv
  obtain ⟨⟨w₁, hw⟩, ⟨w₂, rfl⟩, h0, hw0⟩ :
      ∃ w₁ w₂ : { x // C.colour v₀ x = c }, w₁ ≠ w₂ ∧ C.colour v w₁ = C.colour v w₂ := by
    have hv' := C.incidence_finite v
    let f (w : { x // C.colour v₀ x = c }) : Set.range (C.colour v) := ⟨C.colour v w, w, rfl⟩
    simpa only [f, Subtype.mk.injEq] using Finite.exists_ne_map_eq_of_infinite f
  replace h0 : w₁ ≠ w₂ := by simpa using h0
  rw [C.colour_symm, C.colour_symm v₀]
  refine h hv ?_
  rw [C.colour_symm, ← h h0 hw0, h h0 hw, C.colour_symm]

/-- Final solution -/
theorem final_solution (h : ∀ c : α, ∃ x y : V, x ≠ y ∧ C.colour x y ≠ c) :
    ∃ x y z, y ≠ z ∧ C.colour x y = C.colour x z ∧ C.colour y z ≠ C.colour x z := by
  contrapose! h; exact monochromatic_of_triangle C λ h0 ↦ h _ _ _ h0
