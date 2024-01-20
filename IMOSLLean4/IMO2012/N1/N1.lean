/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Basic

/-!
# IMO 2012 N1

Let $R$ be a commutative ring.
A set $A ⊆ R$ is called admissible if for any $x, y \in A$
  and $r \in R$, we have $x^2 + rxy + y^2 \in A$.
Determine all pairs $(x, y) ∈ R^2$ such that
  the only admissible set containing $x$ and $y$ is $R$.
-/

namespace IMOSL
namespace IMO2012N1

def admissible [Semiring R] (A : Set R) :=
  ∀ x y : R, x ∈ A → y ∈ A → ∀ r : R, x ^ 2 + r * x * y + y ^ 2 ∈ A

theorem admissible_ideal [CommSemiring R] (I : Ideal R) :
    admissible I.carrier :=
  λ u v h h0 r ↦ I.add_mem
    (I.add_mem (sq u ▸ I.mul_mem_left u h) (I.mul_mem_left (r * u) h0))
    (sq v ▸ I.mul_mem_left v h0)

theorem admissible_mem_sq_mul [CommRing R] {A : Set R} (h : admissible A)
    (h0 : z ∈ A) (k : R) : k * z ^ 2 ∈ A := by
  have h1 := h z z h0 h0 (k - 2)
  rwa [mul_assoc, ← sq, ← one_add_mul, ← add_one_mul,
    add_right_comm, one_add_one_eq_two, add_sub_cancel'_right] at h1

theorem admissible_add_sq [CommSemiring R] {A : Set R} (h : admissible A)
    (h0 : x ∈ A) (h1 : y ∈ A) : (x + y) ^ 2 ∈ A :=
  add_sq x y ▸ h x y h0 h1 2

/-- Final solution -/
theorem final_solution [CommRing R] (x y : R) :
    (∀ A : Set R, admissible A → x ∈ A → y ∈ A → ∀ z : R, z ∈ A)
      ↔ IsCoprime x y :=
  ---- `→`
  ⟨λ h ↦ by
    specialize h (Ideal.span {x, y}) (admissible_ideal _)
      (Ideal.subset_span (Set.mem_insert x _))
      (Ideal.subset_span (Set.mem_insert_of_mem x rfl)) 1
    rwa [SetLike.mem_coe, Ideal.mem_span_pair] at h,
  ---- `←`
  λ h A h0 h1 h2 ↦ by
    suffices 1 ∈ A from λ z ↦ mul_one z ▸
      one_pow (M := R) 2 ▸ admissible_mem_sq_mul h0 this z
    obtain ⟨a, b, h⟩ : IsCoprime (x ^ 2) (y ^ 2) := IsCoprime.pow h
    rw [← one_pow 2, ← h]
    refine admissible_add_sq h0 (admissible_mem_sq_mul h0 h1 a)
      (admissible_mem_sq_mul h0 h2 b)⟩
