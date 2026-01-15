/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Polynomial.Roots

/-!
# IMO 2006 N4 (P5)

Let $R$ be an integral domain such that $|R^×| ≤ 2$.
Let $f$ be an polynomial over $R$ of degree $n > 1$.
Prove that the polynomial $g = f ∘ f ∘ … ∘ f$ has no more than $n$ integer fixed points,
  where $f$ occurs $k$ times for some positive integer $k$.

### Solution

We prove something more general as follows.
A pair $(f, S)$, where $f ∈ R[X]$ and $S ⊆ R$ is a finite subset, is called **good** if
  for all $x, y ∈ S$ with $x ≠ y$, there exists $α ∈ R^×$ such that $f(x) - f(y) = α(x - y)$.
Then we claim that for any such pairs, either $f$ is linear or $\deg(f) ≥ |S|$.

The original problem follows by taking $S$ to be the set of fixed points of $g$.
Indeed, for any $x ≠ y ∈ S$, we have $x - y ∣ f(x) - f(y) ∣ g(x) - g(y) = x - y$.
Since $R$ is an integral domain, this implies that $(f, S)$ is a good pair.
Since $f$ is non-linear, the claim implies $\deg(f) ≥ |S|$.

### Proof of the claim

First fix $x, y, z ∈ S$ pairwise distinct.
Choose units $α, β, γ ∈ R^×$ such that $f(x) - f(y) = α(x - y)$,
  $f(y) - f(z) = β(y - z)$, and $f(x) - f(z) = γ(x - z)$.
Since $|R^×| ≤ 2$, two of $α, β, γ$ are equal; assume WLOG that $α = β$.
But then we would also get $f(x) - f(z) = α(x - z)$, forcing $γ = α$.
So all the three units are equal.

As a result, there exists a unit $γ$ such that $f(x) - f(y) = γ(x - y)$ for all $x, y ∈ S$.
Then any element of $S$ is a root of the polynomial $g(x) = f(x) - (γx + c)$ for some $c$.
Thus we get $|S| ≤ \deg(g) = \deg(f)$, as desired.
-/

namespace IMOSL
namespace IMO2006N4

open Polynomial

/-- A pair `(f, S)`, where `f ∈ R[X]` and `S ⊆ R`, is a **good pair** if for all `x, y ∈ S`
  with `x ≠ y`, there exists a unit `α ∈ Rˣ` such that `f(x) - f(y) = α(x - y)`. -/
structure GoodPair (R) [Ring R] where
  /-- This is the corresponding polynomial of the good pair. -/
  f : R[X]
  /-- This is the corresponding set of the good pair. -/
  S : Set R
  /-- This is the corresponding collection of units of the good pair. -/
  α (x : S) (y : S) (_ : x.1 ≠ y) : Rˣ
  spec (x y : S) (h : x.1 ≠ y) : f.eval x.1 - f.eval y.1 = α x y h * (x - y)


namespace GoodPair

variable [Ring R] [NoZeroDivisors R]

/-- To check if two good pairs are equal, no need to check the unit equality. -/
@[ext] theorem ext {U V : GoodPair R} (hf : U.f = V.f) (hS : U.S = V.S) : U = V := by
  rcases U with ⟨f, S, α₁, h₁⟩
  rcases V with ⟨f', S', α₂, h₂⟩
  subst hf hS; dsimp only at α₂ h₂ ⊢
  rw [mk.injEq, heq_eq_eq]
  refine ⟨rfl, rfl, funext₃ λ x y hxy ↦ ?_⟩
  have h : α₁ x y hxy * (x.1 - y) = α₂ x y hxy * (x.1 - y) :=
    (h₁ x y _).symm.trans (h₂ x y _)
  exact Units.val_injective (mul_right_cancel₀ (sub_ne_zero_of_ne hxy) h)

/-- For any `x ≠ y`, we have `α_{xy} = α_{yx}`. -/
theorem α_comm (U : GoodPair R) {x y : U.S} {hxy : x.1 ≠ y} :
    U.α x y hxy = U.α y x hxy.symm := by
  have h : U.α x y hxy * (x.1 - y) = U.α y x hxy.symm * (x.1 - y) := by
    rw [← U.spec, ← neg_sub, U.spec _ _ hxy.symm, ← mul_neg, neg_sub]
  exact Units.val_injective (mul_right_cancel₀ (sub_ne_zero_of_ne hxy) h)

/-- If `α_{xy} = α_{yz} = α`, then `α_{xz} = α`. -/
theorem α_eq_trans (U : GoodPair R) {α : Rˣ} {x y z : U.S} (hxy : x.1 ≠ y)
    (hxy0 : U.α x y hxy = α) (hyz : y.1 ≠ z) (hxz0 : U.α y z hyz = α) (hxz : x.1 ≠ z) :
    U.α x z hxz = α := by
  have h : U.α x z hxz * (x.1 - z) = α * (x.1 - z) := calc
    _ = U.f.eval x.1 - U.f.eval z.1 := (U.spec x z hxz).symm
    _ = (U.f.eval x.1 - U.f.eval y.1) + (U.f.eval y.1 - U.f.eval z.1) :=
      (sub_add_sub_cancel _ _ _).symm
    _ = α * (x.1 - y) + α * (y.1 - z) := by
      rw [U.spec _ _ hxy, U.spec _ _ hyz, hxy0, hxz0]
    _ = α * (x.1 - z) := by rw [← mul_add, sub_add_sub_cancel]
  exact Units.val_injective (mul_right_cancel₀ (sub_ne_zero_of_ne hxz) h)


variable [Fintype Rˣ] (hR : Fintype.card Rˣ ≤ 2) (U : GoodPair R)
include hR

/-- If `|Rˣ| ≤ 2`, then all the `α_{xy}`'s are equal. -/
theorem α_constant_of_card_units_le_two {x y z w : U.S} {hxy : x.1 ≠ y} {hzw : z.1 ≠ w} :
    U.α x y hxy = U.α z w hzw := by
  ---- The case `y = z` yields the general case, so we may assume that `y = z`.
  wlog hyz : y = z generalizing x y z w
  · calc U.α x y hxy
      _ = U.α y z (Subtype.coe_ne_coe.mpr hyz) := this rfl
      _ = U.α z w hzw := this rfl
  ---- If `w = x` then we are done.
  subst hyz; rename y.1 ≠ w => hyw
  obtain rfl | hwx : w = x ∨ w ≠ x := eq_or_ne _ _
  · exact U.α_comm
  ---- If `w ≠ x` then two of the `α_{xy}, α_{yw}, α_{wx}`'s are equal.
  replace hwx : w.1 ≠ x := Subtype.coe_ne_coe.mpr hwx
  set α : Rˣ := U.α x y hxy
  set β : Rˣ := U.α y w hyw
  set γ : Rˣ := U.α w x hwx
  obtain h | h | h : α = β ∨ α = γ ∨ β = γ := by
    rw [← Nat.not_lt, Fintype.two_lt_card_iff] at hR
    simp_rw [Ne, not_exists, ← not_or, not_not] at hR
    exact hR α β γ
  exacts [h, (U.α_eq_trans hxy.symm U.α_comm hwx.symm (U.α_comm.trans h.symm) _).symm,
    U.α_eq_trans hwx.symm (U.α_comm.trans h.symm) hyw.symm U.α_comm _]

/-- If `|Rˣ| ≤ 2`, then all the `α_{xy}`'s are equal to some `γ ∈ Rˣ`. -/
theorem exists_const_α_of_card_units_le_two : ∃ γ : Rˣ, ∀ x y hxy, U.α x y hxy = γ := by
  obtain hS | ⟨x, y, hxy⟩ : (∀ x y : U.S, x.1 = y) ∨ (∃ x y : U.S, x.1 ≠ y) := by
    simpa only [← not_forall] using em _
  exacts [⟨1, λ _ _ h ↦ absurd (hS _ _) h⟩,
    ⟨U.α x y hxy, λ _ _ _ ↦ α_constant_of_card_units_le_two hR U⟩]

/-- If `|Rˣ| ≤ 2`, then there exists `γ ∈ Rˣ` and `c ∈ R` such that
  all elements of `S` are roots of `f(X) - (γX + c)`. -/
theorem exists_α_c_mem_S_imp_IsRoot_f_sub_αX_add_c :
    ∃ γ : Rˣ, ∃ c, ∀ x : U.S, (U.f - (C γ.val * Polynomial.X + C c)).IsRoot x := by
  ---- Pick `γ ∈ Rˣ` such that all the `α_{xy}`'s are equal to `α`.
  obtain ⟨γ, hγ⟩ : ∃ γ : Rˣ, ∀ x y hxy, U.α x y hxy = γ :=
    U.exists_const_α_of_card_units_le_two hR
  refine ⟨γ, ?_⟩
  ---- In particular, we get `f(x) - αx = f(y) - αy` for all `x` and `y`.
  replace hγ (x y : U.S) : U.f.eval x.1 - γ * x = U.f.eval y.1 - γ * y := by
    obtain hxy | hxy : x.1 = y ∨ x.1 ≠ y := eq_or_ne _ _
    · rw [hxy]
    · rw [sub_eq_sub_iff_sub_eq_sub, U.spec x y hxy, hγ, mul_sub]
  ---- If `S` is empty then `c` can be anything; pick `c = 0`.
  obtain hS | ⟨x, hxS⟩ : U.S = ∅ ∨ U.S.Nonempty := U.S.eq_empty_or_nonempty
  · exact ⟨0, λ ⟨x, hx⟩ ↦ absurd hx (hS ▸ Set.notMem_empty x)⟩
  ---- Otherwise if `x ∈ S` then pick `c = f(x) - αx`.
  lift x to U.S using hxS
  refine ⟨U.f.eval x.1 - γ * x, λ y ↦ ?_⟩
  rw [IsRoot.def, eval_sub, eval_add, eval_C_mul,
    eval_X, eval_C, hγ x y, add_sub_cancel, sub_self]

end GoodPair


/-- Final solution -/
theorem final_solution [CommRing R] [IsDomain R] [DecidableEq R] [Fintype Rˣ]
    (hR : Fintype.card Rˣ ≤ 2) {f : R[X]} (hf : f.natDegree ≥ 2) (k) :
    (f.comp^[k] X - X).roots.toFinset.card ≤ f.natDegree := by
  ---- Assume `k > 0`, as otherwise we are done.
  cases k with
  | zero => rw [Function.iterate_zero_apply, sub_self, roots_zero]; exact Nat.zero_le _
  | succ k => ?_
  ---- For convenience, let `S` be the set of roots of `F(X) = f(f(…(f(X)))) - X`.
  let F : R[X] := f.comp^[k + 1] X - X
  set S : Finset R := F.roots.toFinset
  ---- First we find the desired `α` with `f(x) - f(y) = α(x - y)` for each `x, y ∈ S`.
  obtain ⟨α, h⟩ : ∃ α : (x : S) → (y : S) → (_ : x.1 ≠ y) → Rˣ,
      ∀ (x y : S) (hxy : x.1 ≠ y), f.eval x.1 - f.eval y.1 = α x y hxy * (x.1 - y) := by
    suffices ∀ x y : S, x.1 ≠ y → ∃ α : Rˣ, f.eval x.1 - f.eval y.1 = α * (x.1 - y)
      from ⟨λ x y hxy ↦ (this x y hxy).choose, λ x y hxy ↦ (this x y hxy).choose_spec⟩
    rintro x y -
    -- It suffices to show that `f(x) - f(y) ∣ x - y`.
    suffices f.eval x.1 - f.eval y.1 ∣ x.1 - y by
      -- Note that `x - y ∣ f(x) - f(y)` is automatic since `f` is a polynomial.
      obtain ⟨α, hα⟩ : Associated (x.1 - y) (f.eval x.1 - f.eval y.1) :=
        associated_of_dvd_dvd (f.sub_dvd_eval_sub _ _) this
      exact ⟨α, hα.symm.trans (mul_comm _ _)⟩
    -- Indeed, since `x, y ∈ S` and `k > 0`, we have `f^k(x) = x` and `f^k(y) = y`.
    have h (z : S) : (f.comp^[k] X).eval (f.eval z.1) = z :=
      calc (f.comp^[k] X).eval (f.eval z.1)
        _ = (f.comp^[k + 1] X).eval z.1 := by
          rw [iterate_comp_eval, iterate_comp_eval, eval_X, eval_X]; rfl
        _ = F.eval z.1 + z := by rw [eval_sub, eval_X, sub_add_cancel]
        _ = z := add_eq_right.mpr (isRoot_of_mem_roots (Multiset.mem_toFinset.mp z.2))
    -- Thus we get `f(x) - f(y) ∣ f^k(x) - f^k(y) ∣ x - y`.
    calc f.eval x.1 - f.eval y.1
      _ ∣ (f.comp^[k] X).eval (f.eval x.1) - (f.comp^[k] X).eval (f.eval y.1) :=
        sub_dvd_eval_sub _ _ _
      _ = x.1 - y := congrArg₂ (· - ·) (h _) (h _)
  /- Then `(f, S)` is a good pair, so there exists `γ ∈ R^×` and `c ∈ R`
    such that every element of `S` is a root of `G(X) = f(X) - (γX + c)`. -/
  obtain ⟨γ, c, h0⟩ :
      ∃ γ : Rˣ, ∃ c : R, ∀ x : S, (f - (C γ.val * Polynomial.X + C c)).IsRoot x :=
    (⟨f, S, α, h⟩ : GoodPair R).exists_α_c_mem_S_imp_IsRoot_f_sub_αX_add_c hR
  ---- Note that `deg(g) = deg(f)` and `S` is the subset of the set of roots of `g`.
  set G : R[X] := f - (C γ.val * Polynomial.X + C c)
  have hG : G.natDegree = f.natDegree := by
    refine natDegree_sub_eq_left_of_natDegree_lt ?_
    rwa [natDegree_add_C, natDegree_C_mul_X _ γ.ne_zero]
  replace h : G ≠ 0 := by
    intro hG0; rw [← hG, hG0] at hf
    exact hf.not_gt Nat.two_pos
  replace h0 : S ⊆ G.roots.toFinset := by
    intro x hxS
    rw [Multiset.mem_toFinset, mem_roots h]
    exact h0 ⟨x, hxS⟩
  ---- Finally, just do the calculations.
  calc S.card
    _ ≤ G.roots.toFinset.card := Finset.card_le_card h0
    _ ≤ G.roots.card := G.roots.toFinset_card_le
    _ ≤ G.natDegree := G.card_roots'
    _ = f.natDegree := hG
