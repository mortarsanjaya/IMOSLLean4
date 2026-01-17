/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Polynomial.Roots

/-!
# IMO 2006 N4 (P5)

Let $R$ be an integral domain such that $|Rˣ| ≤ 2$.
Let $f$ be an polynomial over $R$ of degree $n > 1$.
Prove that the polynomial $g = f ∘ f ∘ … ∘ f$ has no more than $n$ integer fixed points,
  where $f$ occurs $k$ times for some positive integer $k$.

### Solution

We prove something more general as follows.
Given a subset $A ⊆ R$, we say that a function $α : A × A → Rˣ$ is $A$-**admissible** if
  for all $x, y, z ∈ A$, we have $α(x, y)(x - y) + α(y, z)(y - z) + α(z, x)(z - x) = 0$.
We say that $A$ is an $Rˣ$-**good** subset if for any $A$-**admissible** function $α$,
  there exists $β ∈ Rˣ$ such that $α(x, y) = β$ for any $x, y ∈ A$ with $x ≠ y$.
Assuming $|Rˣ| ≤ 2$, we claim that every subset of $R$ is $Rˣ$-good.

Indeed, the $A$-admissible equation implies that for any $x, y, z ∈ A$ pairwise distinct,
  if two of $α(x, y), α(y, z), α(z, x)$ are equal, then all three are equal.
This is always the case if $|Rˣ| ≤ 2$, which implies all the $α(x, y)$'s are equal.
(We do not care about $α(x, y)$ for $x = y$.)

The original problem follows by taking $A$ to be the set of fixed points of $g$.
Indeed, for any $x ≠ y ∈ A$, we have $x - y ∣ f(x) - f(y) ∣ g(x) - g(y) = x - y$,
  and so there exists $α(x, y) ∈ Rˣ$ such that $f(x) - f(y) = α(x, y)(x - y)$.
Defining $α(x, x) ∈ Rˣ$ arbitrarily for all $x ∈ A$ gives an $A$-admissible function.
The claim implies that $α$ is constant on pairs of distinct elements of $A$.
Thus there exists $γ ∈ Rˣ$ and $c ∈ R$ such that $f(x) = γx + c$ for all $x ∈ A$.
That is, all elements of $A$ are roots of the polynomial $P(X) = f(X) - (γX + c)$.
Since $\deg(P) = \deg(f) = 2$, we then get $|A| ≤ \deg(f)$.

### Note

We generalize the definition of $A$-admissible functions and $Rˣ$-good sets.
Let $G$ be a monoid and $M$ be a $G$-module.
A function $α : A × A → G$ is called $A$-**admissible** if for all $x, y, z ∈ A$,
  we have $α(x, y)(x - y) + α(y, z)(y - z) + α(z, x)(z - x) = 0$.
The definition of $G$-**good** sets is generalized accordingly.

The solution also proves that $f₀ ∘ f$ has no more than
  $n$ integer fixed points for any polynomial $f₀ ∈ R[X]$.
-/

namespace IMOSL
namespace IMO2006N4

/-! ### Admissible functions and good sets -/

section

variable (G) {M} [AddCommGroup M] [SMul G M]

/-- Given a subset `A ⊆ M` of a `G`-module, a function `α : A × A → G` is called
  `A`-**admissible** if `α(x, y)(x - y) + α(y, z)(y - z) + α(z, x)(z - x) = 0`
  for all `x, y, z ∈ A`. -/
def admissible (A : Set M) (α : A → A → G) :=
  ∀ x y z, α x y • (x.1 - y) + α y z • (y.1 - z) + α z x • (z.1 - x) = 0

/-- A subset `A ⊆ M` is called `G`-**good** if any `A`-**admissible** function
  `α : A × A → G` is constant on pairs of distinct elements of `A`. -/
def good (A : Set M) := ∀ α, admissible G A α → ∃ β, ∀ x y, x ≠ y → α x y = β

end


namespace admissible

variable {R} [Ring R] [IsDomain R] {M} [AddCommGroup M]
  [Module R M] [Module.IsTorsionFree R M]
  {A : Set M} {α : A → A → Rˣ} (hα : admissible Rˣ A α)
include hα

/-- If `α : A × A → Rˣ` is `A`-admissible, then `α(x, y) = α(y, x)` for any `x, y ∈ Rˣ`. -/
theorem comm (x y : A) : α x y = α y x := by
  ---- If `x = y` then there is nothing to do.
  obtain hxy | hxy : x.1 = y ∨ x.1 ≠ y := eq_or_ne x.1 y.1
  · rw [SetCoe.ext hxy]
  ---- If `x ≠ y` then plugging `z = x` does the work.
  have h := hα x y x
  rw [sub_self, smul_zero, add_zero, add_eq_zero_iff_eq_neg, ← smul_neg, neg_sub,
    Units.smul_def, Units.smul_def] at h
  exact Units.val_injective (smul_left_injective R (sub_ne_zero_of_ne hxy) h)

/-- If `α : A × A → Rˣ` is `A`-admissible and `α(x, y) = α(y, z) = γ` where `x ≠ z`,
  then `α(x, z) = γ`; no triangle of two colours. -/
theorem eq_trans (hxy : α x y = β) (hyz : α y z = β) (hxz : x ≠ z) : α x z = β := by
  replace hxz : x.1 ≠ z.1 := Subtype.coe_ne_coe.mpr hxz
  have h := hα x y z
  rw [hxy, hyz, ← smul_add, sub_add_sub_cancel, add_eq_zero_iff_eq_neg,
    ← smul_neg, neg_sub, hα.comm, Units.smul_def, Units.smul_def] at h
  exact Units.val_injective (smul_left_injective R (sub_ne_zero_of_ne hxz) h).symm

end admissible


/-- A set of size at most one is `G`-good. -/
theorem good_of_forall_mem_eq [hG : Nonempty G] [AddCommGroup M] [SMul G M]
    {A : Set M} (hA : ∀ x y : A, x = y) : good G A :=
  hG.elim λ g _ _ ↦ ⟨g, λ x y ↦ absurd (hA x y)⟩

/-- If `|Rˣ| ≤ 2`, there is no good subset of any `R`-module. -/
theorem good_of_card_units_le_two
    {R} [Ring R] [IsDomain R] [Fintype Rˣ] (hR : Fintype.card Rˣ ≤ 2)
    {M} [AddCommGroup M] [Module R M] [Module.IsTorsionFree R M] (A : Set M) :
    good Rˣ A := by
  ---- If `|A| ≤ 1`, we are done, so now pick two distinct elements of `A`, say `x ≠ y`.
  obtain hA | ⟨x, y, hxy⟩ : (∀ x y : A, x = y) ∨ (∃ x y : A, x ≠ y) := by
    simpa only [← not_forall] using em _
  · exact good_of_forall_mem_eq hA
  ---- Let `α` be an `A`-admissible function; pick `β = α(x, y)`.
  intro α hα; refine ⟨α x y, λ z w hzw ↦ ?_⟩
  ---- The case `y = z` yields the general case, so we may assume that `y = z`.
  wlog hyz : y = z generalizing x y z w
  · rw [this _ _ hyz _ _ hzw rfl, this _ _ hxy _ _ hyz rfl]
  ---- If `w = x` then we are done.
  subst hyz; rename y ≠ w => hyw
  obtain rfl | hwx : w = x ∨ w ≠ x := eq_or_ne _ _
  · exact hα.comm y w
  ---- If `w ≠ x` then two of `α(x, y), α(y, w), α(w, x)` are equal.
  obtain h | h | h : α x y = α y w ∨ α x y = α w x ∨ α y w = α w x := by
    rw [← Nat.not_lt, Fintype.two_lt_card_iff] at hR
    simp_rw [Ne, not_exists, ← not_or, not_not] at hR
    exact hR _ _ _
  exacts [h.symm, hα.eq_trans (hα.comm y x) (h.trans (hα.comm w x)).symm hyw,
    (hα.eq_trans ((hα.comm x w).trans h.symm) (hα.comm w y) hxy).symm]





/-! ### Application of admissible functions on polynomials -/

section

open Polynomial Function

variable [CommRing R] [IsDomain R] [DecidableEq R]

/-- Let `f ∈ R[X]` be a polynomial of degree at least `2`, and let `A ⊆ R` be an `Rˣ`-good
  finite subset such that `f(x) - f(y) ∣ x - y` for all `x, y ∈ A`. Then `|A| ≤ deg(f)`. -/
theorem card_le_natDegree_of_eval_sub_eval_dvd_sub
    {f : R[X]} (hf : f.natDegree ≥ 2) {A : Finset R} (hA : good Rˣ (A : Set R))
    (hfA : ∀ x y : A, f.eval x.1 - f.eval y.1 ∣ x - y) :
    A.card ≤ f.natDegree := by
  /- It suffices to find `β ∈ Rˣ` and `c ∈ R` such that all
    elements of `A` are roots of `g(X) = f(X) - (βX + c)`. -/
  suffices ∃ β : Rˣ, ∃ c, ∀ x : A, (f - (C β.val * X + C c)).IsRoot x by
    rcases this with ⟨β, c, h⟩
    set g : R[X] := f - (C β.val * X + C c)
    have hg : g.natDegree = f.natDegree := by
      refine natDegree_sub_eq_left_of_natDegree_lt ?_
      rwa [natDegree_add_C, natDegree_C_mul_X _ β.ne_zero]
    have hg0 : g ≠ 0 := by
      intro hg0; rw [← hg, hg0] at hf
      exact hf.not_gt Nat.two_pos
    replace h : A ⊆ g.roots.toFinset := by
      intro x hxS
      rw [Multiset.mem_toFinset, mem_roots hg0]
      exact h ⟨x, hxS⟩
    calc A.card
      _ ≤ g.roots.toFinset.card := Finset.card_le_card h
      _ ≤ g.roots.card := g.roots.toFinset_card_le
      _ ≤ g.natDegree := g.card_roots'
      _ = f.natDegree := hg
  ---- First, for all `x, y ∈ A`, there exists `α ∈ Rˣ` such that `f(x) - f(y) = α(x - y)`.
  replace hfA (x y : A) : ∃ α : Rˣ, f.eval x.1 - f.eval y.1 = α • (x - y) := by
    obtain ⟨α, hα⟩ : Associated (x.1 - y) (f.eval x.1 - f.eval y.1) :=
      associated_of_dvd_dvd (f.sub_dvd_eval_sub x.1 y.1) (hfA x y)
    exact ⟨α, hα.symm.trans (mul_comm _ _)⟩
  ---- We then construct a corresponding function `α : A × A → Rˣ` using choice.
  obtain ⟨α, hα⟩ : ∃ α : A → A → Rˣ, ∀ x y, f.eval x.1 - f.eval y.1 = α x y • (x - y) :=
    ⟨λ x y ↦ Classical.choose (hfA x y), λ x y ↦ Classical.choose_spec (hfA x y)⟩
  ---- It is easy to see that `α` is `A`-admissible.
  replace hfA : admissible Rˣ (A : Set R) α := by
    intro x y z; rw [← hα, ← hα, ← hα, sub_add_sub_cancel, sub_add_sub_cancel, sub_self]
  ---- Since `A` is `Rˣ`-good, `α` is constant (on pairs of distinct elements); `β` found.
  obtain ⟨β, hβ⟩ : ∃ β, ∀ x y : A, x ≠ y → α x y = β := hA α hfA
  refine ⟨β, ?_⟩
  ---- If `A = ∅`, taking any value of `c` works; we use `c = 0`.
  obtain rfl | ⟨z, hz⟩ : A = ∅ ∨ A.Nonempty := A.eq_empty_or_nonempty
  · exact ⟨0, λ ⟨x, hx⟩ ↦ absurd hx (Finset.notMem_empty x)⟩
  ---- Otherwise, pick `c = f(z) - βz` for any `z ∈ A`.
  lift z to ↑A using hz
  refine ⟨f.eval z.1 - β * z, λ x ↦ ?_⟩
  rw [IsRoot.def, eval_sub, eval_add, eval_C, eval_C_mul, eval_X]
  obtain rfl | hxz : x = z ∨ x ≠ z := eq_or_ne x z
  · rw [add_sub_cancel, sub_self]
  · rw [← sub_sub, sub_sub_sub_comm, ← mul_sub, sub_eq_zero, hα, hβ _ _ hxz]; rfl

/-- Final solution -/
theorem final_solution [Fintype Rˣ] (hR : Fintype.card Rˣ ≤ 2)
    {f : R[X]} (hf : f.natDegree ≥ 2) (k) :
    (f.comp^[k] X - X).roots.toFinset.card ≤ f.natDegree := by
  ---- The case `k = 0` is trivial by the junk value of `Polynomial.roots`.
  cases k with
  | zero => rw [iterate_zero_apply, sub_self, roots_zero]; exact Nat.zero_le _
  | succ k => ?_
  ---- The case `k > 0` follows since `f^k = f^{k - 1} ∘ f`.
  set g : R[X] := f.comp^[k + 1] X - X
  set A : Finset R := g.roots.toFinset
  refine card_le_natDegree_of_eval_sub_eval_dvd_sub hf (good_of_card_units_le_two hR _) ?_
  have h (z : A) : (f.comp^[k] X).eval (f.eval z.1) = z :=
    calc (f.comp^[k] X).eval (f.eval z.1)
    _ = f.eval^[k + 1] z.1 := by rw [iterate_comp_eval, eval_X, iterate_succ_apply]
    _ = (f.comp^[k + 1] X).eval z.1 := by rw [iterate_comp_eval, eval_X]
    _ = (f.comp^[k + 1] X - X + X).eval z.1 := by rw [sub_add_cancel]
    _ = (f.comp^[k + 1] X - X).eval z.1 + z := by rw [eval_add, eval_X]
    _ = z := by rw [add_eq_right, isRoot_of_mem_roots (Multiset.mem_toFinset.mp z.2)]
  intro x y; calc f.eval x.1 - f.eval y.1
    _ ∣ (f.comp^[k] X).eval (f.eval x.1) - (f.comp^[k] X).eval (f.eval y.1) := by
      exact sub_dvd_eval_sub _ _ _
    _ = x.1 - y := congrArg₂ (· - ·) (h x) (h y)

end
