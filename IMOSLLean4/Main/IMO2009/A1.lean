/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Bounds.Defs

/-!
# IMO 2009 A1

Let $n$ be a positive integer and $G$ be a nontrivial totally ordered abelian group.
We say that a function $f : \{1, 2, …, n\} × \{0, 1, 2\} → G$ is *good* if;
* for each $1 ≤ i₁ ≤ i₂ ≤ n$ and $j = 0, 1, 2$, we have $f(i₁, j) ≤ f(i₂, j)$; and
* there exist permutations $σ_0, σ_1, σ_2$ of $\{1, 2, …, n\}$ such that for each $i$, the
  elements $f(σ_0(i), 0), f(σ_1(i), 1), f(σ_2(i), 2)$ form the side lengths of a triangle.

Find the smallest possible number of indices $i ≤ n$ such that
  $f(i, 0), f(i, 1), f(i, 2)$ form the side lengths of a triangle.

### Answer

$1$.

### Solution

We follow the [official solution](https://www.imo-official.org/problems/IMO2009SL.pdf).
We modify the largest triangle to have side lengths $2n, n, 2n$ instead of all sides $2n$.

For convenience, we define the following notions:
* `IMOSL.IMO2009A1.GoodFun.triangular`: an index $i$ is called $f$-*triangular*
  if $f(i, 0), f(i, 1), f(i, 2)$ form the side lengths of a triangle.
* `IMOSL.IMO2009A1.NiceSeq`: a sequence $(a_i)_{i = 0}^n$ of elements of $G$ is
  called *nice* if $0 < a_0 < … < a_n$ and $a_{i + 1} ≤ 2a_i$ for each $i < n$.

We use nice sequences to construct good functions with only one triangular index.
-/

namespace IMOSL
namespace IMO2009A1

open Finset

/-! ### Triangle side lengths -/

/-- The triple `(a, b, c)` is called a triangle side length
  if `a < b + c`, `b < c + a`, and `c < a + b`. -/
def isTriangleSideLengths [Add G] [LT G] (x : Fin 3 → G) :=
  ∀ j, x j < x (j + 1) + x (j + 2)

/-- The triangle side length property is decidable. -/
instance instDecidableIsTriangleSideLengths [Add G] [LT G] [DecidableLT G] :
    DecidablePred (isTriangleSideLengths (G := G)) :=
  λ _ ↦ Nat.decidableForallFin _

/-- For any `g : G`, the triple `(g, g, 2g)` is not a triangle side length. -/
theorem not_isTriangleSideLengths_add_self [Add G] [Preorder G] (g : G) :
    ¬isTriangleSideLengths ![g, g, g + g] :=
  λ hg ↦ (hg 2).ne rfl

/-- If `a < b ≤ c ≤ a + a`, then `(a, b, c)` is a triangle side length. -/
theorem isTriangleSideLengths_of_lt_le_le_add
    [Add G] [Preorder G] [AddLeftStrictMono G] [AddRightStrictMono G]
    {x : Fin 3 → G} (hx : x 0 < x 1) (hx0 : x 1 ≤ x 2) (hx1 : x 2 ≤ x 0 + x 0) :
    isTriangleSideLengths x := by
  have hx2 : x 0 < x 2 := hx.trans_le hx0
  intro j; match j with
    | 0 => exact hx2.trans (hx1.trans_lt (add_lt_add hx hx2))
    | 1 => exact (hx0.trans hx1).trans_lt (add_lt_add_left hx2 _)
    | 2 => exact hx1.trans_lt (add_lt_add_right hx _)

/-- If `0 < b ≤ a`, then `(a, b, a)` is a triangle side length. -/
theorem isTriangleSideLengths_of_pos_of_le
    [AddZeroClass G] [Preorder G] [AddLeftStrictMono G] [AddRightStrictMono G]
    {x : Fin 3 → G} (hx : 0 < x 1) (hx0 : x 1 ≤ x 0) (hx1 : x 2 = x 0) :
    isTriangleSideLengths x := by
  intro j; match j with
  | 0 => exact lt_add_of_pos_of_le hx hx1.ge
  | 1 => exact lt_add_of_le_of_pos (hx0.trans_eq hx1.symm) (hx.trans_le hx0)
  | 2 => exact lt_add_of_le_of_pos hx1.le hx





/-! ### Good functions -/

/-- A *good* function is a function `f : Fin n × Fin 3 → G` such that
* for each `i₁ ≤ i₂` and `j`, we have `f(i₁, j) ≤ f(i₂, j)`; and
* there exist permutations `σ_0, σ_1, σ_2` such that for each `i`, the elements
  `f(σ_0(i), 0), f(σ_1(i), 1), f(σ_2(i), 2)` form the side lengths of a triangle. -/
@[ext] structure GoodFun (G) [Add G] [Preorder G] (n : ℕ) where
  toFun : Fin n → Fin 3 → G
  monotone_left' j : Monotone (λ i ↦ toFun i j)
  exists_triangle_perm' :
    ∃ σ : Fin 3 → Equiv.Perm (Fin n), ∀ i, isTriangleSideLengths (λ j ↦ toFun (σ j i) j)


namespace GoodFun

variable [Add G] [Preorder G]

instance : FunLike (GoodFun G n) (Fin n) (Fin 3 → G) where
  coe := toFun
  coe_injective' _ _ := GoodFun.ext

/-- If `f` is a good function, then the function `i ↦ f(i, j)` is monotone for each `j`. -/
theorem monotone_left (f : GoodFun G n) (j) : Monotone (λ i ↦ f i j) :=
  f.monotone_left' j

/-- If `f` is a good function, then there exist permutations `σ_0, σ_1, σ_2` such that for
  all `i`, `f(σ_0(i), 0), f(σ_1(i), 1), f(σ_2(i), 2)` form the side lengths of a triangle. -/
theorem exists_triangle_perm (f : GoodFun G n) :
    ∃ σ : Fin 3 → Fin n ≃ Fin n, ∀ i, isTriangleSideLengths (λ j ↦ f (σ j i) j) :=
  f.exists_triangle_perm'

/-- An index `i` is called `f`-*triangular* if the elements
  `f(i, 0), f(i, 1), f(i, 2)` form the side lengths of a triangle. -/
def triangular (f : GoodFun G n) (i : Fin n) := isTriangleSideLengths (f i)

/-- Triangularity of an index is decidable. -/
instance [DecidableLT G] (f : GoodFun G n) : DecidablePred f.triangular :=
  λ _ ↦ instDecidableIsTriangleSideLengths _

/-- If `f : Fin (n + 1) × Fin 3 → G` is a good function, then `n` is `f`-triangular. -/
theorem last_is_triangular [AddLeftMono G] [AddRightMono G] (f : GoodFun G (n + 1)) :
    f.triangular (Fin.last n) := by
  ---- Choose corresponding permutations `σ_0, σ_1, σ_2`.
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin 3 → Equiv.Perm (Fin (n + 1)),
      ∀ i, isTriangleSideLengths (λ j ↦ f (σ j i) j) :=
    f.exists_triangle_perm
  ---- Fix `j ∈ {0, 1, 2}`, and let `i = σ_j^{-1}(n)`.
  intro j; let i := (σ j).symm (Fin.last n)
  ---- Then `f(n, j) < f(σ_{j + 1}(i), j + 1) + f(σ_{j + 2}(i), j + 2) ≤ …`.
  calc f (Fin.last n) j
    _ = f (σ j i) j := congrArg (λ i ↦ f i j) ((σ j).apply_symm_apply _).symm
    _ < f (σ (j + 1) i) (j + 1) + f (σ (j + 2) i) (j + 2) := hσ i j
    _ ≤ f (Fin.last n) (j + 1) + f (Fin.last n) (j + 2) :=
      add_le_add (f.monotone_left _ (Fin.le_last _)) (f.monotone_left _ (Fin.le_last _))

end GoodFun





/-! ### Nice sequences -/

/-- A sequence `(a_i)_{i = 0}^n` of elements of `G` is called *nice* if
  `0 < a_0 < … < a_n` and `a_{i + 1} ≤ 2a_i` for each `i < n`. -/
@[ext] structure NiceSeq (G) [AddZero G] [Preorder G] (n) where
  toFun : Fin (n + 1) → G
  map_zero_pos' : toFun 0 > 0
  strictMono' : StrictMono toFun
  map_add_one_le' (i) (hi : i ≠ Fin.last n) : toFun (i + 1) ≤ toFun i + toFun i


namespace NiceSeq

section

variable [AddZero G] [Preorder G] (a : NiceSeq G n)

instance : FunLike (NiceSeq G n) (Fin (n + 1)) G where
  coe := toFun
  coe_injective' _ _ := NiceSeq.ext

/-- If `a : Fin (n + 1) → G` is a nice sequence, then `a` is strictly monotone. -/
theorem strictMono : StrictMono a :=
  a.strictMono'

/-- If `a : Fin (n + 1) → G` is a nice sequence, then `a` is monotone. -/
theorem monotone : Monotone a :=
  a.strictMono.monotone

/-- If `a : Fin (n + 1) → G` is a nice sequence, then `a_i > 0` for all `i`. -/
theorem map_pos (i) : a i > 0 :=
  a.map_zero_pos'.trans_le (a.monotone i.zero_le)

/-- If `a : Fin (n + 1) → G` is a nice sequence, then `a_i ≥ 0` for all `i`. -/
theorem map_nonneg (i) : a i ≥ 0 :=
  (a.map_pos i).le

/-- If `a : Fin (n + 1) → G` is a nice sequence, then `a_{i + 1} ≤ 2a_i` for all `i ≠ n`. -/
theorem map_add_one_le {i} (hi : i ≠ Fin.last n) : a (i + 1) ≤ a i + a i :=
  a.map_add_one_le' i hi

/-- The function `f : Fin (n + 1) × Fin 3 → G` defined by `f(i, 0) = f(i, 1) = a_i`
  and `f(i, 2) = 2a_i` for `i ≤ n`, except `f(i, n) = 2a_n`. -/
def mkFun (i : Fin (n + 1)) : Fin 3 → G :=
  ![if i = Fin.last n then a (Fin.last n) + a (Fin.last n) else a i, a i, a i + a i]

/-- The value of `a.mkFun i 0` is `a_i` for `i ≠ n`. -/
theorem mkFun_apply_zero_of_ne_last (hi : i ≠ Fin.last n) : a.mkFun i 0 = a i :=
  if_neg hi

/-- The value of `a.mkFun i 0` is `a_i` for `i < n`. -/
theorem mkFun_apply_zero_of_lt_last (hi : i < Fin.last n) : a.mkFun i 0 = a i :=
  a.mkFun_apply_zero_of_ne_last hi.ne

/-- The value of `a.mkFun n 0` is `2a_n`. -/
theorem mkFun_last_zero : a.mkFun (Fin.last n) 0 = a (Fin.last n) + a (Fin.last n) :=
  if_pos rfl

end


section

variable [AddZeroClass G] [Preorder G]
  [AddLeftStrictMono G] [AddRightStrictMono G] (a : NiceSeq G n)

/-- For each `j : Fin 3`, the function `i ↦ a.mkFun i j` is strictly monotone. -/
theorem mkFun_strictMono_left (j) : StrictMono (λ i ↦ a.mkFun i j) := by
  ---- We only need to solve the case `j = 0`.
  intro i₁ i₂ hi
  have hi0 : a i₁ < a i₂ := a.strictMono hi
  match j with | 0 => ?_ | 1 => exact hi0 | 2 => exact add_lt_add hi0 hi0
  ---- Now split into two cases: `i₂ < n` and `i₂ = n`.
  dsimp only
  obtain hi₂ | rfl : i₂ < Fin.last n ∨ i₂ = Fin.last n := i₂.le_last.lt_or_eq
  ---- If `i₂ < n` then the goal is `a_{i₁} < a_{i₂}` which follows by property of `a`.
  · rwa [a.mkFun_apply_zero_of_lt_last (hi.trans hi₂), a.mkFun_apply_zero_of_lt_last hi₂]
  ---- If `i₂ = n` then the goal is `a_{i₁} < 2a_n` which also follows by property of `a`.
  · rw [a.mkFun_apply_zero_of_lt_last hi, a.mkFun_last_zero]
    exact lt_add_of_lt_of_pos hi0 (a.map_pos _)

/-- For each `j : Fin 3`, the function `i ↦ a.mkFun i j` is monotone. -/
theorem mkFun_monotone_left (j) : Monotone (λ i ↦ a.mkFun i j) :=
  (a.mkFun_strictMono_left j).monotone

/-- Letting `f = a.mkFun`, for each index `i`, the elements
  `f(i, 0), f(i + 1, 1), f(i, 2)` form the side lengths of a triangle. -/
theorem mkFun_isTriangleSideLengths (i) :
    isTriangleSideLengths
      (λ j ↦ a.mkFun (![Equiv.refl _, Equiv.addRight 1, Equiv.refl _] j i) j) := by
  set Δ : Fin 3 → G := λ j ↦ a.mkFun (![Equiv.refl _, Equiv.addRight 1, Equiv.refl _] j i) j
  obtain hi | rfl : i ≠ Fin.last n ∨ i = Fin.last n := ne_or_eq _ _
  ---- If `i < n`, the sides to be considered are `a_i, a_{i + 1}, 2a_i`.
  · have h : Δ 0 = a i := a.mkFun_apply_zero_of_ne_last hi
    have h0 : i < i + 1 := by rwa [Fin.lt_add_one_iff, Fin.lt_last_iff_ne_last]
    replace h0 : Δ 0 < a (i + 1) := h.trans_lt (a.strictMono h0)
    exact isTriangleSideLengths_of_lt_le_le_add h0
      (a.map_add_one_le hi) (ge_of_eq (congrArg₂ (· + ·) h h))
  ---- If `i = n`, the sides to be considered are `2a_i, a_{i + 1}, 2a_i`.
  · have h : Δ 0 = a (Fin.last n) + a (Fin.last n) := a.mkFun_last_zero
    have h0 : a (Fin.last n + 1) ≤ Δ 0 :=
      ((lt_add_of_le_of_pos (a.monotone (Fin.le_last _)) (a.map_pos _)).trans_eq h.symm).le
    exact isTriangleSideLengths_of_pos_of_le (a.map_pos _) h0 h.symm

/-- The function `a.mkFun` as a good function. -/
def mkGoodFun : GoodFun G (n + 1) where
  toFun := a.mkFun
  monotone_left' := a.mkFun_monotone_left
  exists_triangle_perm' :=
    ⟨![Equiv.refl _, Equiv.addRight 1, Equiv.refl _], a.mkFun_isTriangleSideLengths⟩

/-- The value of `a.mkGoodFun i` for `i ≠ n`. -/
theorem mkGoodFun_apply_zero_of_ne_last (hi : i ≠ Fin.last n) :
    a.mkGoodFun i = ![a i, a i, a i + a i] :=
  congrArg (![·, a i, a i + a i]) (if_neg hi)

end


/-- The only `a.mkFun`-triangular index is `n`. -/
theorem mkGoodFun_triangular_iff [AddZeroClass G] [Preorder G] [AddLeftMono G]
    [AddRightMono G] [AddLeftStrictMono G] [AddRightStrictMono G] {a : NiceSeq G n} :
  a.mkGoodFun.triangular i ↔ i = Fin.last n := by
  refine ⟨λ hi ↦ (eq_or_ne _ _).resolve_right
      λ hi0 ↦ not_isTriangleSideLengths_add_self (a i) ?_,
    λ hi ↦ hi ▸ a.mkGoodFun.last_is_triangular⟩
  rwa [GoodFun.triangular, a.mkGoodFun_apply_zero_of_ne_last hi0] at hi

/-- A nice sequence made out of a positive element of a group. -/
def of_pos [AddMonoid G] [Preorder G] [AddLeftMono G] [AddLeftStrictMono G]
    (g : G) (hg : g > 0) (n) : NiceSeq G n where
  toFun i := (i.val + 1) • g
  map_zero_pos' := hg.trans_eq (one_nsmul g).symm
  strictMono' i₁ i₂ hi := nsmul_lt_nsmul_left hg (Nat.succ_lt_succ (Fin.lt_def.mp hi))
  map_add_one_le' i hi :=
    calc ((i + 1).val + 1) • g
    _ = (i.val + 2) • g := by rw [Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr hi)]
    _ ≤ (2 * (i.val + 1)) • g :=
      nsmul_le_nsmul_left hg.le <| Nat.add_le_add_right (k := 2) <|
        Nat.le_mul_of_pos_left i.val Nat.two_pos
    _ = (↑i + 1) • g + (↑i + 1) • g := by rw [Nat.two_mul, add_nsmul]

end NiceSeq





/-! ### Summary -/

/-- A nontrivial totally ordered group contains a positive element. -/
theorem exists_pos_of_nontrivial
    (G) [Nontrivial G] [AddGroup G] [LinearOrder G] [AddLeftStrictMono G] :
    ∃ g : G, g > 0 := by
  obtain ⟨g, hg⟩ : ∃ g : G, g ≠ 0 := exists_ne 0
  obtain hg0 | hg0 : g > 0 ∨ g < 0 := gt_or_lt_of_ne hg
  exacts [⟨g, hg0⟩, ⟨-g, neg_pos_of_neg hg0⟩]

open Finset in
/-- Final solution -/
theorem final_solution
    (G) [Nontrivial G] [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] (n) :
    IsLeast (Set.range λ f : GoodFun G (n + 1) ↦ #{i | f.triangular i}) 1 := by
  refine ⟨?_, ?_⟩
  ---- First find a good function `f : Fin (n + 1) × Fin 3 → G` with one triangular index.
  · obtain ⟨g, hg⟩ : ∃ g : G, g > 0 := exists_pos_of_nontrivial G
    refine ⟨(NiceSeq.of_pos g hg n).mkGoodFun, ?_⟩
    simp only [NiceSeq.mkGoodFun_triangular_iff]
    rw [filter_eq', if_pos (mem_univ _), card_singleton]
  ---- Now show that the index `i` must always exist.
  · rintro _ ⟨f, rfl⟩
    exact one_le_card.mpr ⟨Fin.last n, (mem_filter_univ _).mpr f.last_is_triangular⟩
