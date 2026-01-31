/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Bounds.Defs

/-!
# IMO 2009 A1

Let $n$ be a positive integer and $G$ be a nontrivial totally ordered abelian group.
We say that a function $f : \{1, 2, …, n\} × \{0, 1, 2\} → G$ is *good* if;
* for each $1 ≤ i₁ ≤ i₂ ≤ n$ and $j = 0, 1, 2$, we have $f(i₁, j) ≤ f(i₂, j)$; and
* there exist permutations $σ_0, σ_1, σ_2$ of $\{1, 2, …, n\}$ such that the real numbers
    $f(σ_0(i), 0), f(σ_1(i), 1), f(σ_2(i), 2)$ form the side lengths of a triangle.

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
-/

namespace IMOSL
namespace IMO2009A1

open Finset

/-! ### Triangle side lengths -/

/-- The triple `(a, b, c)` is a triangle side length if and only if
  `a < b + c`, `b < c + a`, and `c < a + b`. -/
def isTriangleSideLengths [Add G] [LT G] (x : Fin 3 → G) :=
  ∀ j, x j < x (j + 1) + x (j + 2)

/-- The triangle side length property is decidable. -/
instance instDecidableIsTriangleSideLengths [Add G] [LT G] [DecidableLT G] :
    DecidablePred (isTriangleSideLengths (G := G)) :=
  λ _ ↦ Nat.decidableForallFin _

/-- For any `g : G`, the triple `(g, g, 2g)` is not a triangle side length. -/
theorem not_isTriangleSideLengths_self_self_two_nsmul [AddMonoid G] [Preorder G] (g : G) :
    ¬isTriangleSideLengths ![g, g, 2 • g] :=
  λ hg ↦ (hg 2).ne (two_nsmul g)

/-- If `a < b ≤ 2a`, then `(a, b, 2a)` is a triangle side length. -/
theorem isTriangleSideLengths_of_lt_of_le_two_nsmul
    [AddMonoid G] [Preorder G] [AddLeftStrictMono G] [AddLeftMono G] [AddLeftReflectLT G]
    {a b : G} (hab : a < b) (hab0 : b ≤ 2 • a) :
    isTriangleSideLengths ![a, b, 2 • a] := by
  have ha : 0 < a := by
    rw [← lt_add_iff_pos_right (a := a), ← two_nsmul]
    exact hab.trans_le hab0
  intro j; match j with
  | 0 => exact lt_add_of_lt_of_nonneg hab (nsmul_nonneg ha.le 2)
  | 1 => exact lt_add_of_le_of_pos hab0 ha
  | 2 => exact (add_lt_add_right hab a).trans_eq' (two_nsmul a).symm

/-- If `0 < b ≤ a`, then `(a, b, a)` is a triangle side length. -/
theorem isTriangleSideLengths_of_pos_of_le
    [AddZeroClass G] [Preorder G] [AddLeftStrictMono G] [AddRightStrictMono G]
    {a b : G} (hb : 0 < b) (hab : b ≤ a) :
    isTriangleSideLengths ![a, b, a] := by
  intro j; match j with
  | 0 => exact lt_add_of_pos_left a hb
  | 1 => exact lt_add_of_le_of_pos hab (hb.trans_le hab)
  | 2 => exact lt_add_of_pos_right a hb





/-! ### Good functions -/

/-- A *good* function is a function `f : Fin n × Fin 3 → G` such that
* for each `i₁ ≤ i₂` and `j`, we have `f(i₁, j) ≤ f(i₂, j)`; and
* there exist permutations `σ_0, σ_1, σ_2` such that for each `i`,
  `f(σ_0(i), 0), f(σ_1(i), 1), f(σ_2(i), 2)` forms the side length of a triangle. -/
@[ext] structure GoodFun (G) [Add G] [Preorder G] (n : ℕ) where
  toFun : Fin n → Fin 3 → G
  monotone' j : Monotone (λ i ↦ toFun i j)
  exists_triangle_perm' :
    ∃ σ : Fin 3 → Equiv.Perm (Fin n), ∀ i, isTriangleSideLengths (λ j ↦ toFun (σ j i) j)


namespace GoodFun

variable [Add G] [Preorder G]

instance : FunLike (GoodFun G n) (Fin n) (Fin 3 → G) where
  coe := toFun
  coe_injective' _ _ := GoodFun.ext

/-- If `f` is a good function, then the function `i ↦ f(i, j)` is monotone for each `j`. -/
theorem monotone (f : GoodFun G n) (j) : Monotone (λ i ↦ f i j) :=
  f.monotone' j

/-- If `f` is a good function, then there exist permutations `σ_0, σ_1, σ_2` such that
  `f(σ_0(i), 0), f(σ_1(i), 1), f(σ_2(i), 2)` forms the side length of a triangle. -/
theorem exists_triangle_perm (f : GoodFun G n) :
    ∃ σ : Fin 3 → Fin n ≃ Fin n, ∀ i, isTriangleSideLengths (λ j ↦ f (σ j i) j) :=
  f.exists_triangle_perm'

/-- An index `i` is called `f`-*triangular* if
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
      add_le_add (f.monotone (j + 1) (Fin.le_last _)) (f.monotone (j + 2) (Fin.le_last _))

end GoodFun





/-! ### Nice sequences -/

/-- A sequence `(a_i)_{i = 0}^n` of elements of `G` is called *nice* if
  `0 < a_0 < … < a_n` and `a_{i + 1} ≤ 2a_i` for each `i < n`. -/
@[ext] structure NiceSeq (G) [AddMonoid G] [Preorder G] (n) where
  toFun : Fin (n + 1) → G
  map_zero_pos' : toFun 0 > 0
  strictMono' : StrictMono toFun
  le_two_mul' (i) (hi : i ≠ Fin.last n) : toFun (i + 1) ≤ 2 • toFun i


namespace NiceSeq

section

variable [AddMonoid G] [Preorder G] (a : NiceSeq G n)

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
theorem le_two_mul {i} (hi : i ≠ Fin.last n) : a (i + 1) ≤ 2 • a i :=
  a.le_two_mul' i hi

/-- The function `f : Fin (n + 1) × Fin 3 → G` defined by `f(i, 0) = f(i, 1) = a_i`
  and `f(i, 2) = 2a_i` for `i ≤ n`, except `f(i, n) = 2a_n`. -/
def mkFun (i : Fin (n + 1)) : Fin 3 → G :=
  ![if i = Fin.last n then 2 • a (Fin.last n) else a i, a i, 2 • a i]

/-- The value of `a.mkFun i 0` for `i ≠ n`. -/
theorem mkFun_apply_zero_of_ne_last (hi : i ≠ Fin.last n) : a.mkFun i 0 = a i :=
  if_neg hi

/-- The value of `a.mkFun i 0` for `i < n`. -/
theorem mkFun_apply_zero_of_lt_last (hi : i < Fin.last n) : a.mkFun i 0 = a i :=
  a.mkFun_apply_zero_of_ne_last hi.ne

/-- The value of `a.mkFun n 0`. -/
theorem mkFun_last_zero : a.mkFun (Fin.last n) 0 = 2 • a (Fin.last n) :=
  if_pos rfl

end


/-- A nice sequence made out of a positive element of a group. -/
def of_pos [AddMonoid G] [Preorder G] [AddLeftMono G] [AddLeftStrictMono G]
    (g : G) (hg : g > 0) (n) : NiceSeq G n where
  toFun i := (i.val + 1) • g
  map_zero_pos' := hg.trans_eq (one_nsmul g).symm
  strictMono' i₁ i₂ hi := nsmul_lt_nsmul_left hg (Nat.succ_lt_succ (Fin.lt_def.mp hi))
  le_two_mul' i hi :=
    calc ((i + 1).val + 1) • g
    _ = (i.val + 2) • g := by rw [Fin.val_add_one_of_lt (Fin.lt_last_iff_ne_last.mpr hi)]
    _ ≤ (2 * (i.val + 1)) • g :=
      nsmul_le_nsmul_left hg.le <| Nat.add_le_add_right (k := 2) <|
        Nat.le_mul_of_pos_left i.val Nat.two_pos
    _ = 2 • (i.val + 1) • g := by rw [Nat.mul_comm, mul_nsmul]


section

variable [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] (a : NiceSeq G n)

/-- For each `j : Fin 3`, the function `i ↦ a.mkFun i j` is monotone. -/
theorem mkFun_monotone_left (j) : Monotone (λ i ↦ a.mkFun i j) := by
  ---- We only need to solve the case `j = 0`.
  intro i₁ i₂ hi
  have hi0 : a i₁ ≤ a i₂ := a.monotone hi
  match j with | 0 => ?_ | 1 => exact hi0 | 2 => exact nsmul_le_nsmul_right hi0 2
  ---- If `i₂ < n` then `i₁ < n` as well and we are done.
  dsimp only
  obtain hi₂ | rfl : i₂ < Fin.last n ∨ i₂ = Fin.last n := i₂.le_last.lt_or_eq
  · rwa [a.mkFun_apply_zero_of_lt_last (hi.trans_lt hi₂), a.mkFun_apply_zero_of_lt_last hi₂]
  ---- If `i₁ = i₂ = n` then we are done.
  obtain rfl | hi₁ : i₁ = Fin.last n ∨ i₁ < Fin.last n := hi.eq_or_lt
  · rfl
  ---- If `i₁ < i₂ = n`, then `a_{i₁} ≤ a_n ≤ 2a_n`.
  rw [a.mkFun_apply_zero_of_lt_last hi₁, a.mkFun_last_zero, two_nsmul]
  exact hi0.trans (le_add_of_nonneg_left (a.map_nonneg _))

/-- For each `i : Fin (n + 1)`, if we let `f = a.mkFun`,
  then `f(i, 0), f(i + 1, 1), f(i, 2)` form the side lengths of a triangle. -/
theorem mkFun_isTriangleSideLengths (i) :
    isTriangleSideLengths
      (λ j ↦ a.mkFun (![Equiv.refl _, Equiv.addRight 1, Equiv.refl _] j i) j) := by
  obtain hi | rfl : i ≠ Fin.last n ∨ i = Fin.last n := ne_or_eq _ _
  ---- If `i < n`, the sides to be considered are `a_i, a_{i + 1}, 2a_i`.
  · have hi0 : i < i + 1 := by rwa [Fin.lt_add_one_iff, Fin.lt_last_iff_ne_last]
    convert isTriangleSideLengths_of_lt_of_le_two_nsmul
      (a.strictMono hi0) (a.le_two_mul hi) using 1
    funext j; match j with | 0 => exact if_neg hi | 1 => rfl | 2 => rfl
  ---- If `i = n`, the sides to be considered are `2a_i, a_{i + 1}, 2a_i`.
  · have ha : a 0 ≤ 2 • a (Fin.last n) := calc
      _ ≤ a (Fin.last n) + a (Fin.last n) :=
        le_add_of_le_of_nonneg (a.monotone (Fin.le_last _)) (a.map_nonneg _)
      _ = 2 • a (Fin.last n) := (two_nsmul _).symm
    convert isTriangleSideLengths_of_pos_of_le (a.map_pos 0) ha using 1
    funext j; match j with
      | 0 => exact if_pos rfl
      | 1 => exact congrArg a (Fin.last_add_one n)
      | 2 => rfl

/-- The function `a.mkFun` as a good function. -/
def mkGoodFun : GoodFun G (n + 1) where
  toFun := a.mkFun
  monotone' := a.mkFun_monotone_left
  exists_triangle_perm' :=
    ⟨![Equiv.refl _, Equiv.addRight 1, Equiv.refl _], a.mkFun_isTriangleSideLengths⟩

/-- The value of `a.mkGoodFun i` for `i ≠ n`. -/
theorem mkGoodFun_apply_zero_of_ne_last (hi : i ≠ Fin.last n) :
    a.mkGoodFun i = ![a i, a i, 2 • a i] :=
  congrArg (![·, a i, 2 • a i]) (if_neg hi)

/-- The only `a.mkFun`-triangular index is `n`. -/
theorem mkGoodFun_triangular_iff : a.mkGoodFun.triangular i ↔ i = Fin.last n := by
  ---- The `→` direction has been done before.
  refine ⟨λ hi ↦ ?_, λ hi ↦ hi ▸ a.mkGoodFun.last_is_triangular⟩
  ---- For `←`, If `i ≠ n`, then the sides to be considered is `(g, g, 2g)` with `g = a_i`.
  refine (eq_or_ne _ _).resolve_right λ hi0 ↦
    not_isTriangleSideLengths_self_self_two_nsmul (a i) ?_
  rwa [GoodFun.triangular, a.mkGoodFun_apply_zero_of_ne_last hi0] at hi

end

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
    [Nontrivial G] [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] {n} :
    IsLeast (Set.range λ f : GoodFun G (n + 1) ↦ #{i | f.triangular i}) 1 := by
  refine ⟨?_, ?_⟩
  ---- First find a good function `f : Fin (n + 1) × Fin 3 → G` with one triangular index.
  · obtain ⟨g, hg⟩ : ∃ g : G, g > 0 := exists_pos_of_nontrivial G
    refine ⟨(NiceSeq.of_pos g hg n).mkGoodFun, ?_⟩
    simp_rw [NiceSeq.mkGoodFun_triangular_iff]
    rw [filter_eq', if_pos (mem_univ _), card_singleton]
  ---- Now show that the index `i` must always exist.
  · rintro _ ⟨f, rfl⟩
    exact one_le_card.mpr ⟨Fin.last n, (mem_filter_univ _).mpr f.last_is_triangular⟩
