/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Order.Chebyshev

/-!
# IMO 2012 N8

Let $p > 100$ be a prime number.
Prove that for any integer $r$, there exists two integers $a$ and $b$ such that
$$ p ∣ a^2 + b^5 - r. $$

### Solution

We follow Solution 1 of the official solution, with some simplification.
See [here](https://www.imo-official.org/problems/IMO2012SL.pdf).
However, we do things more generally, as follows.

Let $F$ be a finite field with $q$ elements.
Let $n$ be a positive integer, and suppose that $q > 2n(n - 1)$.
Then we show that for any $r ∈ F$, there exists $a, b ∈ F$ such that $a^2 + b^n = r$.
The original statement is recovered by taking $F = 𝔽_p$.

Using the double-counting technique from Solution 1, we get that the number of elements
  of $F$ of the form $a^2 + b^n$ is at least $\dfrac{q^3}{(q - 1)(q + n) + 1}$.
We simplify the bound to $q - (n - 1)$.
Thus, we proved that number of elements **not** of the form $a^2 + b^n$ is at most $n - 1$.
To give a lower bound on the number of such elements, we consider the action of $Fˣ$
  only on the **units** $u$ not of the form $a^2 + b^n$, given by $g • u = g^{2n} u$.
By ...

Note that the case where $F$ has characteristic $2$ is trivial, as squaring is surjective.
We deal with this characteristic $2$ case separately in the beginning.

### Generalization

Actually, we can show more when $n = 5$: any $q ≠ 11$ works.
The map $a ↦ a^n$ is bijective on $F$ if $\gcd(q - 1, n) = 1$.
Thus, we are also done if $q$ is even or if $5 ∤ q - 1$.
The remaining case is $q ≡ 1 (mod 10)$, for which $q ≤ 40$ implies $q ∈ \{11, 31\}$.
By computer search, $q = 31$ succeeds, while $q = 11$ fails with $r = 7$.

See `Generalization/IMO2012N8/IMO2012N8.lean` for the implementation.

### TODO

Implement the generalization.
-/

namespace IMOSL
namespace IMO2012N8

open Finset

variable {F} [Field F] [Fintype F] [DecidableEq F]
local notation "q" => Fintype.card F

/-! ### The characteristic 2 case -/

omit [DecidableEq F] in
/-- If `char(F) = 2`, then every element is of the form `a^2 + f(b)`, whatever `f` is. -/
theorem exists_eq_sq_add_map_of_char_eq_two (hF : ringChar F = 2)
    [hβ : Nonempty β] (f : β → F) (r : F) :
    ∃ a b, a ^ 2 + f b = r := by
  refine Nonempty.elim hβ λ b : β ↦ ?_
  obtain ⟨a, ha⟩ : IsSquare (r - f b) := FiniteField.isSquare_of_char_two hF _
  refine ⟨a, b, ?_⟩
  rw [sq, ← ha, sub_add_cancel]





/-! ### Double counting methods -/

/-- `Finset.card_eq_sum_card_fiberwise` with both sides being `Finset.univ`.
  TODO: Remove this lemma once it gets into `mathlib`, because it should. -/
theorem Fintype_card_eq_sum_card_fiberwise
    [Fintype α] [Fintype β] [DecidableEq β] (f : α → β) :
    Fintype.card α = ∑ b, #{a | f a = b} :=
  card_eq_sum_card_fiberwise λ _ _ ↦ mem_univ _

/-- Cardinality of pairs `(i, j)` with `f(i) = g(j)` as a sum over fibers. -/
theorem Fintype_card_fiber_product_eq_fiberwise
    [Fintype α] [Fintype β] [Fintype κ] [DecidableEq κ] (f : α → κ) (g : β → κ) :
    #{x : α × β | f x.1 = g x.2} = ∑ k, #{a | f a = k} * #{b | g b = k} :=
  calc #{x : α × β | f x.1 = g x.2}
  _ = ∑ x : α × β, if f x.1 = g x.2 then 1 else 0 := (sum_boole _ _).symm
  _ = ∑ a, ∑ b, if f a = g b then 1 else 0 := Fintype.sum_prod_type _
  _ = ∑ k, ∑ a : {a // f a = k}, ∑ b, if f a = g b then 1 else 0 :=
    (Fintype.sum_fiberwise _ _).symm
  _ = ∑ k, #{a : α | f a = k} * #{b : β | g b = k} :=
    ---- Term-wise matching
    Fintype.sum_congr _ _ λ k ↦
      calc ∑ a : {a // f a = k}, ∑ b, if f a = g b then 1 else 0
      _ = ∑ a : {a // f a = k}, ∑ b, if g b = k then 1 else 0 :=
        Fintype.sum_congr _ _ λ i ↦ Fintype.sum_congr _ _ λ j ↦
          if_congr (by rw [i.2, eq_comm]) rfl rfl
      _ = #{a | f a = k} * #{b | g b = k} := by
        rw [sum_const, card_univ, Fintype.card_subtype,
          smul_eq_mul, sum_boole, Nat.cast_id]

/-- Cardinality of pairs `(i, j)` with `f(i) = f(j)` as a sum of squares. -/
theorem Fintype_card_eqpair_eq_fiberwise
    [Fintype ι] [Fintype κ] [DecidableEq κ] (f : ι → κ) :
    #{x : ι × ι | f x.1 = f x.2} = ∑ k, #{i | f i = k} ^ 2 := by
  conv => right; right; ext; rw [sq]
  exact Fintype_card_fiber_product_eq_fiberwise f f

/-- Double-counting `4`-tuples `(i, j, i', j')` such that `f(i) + g(j) = f(i') + g(j')`,
  where `f : α → G` and `g : β → G` are functions to a finite abelian group `G`. -/
theorem Fintype_quad_fiber_product_double_count [Fintype α] [Fintype β]
    [AddCommGroup G] [Fintype G] [DecidableEq G] (f : α → G) (g : β → G) :
    ∑ x, #{p : α × α | f p.1 - f p.2 = x} * #{p : β × β | g p.1 - g p.2 = x}
      = ∑ x, #{p : α × β | f p.1 + g p.2 = x} ^ 2 :=
  calc ∑ x, #{p : α × α | f p.1 - f p.2 = x} * #{p : β × β | g p.1 - g p.2 = x}
  _ = ∑ x, #{p : α × α | f p.1 - f p.2 = x} * #{p : β × β | g p.2 - g p.1 = x} :=
    Fintype.sum_congr _ _ λ x ↦ congrArg (_ * ·) <|
      card_equiv (Equiv.prodComm β β) λ p ↦ by simp only [mem_filter_univ]; rfl
  _ = #{p : (α × α) × (β × β) | f p.1.1 - f p.1.2 = g p.2.2 - g p.2.1} :=
    (Fintype_card_fiber_product_eq_fiberwise
      (λ p : α × α ↦ f p.1 - f p.2) (λ p : β × β ↦ g p.2 - g p.1)).symm
  _ = #{p : (α × α) × (β × β) | f p.1.1 + g p.2.1 = f p.1.2 + g p.2.2} := by
    conv => left; congr; congr; ext; rw [sub_eq_sub_iff_add_eq_add, add_comm (g _)]
  _ = #{p : (α × β) × (α × β) | f p.1.1 + g p.1.2 = f p.2.1 + g p.2.2} :=
    card_equiv (Equiv.prodProdProdComm α α β β) λ ((a, a'), (b, b')) ↦ by
      simp only [Equiv.prodProdProdComm_apply, mem_filter_univ]
  _ = ∑ x, #{p : α × β | f p.1 + g p.2 = x} ^ 2 :=
    Fintype_card_eqpair_eq_fiberwise (λ p : α × β ↦ f p.1 + g p.2)

/-- Cauchy-Schwarz inequality on the double-counting formula for `4`-tuples
  `(i, j, i', j')` such that `f(i) + g(j) = f(i') + g(j')`. -/
theorem Fintype_quad_fiber_product_CauchySchwarz [Fintype α] [Fintype β]
    [AddCommGroup G] [Fintype G] [DecidableEq G] (f : α → G) (g : β → G) :
    (Fintype.card α * Fintype.card β) ^ 2 ≤
      #{x | ∃ a b, f a + g b = x} *
        ∑ x, #{p : α × α | f p.1 - f p.2 = x} * #{p : β × β | g p.1 - g p.2 = x} :=
  calc (Fintype.card α * Fintype.card β) ^ 2
  _ = (∑ x with #{p : α × β | f p.1 + g p.2 = x} ≠ 0,
        #{p : α × β | f p.1 + g p.2 = x}) ^ 2 := by
    rw [sum_filter_ne_zero, ← Fintype.card_prod, ← Fintype_card_eq_sum_card_fiberwise]
  _ ≤ #{x | #{p : α × β | f p.1 + g p.2 = x} ≠ 0} *
        ∑ x with #{p : α × β | f p.1 + g p.2 = x} ≠ 0,
          #{p : α × β | f p.1 + g p.2 = x} ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  _ = #{x | ∃ a b, f a + g b = x} * ∑ x, _ := by
    ---- Split into two parts.
    refine congrArg₂ _ ?_ ?_
    ---- `#{(a, b) : f(a) + g(b) = x} ≠ 0` iff `f(a) + g(b) = x` for some `a` and `b`.
    · refine congrArg _ (ext λ x ↦ ?_)
      simp only [mem_filter_univ, card_ne_zero, Finset.Nonempty, Prod.exists]
    ---- Show a double counting identity.
    · rw [sum_filter_of_ne λ x _ ↦ by exact Nat.ne_zero_of_mul_ne_zero_right,
        Fintype_quad_fiber_product_double_count]





/- ### Counting pairs `(a, b) ∈ F^2` such that `a^2 - b^2 = r` when `char(F) ≠ 2` -/

/-- Number of pairs `(a, b) ∈ R^2` such that `ab = 0`, where `R` is a domain. -/
theorem card_mul_eq_zero [Ring R] [IsDomain R] [Fintype R] [DecidableEq R] :
    #{p : R × R | p.1 * p.2 = 0} = 2 * Fintype.card R - 1 :=
  calc #{p : R × R | p.1 * p.2 = 0}
  _ = #({(0 : R)} ×ˢ univ ∪ univ ×ˢ {(0 : R)}) := by
    refine congrArg card (ext λ (a, b) ↦ ?_)
    rw [mem_filter_univ, mul_eq_zero, mem_union]
    simp only [mem_product, mem_singleton, mem_univ, true_and, and_true]
  _ = #({(0 : R)} ×ˢ (univ : Finset R)) + #((univ : Finset R) ×ˢ {(0 : R)})
      - #({(0 : R)} ×ˢ univ ∩ univ ×ˢ {(0 : R)}) :=
    card_union _ _
  _ = 2 * Fintype.card R - 1 := by
    rw [card_product, card_product, product_inter_product, inter_univ, univ_inter,
      card_product, card_singleton, card_univ, Nat.one_mul, Nat.mul_one, Nat.two_mul]

/-- Number of pairs `(a, b) ∈ G^2` such that `ab = g`, where `g ∈ G`; `G` is a group. -/
theorem card_group_antidiagonal [Group G] [Fintype G] [DecidableEq G] (g : G) :
    #{p : G × G | p.1 * p.2 = g} = Fintype.card G :=
  calc #{p : G × G | p.1 * p.2 = g}
  _ = ∑ p : G × G, if p.1 * p.2 = g then 1 else 0 := (sum_boole _ _).symm
  _ = ∑ a, ∑ b, if a * b = g then 1 else 0 := Fintype.sum_prod_type _
  _ = ∑ a, ∑ b, if a⁻¹ * g = b then 1 else 0 := by
    conv => right; right; ext; right; ext; congr; rw [inv_mul_eq_iff_eq_mul, eq_comm]
  _ = ∑ a : G, 1 := Fintype.sum_congr _ _ λ a ↦ Fintype.sum_ite_eq _ _
  _ = Fintype.card G := Fintype.card_eq_sum_ones.symm

/-- Number of pairs `(a, b) ∈ R^2` such that `ab = r`, where `r ∈ Rˣ`. -/
theorem card_mul_eq_unit [CommRing R] [Fintype R] [DecidableEq R] (r : Rˣ) :
    #{p : R × R | p.1 * p.2 = r} = Fintype.card Rˣ := by
  ---- Consider the map `f : Rˣ → R × R` defined by `x ↦ (x, x⁻¹ r)`.
  refine (card_nbij (λ x : Rˣ ↦ (x.val, (x⁻¹ * r).val)) ?_ ?_ ?_).symm
  ---- We first need to show that the image of the map is in `{(a, b) : R × R | ab = r}`.
  · rintro x -; rw [mem_coe, mem_filter_univ, ← Units.val_mul, mul_inv_cancel_left]
  ---- Next we need to show that the map is injective.
  · rintro x - y - h; exact Units.val_inj.mp (congrArg Prod.fst h)
  ---- Finally, we need to show that the map surjects into `{(a, b) : R × R | ab = r}`.
  · rintro ⟨x, y⟩ h
    rw [mem_coe, mem_filter_univ] at h
    -- First lift `x` to a unit.
    lift x to Rˣ using isUnit_of_mul_eq_one x (y * r⁻¹) (by rw [← mul_assoc, h, r.mul_inv])
    refine ⟨x, mem_univ _, Prod.ext rfl ?_⟩
    -- Now it remains to show that `y = x⁻¹ r`.
    dsimp only; rw [Units.val_mul, ← h, Units.inv_mul_cancel_left]

/-- Number of pairs `(a, b) ∈ F^2` such that `ab = r`. -/
theorem FiniteField_card_mul_fiber (r : F) :
    #{p : F × F | p.1 * p.2 = r} = if r = 0 then 2 * q - 1 else q - 1 := by
  ---- If `r = 0`, then the count holds since `F` is a domain. If `r ≠ 0`, `r` is a unit.
  split_ifs with h
  · exact h ▸ card_mul_eq_zero
  · lift r to Fˣ using isUnit_iff_ne_zero.mpr h
    rw [card_mul_eq_unit, Fintype.card_units]

/-- Number of pairs `(a, b) ∈ F^2` with `a^2 - b^2 = r`, where `char(F) ≠ 2`. -/
theorem FiniteField_card_sq_sub_sq_fiber_of_two_ne_zero (hF : ringChar F ≠ 2) (r : F) :
    #{p : F × F | p.1 ^ 2 - p.2 ^ 2 = r} = if r = 0 then 2 * q - 1 else q - 1 := by
  replace hF (a : F) : (a + a) / 2 = a := by
    rw [← two_mul, mul_div_cancel_left₀ a (Ring.two_ne_zero hF)]
  ---- Constructing permutation `e` on `F × F` sending `(a, b)` to `(a + b, a - b)`.
  let e : F × F ≃ F × F :=
    { toFun p := (p.1 + p.2, p.1 - p.2)
      invFun p := ((p.1 + p.2) / 2, (p.1 - p.2) / 2)
      left_inv p := by dsimp only; rw [add_add_sub_cancel, hF, add_sub_sub_cancel, hF]
      right_inv p := by dsimp only; rw [← add_div, add_add_sub_cancel, hF,
        ← sub_div, add_sub_sub_cancel, hF] }
  ---- The bijection implies `#{(a, b) | a^2 - b^2 = r} = #{(a, b) | ab = r} = RHS`.
  refine (card_equiv e λ p ↦ ?_).trans (FiniteField_card_mul_fiber r)
  rw [mem_filter_univ, mem_filter_univ, sq_sub_sq]; rfl

/-- Number of pairs `(a, b) ∈ F^2` with `a^2 - b^2 = r`, where `char(F) ≠ 2`. -/
theorem FiniteField_card_sq_sub_sq_fiber_of_two_ne_zero' (hF : ringChar F ≠ 2) (r : F) :
    #{p : F × F | p.1 ^ 2 - p.2 ^ 2 = r} = q - 1 + if r = 0 then q else 0 := by
  rw [FiniteField_card_sq_sub_sq_fiber_of_two_ne_zero hF, add_ite,
    Nat.add_zero, ← Nat.self_add_sub_one, Nat.add_comm]





/-! ### Lower bound on the number of elements of the form `a^2 + b^n`, `n > 1` -/

section

open Polynomial

/-- Bound on the number of `a ∈ F` such that `P(a) = r`. -/
theorem card_Polynomial_fiber_le_degree {P : F[X]} (hP : 0 < P.natDegree) (r : F) :
    #{a : F | P.eval a = r} ≤ P.natDegree :=
  have hP0 : 0 < P.degree := natDegree_pos_iff_degree_pos.mp hP
  calc #{a | P.eval a = r}
  _ ≤ (P - C r).roots.card :=
    Multiset.card_le_card <| Finset.val_le_iff_val_subset.mpr λ a ↦ by
      rw [mem_val, mem_filter_univ, mem_roots_sub_C hP0]; exact id
  _ ≤ P.natDegree := card_roots_sub_C' hP0

/-- Bound on the number of `(a, b) ∈ F^2` such that `P(a) = P(b)`. -/
theorem card_Polynomial_eqpair_le_of_degree_mul_q {P : F[X]} (hP : 0 < P.natDegree) :
    #{p : F × F | P.eval p.1 = P.eval p.2} ≤ P.natDegree * q :=
  calc #{p : F × F | P.eval p.1 = P.eval p.2}
  _ = ∑ r, #{a | P.eval a = r} * #{b | P.eval b = r} :=
    Fintype_card_fiber_product_eq_fiberwise P.eval P.eval
  _ ≤ ∑ r, P.natDegree * #{b | P.eval b = r} :=
    Finset.sum_le_sum λ r _ ↦ Nat.mul_le_mul_right _ (card_Polynomial_fiber_le_degree hP r)
  _ = P.natDegree * q := by rw [← mul_sum, ← Fintype_card_eq_sum_card_fiberwise]

/-- Bound on the number of elements of `F` of the form `a^2 + f(b)`. -/
theorem card_sq_add_fn_fiber_lower_bound (hF : ringChar F ≠ 2) (f : F → F) :
    q ^ 3 ≤ #{r | ∃ a b, a ^ 2 + f b = r} *
      ((q - 1) * q + #{p : F × F | f p.1 = f p.2}) := by
  ---- First de-cancel a factor of `q` from both sides.
  refine Nat.le_of_mul_le_mul_right (c := q) ?_ Fintype.card_pos
  ---- Reduce to evaluating `∑ r, #{(a, b) | a^2 - b^2 = r} #{(a, b) | f(a) - f(b) = r}`.
  calc q ^ 4
    _ = (q * q) ^ 2 := by rw [← Nat.pow_two, ← Nat.pow_mul]
    _ ≤ #{r | ∃ a b, a ^ 2 + f b = r} *
          ∑ r, #{p : F × F | p.1 ^ 2 - p.2 ^ 2 = r} * #{p : F × F | f p.1 - f p.2 = r} :=
      Fintype_quad_fiber_product_CauchySchwarz _ f
    _ = _ * (((q - 1) * q + #{p : F × F | f p.1 = f p.2}) * q) := congrArg (_ * ·) ?_
    _ = _ := (Nat.mul_assoc _ _ _).symm
  ---- Now evaluate `∑ r, #{(a, b) | a^2 - b^2 = r} #{(a, b) | f(a) - f(b) = r}`.
  calc ∑ r, #{p : F × F | p.1 ^ 2 - p.2 ^ 2 = r} * #{p : F × F | f p.1 - f p.2 = r}
    _ = ∑ r, ((q - 1) * #{p : F × F | f p.1 - f p.2 = r} +
          if 0 = r then q * #{p : F × F | f p.1 - f p.2 = r} else 0) := by
      refine Fintype.sum_congr _ _ λ r ↦ ?_
      rw [FiniteField_card_sq_sub_sq_fiber_of_two_ne_zero' hF,
        Nat.add_mul, ite_zero_mul, if_congr eq_comm rfl rfl]
    _ = (q - 1) * ∑ r, #{p : F × F | f p.1 - f p.2 = r} +
          q * #{p : F × F | f p.1 - f p.2 = 0} := by
      rw [sum_add_distrib, mul_sum, Fintype.sum_ite_eq]
    _ = (q - 1) * (q * q) + #{p : F × F | f p.1 = f p.2} * q :=
      congrArg₂ _ (by rw [← Fintype_card_eq_sum_card_fiberwise, Fintype.card_prod])
        (by simp only [Nat.mul_comm q, sub_eq_zero])
    _ = ((q - 1) * q + #{p : F × F | f p.1 = f p.2}) * q := by
      rw [Nat.add_mul, Nat.mul_assoc]

/-- Bound on the number of elements of `F` of the form `a^2 + P(b)`, `P ∈ F[X]`. -/
theorem card_sq_add_Polynomial_fiber_lower_bound {P : F[X]} (hP : 0 < P.natDegree) :
    q ^ 2 ≤ #{r | ∃ a b, a ^ 2 + P.eval b = r} * (q + (P.natDegree - 1)) := by
  ---- The case `char(F) = 2` is easier.
  obtain hF | hF : ringChar F = 2 ∨ ringChar F ≠ 2 := eq_or_ne _ _
  · have h : ({r : F | ∃ a b, a ^ 2 + P.eval b = r} : Finset F) = univ :=
      eq_univ_of_forall λ r ↦ (mem_filter_univ _).mpr <|
        exists_eq_sq_add_map_of_char_eq_two hF _ _
    rw [h, sq, Nat.mul_add]; exact Nat.le_add_right _ _
  ---- Now assume `char(F) ≠ 2`. First de-cancel a factor of `q` from both sides.
  have hq : 1 ≤ q := Fintype.card_pos
  refine Nat.le_of_mul_le_mul_right (c := q) ?_ hq
  ---- Now estimate.
  calc q ^ 3
    _ ≤ #{r | ∃ a b, a ^ 2 + P.eval b = r} *
          ((q - 1) * q + #{p : F × F | P.eval p.1 = P.eval p.2}) :=
      card_sq_add_fn_fiber_lower_bound hF P.eval
    _ ≤ _ * ((q - 1) * q + P.natDegree * q) :=
      Nat.mul_le_mul_left _
        (Nat.add_le_add_left (card_Polynomial_eqpair_le_of_degree_mul_q hP) _)
    _ = _ * (q - 1 + P.natDegree) * q := by rw [Nat.mul_assoc, ← Nat.add_mul]
    _ = _ * (q + (P.natDegree - 1)) * q := by
      rw [Nat.add_comm, ← Nat.add_sub_assoc hq, Nat.add_comm, Nat.add_sub_assoc hP]

/-- Simple bound on the number of elements of `F` of the form `a^2 + P(b)`, `P ∈ F[X]`. -/
theorem card_sq_add_Polynomial_fiber_lower_bound_simple {P : F[X]} (hP : 1 < P.natDegree) :
    q < #{r | ∃ a b, a ^ 2 + P.eval b = r} + (P.natDegree - 1) := by
  ---- Let `n' = deg(P) - 1`, and first write down `n' > 0`.
  set n' : ℕ := P.natDegree - 1
  have hn' : 0 < n' := Nat.sub_pos_of_lt hP
  ---- First de-cancel a factor of `q + n - 1` from both sides, where `n = deg(P)`.
  refine Nat.lt_of_mul_lt_mul_right (a := q + n') ?_
  ---- Now estimate.
  calc q * (q + n')
    _ = q ^ 2 + q * n' := by rw [Nat.mul_add, Nat.pow_two]
    _ < #{r | ∃ a b, a ^ 2 + P.eval b = r} * (q + n') + (q + n') * n' :=
      Nat.add_lt_add_of_le_of_lt
        (card_sq_add_Polynomial_fiber_lower_bound (Nat.zero_lt_of_lt hP))
        (Nat.mul_lt_mul_of_pos_right (Nat.lt_add_of_pos_right hn') hn')
    _ = _ := by rw [Nat.mul_comm _ n', Nat.add_mul]





/-! ### Upper bound on the number of elements of `Fˣ` not of the form `a^2 + b^n` -/

/-- Simple bound on the number elements of `F` not of the form `a^2 + P(b)`, `P ∈ F[X]`. -/
theorem card_sq_add_Polynomial_not_fiber_upper_bound {P : F[X]} (hP : 1 < P.natDegree) :
    #{r | ¬∃ a b, a ^ 2 + P.eval b = r} < P.natDegree - 1 := by
  rw [← Nat.add_lt_add_iff_left, filter_card_add_filter_neg_card_eq_card]
  exact card_sq_add_Polynomial_fiber_lower_bound_simple hP

/-- Simple bound on the number elements of `F` not of the form `a^2 + b^n`, `n > 1`. -/
theorem card_sq_add_pow_not_fiber_upper_bound (hn : 1 < n) :
    #{r : F | ¬∃ a b, a ^ 2 + b ^ n = r} < n - 1 := by
  have hn0 : (X ^ n : F[X]).natDegree = n := natDegree_X_pow n
  simpa only [eval_pow, eval_X, hn0] using
    card_sq_add_Polynomial_not_fiber_upper_bound (hn.trans_eq hn0.symm)

/-- Simple bound on the number elements of `Fˣ` not of the form `a^2 + b^n`, `n > 1`. -/
theorem card_sq_add_pow_not_unit_fiber_upper_bound (hn : 1 < n) :
    #{r : Fˣ | ¬∃ a b, a ^ 2 + b ^ n = r.val} < n - 1 :=
  calc #{r : Fˣ | ¬∃ a b, a ^ 2 + b ^ n = r.val}
  _ ≤ #{r : F | ¬∃ a b, a ^ 2 + b ^ n = r} :=
    card_le_card_of_injOn Units.val
      (λ r hr ↦ by simpa only [mem_coe, mem_filter_univ] using hr)
      (Set.injOn_of_injective Units.val_injective)
  _ < n - 1 := card_sq_add_pow_not_fiber_upper_bound hn

end





/-! ### Lower bound on the number of elements of `Fˣ` not of the form `a^2 + b^n` -/

section

/-- Two distinct orbits of `⟨x₀⟩` above any subset is pairwise disjoint. -/
theorem orbit_zpowers_PairwiseDisjoint
    [Group G] [DecidableEq G] (H : Subgroup G) [Fintype H] [DecidableEq H] :
    (Set.range λ b : G ↦ image (λ a : H ↦ a * b) univ).PairwiseDisjoint id := by
  ---- Pick two orbits, say `⟨x⟩` and `⟨y⟩`. Claim: if they're not disjoint, `⟨x⟩ = ⟨y⟩`.
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
  refine disjoint_right.mpr λ a ha ha0 ↦ h (ext λ g ↦ ?_)
  simp only [id, mem_image, mem_univ, true_and] at ha ha0 ⊢
  rcases ha with ⟨z, rfl⟩; rcases ha0 with ⟨w, h⟩
  ---- Since `⟨x⟩` and `⟨y⟩` are not disjoint, `x = vy` for some `v ∈ H`.
  replace h : ((z⁻¹ * w : H) : G) * x = y := by
    rwa [← inv_mul_eq_iff_eq_mul, ← mul_assoc] at h
  generalize z⁻¹ * w = v at h
  subst h; clear z w
  ---- Now just split into cases and bash.
  refine ⟨?_, ?_⟩
  · rintro ⟨a, rfl⟩; refine ⟨a * v⁻¹, (?_ : a * (v : G)⁻¹ * _ = a * x)⟩
    rw [mul_assoc, ← mul_assoc _ _ x, inv_mul_cancel, one_mul]
  · rintro ⟨a, rfl⟩; exact ⟨a * v, mul_assoc _ _ _⟩

variable [Group G] [Fintype G] [DecidableEq G] {x₀ : G}
variable {S : Finset G} (hS : ∀ n : ℤ, ∀ s ∈ S, x₀ ^ n * s ∈ S)
include hS

/-- If `S` is invariant under left multiplication by `x₀`, then the
  binary image of `⟨x₀⟩ × S` under pointwise multiplication is exactly `S`. -/
theorem image_mul_zpowers_eq_self_of_mul_invariant :
    image₂ (λ (x : Subgroup.zpowers x₀) (s : G) ↦ x * s) univ S = S := by
  ext x; simp only [mem_image₂, mem_univ, true_and, Subgroup.exists_zpowers]
  exact ⟨λ ⟨m, y, hy, h⟩ ↦ h ▸ hS m y hy, λ hx ↦ ⟨0, x, hx, by rw [zpow_zero, one_mul]⟩⟩

/-- If `S` is invariant under left multiplication by `x₀`, then `ord(x_0) ∣ S`. -/
theorem order_dvd_card_Finset_of_mul_invariant : orderOf x₀ ∣ #S :=
  calc orderOf x₀
  _ = Fintype.card (Subgroup.zpowers x₀) := Fintype.card_zpowers.symm
  _ ∣ #(image₂ (λ (x : Subgroup.zpowers x₀) (s : G) ↦ x * s) univ S) :=
    card_dvd_card_image₂_left (λ b _ x y h ↦ by simpa using h)
      (Set.PairwiseDisjoint.subset (orbit_zpowers_PairwiseDisjoint _)
        (Set.image_subset_range _ _))
  _ = #S := congrArg card (image_mul_zpowers_eq_self_of_mul_invariant hS)

end


/-- `(q - 1)/gcd(q - 1, 2n)` divides the number of units not of the form `a^2 + b^n`. -/
theorem dvd_card_sq_add_pow_not_unit_fiber :
    (q - 1) / (q - 1).gcd (2 * n) ∣ #{r : Fˣ | ¬∃ a b, a ^ 2 + b ^ n = r.val} := by
  ---- Find a generator `g` for `Fˣ`.
  obtain ⟨g, hg⟩ : ∃ g : Fˣ, ∀ x : Fˣ, x ∈ Subgroup.zpowers g := IsCyclic.exists_generator
  /- Reduce calculation to showing that the bad set of elements not of the form
    `a^2 + b^5` is invariant under left multiplication by `x₀^{2n}`. -/
  calc (q - 1) / (q - 1).gcd (2 * n)
    _ = orderOf (g ^ (2 * n)) := by
      rw [orderOf_pow, orderOf_eq_card_of_forall_mem_zpowers hg,
        Nat.card_eq_fintype_card, Fintype.card_units]
    _ ∣ _ := order_dvd_card_Finset_of_mul_invariant λ k r hr ↦ ?_
  ---- Finally, show that the bad set is indeed invariant with respect to `x₀^{2n}`.
  rw [mem_filter_univ] at hr ⊢
  rintro ⟨a, b, h⟩
  refine hr ⟨(g⁻¹ ^ k) ^ n * a, (g⁻¹ ^ k) ^ 2 * b, ?_⟩
  calc ((g⁻¹ ^ k) ^ n * a) ^ 2 + ((g⁻¹ ^ k) ^ 2 * b) ^ n
    _ = (g⁻¹ ^ k) ^ (2 * n) * ((g ^ (2 * n)) ^ k * r : Fˣ) := by
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm, ← mul_add, h]
    _ = (g⁻¹ ^ k : Fˣ) ^ (2 * n) * (((g ^ (2 * n)) ^ k * r) : Fˣ) := by
      rw [← Units.val_zpow_eq_zpow_val]
    _ = ((g⁻¹ ^ k) ^ ((2 * n : ℕ) : ℤ) * ((g ^ ((2 * n : ℕ) : ℤ)) ^ k * r) : Fˣ) := rfl
    _ = (g⁻¹ ^ (k * (2 * n : ℕ)) * g ^ ((2 * n : ℕ) * k) * r : Fˣ) := by
      rw [← zpow_mul, ← zpow_mul, mul_assoc]
    _ = r := by rw [Int.mul_comm, ← mul_zpow, inv_mul_cancel, one_zpow, one_mul]

/-- `q - 1` divides `2n` times the number of units not of the form `a^2 + b^n`. -/
theorem dvd_two_mul_exp_mul_card_sq_add_pow_not_unit_fiber (hn : 0 < n) :
    q - 1 ∣ 2 * n * #{r : Fˣ | ¬∃ a b, a ^ 2 + b ^ n = r.val} := by
  have h : (q - 1).gcd (2 * n) ∣ q - 1 := Nat.gcd_dvd_left _ _
  have h0 : 0 < (q - 1).gcd (2 * n) :=
    Nat.gcd_pos_of_pos_right _ (Nat.mul_pos Nat.two_pos hn)
  rw [← Nat.dvd_gcd_mul_iff_dvd_mul, ← Nat.div_dvd_iff_dvd_mul h h0]
  exact dvd_card_sq_add_pow_not_unit_fiber





/-! ### Summary -/

/-- If `q > 2n(n - 1)`, every element of `F` is of the form `a^2 + b^n`. -/
theorem exists_eq_sq_add_pow (hn : 1 < n) (h : 2 * n * (n - 1) < q) :
    ∀ r : F, ∃ a b : F, a ^ 2 + b ^ n = r := by
  ---- Reduce to just the units.
  suffices ∀ r : Fˣ, ∃ a b : F, a ^ 2 + b ^ n = r by
    intro r; obtain rfl | hr : r = 0 ∨ r ≠ 0 := eq_or_ne r 0
    · refine ⟨0, 0, ?_⟩
      rw [zero_pow (Nat.succ_ne_zero 1), zero_add, zero_pow (Nat.ne_zero_of_lt hn)]
    · lift r to Fˣ using Ne.isUnit hr
      exact this r
  ---- Now the statement is equivalent to `N = #{r : Fˣ | ∃ a b, a^2 + b^n = r.val} = 0`.
  let N : ℕ := #{r : Fˣ | ¬∃ a b, a ^ 2 + b ^ n = r.val}
  suffices N = 0 by
    simpa only [N, card_filter_eq_zero_iff, mem_univ, forall_const, not_not] using this
  ---- We have `N < n - 1` and `q - 1 ∣ 2nN`.
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  replace hn : N < n - 1 := card_sq_add_pow_not_unit_fiber_upper_bound hn
  have h0 : q - 1 ∣ 2 * n * N := dvd_two_mul_exp_mul_card_sq_add_pow_not_unit_fiber hn0
  ---- Then `2nN < 2n(n - 1) ≤ q - 1`, so `2nN = 0` and thus `N = 0`.
  replace hn0 : 0 < 2 * n := Nat.mul_pos Nat.two_pos hn0
  replace h0 : 2 * n * N = 0 := Nat.eq_zero_of_dvd_of_lt h0 <| by
    calc 2 * n * N
      _ < 2 * n * (n - 1) := Nat.mul_lt_mul_of_pos_left hn hn0
      _ ≤ q - 1 := Nat.le_sub_one_of_lt h
  exact (Nat.mul_eq_zero.mp h0).resolve_left hn0.ne.symm

/-- If `q > 40`, every element of `F` is of the form `a^2 + b^5`. -/
theorem exists_eq_sq_add_pow_five (hF : 40 < q) :
    ∀ r : F, ∃ a b : F, a ^ 2 + b ^ 5 = r :=
  exists_eq_sq_add_pow (n := 5) (Nat.one_lt_succ_succ 3 : 1 < 5) hF

/-- Final solution -/
theorem final_solution {p : ℕ} [Fact p.Prime] (hp : 40 < p) (r : ℤ) :
    ∃ a b : ℤ, a ^ 2 + b ^ 5 ≡ r [ZMOD p] := by
  obtain ⟨a, b, h0⟩ : ∃ a b : ZMod p, a ^ 2 + b ^ 5 = r :=
    exists_eq_sq_add_pow_five (hp.trans_eq (ZMod.card p).symm) r
  exact ⟨a.val, b.val, (ZMod.intCast_eq_intCast_iff _ _ _).mp (by simpa using h0)⟩
