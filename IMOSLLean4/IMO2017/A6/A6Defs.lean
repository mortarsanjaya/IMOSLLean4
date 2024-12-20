/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.FunLike.Basic

/-!
# IMO 2017 A6 (P2, Definitions)

Let $R$ be a ring, $G$ be an abelian group, and $ι : R → G$ be a group homomorphism.
Determine all functions $f : R → G$ such that, for any $x, y ∈ R$,
$$ f(ι(f(x)) ι(f(y))) + f(x + y) = f(xy). $$

We say that $f$ is
* *$ι$-good* if $f$ satisfies the above functional equation;
* *non-periodic $ι$-good* if $f$ is $ι$-good and has no non-zero period.

This file defines the functional equation and prove basic properties.
The good functions are characterized for a decent amount of subcases.
The file `IMOSLLean4/IMO2017/A6/A6.lean` collects all the main results.

### Note

Currently, the definition only assumes that $ι$ is a function for extreme generality.
I think only defining good functions for homomorphisms is a better practice, but...
-/

namespace IMOSL
namespace IMO2017A6

/-! ### Good functions -/

section

variable [Add R] [Mul R] [Add G]

/-- Good function. -/
structure GoodFun (ι : G → R) where
  toFun : R → G
  good_def' : ∀ x y, toFun (ι (toFun x) * ι (toFun y)) + toFun (x + y) = toFun (x * y)

/-- Class of good functions; see mathlib's `DFunLike` design. -/
class GoodFunClass (F) (ι : G → R) [FunLike F R G] where
  good_def : ∀ (f : F) (x y : R), f (ι (f x) * ι (f y)) + f (x + y) = f (x * y)


namespace GoodFun

instance (ι : G → R) : FunLike (GoodFun ι) R G where
  coe f := f.toFun
  coe_injective' f g h := by rwa [GoodFun.mk.injEq]

instance (ι : G → R) : GoodFunClass (GoodFun ι) ι where
  good_def f := f.good_def'

@[ext] theorem ext {ι : G → R} {f g : GoodFun ι} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

/-- The zero function as a good function. -/
protected def zero {G} [AddZeroClass G] (ι : G → R) : GoodFun ι where
  toFun _ := 0
  good_def' _ _ := zero_add 0

instance {G} [AddZeroClass G] (ι : G → R) : Zero (GoodFun ι) := ⟨GoodFun.zero ι⟩

end GoodFun


variable (ι : G → R) [FunLike F R G] [GoodFunClass F ι]

/-- Coercion from `GoodFunClass` to `GoodFun`. -/
def GoodFunClass.toGoodFun (f : F) : GoodFun ι where
  toFun := f
  good_def' := good_def f

theorem good_def (f : F) : ∀ x y, f (ι (f x) * ι (f y)) + f (x + y) = f (x * y) :=
  GoodFunClass.good_def f

end





/-! ### Non-periodic good functions -/

section

variable [Add R] [Mul R] [Add G]

/-- Non-periodic good functions. -/
structure NonperiodicGoodFun (ι : G → R) extends GoodFun ι where
  period_imp_eq' (c d) (_ : ∀ x, toFun (x + c) = toFun (x + d)) : c = d

/-- Class of non-periodic good functions; see mathlib's `DFunLike` design. -/
class NonperiodicGoodFunClass (F) (ι : G → R) [FunLike F R G] extends GoodFunClass F ι where
  period_imp_eq (f : F) (c d) (_ : ∀ x, f (x + c) = f (x + d)) : c = d


namespace NonperiodicGoodFun

instance (ι : G → R) : FunLike (NonperiodicGoodFun ι) R G where
  coe f := f.toFun
  coe_injective' f g h := by rwa [NonperiodicGoodFun.mk.injEq, ← DFunLike.coe_fn_eq]

instance (ι : G → R) : NonperiodicGoodFunClass (NonperiodicGoodFun ι) ι where
  good_def f := f.good_def'
  period_imp_eq f := f.period_imp_eq'

@[ext] theorem ext {ι : G → R} {f g : NonperiodicGoodFun ι} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

end NonperiodicGoodFun


variable (ι : G → R) [FunLike F R G] [NonperiodicGoodFunClass F ι]
include ι

/-- Coercion from `NonperiodicGoodFunClass` to `NonperiodicGoodFun`. -/
def NonperiodicGoodFunClass.toNonperiodicGoodFun (f : F) : NonperiodicGoodFun ι :=
  { GoodFunClass.toGoodFun ι f with period_imp_eq' := period_imp_eq ι f }

theorem period_imp_eq {f : F} : (∀ x, f (x + c) = f (x + d)) → c = d :=
  NonperiodicGoodFunClass.period_imp_eq ι f _ _

theorem period_iff_eq {f : F} : (∀ x, f (x + c) = f (x + d)) ↔ c = d :=
  ⟨period_imp_eq ι, λ h _ ↦ by rw [h]⟩

end


section

variable [AddZeroClass R] [Mul R] [Add G] (ι : G → R)
  [FunLike F R G] [NonperiodicGoodFunClass F ι] {f : F}
include ι

theorem period_imp_zero (h : ∀ x, f (x + c) = f x) : c = 0 :=
  period_imp_eq ι (f := f) λ x ↦ by rw [h, add_zero]

theorem period_iff_zero : (∀ x, f (x + c) = f x) ↔ c = 0 :=
  ⟨period_imp_zero ι, λ h _ ↦ by rw [h, add_zero]⟩

end





/-! ### Properties of good functions involving equality of values of `f` -/

section

variable [Add R] [Mul R] [Add G] (ι : G → R) [FunLike F R G] [GoodFunClass F ι]
include ι

lemma map_mul_eq_of_map_eq_of_map_add_eq
    {f : F} (h : f a = f b) (h0 : f c = f d) (h1 : f (a + c) = f (b + d)) :
    f (a * c) = f (b * d) := by
  rw [← good_def ι, h, h0, h1, good_def]

lemma map_mul_left_eq_of_map_add_left_eq
    {f : F} (h : f a = f b) (h0 : f (c + a) = f (c + b)) :
    f (c * a) = f (c * b) :=
  map_mul_eq_of_map_eq_of_map_add_eq ι rfl h h0

lemma map_mul_right_eq_of_map_add_right_eq
    {f : F} (h : f a = f b) (h0 : f (a + c) = f (b + c)) :
    f (a * c) = f (b * c) :=
  map_mul_eq_of_map_eq_of_map_add_eq ι h rfl h0

end


section

variable [Add R] [Mul R] [Add G] [IsCancelAdd G] (ι : G → R)
  [FunLike F R G] [GoodFunClass F ι] {f : F} (h : f a = f b)
include ι h

lemma map_add_eq_iff_map_mul_eq (h0 : f c = f d) :
    f (a + c) = f (b + d) ↔ f (a * c) = f (b * d) := by
  rw [← good_def ι, h, h0, ← good_def ι f b, add_left_cancel_iff]

lemma map_add_right_eq_iff_map_mul_right_eq :
    f (a + c) = f (b + c) ↔ f (a * c) = f (b * c) :=
  map_add_eq_iff_map_mul_eq ι h rfl

lemma map_add_left_eq_iff_map_mul_left_eq :
    f (c + a) = f (c + b) ↔ f (c * a) = f (c * b) :=
  map_add_eq_iff_map_mul_eq ι rfl h

end


lemma map_add_one_eq_of_map_eq [Add R] [MulOneClass R] [Add G] [IsCancelAdd G] (ι : G → R)
    [FunLike F R G] [GoodFunClass F ι] {f : F} (h : f a = f b) : f (a + 1) = f (b + 1) := by
  rwa [map_add_right_eq_iff_map_mul_right_eq ι h, mul_one, mul_one]


section

variable [NonAssocSemiring R] [Add G] [IsCancelAdd G] (ι : G → R)
  [FunLike F R G] [GoodFunClass F ι] {f : F} (h : f a = f b)
include ι h

lemma map_add_nat_eq_of_map_eq (n : ℕ) : f (a + n) = f (b + n) := by
  induction n with
  | zero => simpa using h
  | succ n n_ih => simpa [add_assoc] using map_add_one_eq_of_map_eq ι n_ih

lemma map_mul_nat_eq_of_map_eq (n : ℕ) : f (a * n) = f (b * n) :=
  (map_add_right_eq_iff_map_mul_right_eq ι h).mp (map_add_nat_eq_of_map_eq ι h n)

end


section

variable [NonAssocRing R] [Add G] [IsCancelAdd G] (ι : G → R)
  [FunLike F R G] [GoodFunClass F ι] {f : F}
include ι

lemma map_neg_add_one_eq_of_map_eq (h : f a = f b) : f (-(a + 1)) = f (-(b + 1)) := by
  simpa only [mul_neg_one] using map_mul_right_eq_of_map_add_right_eq ι
    (map_add_one_eq_of_map_eq ι h) (c := -1) (by simp only [add_neg_cancel_right, h])

lemma map_neg_eq_of_map_eq (h : f a = f b) : f (-a) = f (-b) := by
  simpa using map_add_one_eq_of_map_eq ι (map_neg_add_one_eq_of_map_eq ι h)

lemma map_neg_eq_iff_map_eq : f (-a) = f (-b) ↔ f a = f b :=
  ⟨λ h ↦ by simpa only [neg_neg] using map_neg_eq_of_map_eq ι h, map_neg_eq_of_map_eq ι⟩

lemma map_neg_eq_iff_map_eq' : f (-a) = f b ↔ f a = f (-b) := by
  rw [← map_neg_eq_iff_map_eq ι, neg_neg]

lemma map_sub_eq_iff_map_mul_eq (h : f a = f b) (h0 : f c = f d) :
    f (a - c) = f (b - d) ↔ f (a * c) = f (b * d) := by
  rw [← map_neg_eq_iff_map_eq ι (a := a * c), sub_eq_add_neg, sub_eq_add_neg,
    map_add_eq_iff_map_mul_eq ι h (map_neg_eq_of_map_eq ι h0), mul_neg, mul_neg]

lemma map_sub_one_eq_of_map_eq (h : f a = f b) : f (a - 1) = f (b - 1) := by
  rwa [map_sub_eq_iff_map_mul_eq ι h rfl, mul_one, mul_one]

lemma map_sub_nat_eq_of_map_eq (h : f a = f b) (n : ℕ) : f (a - n) = f (b - n) :=
  (map_sub_eq_iff_map_mul_eq ι h rfl).mpr (map_mul_nat_eq_of_map_eq ι h n)

lemma map_add_nat_eq_iff_map_eq {n : ℕ} : f (a + n) = f (b + n) ↔ f a = f b :=
  ⟨λ h ↦ by simpa [sub_eq_add_neg] using map_sub_nat_eq_of_map_eq ι h n,
  λ h ↦ map_add_nat_eq_of_map_eq ι h n⟩

lemma map_sub_nat_eq_iff_map_eq {n : ℕ} : f (a - n) = f (b - n) ↔ f a = f b :=
  (map_add_nat_eq_iff_map_eq ι (n := n)).symm.trans (by simp [sub_eq_add_neg, add_assoc])

lemma map_add_one_eq_iff_map_eq : f (a + 1) = f (b + 1) ↔ f a = f b := by
  simpa only [Nat.cast_one] using map_add_nat_eq_iff_map_eq ι (f := f) (n := 1)

lemma map_sub_one_eq_iff_map_eq : f (a - 1) = f (b - 1) ↔ f a = f b := by
  simpa only [Nat.cast_one] using map_sub_nat_eq_iff_map_eq ι (f := f) (n := 1)

end





/-! ### Additional basic properties of good functions -/

section

variable [NonUnitalNonAssocSemiring R] [Add G] (ι : G → R)
  [FunLike F R G] [GoodFunClass F ι] (f : F) (x : R)

theorem map_incl_map_zero_mul_incl_map_add_map : f (ι (f 0) * ι (f x)) + f x = f 0 := by
  simpa only [zero_add, zero_mul] using good_def ι f 0 x

theorem map_incl_map_mul_incl_map_zero_add_map : f (ι (f x) * ι (f 0)) + f x = f 0 := by
  simpa only [add_zero, mul_zero] using good_def ι f x 0

end


section

variable [NonUnitalNonAssocSemiring R] [Add G] [IsCancelAdd G] (ι : G → R)
  [FunLike F R G] [GoodFunClass F ι]

lemma map_eq_of_incl_map_eq {f : F} (h : ι (f a) = ι (f b)) : f a = f b := by
  rw [← add_left_cancel_iff, map_incl_map_zero_mul_incl_map_add_map ι,
    h, map_incl_map_zero_mul_incl_map_add_map ι]

theorem map_incl_map_comm_incl_map_zero (f : F) (x) :
    f (ι (f x) * ι (f 0)) = f (ι (f 0) * ι (f x)) := by
  rw [← add_right_cancel_iff, map_incl_map_zero_mul_incl_map_add_map,
    map_incl_map_mul_incl_map_zero_add_map]

end


section

variable [NonUnitalNonAssocSemiring R] [AddZeroClass G] [IsCancelAdd G] (ι : G → R)
  [FunLike F R G] [GoodFunClass F ι]

lemma map_eq_zero_of_incl_map_eq_zero {f : F} (h : ι (f a) = 0) : f a = 0 := by
  rw [← add_left_cancel_iff, map_incl_map_zero_mul_incl_map_add_map ι, h, mul_zero, add_zero]

lemma map_incl_map_zero_mul_self (f : F) : f (ι (f 0) * ι (f 0)) = 0 := by
  rw [← add_right_cancel_iff, map_incl_map_zero_mul_incl_map_add_map, zero_add]

end
