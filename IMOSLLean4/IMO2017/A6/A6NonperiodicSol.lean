/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2017.A6.A6Basic
import IMOSLLean4.IMO2017.A6.ExcellentFun.AddHom
import IMOSLLean4.IMO2017.A6.Extra.CentralInvolutive
import Mathlib.Algebra.Ring.Basic

/-!
# IMO 2017 A6 (P2, Construction of non-periodic good functions)

Let $R$ be a ring, $G$ be an abelian group, and $ι : G → R$ be a group homomorphisms.
We construct a class of non-periodic $ι$-good functions.
We also define a condition that implies that these are the only ones for a given $ι$.
-/

namespace IMOSL
namespace IMO2017A6
namespace NonperiodicGoodFun

/-! ### The main constructor for non-periodic good functions -/

section

variable [Ring R] [AddZeroClass G] (ι : G → R)

def ofProdCenterHom_uncurry
    (a : CentralInvolutive R) (φ : {φ : R →+ G // ∀ x, ι (φ x) = x}) :
    NonperiodicGoodFun ι where
  toFun x := φ.1 (a.1 * (1 - x))
  good_def' x y := by
    rw [φ.2, φ.2, ← φ.1.map_add, ← mul_add]
    refine congrArg (λ x ↦ φ.1 (a.1 * x)) ?_
    rw [a.mul_comm, mul_assoc, ← mul_assoc a.1, a.2, one_mul, mul_one_sub, one_sub_mul,
      sub_sub, sub_sub_cancel, ← add_sub_assoc x, sub_add_sub_cancel']
  period_imp_eq' c d h := by
    dsimp only at h
    replace h : a.1 * ι (φ.1 _) = a.1 * ι (φ.1 _) := congrArg (a.1 * ι ·) (h 1)
    rwa [φ.2, φ.2, ← mul_assoc, ← mul_assoc, a.2, one_mul, one_mul,
      sub_add_cancel_left, sub_add_cancel_left, neg_inj] at h

variable (p : CentralInvolutive R × {φ : R →+ G // ∀ x, ι (φ x) = x})
include p

def ofProdCenterHom : NonperiodicGoodFun ι :=
  ofProdCenterHom_uncurry ι p.1 p.2

@[simp] theorem ofProdCenterHom_apply (x) :
    ofProdCenterHom ι p x = p.2.1 (p.1.1 * (1 - x)) := rfl

end





/-! ### Injectivity of non-periodic good functions -/

/-- Class stating that all non-periodic $ι$-good functions are injective. -/
class IsForallInjective [AddZeroClass R] [Mul R] [AddZeroClass G] (ι : G → R) : Prop where
  is_injective : ∀ f : NonperiodicGoodFun ι, Function.Injective f

theorem is_injective [Ring R] [AddZeroClass G] {ι : G → R} [IsForallInjective ι] :
    ∀ f : NonperiodicGoodFun ι, Function.Injective f :=
  IsForallInjective.is_injective


variable [Ring R] [AddCancelMonoid G]


section

variable {ι : G →+ R} [IsForallInjective ι] (f : NonperiodicGoodFun ι)
include f

/-- If possible, use `Center_spec` instead. -/
theorem incl_map_eq (x) : ι (f x) = ι (f 0) * (1 - x) := by
  rw [← f.is_injective (map_incl_map_zero_mul_incl_map_eq_map_one_sub ι f x),
    ← mul_assoc, incl_map_zero_mul_self, one_mul]

theorem incl_map_zero_comm (x) : ι (f 0) * x = x * ι (f 0) := by
  have h := incl_map_zero_comm_incl_map ι f (1 - x)
  rw [f.incl_map_eq (1 - x), sub_sub_cancel, mul_assoc] at h
  replace h : ι (f 0) * _ = ι (f 0) * _ := congrArg (_ * ·) h
  rwa [← mul_assoc, ← mul_assoc (ι (f 0)), incl_map_zero_mul_self, one_mul, one_mul] at h

/-- Center of a non-periodic $ι$-good function: $ι(f(0))$ bundled with its properties. -/
@[irreducible] def Center : CentralInvolutive R :=
  ⟨ι (f 0), incl_map_zero_mul_self ι f, f.incl_map_zero_comm⟩

/-- In practice, this should not be used. -/
theorem Center_def : f.Center.val = ι (f 0) := by
  rw [Center]

theorem Center_spec (x) : ι (f x) = f.Center.1 * (1 - x) := by
  rw [Center, f.incl_map_eq x]

/-- An $ι$-good function as an excellent function. -/
def mkExcellentFun : ExcellentFun R G where
  toFun x := f (1 - x)
  excellent_def' x y := by
    simp only [sub_sub_cancel]; convert good_def ι f x y using 3
    rw [f.Center_spec, f.Center_spec, f.Center.mul_comm, mul_assoc, ← mul_assoc f.Center.1,
      f.Center.mul_self_eq_one, one_mul, mul_one_sub, one_sub_mul, sub_sub, add_sub_assoc]

@[simp] theorem mkExcellentFun_apply (x) : f.mkExcellentFun x = f (1 - x) := rfl

end


section

variable [ExcellentFun.IsOfAddMonoidHomSurjective R G]
  {ι : G →+ R} [IsForallInjective ι] (f : NonperiodicGoodFun ι)
include f

/-- The function $x ↦ f(1 - ax)$ as a group homomorphism, where $a = ι(f(0))$. -/
def mkAddMonoidHom : R →+ G :=
  f.mkExcellentFun.toAddMonoidHom.comp (AddMonoidHom.mulLeft f.Center.1)

@[simp] theorem mkAddMonoidHom_apply (x) : f.mkAddMonoidHom x = f (1 - f.Center.1 * x) := rfl

theorem incl_mkAddMonoidHom_apply (x) : ι (f.mkAddMonoidHom x) = x := by
  rw [mkAddMonoidHom_apply, Center_spec, sub_sub_cancel,
    ← mul_assoc, f.Center.mul_self_eq_one, one_mul]

def toProdCenterHom : CentralInvolutive R × {φ : R →+ G // ∀ x, ι (φ x) = x} :=
  ⟨f.Center, f.mkAddMonoidHom, f.incl_mkAddMonoidHom_apply⟩

theorem toProdCenterHom_ofProdCenterHom : ofProdCenterHom ι f.toProdCenterHom = f := by
  refine NonperiodicGoodFun.ext λ x ↦ ?_
  change f (1 - f.Center.val * (f.Center.val * (1 - x))) = f x
  rw [← mul_assoc, f.Center.mul_self_eq_one, one_mul, sub_sub_cancel]

end
