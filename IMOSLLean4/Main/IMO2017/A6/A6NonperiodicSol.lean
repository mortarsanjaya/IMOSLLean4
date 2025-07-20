/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Main.IMO2017.A6.A6Basic
import IMOSLLean4.Main.IMO2017.A6.ExcellentFun.AddMonoidHom
import IMOSLLean4.Main.IMO2017.A6.CentralInvolutive.Defs
import Mathlib.Algebra.Ring.Basic

/-!
# IMO 2017 A6 (P2, Construction of non-periodic good functions)

Let $R$ be a ring, $G$ be an abelian group, and $ι : G → R$ be a group homomorphisms.
We construct a class of non-periodic $ι$-good functions from
* $a ∈ Z(R)$ with $a^2 = 1$ and an excellent function $φ : R → G$ such that $ι(φ(x)) = ax$;
* $a ∈ Z(R)$ with $a^2 = 1$ and a group homomorphism $φ : R → G$ such that $ι(φ(x)) = x$.
We show that the first construction gives all the injective non-periodic $ι$-good functions.

In addition, we provide a simpler constructor for the case $ι = id$.
It only takes $a ∈ Z(R)$ with $a^2 = 1$ as a parameter.
-/

namespace IMOSL
namespace IMO2017A6

/-! ### `x ↦ 1 - x` and variants as a non-periodic good function -/

section

variable [NonAssocRing R]

theorem one_sub_mul_one_sub (x y : R) : (1 - x) * (1 - y) = 1 - (x + y - x * y) := by
  rw [mul_one_sub, one_sub_mul, sub_sub, add_sub_assoc]

theorem IsGoodFun_one_sub_explicit (x y : R) :
    1 - (1 - x) * (1 - y) + (1 - (x + y)) = 1 - x * y := by
  rw [one_sub_mul_one_sub, sub_sub_cancel, sub_add_sub_cancel']

theorem IsNonperiodicGoodFun.one_sub :
    IsNonperiodicGoodFun (id : R → R) (λ x : R ↦ 1 - x) :=
  ⟨⟨IsGoodFun_one_sub_explicit⟩,
  λ h ↦ by simpa only [sub_add_cancel_left, neg_inj] using h 1⟩

/-- `x ↦ 1 - x` as a non-periodic good function. -/
def NonperiodicGoodFun.one_sub : NonperiodicGoodFun (id : R → R) :=
  IsNonperiodicGoodFun.one_sub.toNonperiodicGoodFun

theorem IsGoodFun_sub_one_explicit (x y : R) :
    (x - 1) * (y - 1) - 1 + (x + y - 1) = x * y - 1 := by
  rw [sub_one_mul, sub_sub, sub_add_cancel, mul_sub_one, sub_sub, sub_add_sub_cancel]

theorem IsNonperiodicGoodFun.sub_one :
    IsNonperiodicGoodFun (id : R → R) (λ x : R ↦ x - 1) :=
  ⟨⟨IsGoodFun_sub_one_explicit⟩,
  λ h ↦ by simpa only [add_sub_cancel_left] using h 1⟩

/-- `x ↦ 1 - x` as a non-periodic good function. -/
def NonperiodicGoodFun.sub_one : NonperiodicGoodFun (id : R → R) :=
  IsNonperiodicGoodFun.sub_one.toNonperiodicGoodFun

end





namespace NonperiodicGoodFun

/-! ### The main constructors for non-periodic good functions -/

section

variable [Ring R] [Add G] (ι : G → R) (a : CentralInvolutive R)

/-- Non-periodic good function from `CentralInvolutive R` and excellent functions. -/
def ofCenterExcellent (φ : {φ : ExcellentFun R G // ∀ x, ι (φ x) = a * x}) :
    NonperiodicGoodFun ι where
  toFun x := φ.1 (1 - x)
  good_def' x y := by rw [φ.2, φ.2, a.mul_mul_mul_cancel_left,
      one_sub_mul_one_sub, sub_sub_cancel, excellent_def]
  period_imp_eq' c d h := a.mul_left_inj.mp (by simpa [φ.2] using congrArg ι (h 1))

@[simp] theorem ofCenterExcellent_apply (φ x) :
  ofCenterExcellent ι a φ x = φ.1 (1 - x) := rfl

end


section

variable [Ring R] [AddZeroClass G] (ι : G → R) (a : CentralInvolutive R)

/-- Non-periodic good functions from `CentralInvolutive R` group homomorphisms. -/
def ofCenterHom (φ : {φ : R →+ G // ∀ x, ι (φ x) = x}) : NonperiodicGoodFun ι :=
  ofCenterExcellent ι a
    ⟨ExcellentFun.ofAddMonoidHom (φ.1.comp (AddMonoidHom.mulLeft a.1)), λ _ ↦ φ.2 _⟩

@[simp] theorem ofCenterHom_apply (φ x) : ofCenterHom ι a φ x = φ.1 (a * (1 - x)) := rfl

end


section

variable [Ring R] (a : CentralInvolutive R)

/-- Non-periodic `id`-good functions from `CentralInvolutive R`. -/
def ofCenterId : NonperiodicGoodFun (id : R → R) :=
  ofCenterHom _ a ⟨AddMonoidHom.id R, λ _ ↦ rfl⟩

@[simp] theorem ofCenterId_apply (x) : ofCenterId a x = a * (1 - x) := rfl

end





/-! ### Injective non-periodic good functions -/

variable [Ring R] [AddCancelMonoid G]


section

variable {ι : G →+ R} (f : NonperiodicGoodFun ι) (hf : Function.Injective f)
include f hf

/-- If possible, use `Center_spec` instead. -/
theorem incl_map_eq (x) : ι (f x) = ι (f 0) * (1 - x) := by
  rw [← hf (map_incl_map_zero_mul_incl_map_eq_map_one_sub ι f x),
    ← mul_assoc, incl_map_zero_mul_self, one_mul]

theorem incl_map_zero_comm (x) : x * ι (f 0) = ι (f 0) * x := by
  have h := (incl_map_zero_comm_incl_map ι f (1 - x)).symm
  rw [f.incl_map_eq hf (1 - x), sub_sub_cancel, mul_assoc] at h
  replace h : ι (f 0) * _ = ι (f 0) * _ := congrArg (_ * ·) h
  rwa [← mul_assoc, ← mul_assoc (ι (f 0)), incl_map_zero_mul_self, one_mul, one_mul] at h

/-- Center of an injective non-periodic $ι$-good function: bundled $ι(f(0))$. -/
def Center : CentralInvolutive R :=
  ⟨ι (f 0), incl_map_zero_mul_self ι f, f.incl_map_zero_comm hf⟩

/-- In practice, this should not be used. -/
theorem Center_def : (f.Center hf).val = ι (f 0) := rfl

theorem Center_spec (x) : ι (f x) = (f.Center hf).val * (1 - x) :=
  f.incl_map_eq hf x

/-- An $ι$-good function as an excellent function. -/
def mkExcellentFun : ExcellentFun R G where
  toFun x := f (1 - x)
  excellent_def' x y := by simpa only [sub_sub_cancel, f.Center_spec hf,
    (f.Center hf).mul_mul_mul_cancel_left, one_sub_mul_one_sub] using good_def ι f x y

@[simp] theorem mkExcellentFun_apply (x) : f.mkExcellentFun hf x = f (1 - x) := rfl

theorem incl_mkExcellentFun_apply (x) :
    ι (f.mkExcellentFun hf x) = (f.Center hf).val * x := by
  rw [f.mkExcellentFun_apply hf, f.Center_spec hf, sub_sub_cancel]

theorem eq_ofCenterExcellent :
    f = ofCenterExcellent ι (f.Center hf)
      ⟨f.mkExcellentFun hf, f.incl_mkExcellentFun_apply hf⟩ :=
  ext λ x ↦ by rw [ofCenterExcellent_apply, mkExcellentFun_apply, sub_sub_cancel]

theorem exists_eq_ofCenterExcellent : ∃ a φ, f = ofCenterExcellent ι a φ :=
  ⟨_, _, f.eq_ofCenterExcellent hf⟩

end


/-- A version of `exists_eq_ofCenterExcellent` with group homomorphisms. -/
theorem exists_eq_ofCenterHom [ExcellentFun.IsOfAddMonoidHomSurjective R G]
    {ι : G →+ R} (f : NonperiodicGoodFun ι) (hf : Function.Injective f) :
    ∃ a φ, f = ofCenterHom ι a φ := by
  obtain ⟨a, φ, rfl⟩ := f.exists_eq_ofCenterExcellent hf
  exact ⟨a, ⟨φ.1.toAddMonoidHom.comp (AddMonoidHom.mulLeft a),
      λ x ↦ (φ.2 (a * x)).trans (a.mul_mul_cancel_left x)⟩,
    congrArg _ (by ext x; exact congrArg φ.1 (a.mul_mul_cancel_left x).symm)⟩

/-- A version of `exists_eq_ofCenterExcellent` for `ι = id`. -/
theorem exists_eq_ofCenterId (f : NonperiodicGoodFun id) (hf : Function.Injective f) :
    ∃ a : CentralInvolutive R, f = ofCenterId a :=
  let ι := AddMonoidHom.id R; ⟨f.Center (ι := ι) hf, ext (f.Center_spec (ι := ι) hf)⟩

end NonperiodicGoodFun
