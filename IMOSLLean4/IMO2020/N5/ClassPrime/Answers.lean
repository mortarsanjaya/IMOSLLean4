/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.Extra.PAdicValCompl.ZModUnit
import IMOSLLean4.IMO2020.N5.Extra.EvenMonoidHom.Basic

/-!
# IMO 2020 N5 (Prime Class Solutions)

Let `p` be a prime and `M` be a commutative monoid.
We construct a map `Hom_mk : (M × (ZMod p)ˣ/{±1} →* M) →* (ℕ+ →* M)`.
For any map `f : ℕ+ →* M` in the image, `p^k` is `f`-nice for all `k : ℕ`.
This fact will be proved in the file `ClassPrime/Main.lean`.

Instead of explicitly using `(ZMod p)ˣ/{±1}`, we use `EvenMonoidHom`.
See `Extra/EvenMonoidHom/Basic.lean` for more details.
-/

namespace IMOSL
namespace IMO2020N5
namespace primeClass

variable (p : Nat.Primes) (M : Type*) [CommMonoid M]

/-- Map `M → (ℕ+ →* M)` -/
def ofPVal (c : M) : ℕ+ →* M :=
  { toFun := λ n ↦ c ^ padicValPNat p n
    map_one' := pow_zero c
    map_mul' := λ x y ↦ by rw [← pow_add, ← padicValPNat.mul] }

lemma ofPVal_one : ofPVal p M 1 = 1 :=
  MonoidHom.ext λ _ ↦ one_pow _

lemma ofPVal_mul (x y : M) : ofPVal p M (x * y) = ofPVal p M x * ofPVal p M y :=
  MonoidHom.ext λ _ ↦ mul_pow x y _

/-- Homomorphism `M →* (ℕ+ →* M)` -/
def Hom_ofPVal : M →* (ℕ+ →* M) :=
  { toFun := ofPVal p M
    map_one' := ofPVal_one p M
    map_mul' := ofPVal_mul p M }



/-- Map `EvenMonoidHom (ZMod p)ˣ M → (ℕ+ →* M)` -/
def ofEvenMonoidHom (f : EvenMonoidHom (ZMod p)ˣ M) : ℕ+ →* M :=
  f.toMonoidHom.comp (padicComplPNat.ZModUnitHom p)

lemma ofEvenMonoidHom_one : ofEvenMonoidHom p M 1 = 1 := rfl

lemma ofEvenMonoidHom_mul (f g : EvenMonoidHom (ZMod p)ˣ M) :
    ofEvenMonoidHom p M (f * g) =
      ofEvenMonoidHom p M f * ofEvenMonoidHom p M g := rfl

lemma ofEvenMonoidHom_apply_self_pred (f : EvenMonoidHom (ZMod p)ˣ M) :
    (ofEvenMonoidHom p M f).toFun (p - 1) = 1 :=
  f.map_neg_one ▸ congr_arg f (padicComplPNat.ZModUnit_pred p)

/-- Homomorphism `EvenMonoidHom (ZMod p)ˣ M →* (ℕ+ →* M)` -/
def Hom_ofEvenMonoidHom : EvenMonoidHom (ZMod p)ˣ M →* (ℕ+ →* M) :=
  { toFun := ofEvenMonoidHom p M
    map_one' := ofEvenMonoidHom_one p M
    map_mul' := ofEvenMonoidHom_mul p M }




/-- Homomorphism `M × EvenMonoidHom (ZMod p)ˣ M →* (ℕ+ →* M)` -/
def Hom_mk : M × EvenMonoidHom (ZMod p)ˣ M →* (ℕ+ →* M) :=
  (Hom_ofPVal p M).coprod (Hom_ofEvenMonoidHom p M)

section

variable (x : M × EvenMonoidHom (ZMod p)ˣ M)

lemma Hom_mk_def :
    (Hom_mk p M).toFun x = ofPVal p M x.1 * ofEvenMonoidHom p M x.2 := rfl

lemma Hom_mk_apply (n : ℕ+) :
    ((Hom_mk p M).toFun x).toFun n =
      x.1 ^ padicValPNat p n * x.2 (padicComplPNat.ZModUnit p n) := rfl

lemma Hom_mk_apply_self :
    ((Hom_mk p M).toFun x).toFun p = x.1 := by
  rw [Hom_mk_apply, padicValPNat.self, pow_one,
    padicComplPNat.ZModUnit_self, x.2.map_one, mul_one]

lemma Hom_mk_apply_of_not_dvd (h0 : ¬(p : ℕ+) ∣ n) :
    ((Hom_mk p M).toFun x).toFun n = x.2 (padicComplPNat.ZModUnit p n) := by
  rw [Hom_mk_apply, padicValPNat.zero_of_not_dvd p h0, pow_zero, one_mul]

lemma Hom_mk_apply_pred : ((Hom_mk p M).toFun x).toFun (p - 1) = 1 := by
  rw [Hom_mk_apply, padicValPNat.pred, pow_zero, one_mul]
  exact (congr_arg _ (padicComplPNat.ZModUnit_pred _)).trans x.2.map_neg_one

lemma Hom_mk_apply_ZModUnit_toPNat (z : (ZMod p)ˣ) :
    ((Hom_mk p M).toFun x).toFun (ZModUnit_toPNat p.2 z) = x.2 z := by
  rw [Hom_mk_apply_of_not_dvd p M x (not_dvd_ZModUnit_toPNat p.2 z),
    padicComplPNat.ZModUnit_of_toPNat]

end
