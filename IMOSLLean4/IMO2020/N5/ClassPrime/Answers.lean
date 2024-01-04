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
We construct a map `goodPHom_mk : (M × (ZMod p)ˣ/{±1} →* M) →* (ℕ+ →* M)`.
For any map `f : ℕ+ →* M` in the image, `p^k` is `f`-nice for all `k : ℕ`.
This fact will be proved in the file `ClassPrime/Main.lean`.

Instead of explicitly using `(ZMod p)ˣ/{±1}`, we use `EvenMonoidHom`.
See `Extra/EvenMonoidHom/Basic.lean` for more details.
-/

namespace IMOSL
namespace IMO2020N5

variable (p : Nat.Primes) (M : Type*) [CommMonoid M]

/-- Map `M → (ℕ+ →* M)` -/
def goodP_ofPVal (c : M) : ℕ+ →* M :=
  { toFun := λ n ↦ c ^ padicValPNat p n
    map_one' := pow_zero c
    map_mul' := λ x y ↦ by rw [← pow_add, ← padicValPNat.mul] }

lemma goodP_ofPVal_one : goodP_ofPVal p M 1 = 1 :=
  MonoidHom.ext λ _ ↦ one_pow _

lemma goodP_ofPVal_mul (x y : M) :
    goodP_ofPVal p M (x * y) = goodP_ofPVal p M x * goodP_ofPVal p M y :=
  MonoidHom.ext λ _ ↦ mul_pow x y _



/-- Homomorphism `M →* (ℕ+ →* M)` -/
def goodPHom_ofPVal : M →* (ℕ+ →* M) :=
  { toFun := goodP_ofPVal p M
    map_one' := goodP_ofPVal_one p M
    map_mul' := goodP_ofPVal_mul p M }

/-- Map `EvenMonoidHom (ZMod p)ˣ M → (ℕ+ →* M)` -/
def goodP_ofEvenMonoidHom (f : EvenMonoidHom (ZMod p)ˣ M) : ℕ+ →* M :=
  f.toMonoidHom.comp (padicComplPNat.ZModUnitHom p)

lemma goodP_ofEvenMonoidHom_one : goodP_ofEvenMonoidHom p M 1 = 1 := rfl

lemma goodP_ofEvenMonoidHom_mul (f g : EvenMonoidHom (ZMod p)ˣ M) :
    goodP_ofEvenMonoidHom p M (f * g) =
      goodP_ofEvenMonoidHom p M f * goodP_ofEvenMonoidHom p M g := rfl

lemma goodP_ofEvenMonoidHom_apply_self_pred (f : EvenMonoidHom (ZMod p)ˣ M) :
    (goodP_ofEvenMonoidHom p M f).toFun (p - 1) = 1 :=
  f.map_neg_one ▸ congr_arg f (padicComplPNat.ZModUnit_pred p)

/-- Homomorphism `EvenMonoidHom (ZMod p)ˣ M →* (ℕ+ →* M)` -/
def goodPHom_ofEvenMonoidHom : EvenMonoidHom (ZMod p)ˣ M →* (ℕ+ →* M) :=
  { toFun := goodP_ofEvenMonoidHom p M
    map_one' := goodP_ofEvenMonoidHom_one p M
    map_mul' := goodP_ofEvenMonoidHom_mul p M }



/-- Homomorphism `M × EvenMonoidHom (ZMod p)ˣ M →* (ℕ+ →* M)` -/
def goodPHom_mk : M × EvenMonoidHom (ZMod p)ˣ M →* (ℕ+ →* M) :=
  (goodPHom_ofPVal p M).coprod (goodPHom_ofEvenMonoidHom p M)
