/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.ClassPrime.Answers
import IMOSLLean4.IMO2020.N5.N5ZModUnit
import IMOSLLean4.IMO2020.N5.Nat.Lemma3

/-!
# IMO 2020 N5 (Prime Class - Main File)

Let `p` be a prime and `M` be a cancellative commutative monoid.
We say that `f : ℕ+ →* M` is of class `p` if `p^k` is `f`-nice for all `k ≥ 0`.
Here, we prove that the image of `primeClass.Hom_mk` defined in
  `ClassPrime/Answers.lean` are precisely the functions of class `p`.
Furthermore, the inverse mapping will be constructed explicitly.
-/

namespace IMOSL
namespace IMO2020N5

def primeClass (p : ℕ+) (f : ℕ+ → α) := ∀ k, nice f (p ^ k)





namespace primeClass

lemma nice_self (h : primeClass p f) : nice f p :=
  pow_one p ▸ h 1

section

variable [CancelCommMonoid M] {p : Nat.Primes} {φ : ℕ+ →* M}

lemma iff_niceNat :
    primeClass p φ.toFun ↔ ∀ k, Nat.nice (MulMap.ofPNatHom φ) (p ^ k) :=
  forall_congr' λ _ ↦ nice_iff_niceNat

lemma iff_Nat :
    primeClass p φ.toFun ↔ φ.toFun (p - 1) = 1 ∧
      ∀ m, ¬(p : ℕ) ∣ m → MulMap.ofPNatHom φ m = MulMap.ofPNatHom φ (m % p) := by
  rw [iff_niceNat, Nat.nice_pow_iff p.2]
  refine and_congr_left' (Eq.congr (?_ : _ = ⇑φ (p - 1)) rfl)
  have h : (1 : ℕ+) < p := p.2.one_lt
  rw [← MulMap.ofPNatHom_spec, PNat.sub_coe, if_pos h]; rfl

lemma iff_PNat :
    primeClass p φ.toFun ↔ φ.toFun (p - 1) = 1 ∧
      ∀ m n, ¬(p : ℕ+) ∣ m → ¬(p : ℕ+) ∣ n →
        (m : ℕ) % p = n % p → φ.toFun m = φ.toFun n :=
  iff_Nat.trans <| and_congr_right'
    ⟨λ h m n hm hn h0 ↦ by
      rw [PNat.dvd_iff] at hm hn
      have h1 := h _ hm
      rwa [MulMap.ofPNatHom_spec, h0, ← h _ hn, MulMap.ofPNatHom_spec] at h1,
    λ h m hm ↦ by
      have h0 : 0 < m % p.1 := Nat.emod_pos_of_not_dvd hm
      specialize h ⟨m, h0.trans_le (m.mod_le _)⟩ ⟨m % p.1, h0⟩
      rw [PNat.dvd_iff, PNat.dvd_iff] at h
      have h1 : ¬p.1 ∣ m % p.1 := Nat.not_dvd_of_pos_of_lt h0 (m.mod_lt p.2.pos)
      specialize h hm h1 (m.mod_mod _).symm
      exact (MulMap.ofPNatHom_spec _ _).trans <|
        h.trans (MulMap.ofPNatHom_spec _ _).symm⟩

end





/-! #### Image of `primeClassHom_mk` -/

theorem Hom_mk_spec (p : Nat.Primes) (M : Type*)
    [CancelCommMonoid M] (x : M × EvenMonoidHom (ZMod p)ˣ M) :
    primeClass p ((Hom_mk p M).toFun x).toFun :=
  iff_PNat.mpr ⟨Hom_mk_apply_pred p M x, λ m n hm hn h ↦ by
    rw [Hom_mk_apply, padicValPNat.zero_of_not_dvd p hm,
      Hom_mk_apply, padicValPNat.zero_of_not_dvd p hn,
      padicComplPNat.ZModUnit_of_not_dvd_mod_eq p hm hn h]⟩





/-! #### Inverse of `primeClassHom_mk` -/

section

variable {p : Nat.Primes} [CancelCommMonoid M]
  {φ : ℕ+ →* M} (h : primeClass p φ.toFun)

lemma PNatHom_toZModUnitEvenHom_apply_padicCompl (n : ℕ+) :
    PNatHom_toZModUnitEvenHom φ p (nice_self h) (padicComplPNat.ZModUnit p n)
      = φ (padicComplPNat p n) := by
  rw [PNatHom_toZModUnitEvenHom_apply, ← MulMap.ofPNatHom_spec,
    ZModUnit_toPNat_val, ← MulMap.ofPNatHom_spec,
    padicComplPNat.ZModUnit_coeZMod, ZMod.val_nat_cast]
  exact ((iff_Nat.mp h).2 _ λ h0 ↦
    padicComplPNat.not_dvd p n <| PNat.dvd_iff.mpr h0).symm

lemma pow_mul_PNatHom_toZModUnitEvenHom_padicCompl (n : ℕ+) :
    φ p ^ padicValPNat p n *
      PNatHom_toZModUnitEvenHom φ p (nice_self h) (padicComplPNat.ZModUnit p n)
      = φ n := by
  rw [PNatHom_toZModUnitEvenHom_apply_padicCompl h,
    ← φ.map_pow, ← φ.map_mul, padicComplPNat.self_pow_Val_mul]

lemma PNatHom_toZModUnitEvenHom_Hom_mk (x : M × EvenMonoidHom (ZMod p)ˣ M) :
    PNatHom_toZModUnitEvenHom (Hom_mk p M x) p (nice_self (Hom_mk_spec p M x))
      = x.2 :=
  EvenMonoidHom.ext λ y ↦ (PNatHom_toZModUnitEvenHom_apply _ p _ y).trans
    (Hom_mk_apply_ZModUnit_toPNat p M x _)

end



section inverse

def Hom_inv (p : Nat.Primes) (M : Type*) [CancelCommMonoid M]
    {φ : ℕ+ →* M} (h : primeClass p φ.toFun) :
    M × EvenMonoidHom (ZMod p)ˣ M :=
  (φ.toFun p, PNatHom_toZModUnitEvenHom φ p (nice_self h))

variable {p : Nat.Primes} {M : Type*} [CancelCommMonoid M]

lemma Hom_mk_inv {φ : ℕ+ →* M} (h : primeClass p φ.toFun) :
    (Hom_mk p M) (Hom_inv p M h) = φ :=
  MonoidHom.ext λ x ↦ pow_mul_PNatHom_toZModUnitEvenHom_padicCompl h x

lemma Hom_inv_mk (x : M × EvenMonoidHom (ZMod p)ˣ M) :
    Hom_inv p M (Hom_mk_spec p M x) = x :=
  Prod.ext (Hom_mk_apply_self p M x) (PNatHom_toZModUnitEvenHom_Hom_mk x)

/-- Main theorem for the prime class -/
theorem primeClass_iff_exists_eq_Hom_mk {φ : ℕ+ →* M} :
    primeClass p φ.toFun ↔ ∃ x, Hom_mk p M x = φ :=
  ⟨λ h ↦ ⟨Hom_inv p M h, Hom_mk_inv _⟩,
  λ h ↦ h.elim λ x h ↦ h ▸ Hom_mk_spec p M x⟩

end inverse
