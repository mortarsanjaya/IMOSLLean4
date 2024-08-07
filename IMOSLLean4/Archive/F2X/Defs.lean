/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.CharTwo.Finset

/-!
# Explicit construction of `𝔽₂[X]`

In this file, we explicitly construct the ring `𝔽₂[X]`.
We prove that it is a ring, and we construct ring homomorphisms from `𝔽₂[X]`.
The explicit construction is done so that proof of equality between
  two expressions involving explicit elements can be done with just `rfl`.

### Implementation details

We implement `𝔽₂[X]` as a wrapper around `Finset ℕ`.
Addition is done by symmetric difference.
Multiplication by `X` is done by adding `1` to every element.
-/

namespace IMOSL
namespace IMO2012A5

open Extra

@[ext] structure 𝔽₂X where
  toFinset : Finset ℕ


namespace 𝔽₂X

/-- Get an element of `𝔽₂[X]` from a `Finset ℕ`.
  This might be preferred over manually typing the polynomial for larger ones. -/
def ofFinset (S : Finset ℕ) : 𝔽₂X := ⟨S⟩

instance : Coe (Finset ℕ) 𝔽₂X := ⟨ofFinset⟩

/-- `X^n`, preferred over `X ^ n`. -/
def Xpow (n : ℕ) : 𝔽₂X := ⟨{n}⟩

instance : Zero 𝔽₂X := ⟨⟨∅⟩⟩
instance : One 𝔽₂X := ⟨⟨{0}⟩⟩
instance : Neg 𝔽₂X := ⟨id⟩

def X : 𝔽₂X := ⟨{1}⟩

instance : DecidableEq 𝔽₂X := λ P Q ↦ match decEq P.toFinset Q.toFinset with
  | isTrue h => isTrue (𝔽₂X.ext h)
  | isFalse h => isFalse λ h0 ↦ h (congrArg toFinset h0)





/-! ### Addition -/

protected def add : 𝔽₂X → 𝔽₂X → 𝔽₂X
  | ⟨S⟩, ⟨T⟩ => ⟨symmDiff S T⟩

instance : Add 𝔽₂X := ⟨𝔽₂X.add⟩

protected lemma add_toFinset (P Q : 𝔽₂X) :
    (P + Q).toFinset = symmDiff P.toFinset Q.toFinset := rfl

protected lemma zero_add (P : 𝔽₂X) : 0 + P = P :=
  𝔽₂X.ext (bot_symmDiff _)

protected lemma add_zero (P : 𝔽₂X) : P + 0 = P :=
  𝔽₂X.ext (symmDiff_bot _)

protected lemma add_comm (P Q : 𝔽₂X) : P + Q = Q + P :=
  𝔽₂X.ext (symmDiff_comm _ _)

protected lemma add_assoc (P Q R : 𝔽₂X) : P + Q + R = P + (Q + R) :=
  𝔽₂X.ext (symmDiff_assoc _ _ _)

protected lemma add_self_eq_zero (P : 𝔽₂X) : P + P = 0 :=
  𝔽₂X.ext (symmDiff_self _)

instance : AddCommGroup 𝔽₂X where
  zero_add := 𝔽₂X.zero_add
  add_zero := 𝔽₂X.add_zero
  add_comm := 𝔽₂X.add_comm
  add_assoc := 𝔽₂X.add_assoc
  add_left_neg := 𝔽₂X.add_self_eq_zero
  nsmul := nsmulRec
  zsmul := zsmulRec

instance : CharTwo 𝔽₂X := ⟨𝔽₂X.add_self_eq_zero⟩





/-! ### Induction principles -/

protected theorem poly_induction {p : 𝔽₂X → Prop} (zero : p 0)
    (add_Xpow : ∀ (n : ℕ) {P : 𝔽₂X}, p P → p (Xpow n + P)) (P : 𝔽₂X) : p P :=
  P.toFinset.induction (p := λ S ↦ p (ofFinset S)) zero λ n _ h h0 ↦
    symmDiff_singleton_eq_insert h ▸ add_Xpow n h0

protected theorem Xpow_add_induction {p : 𝔽₂X → Prop}
    (of_Xpow : ∀ n : ℕ, p (Xpow n)) (add : ∀ {P Q}, p P → p Q → p (P + Q)) :
    ∀ P, p P :=
  𝔽₂X.poly_induction (let h := of_Xpow 0; add h h) λ n _ ↦ add (of_Xpow n)





/-! ### Multiplication by powers of `X` -/

/-- Given `n` and `P(X)`, compute `X^n P(X)` -/
def XpowMul (n : ℕ) (P : 𝔽₂X) : 𝔽₂X :=
  ⟨P.toFinset.image λ k ↦ k + n⟩

lemma XpowMul_nat_zero (P : 𝔽₂X) : P.XpowMul 0 = P :=
  𝔽₂X.ext Finset.image_id

lemma XpowMul_𝔽₂X_zero (n : ℕ) : XpowMul n 0 = 0 :=
  𝔽₂X.ext (Finset.image_empty _)

lemma XpowMul_𝔽₂X_one (n : ℕ) : XpowMul n 1 = Xpow n :=
  𝔽₂X.ext ((Finset.image_singleton _ _).trans (congrArg _ n.zero_add))

lemma XpowMul_Xpow (m n : ℕ) : (Xpow m).XpowMul n = Xpow (m + n) := rfl

lemma XpowMul_nat_add (m n : ℕ) (P : 𝔽₂X) :
    P.XpowMul (m + n) = (P.XpowMul m).XpowMul n := by
  unfold XpowMul; rw [𝔽₂X.ext_iff, eq_comm, Finset.image_image, comp_add_right]

lemma XpowMul_𝔽₂X_add (n : ℕ) (P Q : 𝔽₂X) :
    (P + Q).XpowMul n = P.XpowMul n + Q.XpowMul n :=
  𝔽₂X.ext (Finset.image_symmDiff _ _ (add_left_injective n))

lemma XpowMul_sum (n : ℕ) [DecidableEq ι] (f : ι → 𝔽₂X) (S : Finset ι) :
    (S.sum f).XpowMul n = S.sum λ i ↦ (f i).XpowMul n :=
  S.induction rfl λ i S h h0 ↦ by
    rw [Finset.sum_insert h, Finset.sum_insert h, XpowMul_𝔽₂X_add, h0]

lemma sum_Xpow_eq_ofFinset : ∀ S : Finset ℕ, S.sum Xpow = ofFinset S :=
  Finset.induction rfl λ i S h h0 ↦ by
    rw [Finset.sum_insert h, h0]
    exact 𝔽₂X.ext (symmDiff_singleton_eq_insert h)

lemma toFinset_sum_Xpow_eq_self (P : 𝔽₂X) : P.toFinset.sum Xpow = P :=
  𝔽₂X.sum_Xpow_eq_ofFinset P.toFinset





/-! ### Multiplication -/

protected def mul (P Q : 𝔽₂X) : 𝔽₂X :=
  P.toFinset.sum Q.XpowMul

instance : Mul 𝔽₂X := ⟨𝔽₂X.mul⟩

protected lemma mul_def (P Q : 𝔽₂X) : P * Q = P.toFinset.sum Q.XpowMul := rfl

protected lemma zero_mul (P : 𝔽₂X) : 0 * P = 0 :=
  Finset.sum_empty (f := P.XpowMul)

protected lemma mul_zero (P : 𝔽₂X) : P * 0 = 0 :=
  Finset.sum_eq_zero λ n _ ↦ XpowMul_𝔽₂X_zero n

protected lemma one_mul (P : 𝔽₂X) : 1 * P = P :=
  (Finset.sum_singleton _ _).trans (𝔽₂X.XpowMul_nat_zero P)

protected lemma mul_one (P : 𝔽₂X) : P * 1 = P :=
  (Finset.sum_congr rfl λ n _ ↦ XpowMul_𝔽₂X_one n).trans
    P.toFinset_sum_Xpow_eq_self

protected lemma add_mul (P Q R : 𝔽₂X) : (P + Q) * R = P * R + Q * R :=
  CharTwo.symmDiff_sum_eq _ _ _

protected lemma mul_add (P Q R : 𝔽₂X) : P * (Q + R) = P * Q + P * R :=
  (Finset.sum_congr rfl λ n _ ↦ XpowMul_𝔽₂X_add n Q R).trans
    Finset.sum_add_distrib

lemma XpowMul_eq_Xpow_mul (n : ℕ) (P : 𝔽₂X) : P.XpowMul n = Xpow n * P :=
  (Finset.sum_singleton P.XpowMul n).symm

lemma Xpow_add (k m : ℕ) : Xpow (k + m) = Xpow k * Xpow m := by
  rw [← XpowMul_eq_Xpow_mul, XpowMul_Xpow, add_comm]

lemma XpowMul_eq_mul_Xpow (n : ℕ) : ∀ P : 𝔽₂X, P.XpowMul n = P * Xpow n :=
  𝔽₂X.Xpow_add_induction
    (λ k ↦ by rw [XpowMul_Xpow, Xpow_add])
    (λ h h0 ↦ by rw [XpowMul_𝔽₂X_add, 𝔽₂X.add_mul, h, h0])

protected lemma mul_comm (P : 𝔽₂X) : ∀ Q, P * Q = Q * P :=
  𝔽₂X.Xpow_add_induction
    (λ n ↦ by rw [← XpowMul_eq_Xpow_mul, XpowMul_eq_mul_Xpow])
    (λ h h0 ↦ by rw [𝔽₂X.add_mul, 𝔽₂X.mul_add, h, h0])

lemma mul_XpowMul_left (n : ℕ) (P : 𝔽₂X) : ∀ Q, P.XpowMul n * Q = (P * Q).XpowMul n :=
  𝔽₂X.Xpow_add_induction
    (λ k ↦ by rw [← XpowMul_eq_mul_Xpow, ← XpowMul_eq_mul_Xpow,
      ← XpowMul_nat_add, ← XpowMul_nat_add, Nat.add_comm])
    (λ h h0 ↦ by rw [𝔽₂X.mul_add, 𝔽₂X.mul_add, h, h0, XpowMul_𝔽₂X_add])

lemma mul_XpowMul_right (n : ℕ) (P Q : 𝔽₂X) : P * Q.XpowMul n = (P * Q).XpowMul n := by
  rw [P.mul_comm, mul_XpowMul_left, Q.mul_comm]

protected lemma mul_assoc (P Q : 𝔽₂X) : ∀ R, P * Q * R = P * (Q * R) :=
  𝔽₂X.Xpow_add_induction
    (λ n ↦ by rw [← XpowMul_eq_mul_Xpow, ← XpowMul_eq_mul_Xpow, mul_XpowMul_right])
    (λ h h0 ↦ by rw [𝔽₂X.mul_add, 𝔽₂X.mul_add, 𝔽₂X.mul_add, h, h0])





/-! ### Square -/

def square (P : 𝔽₂X) : 𝔽₂X := ⟨P.toFinset.image λ n ↦ 2 * n⟩

theorem square_zero : square 0 = 0 := rfl

theorem square_one : square 1 = 1 := rfl

theorem square_add (P Q : 𝔽₂X) : square (P + Q) = square P + square Q :=
  𝔽₂X.ext (Finset.image_symmDiff _ _ λ _ _ ↦ (Nat.mul_right_inj (Nat.succ_ne_zero 1)).mp)

theorem square_add_one (P : 𝔽₂X) : square (P + 1) = square P + 1 :=
  P.square_add 1

theorem square_Xpow (n : ℕ) : (Xpow n).square = Xpow (2 * n) := rfl

theorem square_eq_mul_self : ∀ P : 𝔽₂X, square P = P * P :=
  𝔽₂X.poly_induction rfl λ n P h ↦ by
    rw [square_add, square_Xpow, 𝔽₂X.add_mul, 𝔽₂X.mul_add, ← Xpow_add, Nat.two_mul,
      𝔽₂X.mul_add, ← h, ← P.mul_comm, CharTwo.add_add_add_cancel_middle]

theorem square_XpowMul (n : ℕ) (P : 𝔽₂X) :
    (P.XpowMul n).square = P.square.XpowMul (2 * n) := by
  unfold square XpowMul; rw [Finset.image_image, Finset.image_image]
  exact 𝔽₂X.ext (congrArg P.toFinset.image <| funext λ n ↦ Nat.mul_add 2 _ _)

theorem square_mul (P : 𝔽₂X) : ∀ Q, square (P * Q) = square P * square Q :=
  𝔽₂X.Xpow_add_induction
    (λ n ↦ by rw [← XpowMul_eq_mul_Xpow, square_XpowMul,
      square_Xpow, XpowMul_eq_mul_Xpow])
    (λ h h0 ↦ by rw [P.mul_add, square_add, h, h0, square_add, 𝔽₂X.mul_add])





/-! ### Modified, more efficient power -/

protected def natPow (P : 𝔽₂X) (n : ℕ) : 𝔽₂X :=
  if n = 0 then 1 else
    let Q := 𝔽₂X.natPow (square P) (n / 2)
    if n % 2 = 0 then Q else Q * P
termination_by n
decreasing_by apply Nat.bitwise_rec_lemma; assumption

protected lemma natPow_zero (P : 𝔽₂X) : P.natPow 0 = 1 := by
  rw [𝔽₂X.natPow, if_pos rfl]

protected lemma natPow_of_ne_zero (P : 𝔽₂X) (h : n ≠ 0) :
    P.natPow n = if n % 2 = 0 then 𝔽₂X.natPow (square P) (n / 2)
      else 𝔽₂X.natPow (square P) (n / 2) * P := by
  rw [𝔽₂X.natPow, if_neg h]

protected lemma natPow_two_mul (P : 𝔽₂X) (n : ℕ) :
    P.natPow (2 * n) = (square P).natPow n := by
  rcases Decidable.eq_or_ne n 0 with rfl | h
  · rw [Nat.mul_zero, 𝔽₂X.natPow_zero, 𝔽₂X.natPow_zero]
  · have h0 : 0 < 2 := Nat.two_pos
    rw [P.natPow_of_ne_zero (Nat.mul_ne_zero h0.ne.symm h),
      if_pos (Nat.mul_mod_right _ _), Nat.mul_div_right _ h0]

protected lemma natPow_two_mul_add_one (P : 𝔽₂X) (n : ℕ) :
    P.natPow (2 * n + 1) = (square P).natPow n * P := by
  rw [P.natPow_of_ne_zero (2 * n).add_one_ne_zero, Nat.mul_add_mod,
    Nat.mul_add_div Nat.two_pos, if_neg Nat.one_ne_zero,
    Nat.div_eq_of_lt Nat.one_lt_two, Nat.add_zero]

protected lemma natPow_one (P : 𝔽₂X) : P.natPow 1 = P := by
  rw [𝔽₂X.natPow, if_neg Nat.one_ne_zero, 𝔽₂X.natPow_zero,
    if_neg Nat.one_ne_zero, 𝔽₂X.one_mul]

protected lemma natPow_two (P : 𝔽₂X) : P.natPow 2 = square P := by
  rw [𝔽₂X.natPow, if_neg (Nat.succ_ne_zero 1), 𝔽₂X.natPow_one, if_pos rfl]

protected lemma natPow_succ (P : 𝔽₂X) (n : ℕ) : P.natPow n.succ = P.natPow n * P := by
  rw [← n.div_add_mod 2]; rcases n.mod_two_eq_zero_or_one with h0 | h0
  · rw [h0, Nat.add_zero, 𝔽₂X.natPow_two_mul_add_one, 𝔽₂X.natPow_two_mul]
  · rw [h0, Nat.succ_eq_add_one, ← Nat.mul_succ 2, 𝔽₂X.natPow_two_mul,
      𝔽₂X.natPow_two_mul_add_one, 𝔽₂X.mul_assoc, ← P.square_eq_mul_self]
    exact (square P).natPow_succ (n / 2)
termination_by n
decreasing_by apply Nat.bitwise_rec_lemma
              rintro rfl; exact absurd h0.symm Nat.one_ne_zero
