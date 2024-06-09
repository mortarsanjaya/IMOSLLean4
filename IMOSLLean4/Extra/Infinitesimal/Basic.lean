/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Ring.Abs

/-!
# Infinitesimal elements of an ordered ring

Let `R` be an ordered ring.
We say that `ε : R` is *infinitesimal* if `k|ε| < 1` for all `k : ℕ`.
These elements form a non-unital ring with the induced addition and multiplication from `R`.
-/

namespace IMOSL
namespace Extra

variable [LinearOrderedRing R]

def Infinitesimal (ε : R) := ∀ k : ℕ, k • |ε| < 1


namespace Infinitesimal

lemma neg {ε : R} (h : Infinitesimal ε) : Infinitesimal (-ε) :=
  λ k ↦ abs_neg ε ▸ h k

lemma add {ε₁ ε₂ : R} (h₁ : Infinitesimal ε₁) (h₂ : Infinitesimal ε₂) :
    Infinitesimal (ε₁ + ε₂) := λ k ↦ by
  apply (nsmul_le_nsmul_right (abs_add ε₁ ε₂) k).trans_lt
  apply lt_of_nsmul_lt_nsmul_right 2
  rw [← mul_nsmul', nsmul_add, two_nsmul]
  exact add_lt_add (h₁ _) (h₂ _)

lemma sub {ε₁ ε₂ : R} (h₁ : Infinitesimal ε₁) (h₂ : Infinitesimal ε₂) :
    Infinitesimal (ε₁ - ε₂) :=
  sub_eq_add_neg ε₁ ε₂ ▸ h₁.add h₂.neg

lemma abs_lt_one {ε : R} (h : Infinitesimal ε) : |ε| < 1 :=
  (one_nsmul _).symm.trans_lt (h 1)

lemma lt_one {ε : R} (h : Infinitesimal ε) : ε < 1 :=
  (le_abs_self ε).trans_lt h.abs_lt_one

lemma abs_le_one {ε : R} (h : Infinitesimal ε) : |ε| ≤ 1 :=
  (abs_lt_one h).le

lemma le_one {ε : R} (h : Infinitesimal ε) : ε ≤ 1 :=
  (le_abs_self ε).trans h.abs_le_one

lemma mul_of_abs_le_one_left {ε r : R} (hε : Infinitesimal ε) (hr : |r| ≤ 1) :
    Infinitesimal (r * ε) := λ k ↦ by
  rw [abs_mul, nsmul_eq_mul', mul_assoc, ← nsmul_eq_mul']
  exact mul_lt_one_of_nonneg_of_lt_one_right hr (nsmul_nonneg (abs_nonneg ε) k) (hε k)

lemma mul_of_abs_le_one_right {ε r : R} (hε : Infinitesimal ε) (hr : |r| ≤ 1) :
    Infinitesimal (ε * r) := λ k ↦ by
  rw [abs_mul, nsmul_eq_mul, ← mul_assoc, ← nsmul_eq_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left (nsmul_nonneg (abs_nonneg ε) k) (hε k) hr

lemma mul {ε₁ ε₂ : R} (h₁ : Infinitesimal ε₁) (h₂ : Infinitesimal ε₂) :
    Infinitesimal (ε₁ * ε₂) :=
  mul_of_abs_le_one_right h₁ h₂.abs_le_one

lemma nsmul {ε : R} (hε : Infinitesimal ε) (n : ℕ) : Infinitesimal (n • ε) := λ k ↦ by
  rw [abs_nsmul, ← mul_nsmul']; exact hε _

lemma iff_nsmul_Nat_bdd {ε : R} : Infinitesimal ε ↔ ∃ N : ℕ, ∀ k : ℕ, k • |ε| < N :=
  ⟨λ h ↦ ⟨1, λ k ↦ (h k).trans_eq Nat.cast_one.symm⟩,
  λ ⟨N, h⟩ k ↦ lt_of_nsmul_lt_nsmul_right N <| by rw [← mul_nsmul, nsmul_one]; exact h _⟩
