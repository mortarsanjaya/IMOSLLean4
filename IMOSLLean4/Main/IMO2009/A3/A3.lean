/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.Extra.NatSequence.SeqMax
import Mathlib.Data.PNat.Basic

/-!
# IMO 2009 A3 (P5)

Find all functions $f : ℕ → ℕ$ such that for any $x, y ∈ ℕ$, the non-negative integers
  $x$, $f(y)$, and $f(y + f(x))$ form the sides of a possibly degenerate triangle.

### Extra notes

The original version using signature $ℕ^+ → ℕ^+$ is that $x$, $f(y)$,
  and $f(y + f(x) - 1)$ for the sides of a non-degenerate triangle.
-/

namespace IMOSL
namespace IMO2009A3

/-! ### Extra structure -/

@[mk_iff] structure isNatTriangleSide (x y z : ℕ) : Prop where
  side_x : x ≤ y + z
  side_y : y ≤ z + x
  side_z : z ≤ x + y

lemma isNatTriangleSide.rotate (h : isNatTriangleSide x y z) : isNatTriangleSide y z x :=
  ⟨h.side_y, h.side_z, h.side_x⟩

lemma isNatTriangleSide.zero_left_imp (h : isNatTriangleSide 0 x y) : x = y :=
  Nat.le_antisymm h.side_y (h.side_z.trans_eq x.zero_add)





/-! ### `Nat` version -/

def good (f : ℕ → ℕ) := ∀ x y, isNatTriangleSide x (f y) (f (y + f x))

/-- Final solution, `Nat` version -/
theorem final_solution_Nat : good f ↔ f = λ x ↦ x := by
  ---- First solve the `←` direction
  refine Iff.symm ⟨?_, λ h ↦ ?_⟩
  · rintro rfl x y; refine ⟨?_, ?_, (y.add_comm x).le⟩
    · rw [← Nat.add_assoc]; exact Nat.le_add_left x _
    · rw [Nat.add_assoc]; exact Nat.le_add_right y _
  ---- In the `→` direction, first show `f(0) = 0`
  have h0 (y) : f y = f (y + f 0) := (h 0 y).zero_left_imp
  replace h0 (y) : ∀ k, f (y + f 0 * k) = f y :=
    Nat.rec rfl λ k h1 ↦ by rw [Nat.mul_succ, ← Nat.add_assoc, ← h0, h1]
  replace h0 : f 0 = 0 := by
    refine (f 0).eq_zero_or_pos.resolve_right λ h1 ↦ ?_
    replace h0 (y) : f y ≤ Extra.seqMax f (f 0) := by
      rw [← y.mod_add_div (f 0), h0]
      exact Extra.le_seqMax_of_le f (y.mod_lt h1).le
    apply (h (2 * Extra.seqMax f (f 0) + 1) 0).side_x.not_gt
    rw [Nat.lt_succ_iff, Nat.two_mul]
    exact Nat.add_le_add (h0 _) (h0 _)
  ---- Next show `f(f(x)) = x` for all `x`
  have h1 (x) : f (f x) = x := by
    have h1 := (h x 0).rotate
    rw [Nat.zero_add, h0] at h1
    exact h1.zero_left_imp
  ---- Next, show that `f(n f(1)) = n` for all `n : ℕ`
  replace h0 (n) : f (f 1 * n) = n := by
    induction' n using Nat.strongRecOn with n n_ih
    cases n with | zero => exact h0 | succ n => ?_
    -- Focus on the case `n > 0`
    replace h0 : f 1 ≠ 0 := λ h2 ↦ absurd (h1 1) (by rw [h2, h0]; exact Nat.zero_ne_one)
    have h2 := (h 1 (f 1 * n)).side_z
    rw [← (f 1).mul_succ, n_ih n n.lt_succ_self,
      Nat.add_comm, Nat.le_succ_iff, or_comm] at h2
    rcases h2 with h2 | h2; exact h2
    replace h2 := congrArg f (n_ih _ (Nat.lt_succ_of_le h2))
    rwa [h1, h1, Nat.mul_right_inj h0] at h2
  ---- Now finish
  suffices f 1 = 1 from funext λ n ↦ by specialize h0 n; rwa [this, n.one_mul] at h0
  have h2 : f (f (f 1 * f 1)) = f (f 1) := congrArg f (h0 (f 1))
  rw [h1, h1] at h2; exact Nat.eq_one_of_mul_eq_one_left h2





/-! ### `PNat` version -/

theorem PNat_to_Nat_Prop {P : ℕ+ → Prop} : (∀ n : ℕ+, P n) ↔ ∀ n : ℕ, P n.succPNat :=
  ⟨λ h n ↦ h n.succPNat, λ h n ↦ n.succPNat_natPred ▸ h _⟩

theorem PNat_to_Nat_Prop2 {P : ℕ+ → ℕ+ → Prop} :
    (∀ m n : ℕ+, P m n) ↔ ∀ m n : ℕ, P m.succPNat n.succPNat :=
  PNat_to_Nat_Prop.trans (forall_congr' λ _ ↦ PNat_to_Nat_Prop)

@[mk_iff] structure isPNatTriangleSide (x y z : ℕ+) : Prop where
  side_x : x < y + z
  side_y : y < z + x
  side_z : z < x + y

lemma succPNat_add_succPNat (x y : ℕ) : x.succPNat + y.succPNat = (x + y + 1).succPNat :=
  PNat.eq (Nat.add_add_add_comm x 1 y 1)

lemma le_add_iff_lt_succPNat_add {x y z : ℕ} :
    x ≤ y + z ↔ x.succPNat < y.succPNat + z.succPNat := by
  rw [succPNat_add_succPNat, Nat.succPNat_lt_succPNat, Nat.lt_succ_iff]

lemma isNatTriangleSide_iff_isPNatTriangleSide :
    isNatTriangleSide x y z ↔ isPNatTriangleSide x.succPNat y.succPNat z.succPNat := by
  rw [isNatTriangleSide_iff, isPNatTriangleSide_iff]
  exact and_congr le_add_iff_lt_succPNat_add
    (and_congr le_add_iff_lt_succPNat_add le_add_iff_lt_succPNat_add)

def goodPNat (f : ℕ+ → ℕ+) := ∀ x y, isPNatTriangleSide x (f y) (f (y + f x - 1))

theorem goodPNat_iff_good : goodPNat f ↔ good (λ x ↦ (f x.succPNat).natPred) := by
  rw [goodPNat, good, PNat_to_Nat_Prop2]
  refine forall_congr' λ m ↦ forall_congr' λ n ↦ ?_
  simp only [isNatTriangleSide_iff_isPNatTriangleSide, PNat.succPNat_natPred]
  refine Eq.to_iff (congrArg _ (congrArg f ?_))
  generalize f m.succPNat = x
  obtain ⟨y, rfl⟩ : ∃ y : ℕ, y.succPNat = x := ⟨x.natPred, x.succPNat_natPred⟩
  rw [succPNat_add_succPNat]; rfl

/-- Final solution -/
theorem final_solution : goodPNat f ↔ f = λ x ↦ x := by
  rw [goodPNat_iff_good, final_solution_Nat, funext_iff, funext_iff, PNat_to_Nat_Prop]
  refine forall_congr' λ n ↦ ?_
  generalize f n.succPNat = m; refine ⟨?_, ?_⟩
  · rintro rfl; exact (PNat.succPNat_natPred m).symm
  · rintro rfl; rfl
