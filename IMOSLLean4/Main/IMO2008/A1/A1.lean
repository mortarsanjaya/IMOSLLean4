/-
Copyright (c) 2024 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Order.Positive.Ring
import Mathlib.Algebra.Order.Ring.Basic

/-!
# IMO 2008 A1 (P4)

Let $R$ be a totally ordered commutative ring, and let $R_{>0} = \{x ∈ R : x > 0\}$.
Find all functions $f : R_{>0} → R_{>0}$ such that for any $p, q, r, s > 0$ with $pq = rs$,
$$ (f(p)^2 + f(q)^2) (r^2 + s^2) = (p^2 + q^2) (f(r^2) + f(s^2)). $$
-/

namespace IMOSL
namespace IMO2008A1

/-! ### Unbundled version of the problem -/

structure weakGood [Semiring R] [PartialOrder R] (f : R → R) : Prop where
  map_pos_of_pos : ∀ x > 0, f x > 0
  good' : ∀ p > 0, ∀ q > 0, ∀ r > 0, ∀ s > 0, p * q = r * s →
    (f p ^ 2 + f q ^ 2) * (r ^ 2 + s ^ 2) = (p ^ 2 + q ^ 2) * (f (r ^ 2) + f (s ^ 2))

variable [CommSemiring R] [LinearOrder R] [IsStrictOrderedRing R]

theorem side_ineq [ExistsAddOfLE R] {x y : R} (h : (x ^ 2 + 1) * y = (y ^ 2 + 1) * x) :
    x = y ∨ y * x = 1 := by
  wlog h0 : ∃ c, y = x + c
  · rw [eq_comm, mul_comm]; apply this h.symm
    exact exists_add_of_le ((le_total x y).resolve_left (mt exists_add_of_le h0))
  ---- Focus on the case `x ≤ y`
  rw [sq, sq, add_one_mul _ y, add_one_mul _ x, mul_rotate, mul_assoc, mul_assoc] at h
  rcases h0 with ⟨c, rfl⟩
  rw [add_mul x c (_ * x), add_assoc, add_right_inj, add_comm, add_left_inj, eq_comm] at h
  rw [left_eq_add, or_comm, add_comm]
  generalize (c + x) * x = y at h ⊢
  ---- It remains to show `cy = c → y = 1 ∨ c = 0`
  obtain ⟨d, h0⟩ | ⟨d, rfl⟩ : (∃ d, 1 = y + d) ∨ (∃ d, y = 1 + d) :=
    (le_total y 1).imp exists_add_of_le exists_add_of_le
  · rw [h0, left_eq_add, ← mul_eq_zero, mul_comm,
      ← add_eq_left, ← mul_add, ← h0, h, mul_one]
  · rw [mul_one_add c, add_eq_left, mul_eq_zero] at h
    rwa [add_eq_left, or_comm]

theorem weakGood_iff [ExistsAddOfLE R] {f : R → R} :
    weakGood f ↔ (∀ x > 0, f x = x) ∨ (∀ x > 0, x * f x = 1) := by
  refine ⟨λ hf ↦ ?_, λ hf ↦ ?_⟩
  ---- `→` direction
  · have two_pos : (0 : R) < 2 := two_pos
    have h {x} (hx : 0 < x) : f (x ^ 2) = f x ^ 2 := by
      have h := hf.good' x hx x hx x hx x hx rfl
      rwa [mul_comm, ← two_mul, mul_left_cancel_iff_of_pos (mul_pos two_pos (pow_pos hx 2)),
        ← two_mul, ← two_mul, mul_left_cancel_iff_of_pos two_pos, eq_comm] at h
    have h0 : f 1 = 1 := by
      have X : (0 : R) < 1 := one_pos
      have h0 := h X; rw [← one_mul (f (1 ^ 2)), one_pow, sq] at h0
      exact (mul_right_cancel₀ (hf.map_pos_of_pos _ X).ne.symm h0).symm
    have h1 {x y} (hx : 0 < x) (hy : 0 < y) :
        (f x ^ 4 + f y ^ 4) * (x * y) ^ 2 = (x ^ 4 + y ^ 4) * f (x * y) ^ 2 := by
      have X : 0 < x * y := mul_pos hx hy
      have h1 := hf.good' _ (mul_pos hx hx) _ (mul_pos hy hy)
        _ X _ X (mul_mul_mul_comm x x y y)
      rwa [← mul_two, ← mul_two, ← mul_assoc, ← mul_assoc, ← sq, ← sq, h hx, h hy, ← pow_mul,
        ← pow_mul, mul_right_cancel_iff_of_pos two_pos, h X, ← pow_mul, ← pow_mul] at h1
    have h2 {x} (hx : 0 < x) : f x = x ∨ x * f x = 1 := by
      specialize h1 hx one_pos
      rw [h0, one_pow, mul_one, pow_mul _ 2 2, pow_mul _ 2 2] at h1
      have hfx : 0 < f x := hf.map_pos_of_pos x hx
      refine (side_ineq h1).imp (sq_eq_sq₀ hfx.le hx.le).mp λ h2 ↦ ?_
      rwa [← mul_pow, pow_eq_one_iff_of_nonneg (mul_pos hx hfx).le (Nat.succ_ne_zero 1)] at h2
    have h3 {x y} (hx : 0 < x) (hy : 0 < y) (hx' : x * f x ≠ 1) : f y = y := by
      specialize h1 hx hy
      have hx0 : f x = x := (h2 hx).resolve_right hx'
      have hxy : 0 < x * y := mul_pos hx hy
      refine (h2 hy).elim id λ hy0 ↦ (h2 hxy).elim (λ h3 ↦ ?_) (λ h3 ↦ ?_)
      -- Case 1: `f(xy) = xy`
      · rw [h3, mul_right_cancel_iff_of_pos (pow_pos hxy 2), hx0, add_right_inj] at h1
        exact (pow_left_inj₀ (hf.map_pos_of_pos y hy).le hy.le four_ne_zero).mp h1
      -- Case 2: `f(xy) = 1/(xy)`
      · have hx'' : 0 < x * f x := mul_pos hx (hf.map_pos_of_pos x hx)
        rw [← mul_right_cancel_iff_of_pos (pow_pos hxy 2), mul_assoc, ← pow_add, mul_assoc,
          mul_comm (f _ ^ 2), ← mul_pow, h3, one_pow, mul_one, add_mul, ← mul_pow, ← mul_pow,
          ← mul_assoc, mul_left_comm, mul_comm (f y), hy0, mul_one, add_comm, add_right_inj,
          mul_comm (f x), pow_left_inj₀ (mul_pos hx'' hy).le hy.le four_ne_zero] at h1
        refine absurd ?_ hx'; rwa [← mul_right_cancel_iff_of_pos hy, one_mul]
    refine (em' (∀ x > 0, x * f x = 1)).imp_left λ h4 ↦ ?_
    simp only [not_forall] at h4; rcases h4 with ⟨c, hc, h4⟩
    intro x hx; exact h3 hc hx h4
  ---- `←` direction
  · rcases hf with hf | hf
    -- Check `f(x) = x`
    · refine ⟨λ x hx ↦ (hf x hx).symm.trans_gt hx, λ p hp q hq r hr s hs _ ↦ ?_⟩
      rw [hf p hp, hf q hq, hf _ (pow_pos hr 2), hf _ (pow_pos hs 2)]
    -- Check `f(x) = 1/x`
    · refine ⟨λ x hx ↦ pos_of_mul_pos_right (one_pos.trans_eq (hf x hx).symm) hx.le,
        λ p hp q hq r hr s hs h ↦ mul_left_cancel₀ (pow_pos (mul_pos hp hq) 2).ne.symm ?_⟩
      rw [← mul_assoc, mul_add ((p * q) ^ 2), ← mul_pow, mul_right_comm, hf p hp,
        one_mul, ← mul_pow, mul_assoc, hf q hq, mul_one, add_comm, mul_left_comm,
        h, mul_pow, mul_add (_ * _), mul_right_comm, hf _ (pow_pos hr 2), one_mul,
        mul_assoc, hf _ (pow_pos hs 2), mul_one, add_comm (r ^ 2)]





/-! ### The main version -/

def posSubtypeExt (f : {x : R // 0 < x} → {x : R // 0 < x}) (x : R) : R :=
  dite (0 < x) (λ h ↦ f ⟨x, h⟩) (λ _ ↦ 0)

omit [IsStrictOrderedRing R] in
lemma posSubtypeExt_spec (f : {x : R // 0 < x} → {x : R // 0 < x}) (x : {x : R // 0 < x}) :
    posSubtypeExt f x.1 = f x :=
  dif_pos _

def good (f : {x : R // 0 < x} → {x : R // 0 < x}) :=
  ∀ p q r s, p * q = r * s →
    (f p ^ 2 + f q ^ 2) * (r ^ 2 + s ^ 2) = (p ^ 2 + q ^ 2) * (f (r ^ 2) + f (s ^ 2))

lemma good_iff_posSubtypeExt_weakGood {f : {x : R // 0 < x} → {x : R // 0 < x}} :
    good f ↔ weakGood (posSubtypeExt f) := by
  have X (x : {x : R // 0 < x}) : x.1 ^ 2 = (x ^ 2).1 := rfl
  refine ⟨λ h ↦ ?_, λ ⟨_, h⟩ p q r s h0 ↦ ?_⟩
  ---- `→` direction
  · refine ⟨λ x hx ↦ (f ⟨x, hx⟩).2.trans_eq (posSubtypeExt_spec f _).symm,
      λ p hp q hq r hr s hs h0 ↦ ?_⟩
    lift p to {x : R // 0 < x} using hp
    lift q to {x : R // 0 < x} using hq
    lift r to {x : R // 0 < x} using hr
    lift s to {x : R // 0 < x} using hs
    simp only [posSubtypeExt_spec, ← Positive.coe_add, X]
    exact congrArg (λ x ↦ x.1) (h p q r s (Subtype.coe_inj.mp h0))
  ---- `←` direction
  · specialize h p.1 p.2 q.1 q.2 r.1 r.2 s.1 s.2 (congrArg Subtype.val h0)
    simp only [posSubtypeExt_spec, ← Positive.coe_add, X] at h
    exact Subtype.coe_inj.mp h

/-- Final solution -/
theorem final_solution [ExistsAddOfLE R] {f : {x : R // 0 < x} → {x : R // 0 < x}} :
    good f ↔ f = id ∨ ∀ x, x * f x = 1 := by
  rw [good_iff_posSubtypeExt_weakGood, weakGood_iff, funext_iff]
  refine or_congr ⟨λ h x ↦ ?_, λ h x hx ↦ ?_⟩ ⟨λ h x ↦ ?_, λ h x hx ↦ ?_⟩
  · rw [← Subtype.coe_inj, ← posSubtypeExt_spec, h x.1 x.2]; rfl
  · rw [posSubtypeExt_spec f ⟨x, hx⟩, h ⟨x, hx⟩]; rfl
  · rw [← Subtype.coe_inj, Positive.val_mul, ← posSubtypeExt_spec, h x.1 x.2]; rfl
  · rw [posSubtypeExt_spec f ⟨x, hx⟩]; exact congrArg (λ x ↦ x.1) (h ⟨x, hx⟩)
