/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

/-!
# IMO 2019 N2

Find all triples $(a, b, c)$ of nonnegative integers such that $a^3 + b^3 + c^3 = (abc)^2$.

### Answer

$(0, 0, 0)$ and permutations of $(3, 2, 1)$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2019SL.pdf).
The estimate $a^3 - b^3 > 1$ in the solution is unnecessary; we only need $a^3 > b^3$.
On the other hand, we reuse the inequality $a^2 ≤ b^3 + 1$ and $b^2 ≤ 2a$
  to prove that the only working pair $(a, b)$ with $a ≥ b ≥ c = 1$ is $(3, 2)$.
-/

namespace IMOSL
namespace IMO2019N2

/-- A triple `(a, b, c)` of nonnegative integers is called *good*
  if `a^3 + b^3 + c^3 = (abc)^2`. -/
def good (a b c : Nat) := a ^ 3 + b ^ 3 + c ^ 3 = (a * b * c) ^ 2


namespace good

section

variable (h : good a b c)
include h

/-- If `(a, b, c)` is good then `(a, c, b)` is good. -/
theorem perm12 : good a c b := by
  rw [good, Nat.add_right_comm, h, Nat.mul_right_comm]

/-- If `(a, b, c)` is good then `(b, a, c)` is good. -/
theorem perm01 : good b a c := by
  rw [good, Nat.add_comm (b ^ 3), h, Nat.mul_comm a]

/-- If `(a, b, c)` is good then `(b, c, a)` is good. -/
theorem perm012 : good b c a :=
  h.perm01.perm12

/-- If `(a, b, c)` is good then `(c, a, b)` is good. -/
theorem perm021 : good c a b :=
  h.perm12.perm01

/-- If `(a, b, c)` is good then `(c, b, a)` is good. -/
theorem perm02 : good c b a :=
  h.perm012.perm01

/-- If `(a, b, c)` is good and `c ≤ b ≤ a`, then `c = 0` or `c = 1`. -/
theorem c_eq_zero_or_one (hcb : c ≤ b) (hba : b ≤ a) : c = 0 ∨ c = 1 := by
  unfold good at h
  ---- Suppose that `c ≥ 2`.
  refine Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_not_gt λ hc ↦ ?_)
  ---- First note that `a, b, c > 0`.
  have hc0 : c > 0 := Nat.zero_lt_of_lt hc
  have hb0 : b > 0 := Nat.lt_of_lt_of_le hc0 hcb
  have ha0 : a > 0 := Nat.lt_of_lt_of_le hb0 hba
  ---- Note that `(bc)^2 < 3a`.
  have h0 : (b * c) ^ 2 ≤ 3 * a := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.pow_pos ha0 (n := 2))
    calc a ^ 2 * (b * c) ^ 2
      _ = (a * b * c) ^ 2 := by rw [Nat.mul_assoc a, Nat.mul_pow a]
      _ = a ^ 3 + b ^ 3 + c ^ 3 := h.symm
      _ ≤ a ^ 3 + a ^ 3 + a ^ 3 :=
        have X {x y} (h0 : x ≤ y) : x ^ 3 ≤ y ^ 3 := Nat.pow_le_pow_left h0 3
        Nat.add_le_add (Nat.add_le_add_left (X hba) _) (X (Nat.le_trans hcb hba))
      _ = 3 * a ^ 3 := by rw [Nat.succ_mul, Nat.two_mul]
      _ = a ^ 2 * (3 * a) := by rw [Nat.pow_succ, Nat.mul_left_comm]
  ---- Working mod `a^2`, we get `2b^3 ≥ b^3 + c^3 ≥ a^2`.
  replace h : a ^ 2 ≤ b ^ 3 + c ^ 3 := by
    refine Nat.le_of_dvd (Nat.add_pos_left (Nat.pow_pos hb0) _) ?_
    rw [← Nat.dvd_add_right ⟨a, rfl⟩, ← Nat.pow_succ, ← Nat.add_assoc, h, Nat.mul_assoc]
    exact ⟨(b * c) ^ 2, Nat.mul_pow _ _ 2⟩
  replace h : a ^ 2 ≤ 2 * b ^ 3 := calc
    a ^ 2 ≤ b ^ 3 + c ^ 3 := h
    _ ≤ b ^ 3 + b ^ 3 := Nat.add_le_add_left (Nat.pow_le_pow_left hcb 3) _
    _ = 2 * b ^ 3 := (Nat.two_mul _).symm
  ---- Combining the two inequalities with `c ≤ b` gives `18b^3 ≥ b^4 c^4 ≥ b^3 c^5`.
  replace h : c ^ 5 * b ^ 3 ≤ 18 * b ^ 3 := calc
    c ^ 5 * b ^ 3 = c ^ 4 * b ^ 3 * c := by rw [Nat.pow_succ, Nat.mul_right_comm]
    _ ≤ c ^ 4 * b ^ 3 * b := Nat.mul_le_mul_left _ hcb
    _ = b ^ 4 * c ^ 4 := by rw [Nat.mul_assoc, ← Nat.pow_succ, Nat.mul_comm]
    _ = ((b * c) ^ 2) ^ 2 := by rw [← Nat.pow_mul, Nat.mul_pow]
    _ ≤ (3 * a) ^ 2 := Nat.pow_le_pow_left h0 _
    _ = 9 * a ^ 2 := Nat.mul_pow 3 a 2
    _ ≤ 9 * (2 * b ^ 3) := Nat.mul_le_mul_left 9 h
    _ = 18 * b ^ 3 := (Nat.mul_assoc _ _ _).symm
  ---- But `c^5 ≥ 2^5 = 32 > 18`; contradiction!
  replace h : c ^ 5 ≤ 18 := Nat.le_of_mul_le_mul_right h (Nat.pow_pos hb0)
  replace hc : 32 ≤ c ^ 5 := Nat.pow_le_pow_left hc 5
  replace h0 : 18 < 32 := by decide
  exact Nat.not_le_of_lt h0 (Nat.le_trans hc h)

end


/-- If `(a, b, 0)` is good, then `a = 0` and `b = 0`. -/
theorem eq_000_of_c_eq_zero (h : good a b 0) : a = 0 ∧ b = 0 := by
  have h0 {n : Nat} (hn : n ^ 3 = 0) : n = 0 := (Nat.pow_eq_zero.mp hn).1
  rw [good, Nat.mul_zero, Nat.add_zero, Nat.add_eq_zero_iff] at h
  exact h.imp h0 h0

/-- If `(a, b, 1)` is good with `a ≥ b`, then `a = 3` and `b = 2`. -/
theorem eq_321_of_c_eq_one (h : good a b 1) (hba : b ≤ a) : a = 3 ∧ b = 2 := by
  rw [good, Nat.mul_one, Nat.one_pow] at h
  ---- First we prove that `b < a`.
  replace hba : b < a := by
    -- If not then `2a^3 + 1 = a^4 → a^3 ∣ 1 → a = 1`; contradiction.
    refine Nat.lt_of_le_of_ne hba λ h0 ↦ ?_
    rw [h0, ← Nat.pow_two, ← Nat.pow_mul, ← Nat.mul_two, Nat.pow_succ _ 3] at h
    replace h0 : a ^ 3 = 1 := Nat.eq_one_of_dvd_one ((Nat.dvd_add_right ⟨2, rfl⟩).mp ⟨a, h⟩)
    obtain rfl : a = 1 := Nat.eq_one_of_mul_eq_one_left h0
    revert h; decide
  ---- By working modulo `a^2`, we get `a^2 ≤ b^3 + 1`.
  have hba0 : a ^ 2 ≤ b ^ 3 + 1 := by
    refine Nat.le_of_dvd (Nat.succ_pos _) ?_
    rw [← Nat.dvd_add_right ⟨a, rfl⟩, ← Nat.pow_succ, ← Nat.add_assoc, h]
    exact ⟨b ^ 2, Nat.mul_pow a b 2⟩
  ---- Now we prove that `b^2 ≤ 2a`.
  have hba1 : b ^ 2 ≤ 2 * a := by
    refine Nat.le_of_mul_le_mul_left ?_ (Nat.pow_pos (Nat.zero_lt_of_lt hba) (n := 2))
    calc a ^ 2 * b ^ 2
      _ = a ^ 3 + (b ^ 3 + 1) := by rw [← Nat.add_assoc, h, Nat.mul_pow]
      _ ≤ a ^ 3 + a ^ 3 :=
        Nat.add_le_add_left (Nat.pow_lt_pow_left hba (Nat.succ_ne_zero 2)) _
      _ = a ^ 2 * (2 * a) := by rw [← Nat.two_mul, Nat.pow_succ, Nat.mul_left_comm]
  ---- Combining the two inequalities give `b^4 ≤ 4(b^3 + 1)` and so `b ≤ 4`.
  have hb : b ^ 4 ≤ 4 * (b ^ 3 + 1) := calc
    b ^ 4 = (b ^ 2) ^ 2 := Nat.pow_mul b 2 2
    _ ≤ (2 * a) ^ 2 := Nat.pow_le_pow_left hba1 2
    _ = 4 * a ^ 2 := Nat.mul_pow 2 a 2
    _ ≤ 4 * (b ^ 3 + 1) := Nat.mul_le_mul_left 4 hba0
  replace hb : (((b = 0 ∨ b = 1) ∨ b = 2) ∨ b = 3) ∨ b = 4 := by
    suffices b ≤ 4 by simpa only [Nat.le_succ_iff, Nat.le_zero] using this
    refine Nat.le_of_not_gt λ hb0 ↦ Nat.not_lt_of_ge hb ?_
    calc 4 * (b ^ 3 + 1)
      _ < 4 * b ^ 3 + b ^ 3 :=
        Nat.add_lt_add_left (Nat.lt_of_lt_of_le hb0 (Nat.le_pow (Nat.succ_pos 2))) _
      _ = 5 * b ^ 3 := (Nat.succ_mul 4 _).symm
      _ ≤ b * b ^ 3 := Nat.mul_le_mul_right _ hb0
      _ = b ^ 4 := Nat.pow_succ'.symm
  ---- Now split into `5` cases.
  rcases hb with (((rfl | rfl) | rfl) | rfl) | rfl
  ---- Case 1: `b = 0`; contradiction as that would imply `a^3 + 1 = 0`.
  · exact absurd h (Nat.succ_ne_zero (a ^ 3))
  ---- Case 2: `b = 1`; then `a^3 + 2 = a^2`, contradiction.
  · refine absurd h (Nat.ne_of_gt ?_)
    calc (a * 1) ^ 2
      _ = a ^ 2 := by rw [Nat.mul_one]
      _ ≤ a ^ 3 := Nat.pow_le_pow_right (Nat.zero_lt_of_lt hba) (Nat.le_succ 2)
      _ < a ^ 3 + 2 := Nat.lt_add_of_pos_right Nat.two_pos
  ---- Case 3: `b = 2`; we get `a = 3`.
  · refine ⟨Nat.le_antisymm ?_ hba, rfl⟩
    exact (Nat.pow_le_pow_iff_left (Nat.succ_ne_zero 1)).mp hba0
  ---- Case 4: `b = 3`; then `a^2 ≤ 28` and `9 ≤ 2a` yields `a = 5`, contradiction.
  · replace hba1 : 5 ≤ a := Nat.div_lt_of_lt_mul hba1
    replace hba0 : a ≤ 5 := by
      have h0 : 28 < 36 := by decide
      exact Nat.le_of_not_gt λ h1 ↦ Nat.not_lt_of_ge hba0 <|
        Nat.lt_of_lt_of_le h0 (Nat.pow_le_pow_left h1 2)
    obtain rfl : a = 5 := Nat.le_antisymm hba0 hba1
    exfalso; revert h; decide
  ---- Case 5: `b = 4`; then `a^2 ≤ 65` and `16 ≤ 2a` yields `a = 8`, contradiction.
  · replace hba1 : 8 ≤ a := Nat.div_lt_of_lt_mul hba1
    replace hba0 : a ≤ 8 := by
      have h0 : 65 < 81 := by decide
      exact Nat.le_of_not_gt λ h1 ↦ Nat.not_lt_of_ge hba0 <|
        Nat.lt_of_lt_of_le h0 (Nat.pow_le_pow_left h1 2)
    obtain rfl : a = 8 := Nat.le_antisymm hba0 hba1
    exfalso; revert h; decide

/-- If `(a, b, c)` is good and `c ≤ b ≤ a`,
  then `(a, b, c)` is either `(0, 0, 0)` or `(3, 2, 1)`. -/
theorem eq_000_or_321 (h : good a b c) (hcb : c ≤ b) (hba : b ≤ a) :
    (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 3 ∧ b = 2 ∧ c = 1) := by
  obtain rfl | rfl : c = 0 ∨ c = 1 := h.c_eq_zero_or_one hcb hba
  · left; rw [and_iff_left rfl]; exact h.eq_000_of_c_eq_zero
  · right; rw [and_iff_left rfl]; exact h.eq_321_of_c_eq_one hba

end good


/-- Final solution -/
theorem final_solution {p : Nat × Nat × Nat} :
    good p.1 p.2.1 p.2.2 ↔ p = (0, 0, 0) ∨ p = (3, 2, 1) ∨ p = (3, 1, 2)
      ∨ p = (2, 3, 1) ∨ p = (2, 1, 3) ∨ p = (1, 3, 2) ∨ p = (1, 2, 3) := by
  ---- The `←` direction is easy bash.
  refine Iff.symm ⟨λ h ↦ ?_, λ h ↦ ?_⟩
  · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  ---- Now split into `6` cases.
  rcases p with ⟨a, b, c⟩
  obtain hcb | hbc : c ≤ b ∨ b ≤ c := Nat.le_total c b
  all_goals obtain hba | hab : b ≤ a ∨ a ≤ b := Nat.le_total b a
  ---- Case 1: `c ≤ b ≤ a`.
  · obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ :
        (a = 0 ∧ b = 0 ∧ c = 0) ∨ (a = 3 ∧ b = 2 ∧ c = 1) :=
      h.eq_000_or_321 hcb hba
    all_goals trivial
  ---- Case 2: `c ≤ b` and `a ≤ b`; split into two cases again.
  · obtain hac | hca : a ≤ c ∨ c ≤ a := Nat.le_total a c
    -- Case 2.1: `a ≤ c ≤ b`.
    · obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ :
          (b = 0 ∧ c = 0 ∧ a = 0) ∨ (b = 3 ∧ c = 2 ∧ a = 1) :=
        h.perm012.eq_000_or_321 hac hcb
      all_goals trivial
    -- Case 2.2: `c ≤ a ≤ b`.
    · obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ :
          (b = 0 ∧ a = 0 ∧ c = 0) ∨ (b = 3 ∧ a = 2 ∧ c = 1) :=
        h.perm01.eq_000_or_321 hca hab
      all_goals trivial
  ---- Case 3: `b ≤ c` and `b ≤ a`; split into two cases again.
  · obtain hac | hca : a ≤ c ∨ c ≤ a := Nat.le_total a c
    -- Case 3.1: `b ≤ a ≤ c`.
    · obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ :
          (c = 0 ∧ a = 0 ∧ b = 0) ∨ (c = 3 ∧ a = 2 ∧ b = 1) :=
        h.perm021.eq_000_or_321 hba hac
      all_goals trivial
    -- Case 3.2: `b ≤ c ≤ a`.
    · obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ :
          (a = 0 ∧ c = 0 ∧ b = 0) ∨ (a = 3 ∧ c = 2 ∧ b = 1) :=
        h.perm12.eq_000_or_321 hbc hca
      all_goals trivial
  ---- Case 4: `a ≤ b ≤ c`.
  · obtain ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ :
        (c = 0 ∧ b = 0 ∧ a = 0) ∨ (c = 3 ∧ b = 2 ∧ a = 1) :=
      h.perm02.eq_000_or_321 hab hbc
    all_goals trivial
