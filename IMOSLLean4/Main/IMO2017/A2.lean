/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Algebra.Group.Pointwise.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# IMO 2017 A2

For any set $A ⊆ ℝ$, we denote $A - A = \{x - y : x, y ∈ A\}$.

Let $n ≥ 3$ be a positive integer.
Find all real numbers $q$ such that for any finite set $A ⊆ ℝ$ of size $n$
  and for any $x, y ∈ A - A$, there exists $a, b, c, d ∈ A - A$ such that
$$ qxy = a^2 + b^2 - (c^2 + d^2). $$

### Answer

$q ∈ \{0, 2, -2\}$.

### Solution

We follow Solution 1 of the
  [official solution](https://www.imo-official.org/problems/IMO2017SL.pdf).
We generalize $ℝ$ to any commutative ring $R$ of characteristic zero.
The same solution works if $ℝ$ is replaced by any commutative ring of characteristic zero.
We modify the integer set we pick for modulo $8$ argument.
We pick $\{0, 1, 4, 8, 16, 24, …\}$ instead of $\{0, 1, 4, 8, 12, 16, …\}.

We say that $B ⊆ R$ is $q$-*nice* if for any $x, y ∈ B$, there exists $a, b, c, d ∈ B$ with
$$ qxy = a^2 + b^2 - (c^2 + d^2). $$
We say that $q$ is $n$-*good* if $A - A$ is $q$-nice for every subset $A ⊆ R$ of size $n$.
-/

namespace IMOSL
namespace IMO2017A2

open Function Finset
open scoped Pointwise

section

variable [Ring R]

/-- A finite subset `T ⊆ R` is called `q`-*nice* if for every `x, y ∈ T`,
  there exists `a, b, c, d ∈ T` such that `qxy = a^2 + b^2 - c^2 - d^2`. -/
def nice (q : R) (B : Finset R) :=
  ∀ x ∈ B, ∀ y ∈ B, ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, ∃ d ∈ B,
    q * (x * y) = a ^ 2 + b ^ 2 - (c ^ 2 + d ^ 2)

/-- An element `q ∈ R` is called `n`-*good* if
  `A - A` is `q`-nice for any subset `A ⊆ R` of size `n`. -/
def good [DecidableEq R] (n : ℕ) (q : R) := ∀ A : Finset R, #A = n → nice q (A - A)





/-! ### The elements `0` and `2` are good -/

/-- Every finite set is `0`-nice. -/
theorem nice.zero_left (B : Finset R) : nice 0 B :=
  λ x hx _ _ ↦ ⟨x, hx, x, hx, x, hx, x, hx, (zero_mul _).trans (sub_self _).symm⟩

/-- The zero element is always `n`-good. -/
theorem good.zero_right [DecidableEq R] : good n (0 : R) :=
  λ _ _ ↦ nice.zero_left _

/-- If `B` is `q`-nice, then `B` is also `-q`-nice. -/
theorem nice.neg {q : R} (h : nice q B) : nice (-q) B := by
  ---- Indeed, if `qxy = a^2 + b^2 - (c^2 + d^2)`, then `-qxy = c^2 + d^2 - (a^2 + b^2)`.
  intro x hx y hy
  obtain ⟨a, ha, b, hb, c, hc, d, hd, h0⟩ := h x hx y hy
  refine ⟨c, hc, d, hd, a, ha, b, hb, ?_⟩
  rw [neg_mul, h0, neg_sub]

/-- If `q` is `n`-good, then `-q` is also `n`-good. -/
theorem good.neg [DecidableEq R] {q : R} (h : good n q) : good n (-q) :=
  λ S hS ↦ (h S hS).neg

end


/-- Over any commutative ring, `2` is `n`-good. -/
theorem good.two [CommRing R] [DecidableEq R] : good n (2 : R) := by
  ---- Based on `2(t - u)(v - w) = (t - w)^2 + (u - v)^2 - (t - v)^2 - (u - w)^2`.
  rintro S hS x hx y hy
  obtain ⟨t, ht, u, hu, rfl⟩ : ∃ t ∈ S, ∃ u ∈ S, t - u = x := mem_sub.mp hx
  obtain ⟨v, hv, w, hw, rfl⟩ : ∃ v ∈ S, ∃ w ∈ S, v - w = y := mem_sub.mp hy
  exact ⟨t - w, sub_mem_sub ht hw, u - v, sub_mem_sub hu hv,
    t - v, sub_mem_sub ht hv, u - w, sub_mem_sub hu hw, by ring⟩





/-!
### `n`-good elements and ring homomorphisms

In particular, the `n`-good elements over a ring of characteristic zero are integers.
-/

section

variable [Ring R] [Ring S] [DecidableEq S]

/-- If `B` is `q`-nice and `1 ∈ B`, then
  `q = a^2 + b^2 - (c^2 + d^2)` for some `a, b, c, d ∈ B`. -/
theorem nice.exists_sq_add_sq_sub_sq_add_sq {q : R} (h : nice q B) (hB : 1 ∈ B) :
    ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, ∃ d ∈ B, q = a ^ 2 + b ^ 2 - (c ^ 2 + d ^ 2) := by
  simpa only [mul_one] using h 1 hB 1 hB

/-- Let `φ : R → S` be a ring homomorphism, `q ∈ S`, and `B ⊆ R` finite with `1 ∈ B`.
  If `φ(B)` is `q`-nice, then `q = φ(q')` for some `q' ∈ R`. -/
theorem nice.exists_eq_RingHom_apply
    {φ : R →+* S} {q' : S} {B : Finset R} (h : nice q' (B.image φ)) (hB : 1 ∈ B) :
    ∃ q : R, q' = φ q := by
  ---- Since `1 ∈ φ(B)`, we can write `q'` as `φ(a)^2 + φ(b)^2 - (φ(c)^2 + φ(d)^2)`.
  set B' : Finset S := B.image φ
  obtain ⟨a', ha, b', hb, c', hc, d', hd, rfl⟩ :
      ∃ a' ∈ B', ∃ b' ∈ B', ∃ c' ∈ B', ∃ d' ∈ B', q' = a' ^ 2 + b' ^ 2 - (c' ^ 2 + d' ^ 2) :=
    h.exists_sq_add_sq_sub_sq_add_sq (mem_image.mpr ⟨1, hB, φ.map_one⟩)
  obtain ⟨a, -, rfl⟩ : ∃ a ∈ B, φ a = a' := mem_image.mp ha
  obtain ⟨b, -, rfl⟩ : ∃ b ∈ B, φ b = b' := mem_image.mp hb
  obtain ⟨c, -, rfl⟩ : ∃ c ∈ B, φ c = c' := mem_image.mp hc
  obtain ⟨d, -, rfl⟩ : ∃ d ∈ B, φ d = d' := mem_image.mp hd
  ---- Then picking `q = a^2 + b^2 - (c^2 + d^2)` works.
  refine ⟨a ^ 2 + b ^ 2 - (c ^ 2 + d ^ 2), ?_⟩
  simp_rw [φ.map_sub, φ.map_add, φ.map_pow]

/-- Auxiliary lemma: `φ(A - A) = φ(A) - φ(A)`. This is generalizable to `AddMonoidHom`,
  but for implementation convenience, we stick to `RingHom`. -/
lemma Finset_image_sub_RingHom [DecidableEq R] (φ : R →+* S) (A : Finset R) :
    (A - A).image φ = A.image φ - A.image φ := by
  refine ext λ a ↦ ?_
  calc a ∈ (A - A).image φ
    _ ↔ ∃ a', (∃ b ∈ A, ∃ c ∈ A, b - c = a') ∧ φ a' = a := by simp_rw [mem_image, mem_sub]
    _ ↔ ∃ b c, (b ∈ A ∧ c ∈ A ∧ True) ∧ φ (b - c) = a := by simp only [↓existsAndEq]
    _ ↔ ∃ b ∈ A, ∃ c ∈ A, φ (b - c) = a := by simp_rw [and_true, and_assoc, exists_and_left]
    _ ↔ ∃ b ∈ A, ∃ c ∈ A, φ b - φ c = a := by simp_rw [φ.map_sub]
    _ ↔ a ∈ A.image φ - A.image φ := by simp_rw [mem_sub, exists_mem_image]

/-- Let `R` be an infinite ring and `φ : R → S` be an injective ring homomorphism.
  If `q' : S` is `n`-good, where `n ≥ 2`, then `q' = φ(q)` for some `q : R`. -/
theorem good.exists_eq_RingHom_apply [Infinite R] [DecidableEq R]
    {φ : R →+* S} (hφ : Injective φ) {q' : S} {n : ℕ} (hn : n ≥ 2) (h : good n q') :
    ∃ q : R, q' = φ q := by
  ---- We just need to find a set `A` of size `n` containing `0` and `1` so that `1 ∈ A - A`.
  obtain ⟨A, hA, rfl⟩ : ∃ A : Finset R, {0, 1} ⊆ A ∧ #A = n :=
    Infinite.exists_superset_card_eq _ _ (card_le_two.trans hn)
  replace h : nice q' ((A - A).image φ) :=
    Finset_image_sub_RingHom φ A ▸ h (A.image φ) (A.card_image_of_injective hφ)
  have h0 : 1 ∈ A - A :=
    sub_subset_sub hA hA <| mem_sub.mpr
      ⟨1, mem_insert_of_mem (mem_singleton_self _), 0, mem_insert_self _ _, sub_zero _⟩
  exact h.exists_eq_RingHom_apply h0

/-- Let `φ : R → S` be a ring homomorphism, `q ∈ R`, and `B ⊆ R` finite.
  If `B` is `q`-nice, then `φ(B)` is `φ(q)`-nice. -/
theorem nice.RingHom_apply {φ : R →+* S} {q : R} {B : Finset R} (h : nice q B) :
    nice (φ q) (B.image φ) := by
  refine forall_mem_image.mpr λ x hx ↦ forall_mem_image.mpr λ y hy ↦ ?_
  obtain ⟨a, ha, b, hb, c, hc, d, hd, h0⟩ :
      ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, ∃ d ∈ B, q * (x * y) = a ^ 2 + b ^ 2 - (c ^ 2 + d ^ 2) :=
    h x hx y hy
  refine ⟨φ a, mem_image_of_mem _ ha, φ b, mem_image_of_mem _ hb,
    φ c, mem_image_of_mem _ hc, φ d, mem_image_of_mem _ hd, ?_⟩
  simp_rw [← φ.map_mul, ← φ.map_pow, ← φ.map_add, ← φ.map_sub, h0]

/-- Let `φ : R → S` be an injective ring homomorphism, `q ∈ R`, and `B ⊆ R` finite.
  Then `φ(B)` is `φ(q)`-nice if and only if `B` is `q`-nice. -/
theorem nice.RingHom_apply_iff {φ : R →+* S} (hφ : Injective φ) {q : R} {B : Finset R} :
    nice (φ q) (B.image φ) ↔ nice q B := by
  simp_rw [nice, forall_mem_image, exists_mem_image]
  iterate 2 refine forall_congr' λ _ ↦ imp_congr_right λ _ ↦ ?_
  iterate 4 refine exists_congr λ _ ↦ and_congr_right λ _ ↦ ?_
  simp_rw [← φ.map_mul, ← φ.map_pow, ← φ.map_add]
  rw [← φ.map_sub, hφ.eq_iff]

/-- Let `R` be a ring, `q : R`, and `φ : R → S` be an injective ring homomorphism.
  If `φ(q)` is `n`-good, then `q` is `n`-good. -/
theorem good.of_RingHom_apply [DecidableEq R]
    {φ : R →+* S} (hφ : Injective φ) {q n} (h : good n (φ q)) : good n q := by
  rintro A rfl
  replace h : nice (φ q) (A.image φ - A.image φ) := h _ (card_image_of_injective _ hφ)
  rwa [← Finset_image_sub_RingHom, nice.RingHom_apply_iff hφ] at h

/-- Let `R` be an infinite ring, `q : R`, and `φ : R → S` be an injective ring homomorphism.
  If `q' : S` is `n`-good, where `n ≥ 2`, then `q' = φ(q)` for some `n`-good element `q`. -/
theorem good.exists_eq_good_RingHom_apply [Infinite R] [DecidableEq R]
    {φ : R →+* S} (hφ : Injective φ) {q' : S} {n : ℕ} (hn : n ≥ 2) (h : good n q') :
    ∃ q : R, good n q ∧ q' = φ q := by
  obtain ⟨q, rfl⟩ : ∃ q : R, q' = φ q := h.exists_eq_RingHom_apply hφ hn
  exact ⟨q, h.of_RingHom_apply hφ, rfl⟩

/-- The `n`-good elements in a ring of characteristic zero are `n`-good integers. -/
theorem good.exists_intCast_of_CharZero [CharZero R] [DecidableEq R]
    {q : R} {n : ℕ} (hn : n ≥ 2) (h : good n q) : ∃ N : ℤ, good n N ∧ q = N :=
  h.exists_eq_good_RingHom_apply (φ := Int.castRingHom R) Int.cast_injective hn

end





/-! ### The integer case -/

/-- If there is a `q`-nice set of integers containing a non-zero element, then `q ≤ 2`. -/
theorem nice.Int_le_two {B : Finset ℤ} (hB : ∃ N ∈ B, N ≠ 0) (h : nice q B) : q ≤ 2 := by
  ---- Let `x₀` be an element of the maximum absolute value in `B`.
  obtain ⟨x₀, hx₀, hx₀0⟩ : ∃ x₀ ∈ B, ∀ x ∈ B, x.natAbs ≤ x₀.natAbs := by
    have hB0 : B.Nonempty := hB.imp λ _ ↦ And.left
    obtain ⟨x₀, hx₀, hx₀0⟩ : ∃ x₀ ∈ B, B.sup' hB0 Int.natAbs = x₀.natAbs :=
      exists_mem_eq_sup' hB0 Int.natAbs
    exact ⟨x₀, hx₀, λ x hx ↦ (le_sup' Int.natAbs hx).trans_eq hx₀0⟩
  ---- Since `B` contains a non-zero element, we have `|x₀| ≠ 0` and so `x₀^2 > 0`.
  replace hB : 0 < x₀ ^ 2 := by
    rcases hB with ⟨N, hNB, hN⟩
    rw [← Int.natAbs_pow_two, ← Int.natCast_pow, Int.natCast_pos]
    exact Nat.pow_pos ((Int.natAbs_pos.mpr hN).trans_le (hx₀0 _ hNB))
  ---- Thus it suffices to show that `q x₀^2 ≤ 2 x₀^2`.
  suffices q * x₀ ^ 2 ≤ 2 * x₀ ^ 2 from Int.le_of_mul_le_mul_right this hB
  ---- Now by the choice of `x₀`, we have `x^2 ≤ x₀^2` for any `x ∈ B`.
  replace hx₀0 (x) (hx : x ∈ B) : x ^ 2 ≤ x₀ ^ 2 := calc
    _ = ((x.natAbs ^ 2 : ℕ) : ℤ) := (Int.natAbs_pow_two _).symm
    _ ≤ (x₀.natAbs ^ 2 : ℕ) := Int.ofNat_le.mpr (Nat.pow_le_pow_left (hx₀0 x hx) 2)
    _ = x₀ ^ 2 := Int.natAbs_pow_two x₀
  ---- Since `x₀ ∈ B`, we can write `qx₀^2 = a^2 + b^2 - (c^2 + d^2)` with `a, b, c, d ∈ B`.
  obtain ⟨a, ha, b, hb, c, -, d, -, h0⟩ :
      ∃ a ∈ B, ∃ b ∈ B, ∃ c ∈ B, ∃ d ∈ B, q * (x₀ * x₀) = a ^ 2 + b ^ 2 - (c ^ 2 + d ^ 2) :=
    h _ hx₀ _ hx₀
  ---- But `a^2 + b^2 - (c^2 + d^2) ≤ a^2 + b^2 ≤ 2 x₀^2`, so we are done.
  calc q * x₀ ^ 2
    _ = q * (x₀ * x₀) := congrArg (q * ·) (sq _)
    _ = a ^ 2 + b ^ 2 - (c ^ 2 + d ^ 2) := h0
    _ ≤ a ^ 2 + b ^ 2 :=
      Int.sub_le_self _ (Int.add_nonneg (Int.sq_nonnneg _) (Int.sq_nonnneg _))
    _ ≤ x₀ ^ 2 + x₀ ^ 2 := Int.add_le_add (hx₀0 a ha) (hx₀0 b hb)
    _ = 2 * x₀ ^ 2 := (Int.two_mul _).symm

/-- If `n ≥ 2` and an integer `q` is `n`-good, then `q ≤ 2`. -/
theorem good.Int_le_two (hn : n ≥ 2) {q : ℤ} (h : good n q) : q ≤ 2 := by
  let A : Finset ℤ := (range n).image Nat.cast
  replace h : nice q (A - A) :=
    h _ ((card_image_of_injective _ λ _ _ ↦ Int.natCast_inj.mp).trans (card_range n))
  have h0 (i : ℕ) (hi : i < n) : (i : ℤ) ∈ A := mem_image_of_mem _ (mem_range.mpr hi)
  replace h0 : ∃ N ∈ A - A, N ≠ 0 :=
    ⟨1, mem_sub.mpr ⟨1, h0 1 hn, 0, h0 0 (Nat.zero_lt_of_lt hn), rfl⟩, Int.one_ne_zero⟩
  refine h.Int_le_two h0

/-- In `ℤ/8ℤ`, `{0, 1, 3, 4, 5, 7}` is not `1`-nice. -/
theorem not_nice_one_013457 : ¬nice (1 : ZMod 8) ({0, 1, 3, 4, 5, 7} : Finset (ZMod 8)) := by
  ---- Let `B = {0, 1, 4, 7}` and `C = {x^2 : x ∈ B}`.
  set B : Finset (ZMod 8) := {0, 1, 3, 4, 5, 7}
  let C : Finset (ZMod 8) := B.image (λ x ↦ x ^ 2)
  ---- Then `4 = a + b - (c + d)` for some `a, b, c, d ∈ B`.
  intro h; replace h : ∃ a ∈ C, ∃ b ∈ C, ∃ c ∈ C, ∃ d ∈ C, 4 = a + b - (c + d) := by
    simpa only [C, exists_mem_image] using h 1 (by decide) 4 (by decide)
  ---- it is easy to see that `C = {0, 1}`.
  have hC : C = {0, 1} := by decide
  clear_value C; subst hC
  ---- Now we can run the decision procedure, with 16 cases only vs. 256 cases.
  revert h; decide

/-- For any `n ≥ 3`, there is of integers of size `n` whose image mod `8` is `{0, 1, 4}`. -/
theorem exists_Int_card_eq_ZMod8_image_eq (hn : n ≥ 3) :
    ∃ A : Finset ℤ, #A = n ∧ A.image (Int.castRingHom (ZMod 8)) = {0, 1, 4} := by
  ---- We pick `A = {0, 1, 4, 8, 16, 24, …, 8(n - 3)}`.
  let f (i : ℕ) : ℤ := 8 * i
  set φ : ℤ →+* ZMod 8 := Int.castRingHom (ZMod 8)
  refine ⟨(range (n - 2)).image f ∪ {1, 4}, ?_, ?_⟩
  ---- Check that `#A = n`.
  · have h : (8 : ℤ) ≠ 0 := by decide
    have hf : f.Injective := λ _ _ h0 ↦ Int.natCast_inj.mp (Int.eq_of_mul_eq_mul_left h h0)
    have hf0 (A : Finset ℕ) : Disjoint (A.image f) {1, 4} := by
      have hf0 : ∀ x ∈ A.image f, 8 ∣ x := forall_mem_image.mpr λ i hi ↦ ⟨i, rfl⟩
      rw [disjoint_insert_right, disjoint_singleton_right]
      refine ⟨λ h0 ↦ ?_, λ h0 ↦ ?_⟩
      all_goals refine absurd (hf0 _ h0) ?_; decide
    calc #((range (n - 2)).image f ∪ {1, 4})
      _ = #((range (n - 2)).image f) + #{1, 4} := card_union_of_disjoint (hf0 _)
      _ = #(range (n - 2)) + 2 := congrArg₂ _ (card_image_of_injective _ hf) rfl
      _ = n := by rw [card_range, Nat.sub_add_cancel (Nat.le_of_succ_le hn)]
  ---- Check that the image of `A` modulo `8` is `{0, 1, 4}`.
  · have h : φ ∘ f = (λ _ ↦ 0) := funext λ i ↦ (ZMod.natCast_eq_zero_iff _ 8).mpr ⟨i, rfl⟩
    replace hn : (range (n - 2)).Nonempty := ⟨0, mem_range.mpr (Nat.zero_lt_sub_of_lt hn)⟩
    rw [image_union, image_image, h, image_const hn 0]; rfl

/-- The integer `1` is not `n`-good for any `n ≥ 3`. -/
theorem not_good_Int_one (hn : n ≥ 3) : ¬good n (1 : ℤ) := by
  ---- Suppose for the sake of contradiction that `1` is `n`-good.
  intro h
  ---- Pick a set `A` of size `n` whose image mod `8` is `{0, 1, 4}`.
  let φ : ℤ →+* ZMod 8 := Int.castRingHom (ZMod 8)
  obtain ⟨A, hA, hA0⟩ : ∃ A, #A = n ∧ A.image φ = {0, 1, 4} :=
    exists_Int_card_eq_ZMod8_image_eq hn
  ---- Then `A - A` is `1`-nice, and so `A - A` mod `8` is`1`-nice.
  replace h : nice 1 ((A - A).image φ) := (h _ hA).RingHom_apply
  ---- But `A - A = {0, 1, 3, 4, 5, 7}`, which is not `1`-nice; contradiction.
  replace hA0 : (A - A).image φ = {0, 1, 3, 4, 5, 7} := by
    rw [Finset_image_sub_RingHom, hA0]; decide
  exact not_nice_one_013457 (hA0 ▸ h)

/-- If `q` is `n`-good where `n ≥ 3`, then `q` is either equal to `0`, `2`, or `-2`. -/
theorem good.Int_eq_zero_or_two_or_neg_two (hn : n ≥ 3) {q : ℤ} (h : good n q) :
    q = 0 ∨ q = 2 ∨ q = -2 := by
  suffices q = 0 ∨ q.natAbs = 2 from this.imp_right Int.natAbs_eq_natAbs_iff.mp
  ---- WLOG assume `q ≥ 0`.
  wlog hq : 0 ≤ q generalizing q
  · exact (this h.neg (Int.neg_nonneg_of_nonpos (Int.le_of_not_le hq))).imp
      Int.neg_eq_zero.mp (Int.natAbs_neg q).symm.trans
  ---- If `q = 0` then we are done so assume `q > 0`.
  refine hq.eq_or_lt.imp Eq.symm λ hq ↦ ?_
  ---- Then either `q = 1` or `q ≥ 2`.
  obtain rfl | hq : q = 1 ∨ q ≥ 2 := by
    rwa [← Int.add_one_le_iff, Int.zero_add, le_iff_eq_or_lt', ← Int.add_one_le_iff] at hq
  ---- The former fails since `1` is not `n`-good, the latter implies `q = 2`.
  exacts [absurd h (not_good_Int_one hn),
    congrArg Int.natAbs (Int.le_antisymm (h.Int_le_two (Nat.le_of_succ_le hn)) hq)]





/-! ### Summary -/

/-- Final solution -/
theorem final_solution [CommRing R] [DecidableEq R] [CharZero R] {q : R} (hn : n ≥ 3) :
    good n q ↔ q = 0 ∨ q = 2 ∨ q = -2 := by
  refine ⟨λ h ↦ ?_, ?_⟩
  ---- `→` direction.
  · obtain ⟨N, hnN, rfl⟩ : ∃ N : ℤ, good n N ∧ q = N :=
      h.exists_intCast_of_CharZero (Nat.le_of_succ_le hn)
    refine (hnN.Int_eq_zero_or_two_or_neg_two hn).imp ?_ (Or.imp ?_ ?_)
    all_goals rintro rfl; simp
  ---- `←` direction.
  · rintro (rfl | rfl | rfl)
    exacts [good.zero_right, good.two, good.two.neg]
