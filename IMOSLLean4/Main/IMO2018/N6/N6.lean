/-
Copyright (c) 2025 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.PNat.Find

/-!
# IMO 2018 N6

Let $f : ℕ⁺ → ℕ⁺$ be a function such that $f(m + n) ∣ f(m) + f(n)$ for all $m, n ∈ ℕ⁺$.
Prove that there exists $n₀ ∈ ℕ⁺$ such that $f(n₀) ∣ f(n)$ for all $n ∈ ℕ⁺$.
-/

namespace IMOSL
namespace IMO2018N6

/-! ### Extra lemmas -/

lemma PNat_eq_of_dvd_of_lt_mul_one_add_one
    {a b : ℕ+} (h : a ∣ b) (h0 : b < a * (1 + 1)) : b = a := by
  rcases h with ⟨c, rfl⟩
  rw [mul_lt_mul_iff_left, PNat.lt_add_one_iff, PNat.le_one_iff] at h0
  rw [h0, mul_one]

lemma PNat_exists_greatest_infinite_fiber {f : ℕ+ → ℕ+} (h : ∃ N, ∀ n, f n ≤ N) :
    ∃ M, (∀ N, ∃ n ≥ N, f n = M) ∧ (∃ C, ∀ n ≥ C, f n ≤ M) := by
  contrapose! h
  suffices ∀ M N, ∃ n ≥ N, M ≤ f n by
    intro N; obtain ⟨n, -, hn⟩ := this (N + 1) 1
    exact ⟨n, PNat.add_one_le_iff.mp hn⟩
  intro M; induction' M using PNat.recOn with M M_ih
  · intro N; exact ⟨N, le_refl N, (f N).one_le⟩
  · by_contra! h0; rcases h0 with ⟨K, hK⟩
    have h0 (N) : ∃ n ≥ N, f n = M := by
      obtain ⟨n, hn, h1⟩ := M_ih (N + K)
      exact ⟨n, (N.lt_add_right K).le.trans hn,
        h1.antisymm' <| PNat.lt_add_one_iff.mp <| hK n <| (K.lt_add_left N).le.trans hn⟩
    obtain ⟨n, h1, h2⟩ := h _ h0 K
    exact (PNat.add_one_le_iff.mpr h2).not_gt (hK n h1)

lemma PNat_exists_big_not_dvd {d : ℕ+} (hd : d > 1) (N : ℕ+) : ∃ n ≥ N, ¬d.val ∣ n := by
  refine (em' (d.val ∣ N)).elim (λ h ↦ ⟨N, le_refl N, h⟩)
    (λ h ↦ ⟨N + 1, (N.lt_add_right _).le, λ h0 ↦ ?_⟩)
  rw [PNat.add_coe, Nat.dvd_add_right h, ← PNat.dvd_iff] at h0
  exact hd.not_ge (PNat.le_of_dvd h0)





/-! ### Theory of good functions -/

structure GoodFun (G) [Add G] where
  toFun : G → ℕ+
  good_def' m n : toFun (m + n) ∣ toFun m + toFun n


namespace GoodFun

section

variable [Add G]

instance : FunLike (GoodFun G) G ℕ+ where
  coe f := f.toFun
  coe_injective' f g h := by rwa [GoodFun.mk.injEq]

@[ext] theorem ext {f g : GoodFun G} : (∀ x, f x = g x) → f = g :=
  DFunLike.ext _ _

theorem good_def (f : GoodFun G) : ∀ m n, f (m + n) ∣ f m + f n :=
  f.good_def'

theorem good_def2 (f : GoodFun G) (m n) : (f (m + n)).val ∣ f m + f n :=
  PNat.dvd_iff.mp (f.good_def m n)

/-- Scalar multiplication of a good function. -/
protected def smul (c : ℕ+) (f : GoodFun G) : GoodFun G :=
  ⟨λ n ↦ c * f n, λ m n ↦ by simpa only [mul_add] using mul_dvd_mul_left c (f.good_def m n)⟩

instance : SMul ℕ+ (GoodFun G) := ⟨GoodFun.smul⟩

@[simp] theorem smul_apply (c : ℕ+) (f : GoodFun G) (n) : (c • f) n = c * f n := rfl


variable (f : GoodFun G) {M : ℕ+} (h : ∀ n, M ∣ f n)
include h

protected def div : GoodFun G where
  toFun n := (f n).divExact M
  good_def' m n := by
    obtain ⟨k, h0⟩ : f (m + n) ∣ f m + f n := f.good_def m n
    replace h (n) : M * (f n).divExact M = f n := PNat.mul_div_exact (h n)
    rw [← h m, ← h n, ← h (m + n), ← mul_add, mul_assoc, mul_right_inj] at h0
    exact ⟨k, h0⟩

@[simp] theorem div_apply : f.div h n = (f n).divExact M := rfl

theorem smul_div : M • f.div h = f :=
  ext λ n ↦ PNat.mul_div_exact (h n)

end





/-! ### Construction of good functions -/

/-- The identity function as a good function. -/
protected def id : GoodFun ℕ+ :=
  ⟨id, λ m n ↦ dvd_refl (m + n)⟩

@[simp] theorem id_apply (n) : GoodFun.id n = n := rfl


section

variable (G) [Add G]

/-- The constant function as a good function. -/
protected def const (c : ℕ+) : GoodFun G :=
  ⟨λ _ ↦ c, λ _ _ ↦ ⟨2, PNat.coe_inj.mp c.val.mul_two.symm⟩⟩

@[simp] theorem const_apply (c x) : GoodFun.const G c x = c := rfl

theorem const_mul_eq_smul (m n : ℕ+) :
    GoodFun.const G (m * n) = m • GoodFun.const G n := rfl

theorem const_eq_smul_const_one (m : ℕ+) : GoodFun.const G m = m • GoodFun.const G 1 :=
  GoodFun.ext λ _ ↦ (mul_one m).symm

end


/-- The periodic `1-2` function as a good function. -/
protected def periodic_one_two (d : ℕ+) : GoodFun ℕ+ where
  toFun n := if d.val ∣ n then 2 else 1
  good_def' m n := by
    ---- If `d ∤ m + n`, we are done
    obtain h | h : ¬d.val ∣ (m + n : ℕ+) ∨ d.val ∣ (m + n : ℕ+) := dec_em' _
    · simp only [if_neg h]; exact one_dvd _
    simp only [if_pos h]; obtain h0 | h0 : d.val ∣ m ∨ ¬d.val ∣ m := dec_em _
    ---- Case `d ∣ m` and `d ∣ n`
    · rw [PNat.add_coe, Nat.dvd_add_right h0] at h
      rw [if_pos h0, if_pos h]
      exact ⟨2, rfl⟩
    ---- Case `d ∣ m + n`, `d ∤ m`, and `d ∤ n`
    · replace h : ¬d.val ∣ n := λ h1 ↦ h0 (by rwa [PNat.add_coe, Nat.dvd_add_left h1] at h)
      rw [if_neg h0, if_neg h]
      exact dvd_refl 2

@[simp] theorem periodic_one_two_apply (d n) :
    GoodFun.periodic_one_two d n = if d.val ∣ n then 2 else 1 := rfl

theorem periodic_one_two_apply_of_dvd {d n : ℕ+} (h : d.val ∣ n) :
    GoodFun.periodic_one_two d n = 2 := if_pos h

theorem periodic_one_two_apply_of_not_dvd {d n : ℕ+} (h : ¬d.val ∣ n) :
    GoodFun.periodic_one_two d n = 1 := if_neg h





/-! ### Start of the problem -/

theorem map_le_mul_map_one (f : GoodFun ℕ+) (n : ℕ+) : f n ≤ f 1 * n := by
  induction n using PNat.recOn with | one => exact (mul_one _).ge | succ n hn => ?_
  apply (PNat.le_of_dvd (f.good_def n 1)).trans
  rwa [mul_add_one, add_le_add_iff_right]

theorem map_add_eq_of_map_lt_dvd_map_add {f : GoodFun ℕ+}
    (h : f k < M) (h0 : f m < M) (h1 : M ∣ f (k + m)) : f k + f m = M :=
  PNat_eq_of_dvd_of_lt_mul_one_add_one (h1.trans (f.good_def k m))
    ((add_lt_add h h0).trans_eq (by rw [mul_add_one, mul_one]))

theorem map_add_eq_of_map_lt {f : GoodFun ℕ+} (h : f k < f (k + m)) (h0 : f m < f (k + m)) :
    f k + f m = f (k + m) :=
  map_add_eq_of_map_lt_dvd_map_add h h0 (dvd_refl _)

/-- If `f` is unbounded, then `f(n) = f(1) n` for all `n`. -/
theorem eq_smul_id_of_unbounded {f : GoodFun ℕ+} (hf : ∀ N, ∃ n, N < f n) :
    ∃ d : ℕ+, f = d • GoodFun.id := by
  ---- Reduce to just proving `f(n + 1) = f(n) + f(1)`
  suffices ∀ n, f (n + 1) = f n + f 1 by
    refine ⟨f 1, ext λ n ↦ ?_⟩
    induction n using PNat.recOn with
    | one => exact (mul_one (f 1)).symm
    | succ n n_ih => rw [this, n_ih]; exact (mul_add_one _ _).symm
  ---- Find the minimal `N` such that `f(N) > a(2n + 1)`
  intro n
  obtain ⟨N, hN, hN0⟩ :
      ∃ N, f 1 * (n + (n + 1)) < f N ∧ ∀ m < N, f m ≤ f 1 * (n + (n + 1)) := by
    set C := f 1 * (n + (n + 1)); let hC := hf C
    exact ⟨PNat.find hC, PNat.find_spec hC, λ m hm ↦ le_of_not_gt (PNat.find_min hC hm)⟩
  replace hf (m) (hm : m < N) : f m < f N := (hN0 m hm).trans_lt hN
  ---- If `k + m = N`, then `f(k) + f(m) = f(N)`
  replace hf {k m} (h : k + m = N) : f k + f m = f N := by
    subst h; exact f.map_add_eq_of_map_lt (hf _ (k.lt_add_right m)) (hf _ (m.lt_add_left k))
  ---- Rewrite `N` as `M + n + 1`
  obtain ⟨M, rfl⟩ : ∃ M, M + (n + 1) = N :=
    ⟨N - (n + 1), PNat.sub_add_of_lt <| lt_of_not_ge λ h ↦
      hN.not_ge <| (f.map_le_mul_map_one N).trans <|
        mul_le_mul_left' (h.trans (PNat.lt_add_left _ _).le) _⟩
  ---- We get `f(M) + f(n + 1) = f(M + 1) + f(n)`
  replace hf : f M + f (n + 1) = f (M + 1) + f n :=
    (hf rfl).trans (hf (by rw [add_right_comm, add_assoc])).symm
  ---- Reduce to `f(M + 1) = f(M) + f(1)`
  suffices f (M + 1) = f M + f 1 by
    rwa [this, add_right_comm, add_assoc, add_right_inj] at hf
  ---- Finally, prove `f(M + 1) = f(M) + f(1)`
  refine (PNat_eq_of_dvd_of_lt_mul_one_add_one (f.good_def M 1) ?_).symm
  replace hN0 : f M ≤ f 1 * (n + (n + 1)) := hN0 _ (PNat.lt_add_right _ _)
  replace hN : f 1 * (n + 1) < f (M + 1) :=
    lt_of_add_lt_add_right (a := f n) <| calc f 1 * (n + 1) + f n
      _ ≤ f 1 * (n + 1) + f 1 * n := add_le_add_left (f.map_le_mul_map_one n) _
      _ = f 1 * (n + (n + 1)) := by rw [← mul_add, add_comm]
      _ < f (M + (n + 1)) := hN
      _ = f (M + 1 + n) := by rw [add_right_comm, add_assoc]
      _ ≤ f (M + 1) + f n := PNat.le_of_dvd (f.good_def _ _)
  calc f M + f 1
    _ ≤ f 1 * (n + (n + 1)) + f 1 := add_le_add_right hN0 (f 1)
    _ = f 1 * (n + 1) * (1 + 1) := by
      rw [← mul_add_one, add_right_comm, mul_assoc, mul_add_one, mul_one]
    _ < f (M + 1) * 2 := mul_lt_mul_right' hN 2

theorem dvd_map_add_imp_iff {f : GoodFun ℕ+} {M : ℕ}
    (h : M ∣ f (m + n)) (h0 : M ∣ f m) : M ∣ f n :=
  (Nat.dvd_add_right h0).mp (h.trans (PNat.dvd_iff.mp (f.good_def m n)))

theorem dvd_map_dvd_map_mul_add_imp {f : GoodFun ℕ+} {M : ℕ}
    (h : M ∣ f d) (h0 : M ∣ f (d * (m + k))) : M ∣ f (d * m) := by
  have h1 {m} (h1 : M ∣ f (d * (m + 1))) : M ∣ f (d * m) := by
    rw [mul_add_one, add_comm] at h1; exact dvd_map_add_imp_iff h1 h
  induction' k using PNat.caseStrongInductionOn with k k_ih
  exacts [h1 h0, k_ih _ (le_refl k) (h1 (add_assoc m k 1 ▸ h0))]

theorem dvd_map_dvd_map_mul_imp {f : GoodFun ℕ+} {M : ℕ}
    (h : M ∣ f d) (h0 : M ∣ f (d * k)) (h1 : m ≤ k) : M ∣ f (d * m) :=
  h1.eq_or_lt.elim (λ h2 ↦ h2 ▸ h0)
    (λ h2 ↦ dvd_map_dvd_map_mul_add_imp h (by rwa [PNat.add_sub_of_lt h2]))

theorem exists_dvd_dvd_imp {f : GoodFun ℕ+} {M : ℕ} (h : ∃ n, M ∣ f n) :
    ∃ d : ℕ+, M ∣ f d ∧ ∀ n, M ∣ f n → d.val ∣ n := by
  let d := PNat.find h
  have d_spec : M ∣ f d := PNat.find_spec h
  refine ⟨d, d_spec, λ n hn ↦ ?_⟩
  induction' n using PNat.strongInductionOn with n n_ih
  obtain rfl | ⟨m, rfl⟩ : d = n ∨ ∃ m, m + d = n :=
    (PNat.find_min' h hn).eq_or_lt.imp_right λ h0 ↦ ⟨n - d, PNat.sub_add_of_lt h0⟩
  exacts [d.val.dvd_refl, Nat.dvd_add_self_right.mpr <| n_ih _ (m.lt_add_right d) <|
    (Nat.dvd_add_iff_left d_spec).mpr (hn.trans (f.good_def2 m d))]

theorem dvd_set_infinite_imp {f : GoodFun ℕ+} {M : ℕ} (h : ∀ N, ∃ n ≥ N, M ∣ f n) :
    ∃ d : ℕ+, ∀ n, M ∣ f n ↔ d.val ∣ n := by
  obtain ⟨d, hd, hd0⟩ := exists_dvd_dvd_imp ((h 1).imp λ _ ↦ And.right)
  refine ⟨d, λ n ↦ ⟨hd0 n, ?_⟩⟩
  rw [← PNat.dvd_iff]; rintro ⟨k, rfl⟩
  obtain ⟨n, h0, h1⟩ : ∃ n ≥ d * k, M ∣ f n := h (d * k)
  obtain ⟨m, rfl⟩ : d ∣ n := (PNat.dvd_iff).mpr (hd0 n h1)
  exact dvd_map_dvd_map_mul_imp hd h1 ((mul_le_mul_iff_left d).mp h0)

theorem exists_limsup_and_dvd_map_iff {f : GoodFun ℕ+} (h : ∃ N, ∀ n, f n ≤ N) :
    ∃ M, (∃ N, ∀ n ≥ N, f n ≤ M) ∧ (∃ d : ℕ+, ∀ n, M.val ∣ f n ↔ d.val ∣ n) := by
  obtain ⟨M, h0, h1⟩ := PNat_exists_greatest_infinite_fiber h
  exact ⟨M, h1, dvd_set_infinite_imp λ N ↦ (h0 N).imp λ n ↦ And.imp_right λ h2 ↦ by rw [h2]⟩

theorem dvd_set_cofinite_imp {f : GoodFun ℕ+} {M : ℕ} (h : ∃ N, ∀ n ≥ N, M ∣ f n) :
    ∀ n, M ∣ f n := by
  rcases h with ⟨K, h⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ+, ∀ n, M ∣ f n ↔ d.val ∣ n :=
    f.dvd_set_infinite_imp λ N ↦ ⟨K ⊔ N, le_max_right K N, h _ (le_max_left K N)⟩
  suffices d = 1 from λ n ↦ (hd n).mpr (this ▸ n.1.one_dvd)
  simp only [hd] at h
  rw [← PNat.dvd_one_iff, PNat.dvd_iff, Nat.dvd_add_iff_right (h K (le_refl K))]
  exact h (K + 1) (K.lt_add_right 1).le

theorem eq_set_cofinite_imp {f : GoodFun ℕ+} (h : ∃ N, ∀ n ≥ N, f n = M) :
    ∃ g : GoodFun ℕ+, f = M • g ∧ ∃ N, ∀ n ≥ N, g n = 1 := by
  rcases h with ⟨N, hN⟩
  have h0 (n) : M ∣ f n := PNat.dvd_iff.mpr <|
    f.dvd_set_cofinite_imp ⟨N, λ n hn ↦ dvd_of_eq (congrArg _ (hN n hn).symm)⟩ n
  let hg : M • f.div h0 = f := f.smul_div h0
  refine ⟨f.div h0, hg.symm, N, λ n hn ↦ ?_⟩
  rw [← mul_eq_left, ← smul_apply, hg, hN n hn]

theorem eventually_bound_and_dvd_iff_period_imp {f : GoodFun ℕ+} (hN : ∀ n ≥ N, f n ≤ M)
    {d : ℕ+} (hd : d > 1) (hd0 : ∀ n, M.val ∣ f n ↔ d.val ∣ n) :
    ∃ C, 2 * C = M ∧ ∀ n, n ≥ N → f n = C * if d.val ∣ n then 2 else 1 := by
  replace hd0 (n) (hn : n ≥ N) : f n = M ↔ d.val ∣ n := by
    rw [← hd0, ← PNat.dvd_iff]
    exact ⟨λ h ↦ h ▸ dvd_refl _, λ h ↦ (hN n hn).antisymm (PNat.le_of_dvd h)⟩
  replace hN (n) (hn : n ≥ N) (hn0 : ¬d.1 ∣ n) : f n < M :=
    (hN n hn).lt_of_ne λ h ↦ hn0 ((hd0 n hn).mp h)
  ---- Reduce to showing that `2 f(n) = M` whenever `n ≥ N` is not divisible by `d`.
  suffices ∀ n ≥ N, ¬d.1 ∣ n → 2 * f n = M by
    obtain ⟨c, hc, hc0⟩ := PNat_exists_big_not_dvd hd N
    obtain rfl := this c hc hc0
    refine ⟨f c, rfl, λ n hn ↦ ?_⟩
    split_ifs with hn0
    · rw [(hd0 n hn).mpr hn0, mul_comm]
    · rw [mul_one, ← mul_left_cancel_iff, this n hn hn0]
  ---- First, `f(k) + f(m) = M` whenever `k, m ≥ N` not divisible by `d` but `d ∣ k + m`.
  replace hN {k m : ℕ+} (hk : k ≥ N) (hm : m ≥ N) (hk0 : ¬d.val ∣ k)
      (hm0 : ¬d.val ∣ m) (h : d.val ∣ k + m) : f k + f m = M :=
    map_add_eq_of_map_lt_dvd_map_add (hN _ hk hk0) (hN _ hm hm0)
      (dvd_of_eq ((hd0 (k + m) (hk.trans (k.lt_add_right m).le)).mpr h).symm)
  ---- Second, `f(k) ∣ f(m)` whenever `k, m ≥ N` not divisible by `d` but `d ∣ k + m`.
  replace hd0 : f (N * d) = M :=
    (hd0 _ (le_mul_of_one_le_right' d.one_le)).mpr (Nat.dvd_mul_left _ _)
  replace hd0 {k m : ℕ+} (hk : k ≥ N) (hm : m ≥ N) (hk0 : ¬d.val ∣ k)
      (hm0 : ¬d.val ∣ m) (h : d.val ∣ k + m) : (f k).val ∣ f m := by
    have h0 : f k + f m = M := hN hk hm hk0 hm0 h
    have h1 : f (N * d + k) + f m = M := by
      have h1 : d.val ∣ N * d := d.val.dvd_mul_left N
      refine hN (hk.trans (k.lt_add_left _).le) hm ?_ hm0 ?_
      · rwa [PNat.add_coe, PNat.mul_coe, Nat.dvd_add_right h1]
      · rwa [PNat.add_coe, PNat.mul_coe, add_assoc, Nat.dvd_add_right h1]
    rw [← h0, add_left_inj] at h1
    rw [← Nat.dvd_add_self_left, ← PNat.add_coe, h0, ← hd0,
      ← Nat.dvd_add_self_right, ← PNat.add_coe, ← PNat.dvd_iff]
    exact (dvd_of_eq h1.symm).trans (f.good_def _ _)
  ---- Finish
  intro k hk hk0
  obtain ⟨m, hm, h1⟩ : ∃ m ≥ N, d.val ∣ k + m := by
    refine ⟨k * (d - 1), le_mul_of_le_of_one_le hk (PNat.one_le _), ?_⟩
    rw [← PNat.add_coe, ← PNat.dvd_iff, ← mul_one_add, PNat.add_sub_of_lt hd]
    exact dvd_mul_left d k
  have hm0 : ¬d.val ∣ m := λ hm0 ↦ hk0 ((Nat.dvd_add_iff_left hm0).mpr h1)
  change (1 + 1) * f k = M
  rw [← hN hk hm hk0 hm0 h1, add_one_mul, one_mul, add_right_inj, ← PNat.coe_inj]
  exact Nat.dvd_antisymm (hd0 hk hm hk0 hm0 h1) (hd0 hm hk hm0 hk0 (by rwa [add_comm]))

/-- Characterization of bounded good functions. -/
theorem exists_smul_eventually_eq_one_or_one_two {f : GoodFun ℕ+} (h : ∃ N, ∀ n, f n ≤ N) :
    (∃ (C : ℕ+) (g : GoodFun ℕ+), f = C • g ∧ ∃ N, ∀ n ≥ N, g n = 1) ∨
    (∃ (C : ℕ+) (g : GoodFun ℕ+), f = C • g ∧ ∃ d : ℕ+, d > 1 ∧
      ∃ N, ∀ n ≥ N, g n = if d.val ∣ n then 2 else 1) := by
  obtain ⟨M, ⟨N, hN⟩, ⟨d, hd⟩⟩ := exists_limsup_and_dvd_map_iff h
  apply d.one_le.eq_or_lt.imp
  ---- Case 1: `d = 1`
  · rintro rfl; exact ⟨M, eq_set_cofinite_imp ⟨N, λ n hn ↦ (hN n hn).antisymm <|
      PNat.le_of_dvd <| PNat.dvd_iff.mpr <| (hd n).mpr n.1.one_dvd⟩⟩
  ---- Case 2: `d > 1`
  · intro hd0; obtain ⟨C, rfl, hC⟩ := eventually_bound_and_dvd_iff_period_imp hN hd0 hd
    have hC0 (n) : C ∣ f n := PNat.dvd_iff.mpr
      (dvd_set_cofinite_imp ⟨N, λ n hn ↦ PNat.dvd_iff.mp ⟨_, hC n hn⟩⟩ n)
    let hg : f = C • f.div hC0 := (f.smul_div hC0).symm
    refine ⟨C, f.div hC0, hg, d, hd0, N, λ n hn ↦ ?_⟩
    rw [← mul_left_cancel_iff, ← hC n hn]
    exact (GoodFun.ext_iff.mp hg n).symm

/-- Main characterization lemma. -/
theorem exists_smul_id_or_eventually_eq_one_or_one_two (f : GoodFun ℕ+) :
    (∃ C : ℕ+, f = C • GoodFun.id) ∨
    (∃ (C : ℕ+) (g : GoodFun ℕ+), f = C • g ∧ ∃ N, ∀ n ≥ N, g n = 1) ∨
    (∃ (C : ℕ+) (g : GoodFun ℕ+), f = C • g ∧ ∃ d : ℕ+, d > 1 ∧
      ∃ N, ∀ n ≥ N, g n = if d.val ∣ n then 2 else 1) :=
  (forall_or_exists_not λ N ↦ ∃ n, N < f n).imp eq_smul_id_of_unbounded
    λ h ↦ exists_smul_eventually_eq_one_or_one_two (by simpa using h)

end GoodFun





/-! ### Final solution -/

/-- Final solution -/
theorem final_solution (f : GoodFun ℕ+) : ∃ m, ∀ n, f m ∣ f n := by
  obtain ⟨C, rfl⟩ | ⟨C, g, rfl, N, hN⟩ | ⟨C, g, rfl, d, hd, N, hN⟩ :=
    f.exists_smul_id_or_eventually_eq_one_or_one_two
  ---- Case 1: `f(n) = f(1) n`
  · exact ⟨1, λ n ↦ ⟨n, congrArg (· * n) (mul_one C).symm⟩⟩
  ---- Case 2: `f` is eventually constant
  · exact ⟨N, λ n ↦ mul_dvd_mul_left C (hN N (le_refl N) ▸ one_dvd _)⟩
  ---- Case 3: `f` is eventually periodic with minimal period `d > 1`
  · obtain ⟨c, hc, hc0⟩ : ∃ c ≥ N, ¬d.val ∣ c := PNat_exists_big_not_dvd hd N
    refine ⟨c, λ n ↦ mul_dvd_mul_left C ?_⟩
    rw [hN c hc, if_neg hc0]
    exact one_dvd _

alias final_solution_extra := GoodFun.exists_smul_id_or_eventually_eq_one_or_one_two
