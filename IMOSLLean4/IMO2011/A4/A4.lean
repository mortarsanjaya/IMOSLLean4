import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Pnat.Basic

/-! # IMO 2011 A4 -/

namespace IMOSL
namespace IMO2011A4

open Function

/-! ## `ℕ` version -/

lemma main_step {f g : ℕ → ℕ} (h : ∀ k, f^[g k + 2] k < f (k + 1)) : f = id := by
  ---- Start with `f(n) ≥ n` for all `n : ℕ`
  have h0 : ∀ n, n ≤ f n := by
    suffices ∀ k n : ℕ, k ≤ n → k ≤ f n from λ n ↦ this n n n.le_refl
    refine Nat.rec (λ k _ ↦ (f k).zero_le) (λ k h0 n h1 ↦ ?_)
    rcases n with _ | n
    · exact absurd k.succ_pos h1.not_lt
    · refine (h n).trans_le' ?_
      generalize g n + 2 = t
      exact t.rec (Nat.succ_le_succ_iff.mp h1)
        (λ t h2 ↦ (h0 _ h2).trans_eq (f.iterate_succ_apply' _ _).symm)
  ---- Do the remaining work
  have h1 : ∀ t n, n ≤ f^[t] n :=
    Nat.rec Nat.le_refl (λ t h1 n ↦ (h0 n).trans (h1 _))
  have h2 : StrictMono f :=
    strictMono_nat_of_lt_succ (λ n ↦ (h1 _ (f n)).trans_lt (h n))
  refine funext <| λ n ↦ (h0 n).antisymm' <| ?_
  rw [← Nat.lt_succ_iff, ← h2.lt_iff_lt]
  exact (h1 _ _).trans_lt (h n)

/-- Final solution -/
theorem final_solution {f g : ℕ → ℕ} :
    (∀ k, f^[g k + 2] k + (g^[f k + 1] k + g (k + 1)) + 1 = f (k + 1))
      ↔ f = id ∧ g = λ _ ↦ 0 := by
  refine Iff.symm ⟨λ h k ↦ ?_, λ h ↦ ?_⟩
  ---- `←`
  · rcases h with ⟨rfl, rfl⟩
    rw [iterate_id, iterate_succ_apply']; rfl
  ---- `→`
  · obtain rfl : f = id := by
      refine main_step (g := g) (λ k ↦ ?_)
      rw [← h, Nat.lt_succ_iff]
      exact Nat.le_add_right _ _
    refine ⟨rfl, funext (λ n ↦ ?_)⟩
    simp_rw [iterate_id, id_def, Nat.succ_inj',
      add_right_eq_self, add_eq_zero_iff] at h
    rcases n with _ | n
    exacts [(h 0).1, (h n).2]





/-! ## `ℕ+` (original) version -/

theorem PNat_to_Nat_prop {P : ℕ+ → Prop} : (∀ n, P n) ↔ ∀ n : ℕ, P n.succPNat :=
  ⟨λ h n ↦ h n.succPNat, λ h n ↦ n.succPNat_natPred ▸ h _⟩

theorem PNat_exists_Nat_conj (f : ℕ+ → ℕ+) :
    ∃ g : ℕ → ℕ, f = λ n ↦ (g n.natPred).succPNat :=
  ⟨λ n ↦ (f n.succPNat).natPred,
  funext (λ n ↦ by simp_rw [PNat.succPNat_natPred])⟩

theorem PNat_eq_Nat_conj_iff {f : ℕ+ → ℕ+} {g : ℕ → ℕ} :
    (f = λ n ↦ (g n.natPred).succPNat) ↔ g = λ n ↦ (f n.succPNat).natPred :=
  ⟨λ h ↦ funext (λ n ↦ h.symm ▸ rfl),
  λ h ↦ funext (λ n ↦ by rw [h, PNat.succPNat_natPred, PNat.succPNat_natPred])⟩

theorem PNat_Nat_conj_iterate (f : ℕ → ℕ) (m : ℕ+) :
    ∀ k, (λ n ↦ (f n.natPred).succPNat)^[k] m = (f^[k] m.natPred).succPNat
  | 0 => m.succPNat_natPred.symm
  | k + 1 => by rw [iterate_succ_apply', iterate_succ_apply',
                  PNat_Nat_conj_iterate f m k]; rfl

/-- Final solution, `ℕ+` version -/
theorem final_solution_PNat {f g : ℕ+ → ℕ+} :
    (∀ n, f^[g n + 1] n + (g^[f n] n + g (n + 1)) = f (n + 1) + 1)
      ↔ f = id ∧ g = λ _ ↦ 1 := by
  obtain ⟨f, rfl⟩ := PNat_exists_Nat_conj f
  obtain ⟨g, rfl⟩ := PNat_exists_Nat_conj g
  rw [eq_comm, PNat_eq_Nat_conj_iff, eq_comm (b := λ _ ↦ 1),
    PNat_eq_Nat_conj_iff, PNat_to_Nat_prop, Iff.comm]
  refine final_solution.symm.trans <| forall_congr' (λ n ↦ ?_)
  rw [← PNat.coe_inj, PNat_Nat_conj_iterate, PNat_Nat_conj_iterate]
  simp_rw [Nat.natPred_succPNat, PNat.add_coe, Nat.succPNat_coe, Nat.succ_add]
  rw [← add_left_inj 2]; rfl
