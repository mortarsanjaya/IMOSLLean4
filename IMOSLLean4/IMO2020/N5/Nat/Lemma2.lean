/-
Copyright (c) 2023 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import IMOSLLean4.IMO2020.N5.Nat.Basic
import Mathlib.Data.Nat.Prime

/-!
# IMO 2020 N5, ℕ-version (Lemma 2)

This file proves the following result, which is Lemma 2 in the LaTeX file.
* Let `f : MulMap M` and `p : ℕ` be an `f`-nice prime.
  Then `f(km % p) = f(k) f(m)` for any `0 < k, m < p`.
We also prove the variant `f(km % p) = f(k % p) f(m % p)` for `p ∤ k, m`.
It will be useful for the construction of the solutions.
-/

namespace IMOSL
namespace IMO2020N5
namespace Nat

/-! #### Extra lemmas -/

lemma mod_add_mod_eq_of_dvd_add_of_not_dvd {n a b : ℕ}
    (h : n ∣ a + b) (h0 : ¬n ∣ a) : a % n + b % n = n := by
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, ← Nat.dvd_iff_mod_eq_zero] at h
  rcases h with ⟨k, h⟩
  suffices k = 1 by rw [h, this, mul_one]
  have h1 := (Nat.add_pos_left (Nat.emod_pos_of_not_dvd h0) _).trans_eq h
  refine Nat.le_antisymm (Nat.le_of_lt_succ ?_)
    (Nat.pos_of_dvd_of_pos (k.dvd_mul_left n) h1)
  apply Nat.pos_of_dvd_of_pos (n.dvd_mul_right k) at h1
  replace h0 := Nat.add_lt_add (a.mod_lt h1) (b.mod_lt h1)
  rwa [h, ← mul_two, mul_lt_mul_left h1] at h0





/-! #### Main results -/

variable [CancelCommMonoid M] {f : MulMap M}
  (p_prime : Nat.Prime p) (h : nice f p)

theorem nice_map_pred : f (p - 1) = 1 :=
  f.map_one ▸ h _ _ p_prime.pred_pos Nat.one_pos (Nat.sub_add_cancel p_prime.pos)

theorem nice_mul_mod_of_lt
    {k m} (k_pos : 0 < k) (k_lt_p : k < p) (m_pos : 0 < m) (m_lt_p : m < p) :
    f (k * m % p) = f k * f m := by
  ---- Induction setup
  revert m; induction' k using Nat.strong_induction_on with k ih_k
  intro m m_pos m_lt_p; induction' m using Nat.strong_induction_on with m ih_m
  ---- The case `km < p` is easy to pick
  rcases lt_or_le (k * m) p with km_lt_p | p_le_km
  · rw [Nat.mod_eq_of_lt km_lt_p , f.map_mul k_pos m_pos]
  ---- Specialize `ih_m` for `m := r = p % m`
  let r := p % m
  have r_lt_m : r < m := p.mod_lt m_pos
  have not_m_dvd_p := (Nat.prime_def_lt'.mp p_prime).2 m
    (one_lt_of_lt_mul_right <| k_lt_p.trans_le p_le_km) m_lt_p
  have r_pos : 0 < r := Nat.emod_pos_of_not_dvd not_m_dvd_p
  have r_lt_p : r < p := r_lt_m.trans m_lt_p
  specialize ih_m r r_lt_m r_pos r_lt_p
  clear r_lt_m
  ---- Specialize `ih_k` for `m := q = p / m` and `m := k * m % p`
  have not_p_dvd_k := Nat.not_dvd_of_pos_of_lt k_pos k_lt_p
  have not_p_dvd_m := Nat.not_dvd_of_pos_of_lt m_pos m_lt_p
  have not_p_dvd_km := p_prime.not_dvd_mul not_p_dvd_k not_p_dvd_m
  rw [Ne.le_iff_lt (mt dvd_of_eq not_p_dvd_km),
    ← Nat.div_lt_iff_lt_mul m_pos] at p_le_km
  let q := p / m
  rename q < k => q_lt_k
  have q_pos : 0 < q := (Nat.div_pos_iff m_pos.ne.symm).mpr m_lt_p.le
  specialize ih_k q q_lt_k q_pos (q_lt_k.trans k_lt_p)
    (Nat.emod_pos_of_not_dvd not_p_dvd_km) (Nat.mod_lt _ p_prime.pos)
  clear k_pos k_lt_p m_lt_p q_lt_k not_p_dvd_km not_p_dvd_m
  ---- Reduce to equating `ih_k` and `ih_m`
  rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, mul_rotate'] at ih_k
  have X : m * q + r = p := Nat.div_add_mod p m
  rw [← h _ _ (mul_pos m_pos q_pos) r_pos X,
    f.map_mul m_pos q_pos, ← mul_rotate'] at ih_m
  rw [← mul_right_inj (f q), ← ih_k, ← ih_m]
  clear ih_m ih_k
  ---- Prove that `k * (m * q) % p + k * r % p = p`
  rw [← Nat.mul_div_lt_iff_not_dvd] at not_m_dvd_p
  rename m * q < p => mq_lt_p
  have not_p_dvd_kmq := p_prime.not_dvd_mul not_p_dvd_k
    (Nat.not_dvd_of_pos_of_lt (Nat.mul_pos m_pos q_pos) mq_lt_p)
  refine h _ _ (Nat.emod_pos_of_not_dvd not_p_dvd_kmq)
    (Nat.emod_pos_of_not_dvd <| p_prime.not_dvd_mul not_p_dvd_k <|
      Nat.not_dvd_of_pos_of_lt r_pos r_lt_p)
    (mod_add_mod_eq_of_dvd_add_of_not_dvd ⟨k, ?_⟩ not_p_dvd_kmq)
  rw [← mul_add, ← X, mul_comm]

theorem nice_mul_mod_of_not_dvd {k m} (hk : ¬p ∣ k) (hm : ¬p ∣ m) :
    f (k * m % p) = f (k % p) * f (m % p) :=
  (k.mul_mod m p).symm ▸ nice_mul_mod_of_lt p_prime h
    (Nat.emod_pos_of_not_dvd hk) (k.mod_lt p_prime.pos)
    (Nat.emod_pos_of_not_dvd hm) (m.mod_lt p_prime.pos)
