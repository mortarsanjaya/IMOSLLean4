/-
Copyright (c) 2026 Gian Cordana Sanjaya. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gian Cordana Sanjaya
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.PNat.Find

/-!
# IMO 2007 N5

Find all surjective functions $f : ℕ⁺ → ℕ⁺$ such that for any prime $p$ and $m, n ∈ ℕ⁺$,
  we have $p ∣ f(m + n)$ if and only if $p ∣ f(m) + f(n)$.

### Answer

$f(n) = n$.

### Solution

We partially follow the
  [official solution](https://www.imo-official.org/problems/IMO2007SL.pdf).
In particular, some of the steps we use do not assume that $f$ is surjective.
The main lemma can be weakened as follows: if $p ∣ f(m)$ for some $m$, then $p ∣ f(n)$
  if and only if $d ∣ n$, where $d$ is the minimal positive integer with $p ∣ f(d)$.
Furthermore, we have $f(m) ≡ f(n) \pmod{p}$ if and only if $m ≡ n \pmod{d}$.
Unlike the official solution, we do not prove that $d = p$.

Assuming only that infinitely many primes divide $f(n)$ for some $n$,
  we then prove that $f$ is injective.
Indeed, if $f(n + k) = f(n)$ for some $k > 0$, then for some large $p$ and suitable $d$,
$$ f(n + k) ≡ f(n) \pmod{p} \iff d ∣ k \iff p ∣ f(k). $$
This is false if we choose $p > f(k)$.

Surjectivity would imply that every prime $p$ divides some value $f(d)$,
  and the minimal such $d$ is greater than $1$ since otherwise $p ∣ f(n)$ for all $n$.
In particular, we get $f(1) = 1$ and $|f(n + 1) - f(n)| = 1$ for all $n$.
By induction using injectivity of $n$, we then get $f(n) = n$ for all $n$.

### Notes

If $f(ℕ⁺)$ is unbounded, then Kobayashi's theorem does imply that infinitely many
  primes divide an element of $f(ℕ⁺) + f(ℕ⁺)$, which implies that infinitely many
  primes divide an element of $f(ℕ⁺)$ by the condition of the function.
I conjecture that in this case, $f$ has to be linear.
But I still have no idea about how to prove it.
-/

namespace IMOSL
namespace IMO2007N5

/-! ### Extra lemmas -/

/-- A positive integer is equal to `1` if and only if no primes divide it. -/
theorem eq_one_iff_forall_NatPrimes_not_dvd {k : ℕ+} :
    k = 1 ↔ ∀ p : Nat.Primes, ¬(p : ℕ) ∣ k := by
  rw [← PNat.coe_eq_one_iff, Nat.eq_one_iff_not_exists_prime_dvd]
  exact Iff.symm Subtype.forall

/-- If `n ∣ b + c`, then `a ≡ b (mod n)` if and only if `n ∣ a + c`. -/
theorem modeq_iff_dvd_add_of_dvd_add (h : n ∣ b + c) :
    a ≡ b [MOD n] ↔ n ∣ a + c :=
  calc a ≡ b [MOD n]
  _ ↔ a + c ≡ b + c [MOD n] := (Nat.ModEq.add_iff_right rfl).symm
  _ ↔ n ∣ a + c := by rw [Nat.ModEq, Nat.mod_eq_zero_of_dvd h, Nat.dvd_iff_mod_eq_zero]





/-! ### Start of the problem -/

/-- A function `f : ℕ+ → ℕ+` is called *good* if for any prime `p` and `m, n ∈ ℕ+`,
  we have `p ∣ f(m + n)` if and only if `p ∣ f(m) + f(n)`. -/
def good (f : ℕ+ → ℕ+) :=
  ∀ p : Nat.Primes, ∀ m n : ℕ+, (p : ℕ) ∣ f (m + n) ↔ (p : ℕ) ∣ f m + f n

/-- The identity function is good. -/
theorem id_is_good : good id :=
  λ _ _ _ ↦ Iff.rfl


namespace good

variable (hf : good f)
include hf

/-- Suppose that `f` is good and `p ∣ f(m)` for some `m ∈ ℕ+`.
  Letting `d` be the minimal such `m`, we have `p ∣ f(n)` if and only id `d ∣ n`. -/
theorem prime_dvd_map_iff_find_min_dvd (p : Nat.Primes) (hpf : ∃ n, (p : ℕ) ∣ f n) :
    (p : ℕ) ∣ f n ↔ (PNat.find hpf : ℕ) ∣ n := by
  set d : ℕ+ := PNat.find hpf
  ---- Strong induction on `n`.
  induction n using PNat.strongInductionOn with | _ n n_ih => ?_
  ---- Split into three cases: `n < d`, `n = d`, and `n > d`.
  have hd : (p : ℕ) ∣ f d := PNat.find_spec hpf
  obtain hn | rfl | hn : n < d ∨ n = d ∨ d < n := lt_trichotomy _ _
  ---- The case `n < d` is trivial.
  · exact iff_of_false (PNat.find_min hpf hn)
      (λ h ↦ hn.not_ge (PNat.le_of_dvd (PNat.dvd_iff.mpr h)))
  ---- The case `n = d` is also trivial.
  · exact iff_of_true hd (dvd_refl _)
  ---- For the case `n > d`, we have `p ∣ f(n) ↔ p ∣ f(n - d) ↔ d ∣ n - d ↔ d ∣ n`.
  · replace hn : d + (n - d) = n := PNat.add_sub_of_lt hn
    rw [← hn, hf, Nat.dvd_add_right hd, PNat.add_coe, Nat.dvd_add_self_left]
    exact n_ih _ ((PNat.lt_add_left _ _).trans_eq hn)

/-- Assume `f` is good and some `d` satisfies `p ∣ f(n) ↔ d ∣ n`.
  Then for any `m, n ∈ ℕ+`, we have `f(m) ≡ f(n) (mod p) ↔ m ≡ n (mod d)`. -/
theorem map_modeq_prime_iff_modeq
    (p : Nat.Primes) {d : ℕ+} (hpd : ∀ n, (p : ℕ) ∣ f n ↔ (d : ℕ) ∣ n) {m n} :
    f m ≡ f n [MOD p] ↔ m ≡ n [MOD d] := by
  ---- Find a positive integer `k` such that `d ∣ n + k`.
  obtain ⟨k, hk⟩ : ∃ k : ℕ+, (d : ℕ) ∣ n + k := by
    have h : (n : ℕ) % d < d := Nat.mod_lt n d.pos
    refine ⟨⟨d - n % d, Nat.sub_pos_of_lt h⟩, ?_⟩
    rw [PNat.mk_coe, ← Nat.add_sub_assoc h.le, Nat.add_comm,
      Nat.add_sub_assoc (Nat.mod_le _ _), Nat.dvd_add_self_left]
    exact Nat.dvd_sub_mod _
  ---- In particular, `p ∣ f(n) + f(k)` as well.
  have hk0 : (p : ℕ) ∣ f n + f k := by rwa [← PNat.add_coe, ← hpd, hf] at hk
  ---- Then `f(m) ≡ f(n) (mod p) ↔ p ∣ f(m) + f(k) ↔ d ∣ m + k ↔ m ≡ n (mod d)`.
  calc f m ≡ f n [MOD p]
  _ ↔ (p : ℕ) ∣ f m + f k := modeq_iff_dvd_add_of_dvd_add hk0
  _ ↔ (p : ℕ) ∣ f (m + k) := (hf p m k).symm
  _ ↔ (d : ℕ) ∣ m + k := hpd _
  _ ↔ m ≡ n [MOD d] := (modeq_iff_dvd_add_of_dvd_add hk).symm

/-- Assume `f` is good and `p ∣ f(d)` for some `d ∈ ℕ+` minimal.
  Then for any `m, n ∈ ℕ+`, we have `f(m) ≡ f(n) (mod p) ↔ m ≡ n (mod d)`. -/
theorem map_modeq_prime_iff_modeq_find (p : Nat.Primes) (hpf : ∃ n, (p : ℕ) ∣ f n) {m n} :
    f m ≡ f n [MOD p] ↔ m ≡ n [MOD (PNat.find hpf)] :=
  hf.map_modeq_prime_iff_modeq p λ _ ↦ hf.prime_dvd_map_iff_find_min_dvd p _

/-- If `f` is good and infinitely many primes divide some `f(n)`, then `f` is injective. -/
theorem injective_of_infinite_prime_dvd
    (hf0 : ∀ N : ℕ, ∃ p : Nat.Primes, N ≤ p ∧ ∃ n, (p : ℕ) ∣ f n) : f.Injective := by
  ---- Indeed, suppose that `f(m) = f(n)` for some `m ≠ n`; WLOG assume `m > n`.
  intro m n h
  wlog h0 : n < m generalizing h m n
  · exact (eq_or_lt_of_not_gt h0).elim id λ h1 ↦ (this h.symm h1).symm
  ---- Write `m = n + k` for some `k > 0`.
  obtain ⟨k, rfl⟩ : ∃ k, n + k = m := ⟨m - n, PNat.add_sub_of_lt h0⟩
  ---- Pick a prime `p > f(k)` such that `p ∣ f(n)` for some `n`.
  obtain ⟨p, hpk, hp⟩ : ∃ p : Nat.Primes, (f k : ℕ) < p ∧ ∃ n, (p : ℕ) ∣ f n := hf0 _
  /- Let `d` be the minimal positive integer such that `p ∣ f(d)`.
    Then `f(n + k) = f(n)` implies `d ∣ k ↔ p ∣ f(k)`; contradiction. -/
  let d : ℕ+ := PNat.find hp
  replace h0 (n) : (p : ℕ) ∣ f n ↔ (d : ℕ) ∣ n :=
    hf.prime_dvd_map_iff_find_min_dvd p hp
  replace h : n + k ≡ n [MOD d] :=
    (hf.map_modeq_prime_iff_modeq p h0).mp (congrArg (λ (n : ℕ+) ↦ (n : ℕ) % p) h)
  rw [Nat.ModEq.comm, Nat.left_modEq_add_iff, ← h0] at h
  exact absurd (Nat.le_of_dvd (f k).pos h) hpk.not_ge

/-- If `f` is good and surjective, then `f` is the identity map. -/
theorem eq_id_of_surjective (hf0 : f.Surjective) : f = id := by
  ---- Since `f` is surjective, every prime divides some `f(n)`.
  have hf1 (p : Nat.Primes) : ∃ n, (p : ℕ) ∣ f n := by
    obtain ⟨n, hn⟩ : ∃ n, f n = ⟨p.val, p.2.pos⟩ := hf0 _
    exact ⟨n, dvd_of_eq (congrArg PNat.val hn.symm)⟩
  ---- From the previous observation, `f` is injective.
  have hf2 : f.Injective :=
    hf.injective_of_infinite_prime_dvd λ N ↦
      (Nat.exists_infinite_primes N).elim λ p ⟨hpN, hp⟩ ↦ ⟨⟨p, hp⟩, hpN, hf1 _⟩
  ---- For each `p`, the smallest `d` for which `p ∣ f(d)` is greater than `1`.
  have hf3 (p : Nat.Primes) : PNat.find (hf1 p) > 1 := by
    -- Suppose that `d = 1`, and choose `x` such that `f(x) = 1`.
    refine (PNat.one_le _).lt_of_ne' λ h ↦ ?_
    obtain ⟨x, hx⟩ : ∃ x, f x = 1 := hf0 1
    -- Then `d ∣ x ↔ p ∣ f(x) = 1`; contradiction.
    have h0 : (PNat.find (hf1 p) : ℕ) ∣ x := h ▸ Nat.one_dvd _
    rw [← hf.prime_dvd_map_iff_find_min_dvd, hx] at h0
    exact p.2.not_dvd_one h0
  ---- Now we are ready to prove `f(n) = n` for all `n` by strong induction on `n`.
  funext n; change f n = n
  induction n using PNat.caseStrongInductionOn with
  | hz =>
      -- Indeed, no primes `p` divide `f(1)` since the `d` corresponding to `p` is `> 1`.
      refine eq_one_iff_forall_NatPrimes_not_dvd.mpr λ p ↦ ?_
      rw [hf.prime_dvd_map_iff_find_min_dvd p (hf1 p), ← PNat.dvd_iff, PNat.dvd_one_iff]
      exact (hf3 p).ne.symm
  | hi n n_ih =>
      -- If `f(n + 1) ≤ n` then `f(f(n + 1)) = f(n + 1)` by IH; apply injectivity.
      obtain hn | hn : f (n + 1) ≤ n ∨ n < f (n + 1) := le_or_gt _ _
      · exact hf2 (n_ih _ hn)
      -- Now suppose `f(n + 1) > n` and write `f(n + 1) = n + k = f(n) + k` for some `k`.
      obtain ⟨k, hk⟩ : ∃ k, n + k = f (n + 1) := ⟨f (n + 1) - n, PNat.add_sub_of_lt hn⟩
      -- Clearly it suffices to show that `k = 1`.
      suffices k = 1 by rw [← hk, this]
      -- This follows since `¬n + 1 ≡ n (mod d)` for every `d > 1`.
      refine eq_one_iff_forall_NatPrimes_not_dvd.mpr λ p ↦ ?_
      have h : ¬((n + 1 : ℕ+) : ℕ) ≡ n [MOD (PNat.find (hf1 p))] := by
        rw [PNat.add_coe, Nat.add_modEq_left_iff, ← PNat.dvd_iff, PNat.dvd_one_iff]
        exact (hf3 p).ne.symm
      rwa [← hf.map_modeq_prime_iff_modeq_find, ← hk, PNat.add_coe,
        n_ih n (le_refl n), Nat.add_modEq_left_iff] at h

end good


/-- Final solution -/
theorem final_solution {f} : (good f ∧ f.Surjective) ↔ f = id :=
  ⟨λ ⟨hf, hf0⟩ ↦ hf.eq_id_of_surjective hf0,
  λ hf ↦ hf ▸ ⟨id_is_good, Function.surjective_id⟩⟩
