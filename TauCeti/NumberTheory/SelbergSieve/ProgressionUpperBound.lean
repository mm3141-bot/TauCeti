/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebyshev.ResidueClass
public import TauCeti.NumberTheory.SelbergSieve.ArithmeticProgression

import TauCeti.NumberTheory.PrimeCounting
import TauCeti.NumberTheory.SelbergSieve.BoundedRemainder
import TauCeti.NumberTheory.SelbergSieve.CoprimeDiagonal

/-!
# The Selberg upper bound for primes in a progression

Omitting the primes of the modulus from Selberg's sieve gives a diagonal mass at least
`(φ(q) / q) * log z`. The Chinese remainder theorem gives a unit bound for the remainder at
every sieving divisor, uniformly in the modulus and the residue class. Choosing
`z = exp (log (x / q) / 4)` yields a Brun–Titchmarsh bound with an absolute constant.

## References

* D. R. Heath-Brown, *Lectures on sieves*, [§3, (3.5)–(3.6)](https://arxiv.org/pdf/math/0209360v1).
-/

public section

open Finset Real
open scoped Nat

namespace Chebyshev

/-- The progression sieve retains every prime in the class above the sieving cutoff. -/
theorem primeCountAP_le_siftedSum_primeProgression_add (q : ℕ) (a : ZMod q) (x z : ℝ) :
    (primeCountAP q a x : ℝ) ≤
      (BoundingSieve.primeProgression q a x z).siftedSum + Nat.primeCounting ⌊z⌋₊ := by
  rw [primeCountAP_def, BoundingSieve.siftedSum_primeProgression,
    ← Nat.primesLE_card_eq_primeCounting]
  let s := BoundingSieve.primeProgression q a x z
  have hP : s.prodPrimes ∣ primorial ⌊z⌋₊ := by
    rw [BoundingSieve.primeProgression_prodPrimes, primorial_eq_prod_primesLE]
    exact prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)
  have hsub : (Nat.primesLE ⌊x⌋₊).filter (fun p : ℕ ↦ (p : ZMod q) = a) ⊆
      s.support.filter s.prodPrimes.Coprime ∪ Nat.primesLE ⌊z⌋₊ := by
    intro p hp
    obtain ⟨hp, ha⟩ := mem_filter.mp hp
    obtain ⟨hpx, hp⟩ := Nat.mem_primesLE.mp hp
    have hpI : p ∈ Ioc 0 ⌊x⌋₊ := mem_Ioc.mpr ⟨hp.pos, hpx⟩
    have hp' : p ∈ (Ioc ⌊(0 : ℝ)⌋₊ ⌊0 + x⌋₊).filter Nat.Prime := by
      simpa only [Nat.floor_zero, zero_add, mem_filter] using And.intro hpI hp
    rcases mem_union.mp (BoundingSieve.filter_prime_subset_primeInterval_union 0 x z hp') with
      hkeep | hsmall
    · have hs : p ∈ s.support := by
        rw [BoundingSieve.primeProgression_support]
        exact mem_filter.mpr ⟨hpI, ha⟩
      exact mem_union_left _ (mem_filter.mpr ⟨hs, (mem_filter.mp hkeep).2.coprime_dvd_left hP⟩)
    · exact mem_union_right _ hsmall
  exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)

/-- Selberg's upper bound for the prime count in a residue class at any sifting level `z > 1`.
The totient in the main term accounts for the primes of the modulus. -/
theorem primeCountAP_le_div_totient_mul_log_add {q : ℕ} [NeZero q] (a : ZMod q)
    {x z : ℝ} (hx : 0 ≤ x) (hz : 1 < z) :
    (primeCountAP q a x : ℝ) ≤
      x / ((φ q : ℝ) * log z) + z ^ 2 * (1 + 2 * log z) ^ 2 + z := by
  let s := BoundingSieve.primeProgression q a x z
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hφ : 0 < (φ q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  have hlog := log_pos hz
  have hG : (φ q : ℝ) / q * log z ≤ s.diagonalMass z := by
    refine s.totient_div_mul_log_le_diagonalMass q (by linarith) (fun p hp hpz hpq ↦ ?_)
      (fun p _ _ _ ↦ (BoundingSieve.primeProgression_nu_apply q a x z p).ge)
    apply Nat.dvd_of_mem_primeFactors
    simp only [s, BoundingSieve.primeFactors_primeProgression_prodPrimes, mem_filter,
      Nat.mem_primesLE]
    exact ⟨⟨Nat.le_floor hpz.le, hp⟩, hpq⟩
  have hrem (d : ℕ) (hd : d ∣ s.prodPrimes) : |s.rem d| ≤ 1 :=
    (BoundingSieve.abs_rem_primeProgression_lt_one a hx z
      ((BoundingSieve.coprime_primeProgression_prodPrimes q a x z).coprime_dvd_left hd).symm).le
  have hmain : s.totalMass / s.diagonalMass z ≤ x / ((φ q : ℝ) * log z) := by
    rw [BoundingSieve.primeProgression_totalMass]
    calc
      _ ≤ (x / q) / ((φ q : ℝ) / q * log z) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hG
      _ = _ := by field_simp
  have hsmall : (Nat.primeCounting ⌊z⌋₊ : ℝ) ≤ z :=
    (by exact_mod_cast Nat.primeCounting_le_self ⌊z⌋₊ : (Nat.primeCounting ⌊z⌋₊ : ℝ) ≤ ⌊z⌋₊).trans
      (Nat.floor_le (by linarith))
  calc
    _ ≤ s.siftedSum + Nat.primeCounting ⌊z⌋₊ :=
      primeCountAP_le_siftedSum_primeProgression_add q a x z
    _ ≤ _ := add_le_add ((s.siftedSum_le_totalMass_div_diagonalMass_add_of_abs_rem_le_one hz
      (fun d hd _ ↦ hrem d hd)).trans (add_le_add_left hmain _)) hsmall

/-- A uniform Brun–Titchmarsh upper bound for every residue class modulo `q > 0` and `x > q`.
The explicit constant `28` follows from the sifting level `exp (log (x / q) / 4)`. -/
theorem primeCountAP_le_mul_div_totient_mul_log {q : ℕ} [NeZero q] (a : ZMod q) {x : ℝ}
    (hx : (q : ℝ) < x) :
    (primeCountAP q a x : ℝ) ≤ 28 * x / ((φ q : ℝ) * log (x / q)) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hφ : 0 < (φ q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  let u := log (x / q) / 4
  have hu : 0 < u := div_pos (log_pos ((one_lt_div hq).mpr hx)) (by norm_num)
  have hlog : 4 * u = log (x / q) := by dsimp [u]; ring
  have hxpos : 0 < x := hq.trans hx
  have hexp : exp (4 * u) = x / q := by rw [hlog, exp_log (div_pos hxpos hq)]
  have hφq : (φ q : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  -- The first three positive-degree terms of the exponential bound the error polynomial.
  have hpoly : 4 * u * ((1 + 2 * u) ^ 2 + 1) ≤ 24 * exp (2 * u) := by
    have h₁ := pow_div_factorial_le_exp (2 * u) (by positivity) 1
    have h₂ := pow_div_factorial_le_exp (2 * u) (by positivity) 2
    have h₃ := pow_div_factorial_le_exp (2 * u) (by positivity) 3
    norm_num at h₁ h₂ h₃
    nlinarith only [h₁, h₂, h₃]
  have hzsq : exp u ^ 2 = exp (2 * u) := by rw [← exp_natCast_mul, Nat.cast_ofNat]
  have hrem : exp u ^ 2 * (1 + 2 * u) ^ 2 + exp u ≤
      24 * (x / ((φ q : ℝ) * (4 * u))) := calc
    _ ≤ exp u ^ 2 * ((1 + 2 * u) ^ 2 + 1) := by
      rw [mul_add, mul_one]
      gcongr
      exact le_self_pow₀ (one_le_exp hu.le) (by decide)
    _ ≤ exp u ^ 2 * (24 * exp (2 * u) / (4 * u)) := by
      gcongr
      rwa [le_div_iff₀ (by positivity), mul_comm]
    _ = 24 * (exp (4 * u) / (4 * u)) := by
      rw [hzsq, ← mul_div_assoc, mul_left_comm, ← exp_add]
      ring_nf
    _ = 24 * (x / ((q : ℝ) * (4 * u))) := by rw [hexp, div_div]
    _ ≤ _ := by gcongr
  have hmain : x / ((φ q : ℝ) * u) = 4 * (x / ((φ q : ℝ) * (4 * u))) := by
    field_simp
  have hbound := primeCountAP_le_div_totient_mul_log_add a (hq.trans hx).le
    (one_lt_exp_iff.mpr hu)
  rw [log_exp, hmain, add_assoc] at hbound
  rw [← hlog, mul_div_assoc]
  linarith only [hbound, hrem]

end Chebyshev
