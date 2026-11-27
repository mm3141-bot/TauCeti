/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.SelbergSieve.PrimeInterval
public import Mathlib.Data.ZMod.Basic

import Mathlib.Data.Nat.GCD.BigOperators
import TauCeti.Data.Int.CardIntervalMod

/-!
# The prime-progression sieve

Sift the positive integers up to `x` in a residue class modulo `q` by the primes up to `z`
that do not divide `q`. For a divisor `d` of the sieving product, the Chinese remainder theorem
combines the residue class and divisibility by `d` into one class modulo `q * d`.
For `x ≥ 0` and `q > 0`, the count differs from `x / (q * d)` by less than one, uniformly in
the class and the modulus.

The construction follows D. R. Heath-Brown, *Lectures on sieves*,
[§3, second application](https://arxiv.org/pdf/math/0209360v1).
-/

public noncomputable section

open Finset

namespace BoundingSieve

/-- The unit-weight sieve of the positive integers at most `x` in the class `a` modulo `q`,
with sieving primes at most `z` coprime to `q`. The approximate mass is `x / q`. -/
def primeProgression (q : ℕ) (a : ZMod q) (x z : ℝ) : BoundingSieve where
  __ := primeInterval 0 (x / q) z
  support := (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = a)
  prodPrimes := ∏ p ∈ (Nat.primesLE ⌊z⌋₊).filter (fun p ↦ ¬p ∣ q), p
  prodPrimes_squarefree := (squarefree_primorial _).squarefree_of_dvd <| by
    rw [primorial_eq_prod_primesLE]
    exact prod_dvd_prod_of_subset _ _ _ (filter_subset _ _)
  nu_pos_of_prime := by
    intro p hp _
    rw [primeInterval_nu_apply]
    exact inv_pos.mpr (by exact_mod_cast hp.pos)
  nu_lt_one_of_prime := by
    intro p hp _
    rw [primeInterval_nu_apply]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)

/-- The progression sieve is supported on the positive integers in the prescribed class. -/
@[simp] theorem primeProgression_support (q : ℕ) (a : ZMod q) (x z : ℝ) :
    (primeProgression q a x z).support = (Ioc 0 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = a) :=
  (rfl)

/-- The sieving product contains the primes up to the cutoff that do not divide the modulus. -/
theorem primeProgression_prodPrimes (q : ℕ) (a : ZMod q) (x z : ℝ) :
    (primeProgression q a x z).prodPrimes =
      ∏ p ∈ (Nat.primesLE ⌊z⌋₊).filter (fun p ↦ ¬p ∣ q), p :=
  (rfl)

/-- The prime factors of the sieving product are precisely the active primes. -/
@[simp] theorem primeFactors_primeProgression_prodPrimes (q : ℕ) (a : ZMod q) (x z : ℝ) :
    (primeProgression q a x z).prodPrimes.primeFactors =
      (Nat.primesLE ⌊z⌋₊).filter (fun p ↦ ¬p ∣ q) := by
  rw [primeProgression_prodPrimes]
  exact Nat.primeFactors_prod fun _ hp ↦ Nat.prime_of_mem_primesLE (mem_filter.mp hp).1

/-- Every sample has unit weight. -/
@[simp] theorem primeProgression_weights (q : ℕ) (a : ZMod q) (x z : ℝ) :
    (primeProgression q a x z).weights = fun _ ↦ 1 :=
  primeInterval_weights 0 (x / q) z

/-- The approximate mass of the progression sieve is the cutoff divided by the modulus. -/
@[simp] theorem primeProgression_totalMass (q : ℕ) (a : ZMod q) (x z : ℝ) :
    (primeProgression q a x z).totalMass = x / q :=
  primeInterval_totalMass 0 (x / q) z

/-- The local density at index `d` is `1 / d`, including at all divisors of the sieving product. -/
@[simp] theorem primeProgression_nu_apply (q : ℕ) (a : ZMod q) (x z : ℝ) (d : ℕ) :
    (primeProgression q a x z).nu d = (d : ℝ)⁻¹ :=
  primeInterval_nu_apply 0 (x / q) z d

/-- The progression sieve only uses primes coprime to the modulus. -/
theorem coprime_primeProgression_prodPrimes (q : ℕ) (a : ZMod q) (x z : ℝ) :
    (primeProgression q a x z).prodPrimes.Coprime q := by
  rw [primeProgression_prodPrimes, Nat.coprime_prod_left_iff]
  intro p hp
  obtain ⟨hp, hpq⟩ := mem_filter.mp hp
  exact (Nat.prime_of_mem_primesLE hp).coprime_iff_not_dvd.mpr hpq

/-- The multiple sum of the progression sieve counts members of the class divisible by `d`. -/
theorem multSum_primeProgression (q : ℕ) (a : ZMod q) (x z : ℝ) (d : ℕ) :
    (primeProgression q a x z).multSum d =
      (#{n ∈ Ioc 0 ⌊x⌋₊ | ((n : ℕ) : ZMod q) = a ∧ d ∣ n} : ℝ) := by
  rw [multSum, primeProgression_weights, primeProgression_support, sum_boole, filter_filter]

/-- At each index `d` coprime to `q`, the progression sieve has remainder less than one
in absolute value. In particular, this applies to every divisor of the sieving product. -/
theorem abs_rem_primeProgression_lt_one {q : ℕ} [NeZero q] (a : ZMod q) {x : ℝ}
    (hx : 0 ≤ x) (z : ℝ) {d : ℕ} (hc : q.Coprime d) :
    |(primeProgression q a x z).rem d| < 1 := by
  obtain rfl | hd := eq_or_ne d 0
  · simp [rem, zero_dvd_iff]
  let v := Nat.chineseRemainder hc a.val 0
  have hclass (n : ℕ) : ((n : ZMod q) = a ∧ d ∣ n) ↔ n ≡ (v : ℕ) [MOD q * d] := by
    have ha : (n : ZMod q) = a ↔ n ≡ a.val [MOD q] := by
      simpa only [ZMod.natCast_zmod_val] using ZMod.natCast_eq_natCast_iff n a.val q
    rw [ha, ← Nat.modEq_zero_iff_dvd, ← Nat.modEq_and_modEq_iff_modEq_mul hc]
    exact and_congr ⟨fun h ↦ h.trans v.prop.1.symm, fun h ↦ h.trans v.prop.1⟩
      ⟨fun h ↦ h.trans v.prop.2.symm, fun h ↦ h.trans v.prop.2⟩
  rw [rem, multSum_primeProgression, primeProgression_nu_apply, primeProgression_totalMass]
  simp_rw [hclass]
  rw [← card_map (Nat.castEmbedding : ℕ ↪ ℤ), Nat.Ioc_filter_modEq_cast]
  simp only [Nat.cast_zero, Int.natCast_floor_eq_floor hx, inv_mul_eq_div, div_div, ← Nat.cast_mul]
  have hr : 0 < ((q * d : ℕ) : ℤ) :=
    Int.natCast_pos.mpr (Nat.mul_pos (NeZero.pos q) (Nat.pos_of_ne_zero hd))
  simpa only [Int.floor_zero, sub_zero, Int.cast_natCast] using
    Int.abs_card_Ioc_floor_filter_modEq_sub_lt_one hr hx (v : ℕ)

/-- The sifted progression sum counts the members coprime to the sieving product. -/
theorem siftedSum_primeProgression (q : ℕ) (a : ZMod q) (x z : ℝ) :
    (primeProgression q a x z).siftedSum =
      (#{n ∈ (primeProgression q a x z).support | (primeProgression q a x z).prodPrimes.Coprime n}
        : ℝ) := by
  simp only [siftedSum, primeProgression_weights, sum_boole]

end BoundingSieve
