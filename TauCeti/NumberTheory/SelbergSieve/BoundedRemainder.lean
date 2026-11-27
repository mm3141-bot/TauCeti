/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import TauCeti.NumberTheory.SelbergSieve.UpperBound

import TauCeti.NumberTheory.ArithmeticFunction.DivisorBounds

/-!
# Selberg's upper bound with unit remainders

When the divisor counts used by Selberg's sieve each have error of absolute value at most one,
the ordered-divisor majorant gives an explicit upper bound for their total contribution.
This applies to sieving intervals and arithmetic progressions.
-/

public section

open Finset
open scoped ArithmeticFunction.omega

namespace BoundingSieve

/-- The Selberg upper bound when each divisor remainder below `z²` has absolute value at most
one. The error term is the explicit majorant for the sum of `3 ^ ω(d)` up to `z²`. -/
theorem siftedSum_le_totalMass_div_diagonalMass_add_of_abs_rem_le_one
    (s : BoundingSieve) {z : ℝ} (hz : 1 < z)
    (hrem : ∀ d, d ∣ s.prodPrimes → (d : ℝ) < z ^ 2 → |s.rem d| ≤ 1) :
    s.siftedSum ≤ s.totalMass / s.diagonalMass z + z ^ 2 * (1 + 2 * Real.log z) ^ 2 := by
  refine (s.siftedSum_le_totalMass_div_diagonalMass_add_sum_three_pow hz).trans ?_
  apply add_le_add_right
  calc
    _ ≤ ∑ d ∈ s.prodPrimes.divisors.filter (fun d : ℕ ↦ (d : ℝ) < z ^ 2), (3 : ℝ) ^ ω d := by
      refine sum_le_sum fun d hd ↦ ?_
      obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
      exact mul_le_of_le_one_right (by positivity) (hrem d (Nat.dvd_of_mem_divisors hdP) hdz)
    _ ≤ ∑ n ∈ Ioc 0 ⌊z ^ 2⌋₊, (3 : ℝ) ^ ω n := by
      refine sum_le_sum_of_subset_of_nonneg (fun d hd ↦ ?_) fun _ _ _ ↦ by positivity
      obtain ⟨hdP, hdz⟩ := mem_filter.mp hd
      exact mem_Ioc.mpr ⟨Nat.pos_of_mem_divisors hdP, Nat.le_floor hdz.le⟩
    _ ≤ z ^ 2 * (1 + Real.log (z ^ 2)) ^ 2 :=
      ArithmeticFunction.sum_Ioc_three_pow_cardDistinctFactors_le_mul_one_add_log_sq
        (one_le_pow₀ hz.le)
    _ = _ := by rw [Real.log_pow, Nat.cast_ofNat]

end BoundingSieve
