/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.CardIntervalMod

/-!
# Counting integers of an interval with given residue

Mathlib's `Int.Ico_filter_modEq_card` counts the integers of `[a, b)` congruent to `v` modulo
`r > 0` exactly, as a difference of two ceilings. For estimates, the useful consequence is the
uniform bound `(b - a) / r + 1`, independent of the residue `v`: a box of side `L` in `ℤ^n`
contains at most `(L / r + 1) ^ n` points of any one residue class modulo `r`.

For an interval `(a, b]` with `a ≤ b` in an ordered field with floors, the count differs from
`(b - a) / r` by strictly less than one, uniformly in both endpoints and the residue class.
-/

public section

open Finset

namespace Int

/-- An interval `[a, b)` of integers with `a ≤ b` contains at most `(b - a) / r + 1` integers
congruent to `v` modulo `r > 0`, whatever the residue `v`. -/
theorem card_Ico_filter_modEq_le {r : ℤ} (hr : 0 < r) {a b : ℤ} (hab : a ≤ b) (v : ℤ) :
    (#{x ∈ Ico a b | x ≡ v [ZMOD r]} : ℚ) ≤ (b - a) / r + 1 := by
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  have hcard : ((#{x ∈ Ico a b | x ≡ v [ZMOD r]} : ℤ) : ℚ) =
      ((max (⌈(b - v) / (r : ℚ)⌉ - ⌈(a - v) / (r : ℚ)⌉) 0 : ℤ) : ℚ) := by
    rw [Ico_filter_modEq_card _ _ hr]
  rw [Int.cast_natCast] at hcard
  rw [hcard, Int.cast_max, Int.cast_zero, max_le_iff]
  have hba : (0 : ℚ) ≤ (b - a) / r := div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hr'.le
  refine ⟨?_, by linarith⟩
  have h₁ := Int.ceil_lt_add_one ((b - v) / (r : ℚ))
  have h₂ := Int.le_ceil ((a - v) / (r : ℚ))
  have hsplit : ((b : ℚ) - a) / r = (b - v) / r - (a - v) / r := by ring
  push_cast
  linarith

/-- The count of integers in `(a, b]` in any residue class modulo `r > 0` differs from
the interval length divided by `r` by strictly less than one. -/
theorem abs_card_Ioc_floor_filter_modEq_sub_lt_one {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorRing K] {r : ℤ} (hr : 0 < r) {a b : K} (hab : a ≤ b) (v : ℤ) :
    |(#{x ∈ Ioc ⌊a⌋ ⌊b⌋ | x ≡ v [ZMOD r]} : K) - (b - a) / r| < 1 := by
  have hfloor (x : K) : ⌊(⌊x⌋ - v : ℚ) / r⌋ = ⌊(x - v) / r⌋ := by
    rw [Int.floor_div_cast_of_nonneg hr.le, Int.floor_sub_intCast, Int.floor_intCast,
      Int.floor_div_cast_of_nonneg hr.le, Int.floor_sub_intCast]
  have hr' : 0 < (r : K) := Int.cast_pos.mpr hr
  have hmono : (a - v) / (r : K) ≤ (b - v) / r :=
    div_le_div_of_nonneg_right (sub_le_sub_right hab _) hr'.le
  have hcard : ((#{x ∈ Ioc ⌊a⌋ ⌊b⌋ | x ≡ v [ZMOD r]} : ℕ) : ℤ) =
      ⌊(b - v) / (r : K)⌋ - ⌊(a - v) / (r : K)⌋ := by
    rw [Int.Ioc_filter_modEq_card _ _ hr, hfloor, hfloor,
      max_eq_left (sub_nonneg.mpr (Int.floor_mono hmono))]
  rw [← Int.cast_natCast, hcard, Int.cast_sub, abs_lt]
  have hlength : (b - a) / (r : K) = (b - v) / r - (a - v) / r := by ring
  constructor <;> linarith [Int.floor_le ((a - v) / (r : K)),
    Int.lt_floor_add_one ((a - v) / (r : K)), Int.floor_le ((b - v) / (r : K)),
    Int.lt_floor_add_one ((b - v) / (r : K))]

end Int
