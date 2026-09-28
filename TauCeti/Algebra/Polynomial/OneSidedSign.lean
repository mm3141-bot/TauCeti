/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Polynomial.RealClosed.Sign
import Mathlib.Data.Nat.Find

/-! # One-sided signs of a polynomial at a point

`signAtRight p a` is the sign of `p` immediately to the right of `a`, read off as the sign of
the first formal derivative of `p` that does not vanish at `a`; `signAtLeft p a` is the sign
immediately to the left, differing by the parity of that derivative order. The order of that
derivative is the multiplicity of `a` in `p`, so over a real closed field each of these signs
is realized by the sign of `p` at every point of a root-free half-neighbourhood of `a`.

One-sided signs carry the endpoint contributions of a Sturm chain: a root count over an open
interval can then be stated even when an endpoint is itself a root of an entry of the chain.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, §2.7, for one-sided sign variations and the endpoint versions of Sturm's theorem.
-/

public section

namespace Polynomial

open SignType

section Definition

variable {R : Type*} [CommRing R] [LinearOrder R]

open scoped Classical in
/-- The sign of `p` immediately to the right of `a`: the sign of the first formal derivative
of `p` that does not vanish at `a`, or `0` when every derivative of `p` vanishes at `a`. -/
noncomputable def signAtRight (p : R[X]) (a : R) : SignType :=
  if h : ∃ k, (derivative^[k] p).eval a ≠ 0 then sign ((derivative^[Nat.find h] p).eval a) else 0

open scoped Classical in
/-- The sign of `p` immediately to the left of `a`. The sign of `p` before `a` differs from the
sign after `a` by the parity of the order of the first derivative nonzero at `a`. -/
noncomputable def signAtLeft (p : R[X]) (a : R) : SignType :=
  if h : ∃ k, (derivative^[k] p).eval a ≠ 0 then
    sign ((derivative^[Nat.find h] p).eval a) * (-1) ^ Nat.find h
  else 0

/-- The least natural number satisfying a predicate is a witness whose smaller numbers all
fail, and conversely. -/
private theorem natFind_eq (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (h : ∃ n, P n)
    (hm : P m) (hmin : ∀ j < m, ¬ P j) : Nat.find h = m :=
  le_antisymm (Nat.find_min' h hm) (by
    by_contra hc
    exact (hmin (Nat.find h) (by omega) (Nat.find_spec h)).elim)

/-- Where some derivative of `p` does not vanish at `a`, the one-sided sign of `p` at `a` is the
sign of the first such derivative. -/
private theorem signAtRight_eq_sign_find (p : R[X]) (a : R)
    (hex : ∃ k, (derivative^[k] p).eval a ≠ 0) :
    signAtRight p a = sign ((derivative^[Nat.find hex] p).eval a) := by
  rw [signAtRight, dite_eq_left hex]

/-- Where some derivative of `p` does not vanish at `a`, the left one-sided sign of `p` at `a` is
the sign of the first such derivative, times the parity of its order. -/
private theorem signAtLeft_eq_sign_find (p : R[X]) (a : R)
    (hex : ∃ k, (derivative^[k] p).eval a ≠ 0) :
    signAtLeft p a = sign ((derivative^[Nat.find hex] p).eval a) * (-1) ^ Nat.find hex := by
  rw [signAtLeft, dite_eq_left hex]

/-- The one-sided sign of the zero polynomial is zero on either side. -/
@[simp, grind =]
theorem signAtRight_zero (a : R) : signAtRight 0 a = 0 := by simp [signAtRight]

@[simp, grind =]
theorem signAtLeft_zero (a : R) : signAtLeft 0 a = 0 := by simp [signAtLeft]

/-- The one-sided sign of `p` at `a` is the sign of a prescribed derivative that is nonzero there
and whose predecessors all vanish there. -/
theorem signAtRight_eq_sign_derivative {p : R[X]} {a : R} {m : ℕ}
    (hm : (derivative^[m] p).eval a ≠ 0) (hmin : ∀ j < m, (derivative^[j] p).eval a = 0) :
    signAtRight p a = sign ((derivative^[m] p).eval a) := by
  classical
  have hex : ∃ j, (derivative^[j] p).eval a ≠ 0 := ⟨m, hm⟩
  rw [signAtRight, dite_eq_left hex,
    natFind_eq _ hex hm fun n hn hp => hp (hmin n hn)]

/-- The left one-sided sign of `p` at `a` is the sign of a prescribed derivative that is
nonzero there and whose predecessors all vanish there, times the parity of its order. -/
theorem signAtLeft_eq_sign_derivative {p : R[X]} {a : R} {m : ℕ}
    (hm : (derivative^[m] p).eval a ≠ 0) (hmin : ∀ j < m, (derivative^[j] p).eval a = 0) :
    signAtLeft p a = sign ((derivative^[m] p).eval a) * (-1) ^ m := by
  classical
  have hex : ∃ k, (derivative^[k] p).eval a ≠ 0 := ⟨m, hm⟩
  rw [signAtLeft_eq_sign_find p a hex,
    natFind_eq _ hex hm fun n hn hp => hp (hmin n hn)]

/-- Where `p` does not vanish, its one-sided signs are the sign of its value. -/
@[grind =]
theorem signAtRight_eq_sign_eval {p : R[X]} {a : R} (ha : p.eval a ≠ 0) :
    signAtRight p a = sign (p.eval a) := by
  classical
  have hex : ∃ k, (derivative^[k] p).eval a ≠ 0 := ⟨0, by simpa using ha⟩
  rw [signAtRight, dite_eq_left hex, (Nat.find_eq_zero hex).mpr (by simpa using ha),
    Function.iterate_zero_apply]

/-- The left one-sided sign of `p` at `a` is the sign of its value wherever `p` does not vanish. -/
theorem signAtLeft_eq_sign_eval {p : R[X]} {a : R} (ha : p.eval a ≠ 0) :
    signAtLeft p a = sign (p.eval a) := by
  classical
  have hex : ∃ k, (derivative^[k] p).eval a ≠ 0 := ⟨0, by simpa using ha⟩
  rw [signAtLeft, dite_eq_left hex, (Nat.find_eq_zero hex).mpr (by simpa using ha), pow_zero,
    mul_one, Function.iterate_zero_apply]

end Definition

section Derivative

variable {R : Type*} [CommRing R]

/-- The `j`th derivative of `(X - C a) * g`, for positive `j`, is `j` times the derivative of `g`
of order one less, plus `(X - C a)` times its `j`th derivative. -/
private theorem iterate_derivative_sub_mul (a : R) (g : R[X]) (j : ℕ) :
    derivative^[Nat.succ j] ((X - C a) * g) =
      C (Nat.succ j : R) * derivative^[j] g + (X - C a) * derivative^[Nat.succ j] g := by
  induction j with
  | zero =>
      simp only [Function.iterate_one, Function.iterate_zero_apply, derivative_mul, derivative_sub,
        derivative_X, derivative_C, map_one, one_mul, sub_zero, Nat.cast_one]
  | succ k ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [derivative_add, derivative_mul, derivative_sub, derivative_X, derivative_C,
        sub_zero, Nat.cast_succ, add_mul, C_add, C_1, derivative_one, Function.iterate_succ_apply']
      ring

/-- Below the exponent `m` every formal derivative of `(X - C a)^m * q` vanishes at `a`, and the
derivative of that order is the factorial times the value of the cofactor. -/
private theorem eval_iterate_derivative_pow_mul (a : R) (m : ℕ) (q : R[X]) :
    (∀ j, j < m → (derivative^[j] ((X - C a)^m * q)).eval a = 0) ∧
      (derivative^[m] ((X - C a)^m * q)).eval a = (Nat.factorial m : R) * q.eval a := by
  induction m generalizing q with
  | zero =>
      refine ⟨by simp, ?_⟩
      simp only [pow_zero, one_mul, Function.iterate_zero_apply, Nat.factorial_zero, Nat.cast_one]
  | succ m ih =>
      have hdecomp : (X - C a) ^ (m + 1) * q = (X - C a) * ((X - C a)^m * q) := by
        rw [pow_succ]; ring
      rw [hdecomp, iterate_derivative_sub_mul, eval_add, eval_mul, eval_C, eval_mul, eval_sub,
        eval_X, eval_C, sub_self, zero_mul]
      constructor
      · intro j hj
        cases j with
        | zero =>
            rw [Function.iterate_zero_apply, eval_mul, eval_sub, eval_X, eval_C, sub_self,
              zero_mul]
        | succ j =>
            rw [iterate_derivative_sub_mul, eval_add, eval_mul, eval_C, eval_mul, eval_sub,
              eval_X, eval_C, sub_self, zero_mul, (ih q).1 j (by omega), mul_zero, add_zero]
      · rw [(ih q).2, Nat.factorial_succ, Nat.cast_mul, add_zero, ← mul_assoc]

/-- The multiplicity of `a` in a nonzero polynomial `p` is the order of the first formal derivative
of `p` that does not vanish at `a`, and that derivative is a positive multiple of the value
at `a` of the remaining cofactor. -/
theorem exists_pow_mul_of_derivative (p : R[X]) (hp : p ≠ 0) (a : R) :
    ∃ q, p = (X - C a) ^ rootMultiplicity a p * q ∧ q.eval a ≠ 0 ∧
      (∀ j, j < rootMultiplicity a p → (derivative^[j] p).eval a = 0) ∧
      (derivative^[rootMultiplicity a p] p).eval a
        = (Nat.factorial (rootMultiplicity a p) : R) * q.eval a := by
  obtain ⟨q, hq, hnd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  have hq0 : q.eval a ≠ 0 := fun h => hnd (dvd_iff_isRoot.mpr h)
  refine ⟨q, hq, hq0, fun j hj => ?_, ?_⟩
  · calc
      (derivative^[j] p).eval a
          = (derivative^[j] ((X - C a) ^ rootMultiplicity a p * q)).eval a := by rw [← hq]
      _ = 0 := (eval_iterate_derivative_pow_mul a _ q).1 j hj
  · calc
      (derivative^[rootMultiplicity a p] p).eval a
          = (derivative^[rootMultiplicity a p] ((X - C a) ^ rootMultiplicity a p * q)).eval a := by
            rw [← hq]
      _ = (Nat.factorial (rootMultiplicity a p) : R) * q.eval a :=
        (eval_iterate_derivative_pow_mul a _ q).2

end Derivative

section Locality

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]

omit [IsRealClosed R] in
/-- Multiplying an argument by a positive natural number does not change its sign. -/
private theorem sign_mul_natCast_factorial (m : ℕ) (y : R) :
    sign ((Nat.factorial m : R) * y) = sign y := by
  rw [sign_mul, sign_pos (Nat.cast_pos'.mpr (Nat.factorial_pos m)), one_mul]

omit [IsRealClosed R] [IsStrictOrderedRing R] in
/-- A cofactor of a root of `p` at `a` does not vanish at `a` nor to its right, where `p` has no
zero. -/
private theorem cofactor_ne_zero_right {p q : R[X]} {a x : R} {m : ℕ} (hpq : p = (X - C a) ^ m * q)
    (hqa : q.eval a ≠ 0) (hz : ∀ y, a < y → y ≤ x → p.eval y ≠ 0) {y : R} (hy : y ∈ Set.Icc a x) :
    q.eval y ≠ 0 := by
  by_cases hy0 : y = a
  · rw [hy0]; exact hqa
  · intro hqy
    have hay : a < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
    exact hz y hay hy.2 (by
      rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, hqy, mul_zero])

omit [IsRealClosed R] [IsStrictOrderedRing R] in
/-- A cofactor of a root of `p` at `a` does not vanish at `a` nor to its left, where `p` has no
zero. -/
private theorem cofactor_ne_zero_left {p q : R[X]} {x a : R} {m : ℕ} (hpq : p = (X - C a) ^ m * q)
    (hqa : q.eval a ≠ 0) (hz : ∀ y, x ≤ y → y < a → p.eval y ≠ 0) {y : R} (hy : y ∈ Set.Icc x a) :
    q.eval y ≠ 0 := by
  by_cases hy0 : y = a
  · rw [hy0]; exact hqa
  · intro hqy
    have hya : y < a := lt_of_le_of_ne hy.2 hy0
    exact hz y hy.1 hya (by
      rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, hqy, mul_zero])

omit [IsRealClosed R] in
/-- The derivative of the order of the first nonzero derivative of `p` at `a` does not vanish
there. -/
private theorem derivative_of_derivative_ne (p : R[X]) (hp : p ≠ 0) (a : R) :
    (derivative^[rootMultiplicity a p] p).eval a ≠ 0 := by
  obtain ⟨q, _, hq, _, hm⟩ := exists_pow_mul_of_derivative p hp a
  rw [hm]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) hq

/-- Where `p` has no zero in `(a, x]`, the sign after `a` is the sign of its value at `x`. -/
theorem signAtRight_eq_sign_eval_of_notRoot (p : R[X]) (hp : p ≠ 0) {a x : R} (hax : a < x)
    (hz : ∀ y, a < y → y ≤ x → p.eval y ≠ 0) : signAtRight p a = sign (p.eval x) := by
  obtain ⟨q, hpq, hq, hmin, hm⟩ := exists_pow_mul_of_derivative p hp a
  calc
    signAtRight p a = sign ((derivative^[rootMultiplicity a p] p).eval a) :=
      signAtRight_eq_sign_derivative (derivative_of_derivative_ne p hp a) hmin
    _ = sign ((Nat.factorial (rootMultiplicity a p) : R) * q.eval a) := by rw [hm]
    _ = sign (q.eval a) := sign_mul_natCast_factorial _ _
    _ = sign (q.eval x) := sign_eval_const q hax.le fun y hy => cofactor_ne_zero_right hpq hq hz hy
    _ = sign (p.eval x) := by
      rw [hpq, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sign_mul, sign_pow,
        sign_pos (sub_pos.mpr hax), one_pow, one_mul]

/-- Where `p` has no zero in `[x, a)`, the sign before `a` is the sign of its value at `x`. -/
theorem signAtLeft_eq_sign_eval_of_notRoot (p : R[X]) (hp : p ≠ 0) {x a : R} (hax : x < a)
    (hz : ∀ y, x ≤ y → y < a → p.eval y ≠ 0) : signAtLeft p a = sign (p.eval x) := by
  obtain ⟨q, hpq, hq, hmin, hm⟩ := exists_pow_mul_of_derivative p hp a
  calc
    signAtLeft p a
        = sign ((derivative^[rootMultiplicity a p] p).eval a) * (-1) ^ rootMultiplicity a p :=
      signAtLeft_eq_sign_derivative (derivative_of_derivative_ne p hp a) hmin
    _ = sign ((Nat.factorial (rootMultiplicity a p) : R) * q.eval a)
        * (-1) ^ rootMultiplicity a p := by rw [hm]
    _ = sign (q.eval a) * (-1) ^ rootMultiplicity a p := by rw [sign_mul_natCast_factorial]
    _ = sign (q.eval x) * (-1) ^ rootMultiplicity a p := by
      have h := sign_eval_const q hax.le fun y hy => cofactor_ne_zero_left hpq hq hz hy
      rw [← h]
    _ = sign (p.eval x) := by
      conv_rhs => rw [hpq]
      rw [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sign_mul, sign_pow,
        sign_neg (sub_neg.mpr hax), mul_comm]

end Locality

end Polynomial

end
