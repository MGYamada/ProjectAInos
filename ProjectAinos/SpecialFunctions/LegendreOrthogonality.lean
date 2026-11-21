/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Legendre
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

/-! # Orthogonality of Legendre polynomials for Lebesgue measure on `[-1,1]` -/

@[expose] public section
noncomputable section

open Polynomial
namespace ProjectAinos.SpecialFunctions.Legendre

private def pair (p r : ℝ[X]) : ℝ := ∫ x in (-1 : ℝ)..1, p.eval x * r.eval x

private theorem pair_sub (p q r : ℝ[X]) : pair (p - q) r = pair p r - pair q r := by
  simp only [pair, eval_sub, sub_mul]
  exact intervalIntegral.integral_sub (p.continuous.mul r.continuous |>.intervalIntegrable ..)
    (q.continuous.mul r.continuous |>.intervalIntegrable ..)

private theorem pair_scale (a : ℝ) (p r : ℝ[X]) : pair (C a * p) r = a * pair p r := by
  simp only [pair, eval_mul, eval_C, mul_assoc, intervalIntegral.integral_const_mul]

private theorem pair_X (p r : ℝ[X]) : pair (X * p) r = pair (X * r) p := by
  simp only [pair, eval_mul, eval_X, mul_right_comm]

private theorem pair_ne {n m : ℕ} (hne : n ≠ m) : pair (polynomial n) (polynomial m) = 0 := by
  let p := polynomial n
  let r := polynomial m
  let q : ℝ[X] := X ^ 2 - 1
  let W := q * p.derivative * r - q * r.derivative * p
  let c : ℝ := n * (n + 1 : ℝ) - m * (m + 1 : ℝ)
  have hw : W.derivative = C c * (p * r) := by
    dsimp only [W, p, r, q, c]
    rw [derivative_sub, derivative_mul, derivative_mul (f := _ * _), equation, equation]
    simp only [map_sub, map_add, map_mul, map_natCast, map_one]
    ring
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1 : ℝ)) (b := 1) (fun x _ => W.hasDerivAt x)
    (W.derivative.continuous.intervalIntegrable ..)
  rw [hw] at h
  simp only [eval_mul, eval_C, intervalIntegral.integral_const_mul] at h
  have hz (x : ℝ) (hx : x ^ 2 = 1) : W.eval x = 0 := by simp [W, q, hx]
  rw [hz 1 (by norm_num), hz (-1) (by norm_num), sub_zero] at h
  have hc : c ≠ 0 := by
    have hnm : (n : ℝ) ≠ m := by exact_mod_cast hne
    have hpos : (0 : ℝ) < (n : ℝ) + m + 1 := by positivity
    dsimp [c]
    rw [show (n : ℝ) * (n + 1 : ℝ) - m * (m + 1 : ℝ) =
      (n - m : ℝ) * ((n : ℝ) + m + 1) by ring]
    exact mul_ne_zero (sub_ne_zero.mpr hnm) hpos.ne'
  exact (mul_eq_zero.mp h).resolve_left hc

private theorem pair_recurrence (n : ℕ) (r : ℝ[X]) :
    (n + 2 : ℝ) * pair (polynomial (n + 2)) r =
      (2 * n + 3 : ℝ) * pair (X * polynomial (n + 1)) r -
        (n + 1 : ℝ) * pair (polynomial n) r := by
  have e : C (n + 2 : ℝ) * polynomial (n + 2) =
      C (2 * n + 3 : ℝ) * (X * polynomial (n + 1)) - C (n + 1 : ℝ) * polynomial n := by
    simpa [map_ofNat, mul_assoc] using recurrence n
  simpa only [pair_sub, pair_scale] using congrArg (fun p => pair p r) e

private theorem pair_self (n : ℕ) : pair (polynomial n) (polynomial n) = 2 / (2 * n + 1) := by
  induction n with
  | zero => norm_num [pair]
  | succ n ih =>
    have h := pair_recurrence n (polynomial n)
    rw [pair_ne (by omega), pair_X] at h
    have g : (2 * n + 1 : ℝ) * pair (X * polynomial n) (polynomial (n + 1)) =
        (n + 1 : ℝ) * pair (polynomial (n + 1)) (polynomial (n + 1)) := by
      cases n with
      | zero => simp
      | succ k =>
        have h' := pair_recurrence k (polynomial (k + 2))
        rw [pair_ne (n := k) (m := k + 2) (by omega)] at h'
        push_cast
        linarith
    rw [eq_div_iff (by positivity)] at ih ⊢
    push_cast
    apply mul_left_cancel₀ (by positivity : (n + 1 : ℝ) ≠ 0)
    linear_combination -(2 * n + 3 : ℝ) * g - (2 * n + 1 : ℝ) * h + (n + 1 : ℝ) * ih

/-- Orthogonality with the classical normalization for ordinary Lebesgue measure. -/
theorem integral_mul (n m : ℕ) :
    (∫ x in (-1 : ℝ)..1, (polynomial n).eval x * (polynomial m).eval x) =
      if n = m then 2 / (2 * (n : ℝ) + 1) else 0 := by
  split_ifs with h
  · subst m
    exact pair_self n
  · exact pair_ne h

end ProjectAinos.SpecialFunctions.Legendre
