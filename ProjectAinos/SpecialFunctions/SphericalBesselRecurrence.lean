/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.SphericalBessel
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-! # Spherical Bessel recurrences

Integration by parts transfers the two-degree Legendre derivative identity to the spherical
Bessel recurrence. The endpoint terms cancel since the two polynomials have the same parity.
-/

@[expose] public section
noncomputable section

open Complex Polynomial
namespace ProjectAinos.SpecialFunctions.Bessel
open Legendre

private def moment (z : ℂ) (p : ℝ[X]) : ℂ :=
  ∫ t in (-1 : ℝ)..1, exp (I * z * t) * (p.eval t : ℝ)

private theorem parts (z : ℂ) (p : ℝ[X]) :
    moment z p.derivative = exp (I * z) * ((p.eval 1 : ℝ) : ℂ) -
      exp (-(I * z)) * ((p.eval (-1) : ℝ) : ℂ) - I * z * moment z p := by
  let e (t : ℝ) := exp (I * z * t)
  have he t : HasDerivAt e (I * z * e t) t := by
    simpa [e, mul_comm (exp _) (I * z)] using
      (((hasDerivAt_id (t : ℂ)).const_mul (I * z)).cexp.comp_ofReal)
  have hp t : HasDerivAt (fun s : ℝ => Complex.ofReal (p.eval s))
      (Complex.ofReal (p.derivative.eval t)) t :=
    (p.hasDerivAt t).ofReal_comp
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := (-1 : ℝ)) (b := 1)
    (fun t _ => he t) (fun t _ => hp t)
    (Continuous.intervalIntegrable (by unfold e; fun_prop) ..)
    (Continuous.intervalIntegrable (by fun_prop) ..)
  simpa only [e, moment, ofReal_one, ofReal_neg, mul_one, mul_neg, mul_assoc (I * z),
    intervalIntegral.integral_const_mul] using h

private theorem moment_sub (z : ℂ) (p q : ℝ[X]) :
    moment z (p - q) = moment z p - moment z q := by
  simp only [moment, eval_sub, ofReal_sub, mul_sub]
  exact intervalIntegral.integral_sub
    (Continuous.intervalIntegrable (by fun_prop) ..)
    (Continuous.intervalIntegrable (by fun_prop) ..)

private theorem moment_scale (z : ℂ) (c : ℝ) (p : ℝ[X]) :
    moment z (C c * p) = c * moment z p := by
  simp only [moment, eval_mul, eval_C, ofReal_mul]
  simp_rw [mul_left_comm (exp _) (c : ℂ), intervalIntegral.integral_const_mul]

private theorem moment_eq (z : ℂ) (n : ℕ) :
    moment z (polynomial n) = 2 * I ^ n * sphericalJ n z := by
  unfold sphericalJ moment
  field_simp

/-- The first regular mode is `sin(z)/z² − cos(z)/z` away from the origin. -/
theorem sphericalJ_one_order {z : ℂ} (hz : z ≠ 0) :
    sphericalJ 1 z = sin z / z ^ 2 - cos z / z := by
  have h := parts z X
  have hm : moment z X = 2 * I * sphericalJ 1 z := by
    simpa only [polynomial_one, pow_one] using moment_eq z 1
  rw [hm] at h
  simp only [derivative_X, ← polynomial_zero, moment_eq, pow_zero,
    mul_one, eval_X, ofReal_one, ofReal_neg, mul_neg, sub_neg_eq_add,
    sphericalJ_zero_order hz] at h
  rw [mul_comm I z, ← neg_mul, exp_mul_I, exp_mul_I, cos_neg, sin_neg] at h
  field_simp [hz] at h ⊢
  linear_combination -h / 2 + (z ^ 2 * sphericalJ 1 z) * I_sq

/-- Three-term recurrence of regular spherical Bessel functions, including the origin. -/
theorem sphericalJ_recurrence (z : ℂ) (n : ℕ) :
    z * (sphericalJ (n + 2) z + sphericalJ n z) =
      (2 * (n : ℂ) + 3) * sphericalJ (n + 1) z := by
  have h := parts z (polynomial (n + 2) - polynomial n)
  rw [derivative_sub_two, moment_scale, moment_sub] at h
  have hneg (j : ℕ) : (polynomial j).eval (-1) = (-1 : ℝ) ^ j := by
    simpa using polynomial_eval_neg j 1
  simp only [eval_sub, polynomial_eval_one, sub_self, hneg, pow_add (-1 : ℝ) n 2,
    neg_one_sq, mul_one, ofReal_zero, mul_zero, zero_sub, moment_eq] at h
  push_cast at h
  simp only [pow_add, pow_one, I_sq] at h
  apply mul_left_cancel₀ (pow_ne_zero (n + 1) I_ne_zero)
  rw [pow_succ]
  linear_combination -h / 2

end ProjectAinos.SpecialFunctions.Bessel
