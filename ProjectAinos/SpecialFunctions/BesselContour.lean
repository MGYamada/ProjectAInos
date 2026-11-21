/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.BesselIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Tactic

/-! # Shifted integer-order Bessel integral

The vertical edges of a rectangle over one period cancel. Both the ordinary Bessel
integral and its argument derivative can therefore be evaluated below the real axis.
-/

@[expose] public section
noncomputable section

open Complex MeasureTheory Set
open scoped Real
namespace ProjectAinos.SpecialFunctions.Bessel

/-- Entire Fourier integrand for the integer-order Bessel coefficient. -/
def fourierKernel (n : ℤ) (x : ℝ) (w : ℂ) := exp (-(n*w-x*sin w)*I)

private theorem periodic_kernel (n : ℤ) (x : ℝ) (w : ℂ) :
    fourierKernel n x (w+2*π) = fourierKernel n x w := by
  simp only [fourierKernel, sin_add_two_pi]
  rw [show -((n : ℂ)*(w+2*π)-x*sin w)*I = -((n : ℂ)*w-x*sin w)*I +
    (-n : ℤ)*(2*π*I) by push_cast; ring, exp_add, exp_int_mul, exp_two_pi_mul_I]
  simp

/-- The horizontal Bessel integral at any fixed imaginary displacement. -/
theorem integral_shift (n : ℤ) (x h : ℝ) :
    (∫ t in -π..π, fourierKernel n x (t-h*I)) = 2*π*besselJ n x := by
  let F := fourierKernel n x
  have hd : Differentiable ℂ F := by unfold F fourierKernel; fun_prop
  have H := integral_boundary_rect_eq_zero_of_differentiableOn F (-(π : ℂ)) (π-h*I)
    hd.differentiableOn
  have he (t : ℝ) : F ((π : ℂ)+t*I) = F (-(π : ℂ)+t*I) := by
    convert periodic_kernel n x (-(π : ℂ)+t*I) using 2
    ring
  simp only [sub_re, sub_im, mul_I_re, mul_I_im, ofReal_im, ofReal_re, neg_re, neg_im, neg_zero,
    sub_zero, zero_sub, ofReal_zero, ofReal_neg, zero_mul, add_zero, he, neg_mul,
    ← sub_eq_add_neg] at H
  have hf := integral_exponential n x
  have hF (t : ℝ) : F t = exp (-(((n : ℝ)*t-x*Real.sin t : ℝ) : ℂ)*I) := by
    unfold F fourierKernel
    push_cast
    rfl
  simp_rw [← hF] at hf
  change (∫ t in -π..π, F (t-h*I)) = _
  linear_combination hf - H

/-- The same displaced contour evaluates the argument derivative, also at zero. -/
theorem integral_shift_deriv (n : ℤ) (x h : ℝ) :
    (∫ t in -π..π, I*sin (t-h*I)*fourierKernel n x (t-h*I)) = 2*π*deriv (besselJ n) x := by
  have he (w : ℂ) : fourierKernel (n-1) x w - fourierKernel (n+1) x w =
      2*(I*sin w*fourierKernel n x w) := by
    have hl : fourierKernel (n-1) x w = exp (w*I)*fourierKernel n x w := by
      unfold fourierKernel
      rw [← exp_add]
      congr 1
      push_cast
      ring
    have hr : fourierKernel (n+1) x w = exp (-(w*I))*fourierKernel n x w := by
      unfold fourierKernel
      rw [← exp_add]
      congr 1
      push_cast
      ring
    rw [hl, hr, ← sub_mul, exp_mul_I, ← neg_mul, exp_mul_I, cos_neg, sin_neg]
    ring
  have hc (m : ℤ) : Continuous (fun t : ℝ => fourierKernel m x (t-h*I)) := by
    unfold fourierKernel; fun_prop
  have H := intervalIntegral.integral_sub (μ := volume) ((hc (n-1)).intervalIntegrable (-π) π)
    ((hc (n+1)).intervalIntegrable (-π) π)
  simp only [he, intervalIntegral.integral_const_mul, integral_shift] at H
  linear_combination H / 2 - (π : ℂ) * (twice_deriv_int n (x : ℂ))

end ProjectAinos.SpecialFunctions.Bessel
