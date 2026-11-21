/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.Airy
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Tactic

/-! # Ordinary improper Airy integrals on the real axis

At height R the horizontal segment from iR to the decay ray has integral at most 3/R²
as soon as R² ≥ 3|x|. Moving the contour to the imaginary axis gives the cosine integral
for Ai and the sine plus decaying-exponential integral for Bi.
-/

@[expose] public section
noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology Real ComplexConjugate

namespace ProjectAinos.SpecialFunctions.Airy

private def integrand (z w : ℂ) := exp (w^3/3 - z*w)
private def primitive (z w : ℂ) := Complex.wedgeIntegral 0 w (integrand z)

private theorem zero_primitive (z : ℂ) : primitive z 0 = 0 := by simp [primitive, wedgeIntegral]

private theorem deriv_primitive (z w : ℂ) : HasDerivAt (primitive z) (integrand z w) w := by
  have h : Differentiable ℂ (integrand z) := by unfold integrand; fun_prop
  exact (h.differentiableOn.isConservativeOn (U := Metric.ball 0 (‖w‖+1))).hasDerivAt_wedgeIntegral
    h.continuous.continuousOn (by simp)

private theorem segment (z a b : ℂ) (R : ℝ) :
    primitive z (a+b*R) - primitive z a = ∫ t in 0..R, b * integrand z (a+b*t) := by
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => primitive z (a+b*s)) (b*integrand z (a+b*t)) t := by
    have h := ((hasDerivAt_id (t : ℂ)).const_mul b).const_add a
    simpa [Function.comp_def, mul_comm b] using ((deriv_primitive z _).comp (t : ℂ) h).comp_ofReal
  symm
  convert intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := R) (fun t _ => hd t)
    (Continuous.intervalIntegrable (by unfold integrand; fun_prop) ..) using 1
  simp

private theorem on_ray (z : ℂ) (R : ℝ) : primitive z (upper*R) =
    upper * ∫ t in 0..R, exp (-(t : ℂ)^3/3 - upper*z*t) := by
  have hc : upper ^ 3 = -1 := by
    rw [upper, ← exp_nat_mul, ← exp_pi_mul_I]
    congr 1
    push_cast
    ring
  have he (t : ℝ) : integrand z (upper*t) = exp (-(t : ℂ)^3/3 - upper*z*t) := by
    unfold integrand
    rw [mul_pow, hc]
    congr 1
    ring
  have h := segment z 0 upper R
  simpa only [zero_add, zero_primitive, sub_zero, he, pow_zero, one_mul,
    intervalIntegral.integral_const_mul] using h

private theorem ray_limit (z : ℂ) : Tendsto (fun R : ℝ => primitive z (upper * R)) atTop
    (𝓝 (ray upper z)) := by
  simp_rw [on_ray]
  simpa only [pow_zero, one_mul, ray] using (tendsto_moment 0 (upper*z)).const_mul upper

private theorem horizontal (x R : ℝ) (hR : 0 < R) (hx : 3 * |x| ≤ R^2) :
    ‖primitive x (I*R + (R/√3 : ℝ)) - primitive x (I*R)‖ ≤ 3/R^2 := by
  have hs : 0 < √(3 : ℝ) := by positivity
  have hq : 1 ≤ √(3 : ℝ) := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  have ht : 0 ≤ R / √3 := by positivity
  have he (t : ℝ) (h : t ∈ Ioc 0 (R/√3)) :
      ‖integrand x (I*R + t)‖ ≤ Real.exp (-(R^2/3)*t) := by
    rw [integrand, norm_exp, Real.exp_le_exp]
    have htR : t ≤ R := h.2.trans (div_le_self hR.le hq)
    have hsq := pow_le_pow_left₀ h.1.le htR 2
    simp [pow_succ, Complex.mul_re, Complex.mul_im, div_ofNat_re]
    nlinarith [mul_nonneg h.1.le (sub_nonneg.mpr hsq),
      mul_nonneg h.1.le (show 0 ≤ R^2+3*x by linarith [neg_abs_le x])]
  have h := segment x (I*R) 1 (R/√3)
  simp only [one_mul] at h
  rw [h]
  apply (intervalIntegral.norm_integral_le_of_norm_le ht (ae_of_all _ he)
    (Continuous.intervalIntegrable (by fun_prop) ..)).trans
  let c := R^2/3
  have hc : 0 < c := by dsimp [c]; positivity
  have hd (t : ℝ) : HasDerivAt (fun s => -Real.exp (-c*s)/c) (Real.exp (-c*t)) t := by
    convert ((((hasDerivAt_id t).const_mul (-c)).exp).neg.div_const c) using 1
    dsimp
    field_simp
    rfl
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (Continuous.intervalIntegrable (by fun_prop) ..)]
  simp only [mul_zero, Real.exp_zero]
  have hj : 1/c = 3/R^2 := by unfold c; ring
  rw [← hj]
  simp only [neg_div, sub_neg_eq_add]
  linarith [div_nonneg (Real.exp_pos (-c*(R/√3))).le hc.le]

private theorem rescale (R : ℝ) :
    upper * ((2 / √3 * R : ℝ) : ℂ) = I*R + ((R/√3 : ℝ) : ℂ) := by
  rw [upper_eq]
  push_cast
  field_simp
  ring

private theorem segment_vanishes (x : ℝ) :
    Tendsto (fun R : ℝ => primitive x (I*R + ((R/√3 : ℝ) : ℂ)) - primitive x (I*R))
      atTop (𝓝 0) := by
  have hpow : Tendsto (fun R : ℝ => R^2) atTop atTop := tendsto_pow_atTop two_ne_zero
  have hbound : Tendsto (fun R : ℝ => 3/R^2) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hpow
  apply squeeze_zero_norm' _ hbound
  filter_upwards [eventually_gt_atTop (0 : ℝ), hpow.eventually_ge_atTop (3*|x|)] with R hR h
  exact horizontal x R hR h

private theorem vertical_limit (x : ℝ) : Tendsto (fun R : ℝ => primitive x (I*R)) atTop
    (𝓝 (ray upper x)) := by
  have hs : 0 < 2 / √(3 : ℝ) := by positivity
  have hr := (ray_limit x).comp (tendsto_id.const_mul_atTop hs)
  change Tendsto (fun R : ℝ => primitive x (upper * ((2/√3 * R : ℝ) : ℂ))) _ _ at hr
  simp_rw [rescale] at hr
  simpa only [sub_sub_cancel, sub_zero] using hr.sub (segment_vanishes x)

private theorem axis (x R : ℝ) : primitive x (I*R) =
    ↑(∫ t in 0..R, Real.sin (t^3/3+x*t)) + ↑(∫ t in 0..R, Real.cos (t^3/3+x*t)) * I := by
  have h := segment x 0 I R
  have hk (t : ℝ) : I * integrand x (I*t) =
      ↑(Real.sin (t^3/3+x*t)) + ↑(Real.cos (t^3/3+x*t)) * I := by
    unfold integrand
    rw [show (I*t)^3/3 - (x : ℂ)*(I*t) = -((t^3/3+x*t : ℝ) : ℂ) * I by
      push_cast
      rw [mul_pow, pow_succ I 2, I_sq]
      ring, exp_mul_I, cos_neg, sin_neg, ← ofReal_cos, ← ofReal_sin]
    linear_combination -(Real.sin (t^3/3+x*t) : ℂ) * I_sq
  simp only [zero_add, zero_primitive, sub_zero, hk] at h
  rw [h, intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) ..)
    (Continuous.intervalIntegrable (by fun_prop) ..), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]

private theorem real_values (x : ℝ) :
    ai x = ((ray upper x).im / π : ℝ) ∧
    bi x = (((ray upper x).re + (moment 0 (-x)).re) / π : ℝ) := by
  have h := conj_ray upper (x : ℂ)
  rw [conj_ofReal] at h
  have hm := conj_moment 0 (-(x : ℂ))
  rw [map_neg, conj_ofReal] at hm
  have him := congrArg Complex.im hm
  simp only [conj_im] at him
  have hz : (moment 0 (-(x : ℂ))).im = 0 := by linarith
  have hr : ray (-1) x = -moment 0 (-(x : ℂ)) := by simp [ray]
  rw [ai, bi, ← h, hr]
  push_cast
  constructor
  · field_simp [I_ne_zero, Real.pi_ne_zero]
    apply Complex.ext <;> simp; ring
  · field_simp [Real.pi_ne_zero]
    apply Complex.ext <;> simp [hz]; ring

/-- Ordinary improper cosine representation of the first Airy function. -/
theorem tendsto_cos_integral (x : ℝ) :
    Tendsto (fun R : ℝ => (1/π) * ∫ t in 0..R, Real.cos (t^3/3+x*t)) atTop (𝓝 (ai x).re) := by
  have h := (continuous_im.tendsto _).comp (vertical_limit x)
  change Tendsto (fun R : ℝ => (primitive x (I*R)).im) _ _ at h
  simp only [axis, add_im, ofReal_im, mul_I_im, ofReal_re, zero_add] at h
  rw [(real_values x).1, ofReal_re]
  simpa only [div_eq_inv_mul, mul_one] using h.const_mul (1/π)

/-- Ordinary improper sine integral plus the convergent real exponential integral for Bi. -/
theorem tendsto_bi_integral (x : ℝ) :
    Tendsto (fun R : ℝ => (1/π) * ((∫ t in 0..R, Real.sin (t^3/3+x*t)) +
      ∫ t : ℝ in Ioi 0, Real.exp (-t^3/3+x*t))) atTop (𝓝 (bi x).re) := by
  have h := (continuous_re.tendsto _).comp (vertical_limit x)
  change Tendsto (fun R : ℝ => (primitive x (I*R)).re) _ _ at h
  simp only [axis, add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero] at h
  have he : moment 0 (-(x : ℂ)) = ↑(∫ t : ℝ in Ioi 0, Real.exp (-t^3/3+x*t)) := by
    unfold moment
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards with t
    push_cast
    simp
  rw [(real_values x).2, ofReal_re, he, ofReal_re]
  simpa only [div_eq_inv_mul, mul_one] using (h.add_const _).const_mul (1/π)

/-- Finite oscillatory integral for the canonical cubic phase. -/
def cubicIntegral (x R : ℝ) : ℂ :=
  ∫ t in 0..R, exp (((t^3/3+x*t : ℝ) : ℂ) * I)

/-- One-sided cubic profile, including its sine component. -/
def cubicLimit (x : ℝ) : ℂ := I * conj (ray upper x)

private theorem rotate_axis (x R : ℝ) : cubicIntegral x R = I * conj (primitive x (I*R)) := by
  rw [axis, map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  simp_rw [cubicIntegral, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) ..)
    (Continuous.intervalIntegrable (by fun_prop) ..), intervalIntegral.integral_mul_const,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  linear_combination (∫ t in 0..R, Real.cos (t^3/3+x*t) : ℝ) * I_sq

/-- The two symmetric half-lines give the real Airy profile. -/
theorem cubicLimit_add_conj (x : ℝ) : cubicLimit x + conj (cubicLimit x) = 2 * π * ai x := by
  rw [(real_values x).1, cubicLimit]
  push_cast
  field_simp [Real.pi_ne_zero]
  apply Complex.ext <;> simp; ring

/-- Error after truncating the oscillatory integral, uniform for |x| ≤ B. -/
theorem cubic_tail {x R B : ℝ} (hx : |x| ≤ B) (hR : 0 < R) (hB : 3*B ≤ R^2) :
    ‖cubicIntegral x R - cubicLimit x‖ ≤ 3/R^2 +
      ∫ t : ℝ in Ioi (2/√3*R), Real.exp ((B^2+9)/2) * Real.exp (-t^2) := by
  have hw : ‖upper‖ = 1 := by rw [upper, norm_exp]; simp
  have hr : ‖upper * (x : ℂ)‖ ≤ B := by simpa [norm_mul, hw] using hx
  have hm := moment_tail hr (R := 2/√3*R) (by positivity)
  rw [rotate_axis, cubicLimit, ← mul_sub, ← map_sub, norm_mul, norm_I, one_mul, norm_conj]
  simp only [← dist_eq_norm]
  apply (dist_triangle (primitive x (I*R)) (primitive x (upper * ((2/√3*R : ℝ) : ℂ)))
    (ray upper x)).trans
  apply add_le_add
  · rw [rescale, dist_comm, dist_eq_norm]
    exact horizontal x R hR (by linarith)
  · rw [dist_eq_norm, on_ray, ray, ← mul_sub, norm_mul, hw, one_mul, norm_sub_rev]
    exact hm

end ProjectAinos.SpecialFunctions.Airy
