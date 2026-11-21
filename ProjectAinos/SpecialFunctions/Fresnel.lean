/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-! # Fresnel integrals and the complex error function

Integrate the entire Gaussian from the origin to the ray `(1 − i)R`. The vertical segment
from `R` to `R − iR` contributes at most `1/R`: its modulus at depth `y` is
`exp(y² − R²) ≤ exp(R(y − R))`. The real Gaussian integral thus also evaluates the
conditionally convergent Fresnel integrals.
-/

@[expose] public section
noncomputable section

open Complex Real MeasureTheory Filter Set
open scoped Topology
namespace ProjectAinos.SpecialFunctions.Fresnel

private def gaussian (z : ℂ) := Complex.exp (-z ^ 2)

private def G (z : ℂ) := Complex.wedgeIntegral 0 z gaussian

private theorem G_zero : G 0 = 0 := by simp [G, Complex.wedgeIntegral]

private theorem dG (z : ℂ) : HasDerivAt G (gaussian z) z := by
  have h : Differentiable ℂ gaussian := by unfold gaussian; fun_prop
  have hc := h.differentiableOn.isConservativeOn (U := Metric.ball 0 (‖z‖ + 1))
  exact hc.hasDerivAt_wedgeIntegral h.continuous.continuousOn (by simp)

/-- Complex error function, normalized by the real Gaussian integral. -/
def erf (z : ℂ) : ℂ :=
  2 / (√π : ℂ) * (Complex.wedgeIntegral 0 z (fun w => Complex.exp (-w ^ 2)))

/-- Both the complex derivative and normalization of the error function. -/
theorem hasDerivAt_erf (z : ℂ) :
    HasDerivAt erf (2 / (√π : ℂ) * Complex.exp (-z ^ 2)) z := by
  exact (dG z).const_mul _

@[simp] theorem erf_zero : erf 0 = 0 := by simp [erf, Complex.wedgeIntegral]

private theorem segment (a b : ℂ) (R : ℝ) :
    G (a + b * R) - G a = ∫ t in (0 : ℝ)..R, b * gaussian (a + b * t) := by
  have h (t : ℝ) : HasDerivAt (fun s : ℝ => G (a + b * s)) (b * gaussian (a + b * t)) t := by
    have hl := ((hasDerivAt_id (t : ℂ)).const_mul b).const_add a
    simpa [Function.comp_def, mul_comm b] using ((dG _).comp (t : ℂ) hl).comp_ofReal
  symm
  convert intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := R) (fun t _ => h t)
    (Continuous.intervalIntegrable (by unfold gaussian; fun_prop) ..) using 1
  simp

private theorem real_axis (R : ℝ) :
    G R = ((∫ t in (0 : ℝ)..R, Real.exp (-t ^ 2) : ℝ) : ℂ) := by
  simpa [gaussian, G_zero, ← Complex.ofReal_pow, ← Complex.ofReal_neg, ← Complex.ofReal_exp,
    intervalIntegral.integral_ofReal] using segment 0 1 R

private theorem G_limit : Tendsto (fun R : ℝ => G R) atTop (𝓝 ((√π / 2 : ℝ) : ℂ)) := by
  have hi := (integrable_exp_neg_mul_sq (by norm_num : 0 < (1 : ℝ))).integrableOn
    (s := Ioi (0 : ℝ))
  have h := intervalIntegral_tendsto_integral_Ioi 0 hi tendsto_id
  rw [integral_gaussian_Ioi] at h
  simpa [real_axis, Function.comp_def] using (Complex.continuous_ofReal.tendsto _).comp h

/-- The error function tends to one along the positive real axis. -/
theorem tendsto_erf_atTop : Tendsto (fun x : ℝ => erf x) atTop (𝓝 1) := by
  change Tendsto (fun x : ℝ => 2 / (√π : ℂ) * G x) atTop (𝓝 1)
  convert G_limit.const_mul (2 / (√π : ℂ)) using 1
  push_cast
  field_simp [Real.sqrt_pos.mpr Real.pi_pos |>.ne']

private theorem vertical_estimate {R : ℝ} (hR : 0 < R) :
    ‖G (R + -I * R) - G R‖ ≤ 1 / R := by
  rw [segment]
  have hb : ∀ᵐ t ∂volume, t ∈ Ioc 0 R →
      ‖-I * gaussian (R + -I * t)‖ ≤ Real.exp (R * (t - R)) := by
    refine ae_of_all _ fun t ht => ?_
    simp only [gaussian, norm_mul, norm_neg, norm_I, one_mul, Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    simp [sq, Complex.mul_re, Complex.mul_im]
    nlinarith [mul_nonneg ht.1.le (sub_nonneg.mpr ht.2)]
  apply (intervalIntegral.norm_integral_le_of_norm_le hR.le hb
    (Continuous.intervalIntegrable (by fun_prop) ..)).trans
  have hd t : HasDerivAt (fun s => Real.exp (R * (s - R)) / R) (Real.exp (R * (t - R))) t := by
    simpa [hR.ne'] using ((((hasDerivAt_id t).sub_const R).const_mul R).exp.div_const R)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (Continuous.intervalIntegrable (by fun_prop) ..)]
  simp only [sub_self, mul_zero, Real.exp_zero, zero_sub]
  exact sub_le_self _ (by positivity)

private def c : ℂ := ((√π / 2 : ℝ) : ℂ) * (1 - I)

private theorem c_sq : c ^ 2 = -(π : ℂ) / 2 * I := by
  have hr := congrArg Complex.ofReal (Real.sq_sqrt Real.pi_pos.le)
  push_cast at hr
  unfold c
  push_cast
  rw [mul_pow, div_pow, hr, sub_sq, I_sq]
  ring

/-- Complex Fresnel integral in the normalization `C(x) + i S(x)`. -/
def integral (x : ℝ) : ℂ := ∫ t in (0 : ℝ)..x, Complex.exp (((π / 2 * t ^ 2 : ℝ) : ℂ) * I)

/-- Fresnel cosine integral. -/
def cosine (x : ℝ) : ℝ := (integral x).re

/-- Fresnel sine integral. -/
def sine (x : ℝ) : ℝ := (integral x).im

private theorem ray (x : ℝ) : G (c * x) = c * integral x := by
  have h := segment 0 c x
  simp only [zero_add, G_zero, sub_zero, gaussian, mul_pow, c_sq] at h
  rw [integral, ← intervalIntegral.integral_const_mul]
  rw [h]
  apply intervalIntegral.integral_congr
  intro t _
  push_cast
  congr 2
  ring

/-- Actual improper limit of the finite-interval Fresnel integral along the real axis. -/
theorem tendsto_integral_atTop : Tendsto integral atTop (𝓝 ((1 + I) / 2)) := by
  let r (x : ℝ) := √π / 2 * x
  have hr : Tendsto r atTop atTop := tendsto_id.const_mul_atTop (by positivity)
  have hr₀ : ∀ᶠ x in atTop, 0 < r x := hr.eventually_gt_atTop 0
  have he (x : ℝ) : c * x = r x + -I * r x := by dsimp [c, r]; push_cast; ring
  have hdiff : Tendsto (fun x : ℝ => G (c * x) - G (r x)) atTop (𝓝 0) := by
    have ht : Tendsto (fun x => 1 / r x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hr
    apply squeeze_zero_norm' _ ht
    filter_upwards [hr₀] with x hx
    rw [he]
    exact vertical_estimate hx
  have hlim := hdiff.add (G_limit.comp hr)
  simp only [Function.comp_apply, sub_add_cancel, zero_add] at hlim
  have hcn : c ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr (by positivity))
    (sub_ne_zero.mpr (by intro h; have := congrArg Complex.im h; norm_num at this))
  have ha : ∀ x, integral x = G (c * x) / c := fun x => by rw [ray]; field_simp
  simp_rw [show integral = _ from funext ha]
  convert hlim.div_const c using 1
  congr 1
  apply (eq_div_iff hcn).mpr
  dsimp [c]
  push_cast
  linear_combination (-(√π : ℂ) / 4) * I_sq

/-- Oddness fixes the limits on the negative real axis. -/
theorem integral_neg (x : ℝ) : integral (-x) = -integral x := by
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := x)
    (fun t : ℝ => Complex.exp (((π / 2 * t ^ 2 : ℝ) : ℂ) * I))
  simpa [integral, intervalIntegral.integral_symm (-x) 0] using h.symm

@[simp] theorem integral_zero : integral 0 = 0 := by simp [integral]

/-- Both real Fresnel integrals tend to one half at positive infinity. -/
theorem tendsto_cosine_sine_atTop :
    Tendsto cosine atTop (𝓝 (1 / 2)) ∧ Tendsto sine atTop (𝓝 (1 / 2)) := by
  constructor
  · change Tendsto (fun x => (integral x).re) atTop _
    simpa [Function.comp_def, Complex.div_ofNat_re] using
      Complex.continuous_re.continuousAt.tendsto.comp tendsto_integral_atTop
  · change Tendsto (fun x => (integral x).im) atTop _
    simpa [Function.comp_def, Complex.div_ofNat_im] using
      Complex.continuous_im.continuousAt.tendsto.comp tendsto_integral_atTop

/-- The Fresnel primitive has the oscillatory integrand as its derivative. -/
theorem hasDerivAt_integral (x : ℝ) :
    HasDerivAt integral (Complex.exp (((π / 2 * x ^ 2 : ℝ) : ℂ) * I)) x :=
  intervalIntegral.integral_hasDerivAt_right
    (Continuous.intervalIntegrable (by fun_prop) ..)
    (Continuous.stronglyMeasurable (by fun_prop)).aestronglyMeasurable.stronglyMeasurableAtFilter
    (Continuous.continuousAt (by fun_prop))

end ProjectAinos.SpecialFunctions.Fresnel
