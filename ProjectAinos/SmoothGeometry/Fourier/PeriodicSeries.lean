/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic

/-! # Absolute Fourier convergence for smooth functions of period 2π -/

@[expose] public section
noncomputable section

open Complex Set Filter MeasureTheory Function
open scoped Real ContDiff Topology

namespace ProjectAinos.SmoothGeometry.Fourier.PeriodicSeries

/-- Complex Fourier coefficient on one symmetric period. -/
def coefficient (f : ℝ → ℂ) (n : ℤ) : ℂ :=
  (∫ t in -π..π, exp (-((n : ℂ) * t) * I) * f t) / (2 * π)

/-- Fourier coefficients of continuous signals respect complex linear combinations. -/
theorem coefficient_linear {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (a b : ℂ) (n : ℤ) : coefficient (fun t => a * f t + b * g t) n =
      a * coefficient f n + b * coefficient g n := by
  let w (t : ℝ) := exp (-((n : ℂ) * t) * I)
  have hw : Continuous w := by unfold w; fun_prop
  have he (t : ℝ) : w t * (a * f t + b * g t) = a * (w t * f t) + b * (w t * g t) := by ring
  change (∫ t in -π..π, w t * (a * f t + b * g t)) / _ = _
  simp_rw [he]
  have hfi : IntervalIntegrable (fun t => w t * f t) volume (-π) π :=
    (hw.mul hf).intervalIntegrable ..
  have hgi : IntervalIntegrable (fun t => w t * g t) volume (-π) π :=
    (hw.mul hg).intervalIntegrable ..
  rw [intervalIntegral.integral_add (hfi.const_mul a) (hgi.const_mul b),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul]
  unfold coefficient w
  ring

/-- A constant may be taken outside a Fourier coefficient. -/
theorem coefficient_const_mul {f : ℝ → ℂ} (hf : Continuous f) (a : ℂ) (n : ℤ) :
    coefficient (fun t => a * f t) n = a * coefficient f n := by
  simpa using coefficient_linear hf hf a 0 n

private theorem hab : -π < π := by linarith [Real.pi_pos]

private theorem coeff_eq (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn hab f n = coefficient f n := by
  rw [fourierCoeffOn_eq_integral, coefficient, real_smul]
  simp only [smul_eq_mul, fourier_coe_apply, Int.cast_neg, ofReal_sub, ofReal_neg,
    ofReal_div, ofReal_one]
  have h (t : ℝ) : 2 * (π : ℂ) * I * -(n : ℂ) * t / (π - -π) = -((n : ℂ) * t) * I := by
    field_simp [Real.pi_ne_zero]
    ring
  simp_rw [h]
  ring

private theorem coeff_bound (f : ℝ → ℂ) (hc : Continuous f) :
    ∃ M : ℝ, ∀ n, ‖coefficient f n‖ ≤ M := by
  obtain ⟨M,hM⟩ := (isCompact_uIcc (a := -π) (b := π)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun n => ?_⟩
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => exp (-((n : ℂ) * t) * I) * f t) (a := -π) (b := π) (C := M) (by
      intro t ht
      simpa [norm_mul, norm_exp] using hM t (uIoc_subset_uIcc ht))
  rw [coefficient, norm_div, norm_mul, norm_ofNat, norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, div_le_iff₀ (by positivity)]
  rw [abs_of_pos (sub_pos.mpr hab)] at h
  simpa [two_mul] using h

private theorem deriv_period {f : ℝ → ℂ} (hp : Periodic f (2 * π)) :
    Periodic (deriv f) (2 * π) := by
  intro t
  have he : (fun x => f (x + 2 * π)) = f := funext hp
  simpa only [deriv_comp_add_const] using congrFun (congrArg deriv he) t

/-- Integration by parts relates each nonzero Fourier coefficient to its derivative. -/
theorem coefficient_deriv {f : ℝ → ℂ} (hp : Periodic f (2 * π)) (hf : Differentiable ℝ f)
    (hd : Continuous (deriv f)) {n : ℤ} (hn : n ≠ 0) :
    coefficient f n = coefficient (deriv f) n / (I * n) := by
  have h := fourierCoeffOn_of_hasDerivAt hab hn (fun t _ => (hf t).hasDerivAt)
    (hd.intervalIntegrable ..)
  have he : f π = f (-π) := by simpa [two_mul, add_assoc] using hp (-π)
  rw [coeff_eq, coeff_eq, he, sub_self, mul_zero, zero_sub] at h
  rw [h, ofReal_neg]
  field_simp [Real.pi_ne_zero]
  ring

/-- A twice continuously differentiable periodic function has absolutely summable coefficients. -/
theorem summable {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hp : Periodic f (2 * π)) :
    Summable (coefficient f) := by
  have hd : ContDiff ℝ 1 (deriv f) := (hf.of_le (show 1 + 1 ≤ (2 : ℕ∞ω) by norm_num)).deriv'
  have hdd := hd.continuous_deriv le_rfl
  obtain ⟨M,hM⟩ := coeff_bound _ hdd
  apply Summable.of_norm_bounded_eventually ((Real.summable_one_div_int_pow.mpr
    (by norm_num : 1 < 2)).mul_left M)
  filter_upwards [eventually_cofinite_ne (0 : ℤ)] with n hn
  rw [coefficient_deriv hp (hf.differentiable (by norm_num)) hd.continuous hn,
    coefficient_deriv (deriv_period hp) (hd.differentiable one_ne_zero) hdd hn, norm_div,
    norm_div, norm_mul,
    norm_I, one_mul, div_div, ← sq, Complex.norm_intCast, sq_abs, mul_one_div]
  exact div_le_div_of_nonneg_right (hM n) (sq_nonneg _)

/-- The absolutely convergent series represents the original periodic function at every point. -/
theorem hasSum {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hp : Periodic f (2 * π)) (x : ℝ) :
    HasSum (fun n : ℤ => coefficient f n * exp (((n : ℂ) * x) * I)) (f x) := by
  let : Fact (0 < 2 * π) := ⟨by positivity⟩
  let g : C(AddCircle (2 * π), ℂ) := ⟨hp.lift, continuous_coinduced_dom.mpr hf.continuous⟩
  have hc (n : ℤ) : fourierCoeff g n = coefficient f n := by
    rw [fourierCoeff_eq_intervalIntegral _ _ (-π), coefficient, real_smul]
    simp only [smul_eq_mul, fourier_coe_apply, Int.cast_neg, ofReal_mul, ofReal_ofNat,
      ofReal_div, ofReal_one]
    rw [show -π + 2 * π = π by ring]
    have h (t : ℝ) : 2 * (π : ℂ) * I * -(n : ℂ) * t / (2 * π) = -((n : ℂ) * t) * I := by
      field_simp [Real.pi_ne_zero]
    simp_rw [h]
    change _ * (∫ t in -π..π, _ * hp.lift (t : AddCircle (2 * π))) = _
    simp_rw [Periodic.lift_coe]
    ring
  have hg : Summable (fourierCoeff g) := by
    rw [show fourierCoeff g = coefficient f from funext hc]
    exact summable hf hp
  have h := has_pointwise_sum_fourier_series_of_summable hg (x : AddCircle (2 * π))
  change HasSum _ (f x) at h
  apply h.congr_fun
  intro n
  rw [hc, smul_eq_mul, fourier_coe_apply]
  push_cast
  congr 2
  field_simp [Real.pi_ne_zero]

end ProjectAinos.SmoothGeometry.Fourier.PeriodicSeries
