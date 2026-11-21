/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.BesselGenerating
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Bessel's integral for integer order

On the unit circle the Laurent generating series is the Fourier series of the exponential
of a sine. Integrating against a character selects the matching coefficient. Pairing the
two halves of the circle gives the real cosine integral.
-/

@[expose] public section
noncomputable section

open Complex MeasureTheory Real
namespace ProjectAinos.SpecialFunctions.Bessel

private def wave (k : ℤ) (t : ℝ) : ℂ := Complex.exp ((k : ℂ) * (t * I))

private theorem wave_norm (k : ℤ) (t : ℝ) : ‖wave k t‖ = 1 := by
  simp [wave, Complex.norm_exp]

/-- The sine form of the Jacobi–Anger expansion, for complex amplitude and real angle. -/
theorem hasSum_jacobiAnger (z : ℂ) (t : ℝ) :
    HasSum (fun k : ℤ => besselJ k z * Complex.exp ((k : ℂ) * (t * I)))
      (Complex.exp (z * Real.sin t * I)) := by
  have h := hasSum_generating z (w := Complex.exp (t * I)) (Complex.exp_ne_zero _)
  have he : Complex.exp (t * I) - (Complex.exp (t * I))⁻¹ = 2 * Real.sin t * I := by
    rw [← Complex.exp_neg, ← neg_mul, Complex.exp_mul_I, Complex.exp_mul_I]
    simp [← Complex.ofReal_sin]
    ring
  rw [he, show z / 2 * (2 * Real.sin t * I) = z * Real.sin t * I by ring] at h
  simpa only [Complex.exp_int_mul] using h

private theorem integral_wave (k : ℤ) :
    ∫ t in -π..π, wave k t = if k = 0 then 2 * (π : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [wave]
    ring
  simp only [hk, ↓reduceIte]
  have he (t : ℝ) : wave k t = Complex.exp (((k : ℂ) * I) * t) := by
    unfold wave; congr 1; ring
  simp_rw [he]
  rw [integral_exp_mul_complex (mul_ne_zero (by exact_mod_cast hk) I_ne_zero)]
  have h₁ : (k : ℂ) * I * π = k * ((π : ℂ) * I) := by ring
  have h₂ : (k : ℂ) * I * ↑(-π) = k * (-((π : ℂ) * I)) := by push_cast; ring
  rw [h₁, h₂, Complex.exp_int_mul, Complex.exp_int_mul, exp_pi_mul_I, exp_neg_pi_mul_I,
    sub_self, zero_div]

private def phase (k : ℤ) (x t : ℝ) : ℝ := k * t - x * Real.sin t

private theorem fourier (k : ℤ) (x : ℝ) :
    (∫ t in -π..π, Complex.exp (-(phase k x t : ℂ) * I)) = 2 * π * besselJ k x := by
  have hlim (t : ℝ) :
      HasSum (fun j : ℤ => besselJ j x * wave (j - k) t)
        (Complex.exp (-(phase k x t : ℂ) * I)) := by
    have h := (hasSum_jacobiAnger x t).mul_right (wave (-k) t)
    have he : (x : ℂ) * Real.sin t * I + (-k : ℤ) * (t * I) = -(phase k x t : ℂ) * I := by
      unfold phase; push_cast; ring
    rw [wave, ← Complex.exp_add, he] at h
    apply h.congr_fun
    intro j
    rw [wave, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hs : Summable (fun j : ℤ => ‖besselJ j (x : ℂ)‖) := by
    simpa using (hasSum_generating (x : ℂ) (w := 1) one_ne_zero).summable.norm
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (a := -π) (b := π)
    (μ := volume) (F := fun (j : ℤ) t => besselJ j x * wave (j - k) t)
    (fun j _ => ‖besselJ j (x : ℂ)‖)
    (fun _ => Continuous.aestronglyMeasurable (by unfold wave; fun_prop))
    (fun j => ae_of_all _ fun t _ => by simp [wave_norm])
    (ae_of_all _ fun _ _ => hs) intervalIntegrable_const (ae_of_all _ fun t _ => hlim t)
  rw [← h.tsum_eq]
  simp_rw [intervalIntegral.integral_const_mul, integral_wave, sub_eq_zero, mul_ite, mul_zero]
  simp [mul_comm]

/-- Fourier integral on one symmetric period for every integer order and real argument. -/
theorem integral_exponential (k : ℤ) (x : ℝ) :
    (∫ t in -π..π, exp (-(((k : ℝ) * t - x * Real.sin t : ℝ) : ℂ) * I)) =
      2 * π * besselJ k x := fourier k x

/-- Bessel's real integral representation for every integer order and real argument. -/
theorem integral (k : ℤ) (x : ℝ) :
    besselJ k (x : ℂ) =
      ((1 / π * ∫ t in 0..π, Real.cos ((k : ℝ) * t - x * Real.sin t) : ℝ) : ℂ) := by
  let g (t : ℝ) := Complex.exp (-(phase k x t : ℂ) * I)
  have hc : Continuous g := by unfold g phase; fun_prop
  have hsym (t : ℝ) : g (-t) + g t = 2 * (Real.cos (phase k x t) : ℂ) := by
    have ht : phase k x (-t) = -phase k x t := by simp [phase]; ring
    simp only [g, ht, Complex.ofReal_neg, neg_neg, Complex.exp_mul_I, Complex.cos_neg,
      Complex.sin_neg, Complex.ofReal_cos]
    ring
  have h := fourier k x
  change (∫ t in -π..π, g t) = _ at h
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-π) 0)
    (hc.intervalIntegrable 0 π), ← show (∫ t in 0..π, g (-t)) = ∫ t in -π..0, g t by
      simp,
    ← intervalIntegral.integral_add (f := fun t => g (-t)) (g := g) (a := 0) (b := π)
      ((hc.comp continuous_neg).intervalIntegrable ..) (hc.intervalIntegrable ..)] at h
  simp_rw [hsym, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal] at h
  change besselJ k (x : ℂ) = ↑(1 / π * ∫ t in 0..π, Real.cos (phase k x t))
  push_cast
  field_simp at h ⊢
  linear_combination -h

/-- Integer orders have the adjacent-order derivative identity on the whole complex plane. -/
theorem twice_deriv_int (k : ℤ) (z : ℂ) :
    2 * deriv (besselJ k) z = besselJ (k - 1 : ℤ) z - besselJ (k + 1 : ℤ) z := by
  have hl : AnalyticOnNhd ℂ (fun z => 2 * deriv (besselJ k) z) Set.univ :=
    fun z _ => analyticAt_const.mul (analyticAt_besselJ_int k z).deriv
  have hr : AnalyticOnNhd ℂ (fun z => besselJ (k - 1 : ℤ) z - besselJ (k + 1 : ℤ) z) Set.univ :=
    fun z _ => (analyticAt_besselJ_int _ z).sub (analyticAt_besselJ_int _ z)
  have h := hl.eq_of_eventuallyEq hr (z₀ := 1) (Filter.eventually_of_mem
    (isOpen_slitPlane.mem_nhds (by simp [mem_slitPlane_iff])) fun z hz => by
      simpa using twice_deriv k z hz)
  exact congrFun h z

/-- The polynomial form of the integer-order recurrence holds on the whole complex plane. -/
theorem recurrence_int (k : ℤ) (z : ℂ) : z * (besselJ (k - 1 : ℤ) z + besselJ (k + 1 : ℤ) z) =
    2 * k * besselJ k z := by
  have hl : AnalyticOnNhd ℂ (fun w => w * (besselJ (k - 1 : ℤ) w + besselJ (k + 1 : ℤ) w))
      Set.univ := fun w _ => analyticAt_id.mul ((analyticAt_besselJ_int _ w).add
        (analyticAt_besselJ_int _ w))
  have hr : AnalyticOnNhd ℂ (fun w => 2 * k * besselJ k w) Set.univ :=
    fun w _ => analyticAt_const.mul (analyticAt_besselJ_int _ w)
  have h := hl.eq_of_eventuallyEq hr (z₀ := 1) (Filter.eventually_of_mem
    (isOpen_slitPlane.mem_nhds (by simp [mem_slitPlane_iff])) fun w hw => by
      change w * _ = _
      rw [show besselJ (↑(k - 1 : ℤ)) w + besselJ (↑(k + 1 : ℤ)) w =
        2 * k / w * besselJ k w by simpa using recurrence k w hw]
      field_simp [slitPlane_ne_zero hw])
  exact congrFun h z

/-- The derivative integral also holds at the origin and on the negative real axis. -/
theorem deriv_integral (k : ℤ) (x : ℝ) :
    deriv (besselJ k) (x : ℂ) = ((1 / π * ∫ t in 0..π,
      Real.sin ((k : ℝ) * t - x * Real.sin t) * Real.sin t : ℝ) : ℂ) := by
  have he := twice_deriv_int k (x : ℂ)
  rw [integral (k - 1), integral (k + 1), ← Complex.ofReal_sub, ← mul_sub,
    ← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) ..)
      (Continuous.intervalIntegrable (by fun_prop) ..)] at he
  have ht (t : ℝ) : Real.cos (↑(k - 1 : ℤ) * t - x * Real.sin t) -
      Real.cos (↑(k + 1 : ℤ) * t - x * Real.sin t) =
      2 * (Real.sin ((k : ℝ) * t - x * Real.sin t) * Real.sin t) := by
    push_cast
    rw [show ((k : ℝ) - 1) * t - x * Real.sin t = ((k : ℝ) * t - x * Real.sin t) - t by ring,
      show ((k : ℝ) + 1) * t - x * Real.sin t = ((k : ℝ) * t - x * Real.sin t) + t by ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp_rw [ht, intervalIntegral.integral_const_mul] at he
  push_cast at he ⊢
  linear_combination he / 2

end ProjectAinos.SpecialFunctions.Bessel
