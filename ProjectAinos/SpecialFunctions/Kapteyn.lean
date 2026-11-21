/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.BesselIntegral
public import ProjectAinos.SmoothGeometry.ODE.ScalarFlow
public import ProjectAinos.SmoothGeometry.Fourier.PeriodicSeries
import Mathlib.Tactic

/-! # Kapteyn series and Kepler's inverse

Kepler's map E ↦ E − e sin E has a smooth global inverse when |e| < 1. Substitution in the
Fourier integral of its derivative cancels the Jacobian and gives Jₙ(ne) in each integer mode.
-/

@[expose] public section
noncomputable section

open Real Filter Set
open scoped ContDiff

namespace ProjectAinos.SpecialFunctions.Kapteyn

open ProjectAinos.SmoothGeometry.NonlinearODE
open ProjectAinos.SmoothGeometry.Fourier.PeriodicSeries

/-- Mean anomaly of an elliptic orbit as a function of eccentric anomaly. -/
def meanAnomaly (e E : ℝ) : ℝ := E - e * sin E

private def speed (e E : ℝ) : ℝ := (1 - e * cos E)⁻¹

/-- Global eccentric anomaly as a function of mean anomaly for |e| < 1. -/
def eccentricAnomaly (e M : ℝ) : ℝ := flow (fun E => (1 - e * cos E)⁻¹) (M, 0)

private theorem lower (e t : ℝ) : 1 - |e| ≤ 1 - e * cos t := by
  have h := mul_le_mul_of_nonneg_left (abs_cos_le_one t) (abs_nonneg e)
  rw [← abs_mul, mul_one] at h
  linarith [le_abs_self (e * cos t)]

private theorem pos {e : ℝ} (he : |e| < 1) (t : ℝ) : 0 < speed e t :=
  inv_pos.mpr (lt_of_lt_of_le (sub_pos.mpr he) (lower e t))

private theorem smooth {e : ℝ} (he : |e| < 1) : ContDiff ℝ ∞ (speed e) :=
  (contDiff_const.sub (contDiff_const.mul Real.contDiff_cos)).inv
    fun t => (lt_of_lt_of_le (sub_pos.mpr he) (lower e t)).ne'

private theorem bound {e : ℝ} (he : |e| < 1) (t : ℝ) : |speed e t| ≤ (1 - |e|)⁻¹ := by
  rw [abs_of_pos (pos he t)]
  exact inv_anti₀ (sub_pos.mpr he) (lower e t)

private theorem time (e E : ℝ) : scalarTime (speed e) E = meanAnomaly e E := by
  unfold scalarTime speed meanAnomaly
  simp only [inv_inv]
  have h (t : ℝ) : HasDerivAt (fun u => u - e * sin u) (1 - e * cos t) t :=
    (hasDerivAt_id t).sub ((Real.hasDerivAt_sin t).const_mul e)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => h t)
    (Continuous.intervalIntegrable (by fun_prop) ..)]
  simp

/-- Kepler's equation holds at every mean anomaly. -/
theorem mean_eccentric {e : ℝ} (he : |e| < 1) (M : ℝ) :
    meanAnomaly e (eccentricAnomaly e M) = M := by
  rw [← time]
  exact scalarTime_flow (smooth he) (pos he) (bound he) _

/-- The eccentric anomaly is the inverse in the other direction as well. -/
theorem eccentric_mean {e : ℝ} (he : |e| < 1) (E : ℝ) :
    eccentricAnomaly e (meanAnomaly e E) = E := by
  rw [← time]
  exact flow_scalarTime (smooth he) (pos he) (bound he) _

/-- The eccentric anomaly advances by 2π in one mean-anomaly period. -/
theorem eccentric_add_period {e : ℝ} (he : |e| < 1) (M : ℝ) :
    eccentricAnomaly e (M + 2 * π) = eccentricAnomaly e M + 2 * π := by
  have hp (x : ℝ) : speed e (x + 2 * π) = speed e x := by simp [speed]
  have h := flow_add_scalarTime_of_periodic (smooth he) (pos he) (bound he) hp M
  change flow (speed e) (M + 2 * π, 0) = flow (speed e) (M, 0) + 2 * π
  simpa only [time, meanAnomaly, Real.sin_two_pi, mul_zero, sub_zero] using h

/-- Smoothness of the inverse, including the apsides. -/
theorem contDiff_eccentric {e : ℝ} (he : |e| < 1) : ContDiff ℝ ∞ (eccentricAnomaly e) := by
  have hf : ContDiff ℝ ∞ (flow (speed e)) :=
    contDiff_iff_contDiffAt.mpr fun p => contDiffAt_flow (smooth he) (by
      rw [flowDomain_eq_univ_of_abs_le (smooth he) (bound he)]
      exact mem_univ _)
  exact hf.comp (contDiff_id.prodMk contDiff_const)

/-- The inverse Jacobian of Kepler's map. -/
theorem hasDerivAt_eccentric {e : ℝ} (he : |e| < 1) (M : ℝ) :
    HasDerivAt (eccentricAnomaly e) ((1 - e * cos (eccentricAnomaly e M))⁻¹) M :=
  hasDerivAt_flow_zero (smooth he) (bound he) M

private def density (e M : ℝ) : ℂ := speed e (eccentricAnomaly e M)

/-- The oscillating eccentric-anomaly mode used in Fourier analysis of a Kepler orbit. -/
def mode (e : ℝ) (m : ℤ) (M : ℝ) : ℂ :=
  Complex.exp (((m : ℂ) * eccentricAnomaly e M) * Complex.I)

private theorem smooth_mode {e : ℝ} (he : |e| < 1) (m : ℤ) : ContDiff ℝ ∞ (mode e m) := by
  have hc := Complex.ofRealCLM.contDiff.comp (contDiff_eccentric he)
  unfold mode
  exact Complex.contDiff_exp.comp ((contDiff_const.mul hc).mul contDiff_const)

private theorem periodic_mode {e : ℝ} (he : |e| < 1) (m : ℤ) :
    Function.Periodic (mode e m) (2 * π) := by
  intro t
  unfold mode
  rw [eccentric_add_period he, Complex.ofReal_add, mul_add, add_mul, Complex.exp_add]
  have h : (m : ℂ) * ↑(2 * π) * Complex.I = m * (2 * π * Complex.I) := by push_cast; ring
  rw [h, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow, mul_one]

private theorem coef {e : ℝ} (he : |e| < 1) (m n : ℤ) :
    coefficient (fun t => density e t * mode e m t) n =
      Complex.besselJ (n - m : ℤ) ((n : ℝ) * e) := by
  let g (M : ℝ) := Complex.exp (-((n : ℂ) * M) * Complex.I) * (density e M * mode e m M)
  have dg (E : ℝ) : HasDerivAt (meanAnomaly e) (1 - e * cos E) E :=
    (hasDerivAt_id E).sub ((Real.hasDerivAt_sin E).const_mul e)
  have cg : Continuous g := by
    unfold g density
    exact Continuous.mul (by fun_prop) ((Complex.continuous_ofReal.comp
      ((smooth he).comp (contDiff_eccentric he)).continuous).mul (smooth_mode he m).continuous)
  have h := intervalIntegral.integral_deriv_smul_comp (a := -π) (b := π) (g := g)
    (fun t _ => dg t) (fun _ _ => Continuous.continuousWithinAt (by fun_prop)) cg
  have ha : meanAnomaly e (-π) = -π := by simp [meanAnomaly]
  have hb : meanAnomaly e π = π := by simp [meanAnomaly]
  rw [ha, hb] at h
  have hsub (E : ℝ) : (1 - e * cos E) • g (meanAnomaly e E) =
      Complex.exp (-((((n - m : ℤ) : ℝ) * E - ((n : ℝ) * e) * sin E : ℝ) : ℂ) * Complex.I) := by
    simp only [g, density, mode, eccentric_mean he, speed, Complex.real_smul, Complex.ofReal_inv]
    have hn : ((1 - e * cos E : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (lt_of_lt_of_le (sub_pos.mpr he) (lower e E)).ne'
    rw [mul_left_comm, ← mul_assoc (↑(1 - e * cos E) : ℂ), mul_inv_cancel₀ hn, one_mul,
      ← Complex.exp_add]
    congr 1
    unfold meanAnomaly
    push_cast
    ring
  simp_rw [Function.comp_apply, hsub] at h
  rw [Bessel.integral_exponential] at h
  change (∫ t in -π..π, g t) / _ = _
  rw [← h]
  field_simp [Real.pi_ne_zero]
  push_cast
  ring

/-- The shifted Kapteyn coefficients are Jₙ₋ₘ(ne), including zero eccentricity. -/
theorem coefficient_mode_velocity {e : ℝ} (he : |e| < 1) (m n : ℤ) :
    coefficient (fun M => ((deriv (eccentricAnomaly e) M : ℝ) : ℂ) * mode e m M) n =
      Complex.besselJ (n - m : ℤ) ((n : ℝ) * e) := by
  simpa only [(hasDerivAt_eccentric he _).deriv, density, speed] using coef he m n

/-- The full shifted Kapteyn series represents each eccentric-anomaly mode times its velocity. -/
theorem hasSum_mode_velocity {e : ℝ} (he : |e| < 1) (m : ℤ) (M : ℝ) :
    HasSum (fun n : ℤ => Complex.besselJ (n - m : ℤ) ((n : ℝ) * e) *
      Complex.exp (((n : ℂ) * M) * Complex.I))
      (((deriv (eccentricAnomaly e) M : ℝ) : ℂ) * mode e m M) := by
  have hs : ContDiff ℝ 2 (density e) :=
    (Complex.ofRealCLM.contDiff.comp ((smooth he).comp (contDiff_eccentric he))).of_le (by simp)
  have hp : Function.Periodic (density e) (2 * π) := by
    intro t
    simp [density, eccentric_add_period he, speed]
  have h := hasSum (hs.mul ((smooth_mode he m).of_le (by simp))) (hp.mul (periodic_mode he m)) M
  change HasSum (fun n : ℤ => coefficient (fun t => density e t * mode e m t) n *
    Complex.exp (((n : ℂ) * M) * Complex.I)) (density e M * mode e m M) at h
  rw [(hasDerivAt_eccentric he M).deriv]
  change HasSum _ (density e M * mode e m M)
  simpa only [coef he] using h

private theorem deriv_mode {e : ℝ} (he : |e| < 1) (m : ℤ) (t : ℝ) :
    HasDerivAt (mode e m) ((Complex.I * m) * (density e t * mode e m t)) t := by
  have h := (((hasDerivAt_eccentric he t).ofReal_comp.const_mul (m : ℂ)).mul_const Complex.I).cexp
  convert h using 1
  · rfl
  change _ = mode e m t * ((m : ℂ) * density e t * Complex.I)
  ring

/-- Fourier coefficient of the eccentric-anomaly mode itself at nonzero harmonic number. -/
theorem coefficient_mode {e : ℝ} (he : |e| < 1) (m n : ℤ) (hn : n ≠ 0) :
    coefficient (mode e m) n = (m : ℂ) / n * Complex.besselJ (n - m : ℤ) ((n : ℝ) * e) := by
  have h := smooth_mode he m
  rw [coefficient_deriv (periodic_mode he m) (h.differentiable (by simp)) (h.continuous_deriv
    (by simp)) hn, show deriv (mode e m) = fun t => (Complex.I * m) * (density e t * mode e m t)
      from funext fun t => (deriv_mode he m t).deriv]
  have hc : Continuous (fun t => density e t * mode e m t) :=
    (Complex.continuous_ofReal.comp ((smooth he).comp (contDiff_eccentric he)).continuous).mul
      h.continuous
  rw [coefficient_const_mul hc, coef he]
  field_simp [Complex.I_ne_zero, hn]

private theorem modes (e M : ℝ) :
    mode e 1 M = ↑(cos (eccentricAnomaly e M)) + ↑(sin (eccentricAnomaly e M)) * Complex.I ∧
    mode e (-1) M = ↑(cos (eccentricAnomaly e M)) - ↑(sin (eccentricAnomaly e M)) * Complex.I := by
  simp [mode, Complex.exp_mul_I, sub_eq_add_neg]
  rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg, neg_mul]

/-- The major-axis cosine has Fourier coefficient J′ₙ(ne)/n at every nonzero integer mode. -/
theorem coefficient_cos {e : ℝ} (he : |e| < 1) (n : ℤ) (hn : n ≠ 0) :
    coefficient (fun M => (cos (eccentricAnomaly e M) : ℂ)) n =
      deriv (Complex.besselJ n) ((n : ℝ) * e) / n := by
  have h := coefficient_linear (smooth_mode he 1).continuous (smooth_mode he (-1)).continuous
    (1 / 2) (1 / 2) n
  have hf (t : ℝ) : 1 / 2 * mode e 1 t + 1 / 2 * mode e (-1) t = ↑(cos (eccentricAnomaly e t)) := by
    rw [(modes e t).1, (modes e t).2]
    ring
  simp_rw [hf, coefficient_mode he _ _ hn] at h
  rw [h]
  have hd := Bessel.twice_deriv_int n ((n : ℝ) * e)
  simp only [Int.cast_one, Int.cast_neg, sub_neg_eq_add]
  field_simp [hn]
  linear_combination -hd

/-- The minor-axis sine coefficient, in a form regular at the circular orbit. -/
theorem coefficient_sin {e : ℝ} (he : |e| < 1) (n : ℤ) (hn : n ≠ 0) :
    coefficient (fun M => (sin (eccentricAnomaly e M) : ℂ)) n =
      (Complex.besselJ (n - 1 : ℤ) ((n : ℝ) * e) +
        Complex.besselJ (n + 1 : ℤ) ((n : ℝ) * e)) / (2 * Complex.I * n) := by
  have h := coefficient_linear (smooth_mode he 1).continuous (smooth_mode he (-1)).continuous
    (-Complex.I / 2) (Complex.I / 2) n
  have hf (t : ℝ) : -Complex.I / 2 * mode e 1 t + Complex.I / 2 * mode e (-1) t =
      ↑(sin (eccentricAnomaly e t)) := by
    rw [(modes e t).1, (modes e t).2]
    linear_combination -(sin (eccentricAnomaly e t) : ℂ) * Complex.I_sq
  simp_rw [hf, coefficient_mode he _ _ hn] at h
  rw [h]
  simp only [Int.cast_one, Int.cast_neg, sub_neg_eq_add]
  field_simp [hn, Complex.I_ne_zero]
  ring_nf
  simp [Complex.I_sq]

/-- The Kapteyn series for the inverse Jacobian of Kepler's equation. The sum over all integers
converges absolutely for every real mean anomaly and every |e| < 1. -/
theorem hasSum_deriv_eccentric {e : ℝ} (he : |e| < 1) (M : ℝ) :
    HasSum (fun n : ℤ => Complex.besselJ n ((n : ℝ) * e) *
      Complex.exp (((n : ℂ) * M) * Complex.I)) ((deriv (eccentricAnomaly e) M : ℝ) : ℂ) := by
  simpa [mode] using hasSum_mode_velocity he 0 M

end ProjectAinos.SpecialFunctions.Kapteyn
