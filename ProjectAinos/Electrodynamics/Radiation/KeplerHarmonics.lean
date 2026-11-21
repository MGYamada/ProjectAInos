/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Radiation.EccentricOrbit
import Mathlib.Tactic

/-! # Bessel coefficients of the Kepler radiation harmonics (ED §70)

Rescale the symmetric Fourier period from mean anomaly to physical time. Two integrations by
parts convert the Cartesian position coefficients into the acceleration coefficients used in the
existing Parseval formula for radiation.
-/

@[expose] public section
noncomputable section

open Real Complex Set MeasureTheory
open ProjectAinos.SpecialFunctions.Kapteyn
open ProjectAinos.SmoothGeometry.Fourier.PeriodicSeries
open scoped Real

namespace ProjectAinos.Electrodynamics.Radiation.CoulombRadiation

private theorem scale {f : ℝ → ℝ} (hp : Function.Periodic f (2 * π)) {ω T : ℝ}
    (hω : 0 < ω) (hT : 0 < T) (hωT : ω * T = 2 * π) (n : ℤ) :
    harmonicCoeff (fun t => f (ω * t)) T n = coefficient (fun M => (f M : ℂ)) n := by
  let g (M : ℝ) := exp (-((n : ℂ) * M) * I) * (f M : ℂ)
  have hs : 2 * (π : ℂ) / T = ω := by
    apply (div_eq_iff (ofReal_ne_zero.mpr hT.ne')).mpr
    exact_mod_cast hωT.symm
  have phase (t : ℝ) : -(2 * (π : ℂ) * I * n * t / T) = -((n : ℂ) * ↑(ω * t)) * I := by
    push_cast
    rw [← hs]
    ring
  have hper : Function.Periodic g (2 * π) := by
    intro t
    simp only [g, hp t, ofReal_add, mul_add, neg_add_rev, add_mul, Complex.exp_add]
    rw [show -((n : ℂ) * ↑(2 * π)) * I = n * -(2 * π * I) by push_cast; ring,
      Complex.exp_int_mul, Complex.exp_neg, exp_two_pi_mul_I, inv_one, one_zpow, one_mul]
  have ht := hper.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at ht
  unfold harmonicCoeff
  simp_rw [phase]
  change (T : ℂ)⁻¹ * (∫ t in 0..T, g (ω * t)) = _
  rw [intervalIntegral.integral_comp_mul_left _ hω.ne', mul_zero, hωT, ht, real_smul, ofReal_inv]
  change _ = (∫ t in -π..π, g t) / (2 * π)
  have hh := (div_eq_iff (ofReal_ne_zero.mpr hT.ne')).mp hs
  rw [hh]
  field_simp [ofReal_ne_zero.mpr hT.ne', ofReal_ne_zero.mpr hω.ne']

private theorem diff {f d : ℝ → ℝ} {T : ℝ} (hT : 0 < T) (hend : f T = f 0)
    (hd : ∀ t, HasDerivAt f (d t) t) (hc : Continuous d) {n : ℤ} (hn : n ≠ 0) :
    harmonicCoeff d T n = (2 * π * I * n / T) * harmonicCoeff f T n := by
  rw [harmonicCoeff_eq_fourierCoeffOn _ hT, harmonicCoeff_eq_fourierCoeffOn _ hT]
  have h := fourierCoeffOn_of_hasDerivAt hT hn (fun t _ => (hd t).ofReal_comp)
    ((Complex.continuous_ofReal.comp hc).intervalIntegrable ..)
  rw [h, hend]
  simp only [sub_self, mul_zero, zero_sub, ofReal_zero, sub_zero]
  field_simp [hn, Complex.I_ne_zero, Real.pi_ne_zero, ofReal_ne_zero.mpr hT.ne']

private theorem constant_zero (n : ℤ) (hn : n ≠ 0) :
    coefficient (fun _ : ℝ => (1 : ℂ)) n = 0 := by
  rw [coefficient_deriv (f := fun _ : ℝ => (1 : ℂ)) (fun _ => rfl) (differentiable_const _)
    (by simp; exact continuous_const) hn]
  simp [coefficient]

private def major (A e M : ℝ) := A * (Real.cos (eccentricAnomaly e M) - e)
private def minor (A e M : ℝ) := A * √(1-e^2) * Real.sin (eccentricAnomaly e M)

private theorem major_coef {e : ℝ} (he : |e| < 1) (A : ℝ) (n : ℤ) (hn : n ≠ 0) :
    coefficient (fun M => (major A e M : ℂ)) n =
      A * deriv (besselJ n) ((n : ℝ) * e) / n := by
  have hc : Continuous (fun M => (Real.cos (eccentricAnomaly e M) : ℂ)) :=
    continuous_ofReal.comp (Real.continuous_cos.comp (contDiff_eccentric he).continuous)
  have h := coefficient_linear hc (continuous_const (y := (1 : ℂ))) (A : ℂ) (-(A * e)) n
  have eq (t : ℝ) : (major A e t : ℂ) =
      A * (Real.cos (eccentricAnomaly e t) : ℂ) + -((A : ℂ) * e) * 1 := by
    unfold major
    push_cast
    ring
  simp_rw [eq]
  rw [h, coefficient_cos he n hn, constant_zero n hn]
  ring

private theorem minor_coef {e : ℝ} (he : |e| < 1) (he₀ : e ≠ 0) (A : ℝ) (n : ℤ) (hn : n ≠ 0) :
    coefficient (fun M => (minor A e M : ℂ)) n =
      A * ↑(√(1-e^2)) * besselJ n ((n : ℝ) * e) / (I * n * e) := by
  have hc : Continuous (fun M => (Real.sin (eccentricAnomaly e M) : ℂ)) :=
    continuous_ofReal.comp (Real.continuous_sin.comp (contDiff_eccentric he).continuous)
  have h := ProjectAinos.SpecialFunctions.Bessel.recurrence_int n ((n : ℝ) * e)
  have eq (t : ℝ) : (minor A e t : ℂ) =
      ((A : ℂ) * ↑(√(1-e^2))) * ↑(Real.sin (eccentricAnomaly e t)) := by
    unfold minor
    push_cast
    rfl
  simp_rw [eq]
  rw [coefficient_const_mul hc, coefficient_sin he n hn]
  have hn' : (n : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have he' : (e : ℂ) ≠ 0 := ofReal_ne_zero.mpr he₀
  have hsum : besselJ (n - 1 : ℤ) ((n : ℝ) * e) + besselJ (n + 1 : ℤ) ((n : ℝ) * e) =
      2 * besselJ n ((n : ℝ) * e) / e := by
    apply (eq_div_iff he').mpr
    apply mul_left_cancel₀ hn'
    push_cast at h ⊢
    linear_combination h
  rw [hsum]
  ring

/-- Nonzero harmonics of the acceleration of the original Kepler ellipse. These are the same
two Cartesian coefficients used in the dipole-power Parseval identity of §70. -/
theorem keplerAcceleration_harmonics {k ℓ e : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) (h₀ : 0 < e)
    (h₁ : e < 1) (n : ℤ) (hn : n ≠ 0) :
    harmonicCoeff (fun t => (keplerAcceleration k ℓ e t).1) (keplerPeriod k ℓ e) n =
      -(semiMajor k ℓ e * (meanMotion k ℓ e) ^ 2 : ℝ) * (n : ℂ) *
        deriv (besselJ n) ((n : ℝ) * e) ∧
    harmonicCoeff (fun t => (keplerAcceleration k ℓ e t).2) (keplerPeriod k ℓ e) n =
      I * ↑(semiMajor k ℓ e * √(1-e^2) * (meanMotion k ℓ e) ^ 2) * n *
        besselJ n ((n : ℝ) * e) / e := by
  let T := keplerPeriod k ℓ e
  let ω := meanMotion k ℓ e
  let A := semiMajor k ℓ e
  let p := keplerPosition k ℓ e
  let v := keplerVelocity k ℓ e
  let a := keplerAcceleration k ℓ e
  have he : |e| < 1 := by rwa [abs_of_pos h₀]
  have hq : 0 < 1 - e ^ 2 := by nlinarith
  have hω : 0 < ω := by dsimp [ω, meanMotion]; positivity
  have hωT : ω * T = 2 * π := meanMotion_mul_period hk hℓ h₀.le h₁
  have hT : 0 < T := pos_of_mul_pos_right (hωT ▸ (by positivity : 0 < 2 * π)) hω.le
  have dP (t : ℝ) : HasDerivAt p (v t) t := hasDerivAt_keplerPosition hk hℓ h₀.le h₁ t
  have dV (t : ℝ) : HasDerivAt v (a t) t := hasDerivAt_keplerVelocity hk hℓ h₀.le h₁ t
  have cv : Continuous v := continuous_iff_continuousAt.mpr fun t => (dV t).continuousAt
  have ca := continuous_keplerAcceleration hk hℓ h₀.le h₁
  have pp : p T = p 0 := by
    simp [p, T, keplerPosition, keplerRadius, keplerAngle_keplerPeriod hk hℓ h₀.le h₁,
      keplerAngle_zero]
  have pv : v T = v 0 := by
    simp [v, T, keplerVelocity, keplerAngle_keplerPeriod hk hℓ h₀.le h₁, keplerAngle_zero]
  have px : (fun t => (p t).1) = fun t => major A e (ω*t) :=
    funext fun t => congrArg Prod.fst (keplerPosition_eccentric hk hℓ h₀.le h₁ t)
  have py : (fun t => (p t).2) = fun t => minor A e (ω*t) :=
    funext fun t => congrArg Prod.snd (keplerPosition_eccentric hk hℓ h₀.le h₁ t)
  have mx : Function.Periodic (major A e) (2 * π) := fun M => by
    simp [major, eccentric_add_period he]
  have my : Function.Periodic (minor A e) (2 * π) := fun M => by
    simp [minor, eccentric_add_period he]
  have hw : 2 * (π : ℂ) / T = ω := by
    apply (div_eq_iff (ofReal_ne_zero.mpr hT.ne')).mpr
    exact_mod_cast hωT.symm
  have hfreq : 2 * (π : ℂ) * I * n / T = ω * I * n := by rw [← hw]; ring
  have hx := diff hT (congrArg Prod.fst pp) (fun t => (dP t).fst) cv.fst hn
  have hy := diff hT (congrArg Prod.snd pp) (fun t => (dP t).snd) cv.snd hn
  rw [px, scale mx hω hT hωT, major_coef he A n hn, hfreq] at hx
  rw [py, scale my hω hT hωT, minor_coef he h₀.ne' A n hn, hfreq] at hy
  have ax := diff hT (congrArg Prod.fst pv) (fun t => (dV t).fst) ca.fst hn
  have ay := diff hT (congrArg Prod.snd pv) (fun t => (dV t).snd) ca.snd hn
  rw [hx, hfreq] at ax
  rw [hy, hfreq] at ay
  change harmonicCoeff (fun t => (a t).1) T n = _ ∧ harmonicCoeff (fun t => (a t).2) T n = _
  constructor
  · rw [ax]
    change _ = -(↑(A * ω ^ 2) : ℂ) * (n : ℂ) * _
    push_cast
    field_simp [hn]
    ring_nf
    simp [I_sq]
  · rw [ay]
    change _ = I * ↑(A * √(1-e^2) * ω ^ 2) * n * _ / e
    push_cast
    field_simp [hn, h₀.ne', I_ne_zero]

end ProjectAinos.Electrodynamics.Radiation.CoulombRadiation
