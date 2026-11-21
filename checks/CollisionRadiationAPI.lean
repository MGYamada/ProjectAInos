/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.Radiation.Collision
import ProjectAinos.Electrodynamics.Radiation.CoulombRadiation
import ProjectAinos.Electrodynamics.Radiation.CollisionSpectrum

/-! Public consumers of the radiation in collisions (Landau–Lifshitz §§64, 68–70): the dipole
acceleration along the Coulomb scattering orbit with its integrability, the total radiated energy
as a radial quadrature and in closed form, Plancherel's spectral distribution and the effective
radiation, the period average and the harmonic decomposition of the dipole power on a Kepler
ellipse, the spectrum of a hyperbolic collision as an integral over the orbit, and the far-zone
amplitude of a point charge with its time transform and its low-frequency limits. Default
elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/

noncomputable section


section Collision

open Set Filter MeasureTheory

open scoped Real Topology FourierTransform SchwartzMap ContDiff

namespace ProjectAinos.Electrodynamics.Radiation.Collision

open Mechanics.Scattering Mechanics.Scattering.Coulomb

example (w : ℝ × ℝ) :
    ℝ :=
  dipolePower w

example (w : ℝ × ℝ) :
    0 ≤ dipolePower w :=
  dipolePower_nonneg w

example (m₁ m₂ e₁ e₂ : ℝ) :
    ℝ :=
  reducedCharge m₁ m₂ e₁ e₂

example {m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (h : m₁ + m₂ ≠ 0) (e₁ e₂ : ℝ) (r : ℝ × ℝ) :
    e₁ • ((m₂ / (m₁ + m₂)) • r) + e₂ • ((-(m₁ / (m₁ + m₂))) • r) =
      reducedCharge m₁ m₂ e₁ e₂ • r :=
  dipole_eq_reducedCharge_smul h₁ h₂ h e₁ e₂ r

variable {a ρ vinf : ℝ}

example (a ρ vinf t : ℝ) :
    ℝ :=
  orbitRadius a ρ vinf t

example (a ρ vinf t : ℝ) :
    ℝ :=
  orbitAngle a ρ vinf t

example (a ρ : ℝ) :
    ℝ :=
  asymptoteAngle a ρ

example (a ρ vinf t : ℝ) :
    ℝ × ℝ :=
  acceleration a ρ vinf t

example (a ρ vinf t : ℝ) :
    closest a ρ ≤ orbitRadius a ρ vinf t :=
  closest_le_orbitRadius a ρ vinf t

example (hρ : 0 < ρ) (vinf t : ℝ) :
    0 < orbitRadius a ρ vinf t :=
  orbitRadius_pos hρ vinf t

example (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    orbitRadius a ρ vinf (-t) = orbitRadius a ρ vinf t :=
  orbitRadius_neg hρ hv t

example (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    orbitAngle a ρ vinf (-t) = -orbitAngle a ρ vinf t :=
  orbitAngle_neg hρ hv t

example (a ρ vinf : ℝ) :
    orbitAngle a ρ vinf 0 = 0 :=
  orbitAngle_zero a ρ vinf

example (hρ : 0 < ρ) (hv : 0 < vinf) :
    Continuous (orbitRadius a ρ vinf) :=
  continuous_orbitRadius hρ hv

example (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    HasDerivAt (orbitRadius a ρ vinf) (radialVelocity (factor a ρ vinf) (closest a ρ) t) t :=
  hasDerivAt_orbitRadius hρ hv t

example (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    HasDerivAt (orbitAngle a ρ vinf) (ρ * vinf / orbitRadius a ρ vinf t ^ 2) t :=
  hasDerivAt_orbitAngle hρ hv t

example (hρ : 0 < ρ) (hv : 0 < vinf) :
    Continuous (orbitAngle a ρ vinf) :=
  continuous_orbitAngle hρ hv

example (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (orbitAngle a ρ vinf) atTop (𝓝 (asymptoteAngle a ρ)) :=
  tendsto_orbitAngle_atTop hρ hv

example (hρ : 0 < ρ) (hv : 0 < vinf) :
    Tendsto (orbitAngle a ρ vinf) atBot (𝓝 (-asymptoteAngle a ρ)) :=
  tendsto_orbitAngle_atBot hρ hv

example (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    HasDerivAt (velocity (factor a ρ vinf) (closest a ρ) (ρ * vinf)) (acceleration a ρ vinf t) t :=
  hasDerivAt_velocity_coulomb a hρ hv t

example (hρ : 0 < ρ) (hv : 0 < vinf) :
    Continuous (acceleration a ρ vinf) :=
  continuous_acceleration hρ hv

example (e a ρ vinf t : ℝ) :
    dipolePower (e • acceleration a ρ vinf t) =
      2 / 3 * (4 * π)⁻¹ * (e * (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2)) ^ 2 :=
  dipolePower_smul_acceleration e a ρ vinf t

example {f : ℝ → ℝ} (hf : ∀ t, f (-t) = f t) (h : IntegrableOn f (Ioi 0)) :
    Integrable f ∧ ∫ t, f t = 2 * ∫ t in Ioi 0, f t :=
  integrable_and_integral_of_even hf h

example (hρ : 0 < ρ) (hv : 0 < vinf) :
    IntegrableOn (fun t => ρ * vinf / orbitRadius a ρ vinf t ^ 2) (Ioi 0) ∧
      ∫ t in Ioi 0, ρ * vinf / orbitRadius a ρ vinf t ^ 2 = asymptoteAngle a ρ :=
  integrableOn_Ioi_angleRate hρ hv

example (hρ : 0 < ρ) (hv : 0 < vinf) :
    Integrable (fun t => (orbitRadius a ρ vinf t ^ 2)⁻¹) ∧
      ∫ t, (orbitRadius a ρ vinf t ^ 2)⁻¹ = 2 * asymptoteAngle a ρ / (ρ * vinf) :=
  integral_inv_orbitRadius_sq hρ hv

example (hρ : 0 < ρ) (hv : 0 < vinf) :
    Integrable (fun t => (orbitRadius a ρ vinf t ^ 4)⁻¹) :=
  integrable_inv_orbitRadius_pow_four hρ hv

example (e a ρ vinf t : ℝ) :
    ‖e • acceleration a ρ vinf t‖ ≤ |e * (vinf ^ 2 * a)| * (orbitRadius a ρ vinf t ^ 2)⁻¹ :=
  norm_smul_acceleration_le e a ρ vinf t

example (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Integrable (fun t => e • acceleration a ρ vinf t) ∧
      MemLp (fun t => e • acceleration a ρ vinf t) 2 :=
  integrable_dipoleAcceleration_coulomb e a hρ hv

example (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Integrable fun t => dipolePower (e • acceleration a ρ vinf t) :=
  integrable_dipolePower e a hρ hv

example (e a ρ vinf : ℝ) :
    ℝ :=
  totalEnergy e a ρ vinf

example (e a ρ vinf : ℝ) :
    0 ≤ totalEnergy e a ρ vinf :=
  totalEnergy_nonneg e a ρ vinf

example (hρ : 0 < ρ) (hv : 0 < vinf) :
    orbitRadius a ρ vinf '' Ioi 0 = Ioi (closest a ρ) :=
  image_orbitRadius_Ioi hρ hv

example (hρ : 0 < ρ) (hv : 0 < vinf) {t : ℝ} (ht : 0 < t) :
    radialVelocity (factor a ρ vinf) (closest a ρ) t =
      √(speedSq a ρ vinf (orbitRadius a ρ vinf t)) :=
  radialVelocity_eq_sqrt hρ hv ht

example (hρ : 0 < ρ) (hv : 0 < vinf) (g : ℝ → ℝ) :
    ∫ r in Ioi (closest a ρ), g r / √(speedSq a ρ vinf r) =
      ∫ t in Ioi 0, g (orbitRadius a ρ vinf t) :=
  integral_Ioi_div_sqrt_speedSq hρ hv g

example (hρ : 0 < ρ) (hv : 0 < vinf) (g : ℝ → ℝ) :
    IntegrableOn (fun r => g r / √(speedSq a ρ vinf r)) (Ioi (closest a ρ)) ↔
      IntegrableOn (fun t => g (orbitRadius a ρ vinf t)) (Ioi 0) :=
  integrableOn_Ioi_div_sqrt_speedSq_iff hρ hv g

example (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    totalEnergy e a ρ vinf =
      2 * ∫ r in Ioi (closest a ρ),
        2 / 3 * (4 * π)⁻¹ * (e * (vinf ^ 2 * a / r ^ 2)) ^ 2 / √(speedSq a ρ vinf r) :=
  integral_dipolePower_eq e a hρ hv

example (u : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖u‖ ^ 2 = ∫ x, ‖(u : ℝ → ℂ) x‖ ^ 2 :=
  norm_sq_eq_integral u

example {f : ℝ → ℂ} (hf : Integrable f) (hf2 : MemLp f 2) :
    MemLp (𝓕 f) 2 ∧ ∫ ν, ‖𝓕 f ν‖ ^ 2 = ∫ t, ‖f t‖ ^ 2 :=
  integral_norm_sq_fourier hf hf2

example (w : ℝ → ℝ × ℝ) (ν : ℝ) :
    ℝ :=
  spectralDensity w ν

example {w : ℝ → ℝ × ℝ} (hw : Integrable w) (hw2 : MemLp w 2) :
    Integrable (spectralDensity w) ∧ ∫ t, dipolePower (w t) = ∫ ν, spectralDensity w ν :=
  spectral_eq hw hw2

example (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    Integrable (spectralDensity fun t => e • acceleration a ρ vinf t) ∧
      totalEnergy e a ρ vinf = ∫ ν, spectralDensity (fun t => e • acceleration a ρ vinf t) ν :=
  spectral_eq_coulomb e a hρ hv

example (e a vinf : ℝ) :
    ℝ :=
  effectiveRadiation e a vinf

example (e a vinf : ℝ) :
    Prop :=
  IsEffectiveFinite e a vinf

example (e a vinf : ℝ) :
    0 ≤ effectiveRadiation e a vinf :=
  effectiveRadiation_nonneg e a vinf

end ProjectAinos.Electrodynamics.Radiation.Collision

end Collision

section CoulombRadiation

open Set Filter MeasureTheory

open scoped Real Topology FourierTransform ContDiff

namespace ProjectAinos.Electrodynamics.Radiation.CoulombRadiation

open Mechanics.Scattering Mechanics.Scattering.Coulomb Collision

variable {a ρ vinf : ℝ}

example (hρ : 0 < ρ) {r : ℝ} (hr : closest a ρ ≤ r) :
    (ρ ^ 2 / r + a) ^ 2 ≤ hyp a ρ ^ 2 :=
  sq_le_hyp_sq hρ hr

example (hρ : 0 < ρ) {r : ℝ} (hr : closest a ρ ≤ r) :
    Real.cos (primitive a ρ r) = (ρ ^ 2 / r + a) / hyp a ρ :=
  cos_primitive hρ hr

example (hρ : 0 < ρ) (hv : 0 < vinf) {t : ℝ} (ht : 0 ≤ t) :
    orbitAngle a ρ vinf t = primitive a ρ (orbitRadius a ρ vinf t) :=
  orbitAngle_eq_primitive hρ hv ht

example (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    hyp a ρ * Real.cos (orbitAngle a ρ vinf t) - a = ρ ^ 2 / orbitRadius a ρ vinf t :=
  cos_orbitAngle hρ hv t

example (a ρ φ : ℝ) :
    ℝ :=
  angleIntegral a ρ φ

example (a ρ φ : ℝ) :
    HasDerivAt (angleIntegral a ρ) (((hyp a ρ * Real.cos φ - a) / ρ ^ 2) ^ 2) φ :=
  hasDerivAt_angleIntegral a ρ φ

example (a ρ : ℝ) :
    angleIntegral a ρ 0 = 0 :=
  angleIntegral_zero a ρ

example (a ρ : ℝ) :
    Continuous (angleIntegral a ρ) :=
  continuous_angleIntegral a ρ

example (a : ℝ) (hρ : 0 < ρ) :
    angleIntegral a ρ (asymptoteAngle a ρ) =
      ((3 * a ^ 2 + ρ ^ 2) * asymptoteAngle a ρ - 3 * a * ρ) / (2 * ρ ^ 4) :=
  angleIntegral_asymptoteAngle a hρ

example (a ρ vinf r : ℝ) :
    ℝ :=
  radialPrimitive a ρ vinf r

example (hρ : 0 < ρ) (hv : 0 < vinf) {r : ℝ} (hr : closest a ρ < r) :
    HasDerivAt (radialPrimitive a ρ vinf) ((r ^ 4)⁻¹ / √(speedSq a ρ vinf r)) r :=
  hasDerivAt_radialPrimitive hρ hv hr

example (hρ : 0 < ρ) :
    ContinuousWithinAt (radialPrimitive a ρ vinf) (Ici (closest a ρ)) (closest a ρ) :=
  continuousWithinAt_radialPrimitive hρ

example (a ρ vinf : ℝ) :
    Tendsto (radialPrimitive a ρ vinf) atTop
      (𝓝 (angleIntegral a ρ (asymptoteAngle a ρ) / (ρ * vinf))) :=
  tendsto_radialPrimitive_atTop a ρ vinf

example (a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    IntegrableOn (fun r => (r ^ 4)⁻¹ / √(speedSq a ρ vinf r)) (Ioi (closest a ρ)) ∧
      ∫ r in Ioi (closest a ρ), (r ^ 4)⁻¹ / √(speedSq a ρ vinf r) =
        ((3 * a ^ 2 + ρ ^ 2) * asymptoteAngle a ρ - 3 * a * ρ) / (2 * ρ ^ 5 * vinf) :=
  integral_inv_pow_four_div_sqrt a hρ hv

example (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) :
    totalEnergy e a ρ vinf = 2 / 3 * (4 * π)⁻¹ * e ^ 2 * vinf ^ 3 * a ^ 2 *
      ((3 * a ^ 2 + ρ ^ 2) * asymptoteAngle a ρ - 3 * a * ρ) / ρ ^ 5 :=
  totalEnergy_hyperbolic e a hρ hv

example (a : ℝ) (hρ : 0 < ρ) :
    0 ≤ (3 * a ^ 2 + ρ ^ 2) * asymptoteAngle a ρ - 3 * a * ρ :=
  radiationBracket_nonneg a hρ

example (ha : 0 < a) (hρ : 0 < ρ) :
    asymptoteAngle a ρ = Real.arctan (ρ / a) :=
  asymptoteAngle_eq_arctan ha hρ

example (x : ℝ) (hx : 0 ≤ x) :
    x - x ^ 3 / 3 ≤ Real.arctan x :=
  arctan_lower x hx

example (x : ℝ) (hx : 0 ≤ x) :
    Real.arctan x ≤ x - x ^ 3 / 3 + x ^ 5 / 5 :=
  arctan_upper x hx

example (a ρ : ℝ) :
    ℝ :=
  impactPrimitive a ρ

example (ha : 0 < a) {ρ : ℝ} (hρ : 0 < ρ) :
    HasDerivAt (impactPrimitive a)
      (((3 * a ^ 2 + ρ ^ 2) * Real.arctan (ρ / a) - 3 * a * ρ) / ρ ^ 4) ρ :=
  hasDerivAt_impactPrimitive ha hρ

example (ha : 0 < a) :
    Tendsto (impactPrimitive a) atTop (𝓝 0) :=
  tendsto_impactPrimitive_atTop ha

example (ha : 0 < a) :
    Tendsto (impactPrimitive a) (𝓝[>] 0) (𝓝 (-(2 / (3 * a)))) :=
  tendsto_impactPrimitive_zero ha

example (e : ℝ) (ha : 0 < a) (hv : 0 < vinf) :
    IsEffectiveFinite e a vinf ∧ effectiveRadiation e a vinf = 2 / 9 * e ^ 2 * vinf ^ 3 * a :=
  effectiveRadiation_repulsive e ha hv

example {e : ℝ} (he : e ≠ 0) (ha : a < 0) (hv : 0 < vinf) :
    ¬ IsEffectiveFinite e a vinf :=
  not_isEffectiveFinite_attractive he ha hv

example (a ρ vinf φ : ℝ) :
    ℝ :=
  timeOfAngle a ρ vinf φ

example (hρ : 0 < ρ) (hv : 0 < vinf) (t : ℝ) :
    timeOfAngle a ρ vinf (orbitAngle a ρ vinf t) = t :=
  timeOfAngle_orbitAngle hρ hv t

example (hρ : 0 < ρ) (hv : 0 < vinf) :
    range (orbitAngle a ρ vinf) = Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ) :=
  range_orbitAngle hρ hv

example (hρ : 0 < ρ) (hv : 0 < vinf) :
    StrictMono (orbitAngle a ρ vinf) :=
  strictMono_orbitAngle hρ hv

example (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (n : ℝ → ℝ) (ν : ℝ) :
    𝓕 (fun t => ((e * (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2) *
        n (orbitAngle a ρ vinf t) : ℝ) : ℂ)) ν =
      ((e * (vinf * a / ρ) : ℝ) : ℂ) * ∫ φ in Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ),
        Complex.exp (↑(-2 * π * timeOfAngle a ρ vinf φ * ν) * Complex.I) * (n φ : ℂ) :=
  fourier_orbit e a hρ hv n ν

example (e a ρ vinf t : ℝ) :
    (e • acceleration a ρ vinf t).1 =
      e * (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2) * Real.cos (orbitAngle a ρ vinf t) :=
  fst_smul_acceleration e a ρ vinf t

example (e a ρ vinf t : ℝ) :
    (e • acceleration a ρ vinf t).2 =
      e * (vinf ^ 2 * a / orbitRadius a ρ vinf t ^ 2) * Real.sin (orbitAngle a ρ vinf t) :=
  snd_smul_acceleration e a ρ vinf t

example (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (ν : ℝ) :
    𝓕 (fun t => ((e • acceleration a ρ vinf t).1 : ℂ)) ν =
      ((e * (vinf * a / ρ) : ℝ) : ℂ) * ∫ φ in Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ),
        Complex.exp (↑(-2 * π * timeOfAngle a ρ vinf φ * ν) * Complex.I) * (Real.cos φ : ℂ) :=
  fourier_acceleration_fst e a hρ hv ν

example (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (ν : ℝ) :
    𝓕 (fun t => ((e • acceleration a ρ vinf t).2 : ℂ)) ν =
      ((e * (vinf * a / ρ) : ℝ) : ℂ) * ∫ φ in Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ),
        Complex.exp (↑(-2 * π * timeOfAngle a ρ vinf φ * ν) * Complex.I) * (Real.sin φ : ℂ) :=
  fourier_acceleration_snd e a hρ hv ν

example (e a : ℝ) (hρ : 0 < ρ) (hv : 0 < vinf) (ν : ℝ) :
    spectralDensity (fun t => e • acceleration a ρ vinf t) ν =
      2 / 3 * (4 * π)⁻¹ * (e * (vinf * a / ρ)) ^ 2 *
        (‖∫ φ in Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ),
            Complex.exp (↑(-2 * π * timeOfAngle a ρ vinf φ * ν) * Complex.I) *
              (Real.cos φ : ℂ)‖ ^ 2 +
          ‖∫ φ in Ioo (-asymptoteAngle a ρ) (asymptoteAngle a ρ),
            Complex.exp (↑(-2 * π * timeOfAngle a ρ vinf φ * ν) * Complex.I) *
              (Real.sin φ : ℂ)‖ ^ 2) :=
  spectrum_hyperbolic e a hρ hv ν

variable {ε : ℝ}

example (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (φ : ℝ) :
    0 < 1 + ε * Real.cos φ :=
  one_add_mul_cos_pos hε₀ hε₁ φ

example (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) {φ : ℝ} (hφ : φ ∈ Ioo (-π) π) :
    HasDerivAt (fun φ => 2 / √(1 - ε ^ 2) *
      Real.arctan (√(1 - ε ^ 2) / (1 + ε) * Real.tan (φ / 2))) (1 + ε * Real.cos φ)⁻¹ φ :=
  hasDerivAt_arctan_tan_half hε₀ hε₁ hφ

example (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (φ : ℝ) :
    HasDerivAt (fun φ => ε * Real.sin φ / (1 + ε * Real.cos φ))
      ((1 + ε * Real.cos φ)⁻¹ - (1 - ε ^ 2) * ((1 + ε * Real.cos φ) ^ 2)⁻¹) φ :=
  hasDerivAt_sin_div hε₀ hε₁ φ

example :
    Tendsto (fun φ : ℝ => φ / 2) (𝓝[<] π) (𝓝[<] (π / 2)) :=
  tendsto_half_nhdsLT_pi

example :
    Tendsto (fun φ : ℝ => φ / 2) (𝓝[>] (-π)) (𝓝[>] (-(π / 2))) :=
  tendsto_half_nhdsGT_neg_pi

example (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    ∫ φ in (0 : ℝ)..2 * π, ((1 + ε * Real.cos φ) ^ 2)⁻¹ =
      2 * π / ((1 - ε ^ 2) * √(1 - ε ^ 2)) :=
  integral_inv_one_add_mul_cos_sq hε₀ hε₁

variable {k ℓ : ℝ}

example (k ℓ ε φ : ℝ) :
    ℝ :=
  angleField k ℓ ε φ

example (k ℓ ε t : ℝ) :
    ℝ :=
  keplerAngle k ℓ ε t

example (k ℓ : ℝ) :
    ℝ :=
  semiLatus k ℓ

example (k ℓ ε t : ℝ) :
    ℝ :=
  keplerRadius k ℓ ε t

example (k ℓ ε t : ℝ) :
    ℝ × ℝ :=
  keplerPosition k ℓ ε t

example (k ℓ ε t : ℝ) :
    ℝ × ℝ :=
  keplerVelocity k ℓ ε t

example (k ℓ ε t : ℝ) :
    ℝ × ℝ :=
  keplerAcceleration k ℓ ε t

example (k ℓ ε : ℝ) :
    ℝ :=
  keplerPeriod k ℓ ε

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (φ : ℝ) :
    0 < angleField k ℓ ε φ :=
  angleField_pos hk hℓ hε₀ hε₁ φ

example (k ℓ ε : ℝ) :
    ContDiff ℝ ∞ (angleField k ℓ ε) :=
  contDiff_angleField k ℓ ε

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (φ : ℝ) :
    |angleField k ℓ ε φ| ≤ k ^ 2 / ℓ ^ 3 * (1 + ε) ^ 2 :=
  abs_angleField_le hk hℓ hε₀ hε₁ φ

example (k ℓ ε φ : ℝ) :
    angleField k ℓ ε (φ + 2 * π) = angleField k ℓ ε φ :=
  angleField_add_two_pi k ℓ ε φ

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    HasDerivAt (keplerAngle k ℓ ε) (angleField k ℓ ε (keplerAngle k ℓ ε t)) t :=
  hasDerivAt_keplerAngle hk hℓ hε₀ hε₁ t

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    Continuous (keplerAngle k ℓ ε) :=
  continuous_keplerAngle hk hℓ hε₀ hε₁

example (k ℓ ε : ℝ) :
    keplerAngle k ℓ ε 0 = 0 :=
  keplerAngle_zero k ℓ ε

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    keplerAngle k ℓ ε (t + keplerPeriod k ℓ ε) = keplerAngle k ℓ ε t + 2 * π :=
  keplerAngle_add_period hk hℓ hε₀ hε₁ t

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    keplerAngle k ℓ ε (keplerPeriod k ℓ ε) = 2 * π :=
  keplerAngle_keplerPeriod hk hℓ hε₀ hε₁

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    keplerPeriod k ℓ ε = 2 * π * ℓ ^ 3 / (k ^ 2 * ((1 - ε ^ 2) * √(1 - ε ^ 2))) :=
  keplerPeriod_eq hk hℓ hε₀ hε₁

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    keplerPeriod k ℓ ε = 2 * π * √((semiLatus k ℓ / (1 - ε ^ 2)) ^ 3 / k) :=
  keplerPeriod_eq_semiMajor hk hℓ hε₀ hε₁

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    HasDerivAt (keplerRadius k ℓ ε) (k / ℓ * ε * Real.sin (keplerAngle k ℓ ε t)) t :=
  hasDerivAt_keplerRadius hk hℓ hε₀ hε₁ t

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    HasDerivAt (keplerPosition k ℓ ε) (keplerVelocity k ℓ ε t) t :=
  hasDerivAt_keplerPosition hk hℓ hε₀ hε₁ t

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    HasDerivAt (keplerVelocity k ℓ ε) (keplerAcceleration k ℓ ε t) t :=
  hasDerivAt_keplerVelocity hk hℓ hε₀ hε₁ t

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    0 < keplerRadius k ℓ ε t :=
  keplerRadius_pos hk hℓ hε₀ hε₁ t

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    keplerAcceleration k ℓ ε t =
      (-(k / keplerRadius k ℓ ε t ^ 3)) • keplerPosition k ℓ ε t :=
  keplerAcceleration_eq_smul hk hℓ hε₀ hε₁ t

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    (keplerPosition k ℓ ε t).1 * (keplerVelocity k ℓ ε t).2 -
      (keplerPosition k ℓ ε t).2 * (keplerVelocity k ℓ ε t).1 = ℓ :=
  keplerPosition_cross_velocity hk hℓ hε₀ hε₁ t

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    keplerAcceleration k ℓ ε (t + keplerPeriod k ℓ ε) = keplerAcceleration k ℓ ε t :=
  keplerAcceleration_add_period hk hℓ hε₀ hε₁ t

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    Continuous (keplerAcceleration k ℓ ε) :=
  continuous_keplerAcceleration hk hℓ hε₀ hε₁

example (k ℓ ε φ : ℝ) :
    ℝ :=
  meanPrimitive k ℓ ε φ

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (e t : ℝ) :
    dipolePower (e • keplerAcceleration k ℓ ε t) =
      2 / 3 * (4 * π)⁻¹ * e ^ 2 * k ^ 2 *
        (k ^ 4 / ℓ ^ 8 * (1 + ε * Real.cos (keplerAngle k ℓ ε t)) ^ 4) :=
  dipolePower_smul_keplerAcceleration hk hℓ hε₀ hε₁ e t

example (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) (t : ℝ) :
    HasDerivAt (fun t => meanPrimitive k ℓ ε (keplerAngle k ℓ ε t))
      (k ^ 4 / ℓ ^ 8 * (1 + ε * Real.cos (keplerAngle k ℓ ε t)) ^ 4) t :=
  hasDerivAt_meanPrimitive hk hℓ hε₀ hε₁ t

example (e : ℝ) (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    (keplerPeriod k ℓ ε)⁻¹ *
        ∫ t in (0 : ℝ)..keplerPeriod k ℓ ε, dipolePower (e • keplerAcceleration k ℓ ε t) =
      2 / 3 * (4 * π)⁻¹ * e ^ 2 * k ^ 6 * (2 + ε ^ 2) * ((1 - ε ^ 2) * √(1 - ε ^ 2)) /
        (2 * ℓ ^ 8) :=
  average_dipolePower_kepler e hk hℓ hε₀ hε₁

example (e : ℝ) (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    (keplerPeriod k ℓ ε)⁻¹ *
        ∫ t in (0 : ℝ)..keplerPeriod k ℓ ε, dipolePower (e • keplerAcceleration k ℓ ε t) =
      2 / 3 * (4 * π)⁻¹ * e ^ 2 * k ^ 2 * (2 + ε ^ 2) /
        (2 * (semiLatus k ℓ / (1 - ε ^ 2)) ^ 4 * ((1 - ε ^ 2) ^ 2 * √(1 - ε ^ 2))) :=
  average_dipolePower_kepler_semiMajor e hk hℓ hε₀ hε₁

example (w : ℝ → ℝ) (T : ℝ) (n : ℤ) :
    ℂ :=
  harmonicCoeff w T n

example (w : ℝ → ℝ) {T : ℝ} (hT : 0 < T) (n : ℤ) :
    harmonicCoeff w T n = fourierCoeffOn hT (fun t => (w t : ℂ)) n :=
  harmonicCoeff_eq_fourierCoeffOn w hT n

example (e : ℝ) (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    HasSum (fun n : ℤ => 2 / 3 * (4 * π)⁻¹ *
        (‖harmonicCoeff (fun t => (e • keplerAcceleration k ℓ ε t).1) (keplerPeriod k ℓ ε) n‖ ^ 2 +
          ‖harmonicCoeff (fun t => (e • keplerAcceleration k ℓ ε t).2) (keplerPeriod k ℓ ε) n‖ ^ 2))
      ((keplerPeriod k ℓ ε)⁻¹ *
        ∫ t in (0 : ℝ)..keplerPeriod k ℓ ε, dipolePower (e • keplerAcceleration k ℓ ε t)) :=
  harmonic_decomposition e hk hℓ hε₀ hε₁

example (e : ℝ) (hk : 0 < k) (hℓ : 0 < ℓ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1) :
    ∑' n : ℤ, 2 / 3 * (4 * π)⁻¹ *
        (‖harmonicCoeff (fun t => (e • keplerAcceleration k ℓ ε t).1) (keplerPeriod k ℓ ε) n‖ ^ 2 +
          ‖harmonicCoeff (fun t => (e • keplerAcceleration k ℓ ε t).2)
            (keplerPeriod k ℓ ε) n‖ ^ 2) =
      2 / 3 * (4 * π)⁻¹ * e ^ 2 * k ^ 6 * (2 + ε ^ 2) * ((1 - ε ^ 2) * √(1 - ε ^ 2)) /
        (2 * ℓ ^ 8) :=
  tsum_harmonic e hk hℓ hε₀ hε₁

end ProjectAinos.Electrodynamics.Radiation.CoulombRadiation

end CoulombRadiation

section CollisionSpectrum

open MeasureTheory Set Metric Filter Real

open scoped Topology FourierTransform ContDiff ComplexConjugate

namespace ProjectAinos.Electrodynamics.Radiation.CollisionSpectrum

open SmoothGeometry SmoothGeometry.Sphere Relativistic

local notation "E3" => EuclideanSpace ℝ (Fin 3)

local notation "C3" => EuclideanSpace ℂ (Fin 3)

example :
    E3 →L[ℝ] C3 :=
  complexify

example (x : E3) (i : Fin 3) :
    complexify x i = (x i : ℂ) :=
  complexify_apply x i

example (x : E3) :
    ‖complexify x‖ = ‖x‖ :=
  norm_complexify x

example :
    Function.Injective complexify :=
  complexify_injective

example {f : ℝ → E3} (hf : Integrable f) :
    Tendsto (𝓕 (fun t => complexify (f t))) (𝓝 0) (𝓝 (complexify (∫ t, f t))) :=
  tendsto_fourier_complexify hf

example {f : ℝ → E3} (hf : Integrable f) (ν : ℝ) (i : Fin 3) :
    𝓕 (fun t => complexify (f t)) ν i = ∫ t, (𝐞 (-(t * ν)) : ℂ) * (f t i : ℂ) :=
  fourier_complexify_apply hf ν i

example {f : ℝ → E3} (hf : Integrable f) (ν : ℝ) :
    ‖𝓕 (fun t => complexify (f t)) (-ν)‖ = ‖𝓕 (fun t => complexify (f t)) ν‖ :=
  norm_fourier_complexify_neg hf ν

example {v a : ℝ → E3} {v₁ v₂ : E3} (hv : ∀ t, HasDerivAt v (a t) t) (ha : Integrable a)
    (hbot : Tendsto v atBot (𝓝 v₁)) (htop : Tendsto v atTop (𝓝 v₂)) :
    Tendsto (𝓕 (fun t => complexify (a t))) (𝓝 0) (𝓝 (complexify (v₂ - v₁))) :=
  tendsto_fourier_acceleration hv ha hbot htop

example (e : ℝ) (a : ℝ → E3) (ν : ℝ) :
    ℝ :=
  dipoleSpectrum e a ν

example (e : ℝ) {a : ℝ → E3} (ha : Integrable a) (ν : ℝ) :
    dipoleSpectrum e a (-ν) = dipoleSpectrum e a ν :=
  dipoleSpectrum_neg e ha ν

example (e : ℝ) {v a : ℝ → E3} {v₁ v₂ : E3} (hv : ∀ t, HasDerivAt v (a t) t) (ha : Integrable a)
    (hbot : Tendsto v atBot (𝓝 v₁)) (htop : Tendsto v atTop (𝓝 v₂)) :
    Tendsto (dipoleSpectrum e a) (𝓝 0) (𝓝 (2 / 3 * (e ^ 2 / (4 * π)) * ‖v₂ - v₁‖ ^ 2)) :=
  tendsto_dipoleSpectrum e hv ha hbot htop

example (e : ℝ) {v a : ℝ → E3} {v₁ v₂ : E3} (hv : ∀ t, HasDerivAt v (a t) t) (ha : Integrable a)
    (hbot : Tendsto v atBot (𝓝 v₁)) (htop : Tendsto v atTop (𝓝 v₂)) :
    Tendsto (fun ν => 2 * dipoleSpectrum e a ν) (𝓝[>] 0)
      (𝓝 (4 / 3 * (e ^ 2 / (4 * π)) * ‖v₂ - v₁‖ ^ 2)) :=
  tendsto_two_mul_dipoleSpectrum e hv ha hbot htop

example (w : SubluminalWorldline) (n : E3) (τ : ℝ) :
    ℝ :=
  observerTime w n τ

variable (w : SubluminalWorldline)

example (n : E3) (τ : ℝ) :
    HasDerivAt (observerTime w n) (1 - inner ℝ n (deriv w.r τ)) τ :=
  hasDerivAt_observerTime w n τ

example (n : E3) :
    Continuous (observerTime w n) :=
  continuous_observerTime w n

example :
    0 < 1 - w.v₀ :=
  one_sub_v₀_pos w

example (τ : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    1 - w.v₀ ≤ 1 - inner ℝ n (deriv w.r τ) :=
  one_sub_v₀_le w τ hn

example {n : E3} (hn : ‖n‖ = 1) {τ₁ τ₂ : ℝ} (h : τ₁ ≤ τ₂) :
    (1 - w.v₀) * (τ₂ - τ₁) ≤ observerTime w n τ₂ - observerTime w n τ₁ :=
  mul_sub_le_observerTime_sub w hn h

example {n : E3} (hn : ‖n‖ = 1) :
    StrictMono (observerTime w n) :=
  strictMono_observerTime w hn

example {n : E3} (hn : ‖n‖ = 1) :
    Function.Surjective (observerTime w n) :=
  surjective_observerTime w hn

example (w : SubluminalWorldline) (n : E3) :
    ℝ → ℝ :=
  retardedOfObserver w n

example {n : E3} (hn : ‖n‖ = 1) (t : ℝ) :
    observerTime w n (retardedOfObserver w n t) = t :=
  observerTime_retardedOfObserver w hn t

example {n : E3} (hn : ‖n‖ = 1) (τ : ℝ) :
    retardedOfObserver w n (observerTime w n τ) = τ :=
  retardedOfObserver_observerTime w hn τ

example {n : E3} (hn : ‖n‖ = 1) :
    Continuous (retardedOfObserver w n) :=
  continuous_retardedOfObserver w hn

example {n : E3} (hn : ‖n‖ = 1) (t : ℝ) :
    HasDerivAt (retardedOfObserver w n)
      (1 - inner ℝ n (deriv w.r (retardedOfObserver w n t)))⁻¹ t :=
  hasDerivAt_retardedOfObserver w hn t

example (e : ℝ) (w : SubluminalWorldline) (n : E3) (τ : ℝ) :
    E3 :=
  amplitude e w n τ

example (e : ℝ) {τ ρ : ℝ} (hρ : 0 < ρ) {n : E3} (hn : ‖n‖ = 1) :
    ρ • LienardWiechert.accelerationField e w (τ + ρ) (w.r τ + ρ • n) = amplitude e w n τ :=
  smul_accelerationField_lightCone w e hρ hn

example (e τ : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    Tendsto (fun ρ => ρ ^ 2 * ∑ i : Fin 3, poyntingVector (fieldTensor (lienardWiechert e w)) i
        (Minkowski.vector (τ + ρ) (w.r τ + ρ • n)) * n i) atTop
      (𝓝 (‖amplitude e w n τ‖ ^ 2)) :=
  tendsto_sq_mul_inner_poyntingVector_lightCone_eq w e τ hn

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) :
    Continuous (amplitude e w n) :=
  continuous_amplitude w e hn

example (u v : E3) :
    ‖cross u v‖ ≤ ‖u‖ * ‖v‖ :=
  norm_cross_le u v

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (τ : ℝ) :
    ‖(1 - inner ℝ n (deriv w.r τ)) • amplitude e w n τ‖ ≤
      2 * |e| / (4 * π * (1 - w.v₀) ^ 2) * ‖deriv (deriv w.r) τ‖ :=
  norm_smul_amplitude_le w e hn τ

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (ha : Integrable (deriv (deriv w.r))) :
    Integrable fun τ => (1 - inner ℝ n (deriv w.r τ)) • amplitude e w n τ :=
  integrable_smul_amplitude w e hn ha

example (e : ℝ) (n v : E3) :
    E3 :=
  velocityAmplitude e n v

example (e : ℝ) (n : E3) {v : E3} (hv : inner ℝ n v ≠ 1) :
    ContinuousAt (velocityAmplitude e n) v :=
  continuousAt_velocityAmplitude e n hv

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (τ : ℝ) :
    HasDerivAt (fun s => velocityAmplitude e n (deriv w.r s))
      ((1 - inner ℝ n (deriv w.r τ)) • amplitude e w n τ) τ :=
  hasDerivAt_velocityAmplitude w e hn τ

example (e : ℝ) (w : SubluminalWorldline) (n : E3) (t : ℝ) :
    E3 :=
  observedAmplitude e w n t

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (t : ℝ) :
    HasDerivAt (fun t => velocityAmplitude e n (deriv w.r (retardedOfObserver w n t)))
      (observedAmplitude e w n t) t :=
  hasDerivAt_velocityAmplitude_retardedOfObserver w e hn t

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (t : ℝ) :
    observedAmplitude e w n t =
      deriv (fun t => velocityAmplitude e n (deriv w.r (retardedOfObserver w n t))) t :=
  radiationAmplitude_eq_deriv w e hn t

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (ν : ℝ) :
    𝓕 (fun t => complexify (observedAmplitude e w n t)) ν =
      ∫ τ, 𝐞 (-(observerTime w n τ * ν)) •
        complexify ((1 - inner ℝ n (deriv w.r τ)) • amplitude e w n τ) :=
  fourier_radiationAmplitude w e hn ν

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (ν : ℝ) :
    𝓕 (fun t => complexify (observedAmplitude e w n t)) ν =
      ∫ τ, 𝐞 (-(observerTime w n τ * ν)) •
        complexify (deriv (fun s => velocityAmplitude e n (deriv w.r s)) τ) :=
  fourier_radiationAmplitude_eq_deriv w e hn ν

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (ha : Integrable (deriv (deriv w.r))) :
    Integrable (observedAmplitude e w n) :=
  integrable_observedAmplitude w e hn ha

example {l : Filter ℝ} [l.NeBot] {v : E3} (h : Tendsto (deriv w.r) l (𝓝 v)) :
    ‖v‖ ≤ w.v₀ :=
  norm_le_of_tendsto w h

example {n v : E3} (hn : ‖n‖ = 1) (hv : ‖v‖ ≤ w.v₀) :
    inner ℝ n v ≠ 1 :=
  inner_ne_one w hn hv

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) {v₁ v₂ : E3} (ha : Integrable (deriv (deriv w.r)))
    (hbot : Tendsto (deriv w.r) atBot (𝓝 v₁)) (htop : Tendsto (deriv w.r) atTop (𝓝 v₂)) :
    ∫ t, observedAmplitude e w n t = velocityAmplitude e n v₂ - velocityAmplitude e n v₁ :=
  integral_observedAmplitude w e hn ha hbot htop

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) {v₁ v₂ : E3} (ha : Integrable (deriv (deriv w.r)))
    (hbot : Tendsto (deriv w.r) atBot (𝓝 v₁)) (htop : Tendsto (deriv w.r) atTop (𝓝 v₂)) :
    Tendsto (𝓕 (fun t => complexify (observedAmplitude e w n t))) (𝓝 0)
      (𝓝 (complexify (velocityAmplitude e n v₂ - velocityAmplitude e n v₁))) :=
  tendsto_fourier_observedAmplitude w e hn ha hbot htop

example (e : ℝ) (w : SubluminalWorldline) (n : E3) (ν : ℝ) :
    ℝ :=
  angularSpectrum e w n ν

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) (ha : Integrable (deriv (deriv w.r))) (ν : ℝ) :
    angularSpectrum e w n (-ν) = angularSpectrum e w n ν :=
  angularSpectrum_neg w e hn ha ν

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) {v₁ v₂ : E3} (ha : Integrable (deriv (deriv w.r)))
    (hbot : Tendsto (deriv w.r) atBot (𝓝 v₁)) (htop : Tendsto (deriv w.r) atTop (𝓝 v₂)) :
    Tendsto (angularSpectrum e w n) (𝓝 0)
      (𝓝 (‖velocityAmplitude e n v₂ - velocityAmplitude e n v₁‖ ^ 2)) :=
  tendsto_relativisticSpectrum w e hn ha hbot htop

example (e : ℝ) {n : E3} (hn : ‖n‖ = 1) {v₁ v₂ : E3} (ha : Integrable (deriv (deriv w.r)))
    (hbot : Tendsto (deriv w.r) atBot (𝓝 v₁)) (htop : Tendsto (deriv w.r) atTop (𝓝 v₂)) :
    Tendsto (fun ν => 2 * angularSpectrum e w n ν) (𝓝[>] 0)
      (𝓝 (2 * ‖velocityAmplitude e n v₂ - velocityAmplitude e n v₁‖ ^ 2)) :=
  tendsto_two_mul_relativisticSpectrum w e hn ha hbot htop

example (e : ℝ) (X : E3) :
    ∫ n : sphere (0 : E3) 1, 2 * ‖(e / (4 * π)) • cross n (cross n X)‖ ^ 2 ∂sphereMeasure =
      4 / 3 * (e ^ 2 / (4 * π)) * ‖X‖ ^ 2 :=
  integral_two_mul_norm_sq_smul_cross_cross e X

example {β : ℝ} (hβ : |β| < 1) (hβ0 : β ≠ 0) :
    ∫ s in (-1 : ℝ)..1, (1 - s ^ 2) / (1 - β * s) ^ 2 =
      2 * (log ((1 + β) / (1 - β)) - 2 * β) / β ^ 3 :=
  integral_one_sub_sq_div_one_sub_mul_sq hβ hβ0

example (e : ℝ) {ê : E3} (he : ‖ê‖ = 1) {β : ℝ} (hβ : |β| < 1) (n : sphere (0 : E3) 1) :
    2 * ‖velocityAmplitude e n (β • ê) - velocityAmplitude e n 0‖ ^ 2 =
      e ^ 2 * β ^ 2 / (8 * π ^ 2) *
        ((1 - inner ℝ (n : E3) ê ^ 2) / (1 - β * inner ℝ (n : E3) ê) ^ 2) :=
  two_mul_norm_sq_velocityAmplitude_smul e he hβ n

example (e : ℝ) {v : E3} (hv : ‖v‖ < 1) (hv0 : v ≠ 0) :
    ∫ n : sphere (0 : E3) 1,
        2 * ‖velocityAmplitude e n v - velocityAmplitude e n 0‖ ^ 2 ∂sphereMeasure =
      e ^ 2 / (2 * π) * (log ((1 + ‖v‖) / (1 - ‖v‖)) / ‖v‖ - 2) :=
  integral_two_mul_norm_sq_velocityAmplitude e hv hv0

example :
    ‖(EuclideanSpace.single 0 1 : E3)‖ = 1 :=
  norm_single_zero

example (β t : ℝ) :
    E3 :=
  arctanPath β t

example (β t : ℝ) :
    HasDerivAt (arctanPath β) ((2 * β / π * arctan t) • EuclideanSpace.single 0 1) t :=
  hasDerivAt_arctanPath β t

example (β : ℝ) :
    deriv (arctanPath β) = fun t => (2 * β / π * arctan t) • EuclideanSpace.single 0 1 :=
  deriv_arctanPath β

example (β t : ℝ) :
    HasDerivAt (deriv (arctanPath β))
      ((2 * β / π * (1 + t ^ 2)⁻¹) • EuclideanSpace.single 0 1) t :=
  hasDerivAt_deriv_arctanPath β t

example (β : ℝ) :
    deriv (deriv (arctanPath β)) =
      fun t => (2 * β / π * (1 + t ^ 2)⁻¹) • EuclideanSpace.single 0 1 :=
  deriv_deriv_arctanPath β

example (β : ℝ) :
    Integrable (deriv (deriv (arctanPath β))) :=
  integrable_deriv_deriv_arctanPath β

example (β : ℝ) :
    Tendsto (deriv (arctanPath β)) atTop (𝓝 (β • EuclideanSpace.single 0 1)) :=
  tendsto_deriv_arctanPath_atTop β

example (β : ℝ) :
    Tendsto (deriv (arctanPath β)) atBot (𝓝 ((-β) • EuclideanSpace.single 0 1)) :=
  tendsto_deriv_arctanPath_atBot β

example (β : ℝ) (hβ : |β| < 1) :
    SubluminalWorldline :=
  arctanWorldline β hβ

example (e c : ℝ) :
    velocityAmplitude e (EuclideanSpace.single 1 1) (c • EuclideanSpace.single 0 1) =
      (-(e * c) / (4 * π)) • EuclideanSpace.single 0 1 :=
  velocityAmplitude_single e c

example (e β : ℝ) (hβ : |β| < 1) :
    Tendsto (angularSpectrum e (arctanWorldline β hβ) (EuclideanSpace.single 1 1)) (𝓝 0)
      (𝓝 ((e * β / (2 * π)) ^ 2)) :=
  tendsto_angularSpectrum_arctanWorldline e β hβ

example (e β : ℝ) :
    Tendsto (dipoleSpectrum e (deriv (deriv (arctanPath β)))) (𝓝 0)
      (𝓝 (2 / 3 * (e ^ 2 / (4 * π)) * (2 * β) ^ 2)) :=
  tendsto_dipoleSpectrum_arctanPath e β

end ProjectAinos.Electrodynamics.Radiation.CollisionSpectrum

end CollisionSpectrum
