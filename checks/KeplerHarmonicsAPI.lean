module

import ProjectAinos.Electrodynamics.Radiation.KeplerHarmonics

noncomputable section
open Complex Real ProjectAinos.SpecialFunctions.Kapteyn
open ProjectAinos.Electrodynamics.Radiation.CoulombRadiation
open scoped Real

example {k ℓ e : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) (h₀ : 0 ≤ e)
    (h₁ : e < 1) (t : ℝ) :
    keplerPosition k ℓ e t =
      (semiMajor k ℓ e * (Real.cos (eccentricAnomaly e (meanMotion k ℓ e * t)) - e),
       semiMajor k ℓ e * √(1-e^2) * Real.sin (eccentricAnomaly e (meanMotion k ℓ e * t))) :=
  keplerPosition_eccentric hk hℓ h₀ h₁ t

example {k ℓ e : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ)
    (h₀ : 0 ≤ e) (h₁ : e < 1) : meanMotion k ℓ e * keplerPeriod k ℓ e = 2 * π :=
  meanMotion_mul_period hk hℓ h₀ h₁

example {k ℓ e : ℝ} (hk : 0 < k) (hℓ : 0 < ℓ) (h₀ : 0 < e)
    (h₁ : e < 1) (n : ℤ) (hn : n ≠ 0) :
    harmonicCoeff (fun t => (keplerAcceleration k ℓ e t).1) (keplerPeriod k ℓ e) n =
      -(semiMajor k ℓ e * (meanMotion k ℓ e) ^ 2 : ℝ) * (n : ℂ) *
        deriv (besselJ n) ((n : ℝ) * e) ∧
    harmonicCoeff (fun t => (keplerAcceleration k ℓ e t).2) (keplerPeriod k ℓ e) n =
      I * ↑(semiMajor k ℓ e * √(1-e^2) * (meanMotion k ℓ e) ^ 2) * n *
        besselJ n ((n : ℝ) * e) / e :=
  keplerAcceleration_harmonics hk hℓ h₀ h₁ n hn
