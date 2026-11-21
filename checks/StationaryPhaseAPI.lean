module

import ProjectAinos.SpecialFunctions.StationaryPhase

noncomputable section
open Complex Filter MeasureTheory Set
open scoped Real Topology ContDiff
open ProjectAinos.SpecialFunctions.Oscillatory

example {ψ : ℝ → ℝ} {a : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (ha : deriv ψ a = 0) (hp : 0 < deriv (deriv ψ) a) :
    ∃ l < a, ∃ b > a, ∀ s ∈ Ico l a, ∀ t ∈ Ioc a b, ∀ A : ℝ → ℂ, ContDiff ℝ 1 A →
      Tendsto (fun r : ℝ => (r : ℂ) * ∫ x in s..t,
        A x * exp (((r^2 * (ψ x - ψ a) : ℝ) : ℂ) * I)) atTop
        (𝓝 (((√(deriv (deriv ψ) a / π))⁻¹ : ℝ) * A a * (1 + I))) :=
  stationary_minimum hψ ha hp

example {ψ : ℝ → ℝ} {a : ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (ha : deriv ψ a = 0) (hp : deriv (deriv ψ) a < 0) :
    ∃ l < a, ∃ b > a, ∀ s ∈ Ico l a, ∀ t ∈ Ioc a b, ∀ A : ℝ → ℂ, ContDiff ℝ 1 A →
      Tendsto (fun r : ℝ => (r : ℂ) * ∫ x in s..t,
        A x * exp (((r^2 * (ψ x - ψ a) : ℝ) : ℂ) * I)) atTop
        (𝓝 (((√(-deriv (deriv ψ) a / π))⁻¹ : ℝ) * A a * (1 - I))) :=
  stationary_maximum hψ ha hp
