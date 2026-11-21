/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAinos.SpecialFunctions.QuadraticPhase
import ProjectAinos.SpecialFunctions.NonstationaryPhase

open Filter Complex ProjectAinos.SpecialFunctions
open scoped Topology Real ContDiff

noncomputable section

example (z : ℂ) : HasDerivAt Fresnel.erf (2 / (√π : ℂ) * exp (-z ^ 2)) z :=
  Fresnel.hasDerivAt_erf z

example : Fresnel.erf 0 = 0 := Fresnel.erf_zero

example : Tendsto (fun x : ℝ => Fresnel.erf x) atTop (𝓝 1) := Fresnel.tendsto_erf_atTop

example (x : ℝ) : Fresnel.integral x = ∫ t in (0 : ℝ)..x, exp (((π / 2 * t ^ 2 : ℝ) : ℂ) * I) :=
  rfl

example : Tendsto Fresnel.integral atTop (𝓝 ((1 + I) / 2)) := Fresnel.tendsto_integral_atTop

example (x : ℝ) : Fresnel.integral (-x) = -Fresnel.integral x := Fresnel.integral_neg x

example : Fresnel.integral 0 = 0 := Fresnel.integral_zero

example : Tendsto Fresnel.cosine atTop (𝓝 (1 / 2)) ∧ Tendsto Fresnel.sine atTop (𝓝 (1 / 2)) :=
  Fresnel.tendsto_cosine_sine_atTop

example (x : ℝ) : HasDerivAt Fresnel.integral (exp (((π / 2 * x ^ 2 : ℝ) : ℂ) * I)) x :=
  Fresnel.hasDerivAt_integral x

example {d : ℕ} {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (N : ℕ)
    {g : EuclideanSpace ℝ (Fin d) → ℂ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hn : ∀ x ∈ tsupport g, fderiv ℝ ψ x ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, ε ≠ 0 →
      ‖∫ x, g x * exp (I / ε * ψ x)‖ ≤ C * |ε| ^ N := Oscillatory.nonstationary hψ N hg hc hn

example {b : ℝ} (hb : 0 < b) {A D : ℝ → ℂ} (hA : ∀ t ∈ Set.Icc 0 b, HasDerivAt A (D t) t)
    (hD : ContinuousOn D (Set.Icc 0 b)) :
    Tendsto (fun r : ℝ => (r : ℂ) * ∫ t in 0..b, A t * exp (((π / 2 * (r*t)^2 : ℝ) : ℂ) * I))
      atTop (𝓝 (A 0 * ((1 + I) / 2))) := Oscillatory.quadratic_endpoint hb hA hD
