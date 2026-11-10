module

public import ProjectAInos.Variational.Local
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# First variation of an integral action

The measure is explicit: use `volume.restrict Ω` for a region in a chart.
The domination hypothesis is uniform in the variation parameter on one
neighborhood of zero. Pointwise differentiability alone is insufficient.
This proves a derivative along each specified variation, not Fréchet
differentiability of an action on an unspecified function space.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace ProjectAInos.Variational

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E]

/-- Total Bochner-integral expression. Analytic use requires integrability. -/
noncomputable def action (μ : Measure E) (L : Lagrangian E F) (u : E → F) : ℝ :=
  ∫ x, density L u x ∂μ

/-- Integral of the first-variation density. -/
noncomputable def firstVariation (μ : Measure E) (L : Lagrangian E F)
    (u η : E → F) : ℝ := ∫ x, firstVariationDensity L u η x ∂μ

/-- Explicit differentiation-under-the-integral contract, derived from Mathlib.
No boundary condition is needed until integration by parts. -/
theorem hasDerivAt_action {μ : Measure E} {L : Lagrangian E F} {u η : E → F}
    {s : Set ℝ} {bound : E → ℝ}
    (hs : s ∈ 𝓝 (0 : ℝ))
    (hu : ∀ᵐ x ∂μ, DifferentiableAt ℝ u x)
    (hη : ∀ᵐ x ∂μ, DifferentiableAt ℝ η x)
    (hL : ∀ᵐ x ∂μ, ∀ ε ∈ s,
      DifferentiableAt ℝ (L x) (jet (perturb u η ε) x))
    (hmeas : ∀ᶠ ε in 𝓝 (0 : ℝ), AEStronglyMeasurable (density L (perturb u η ε)) μ)
    (hint : Integrable (density L u) μ)
    (hdmeas : AEStronglyMeasurable (firstVariationDensity L u η) μ)
    (hbound : ∀ᵐ x ∂μ, ∀ ε ∈ s,
      ‖firstVariationDensity L (perturb u η ε) η x‖ ≤ bound x)
    (hbound_int : Integrable bound μ) :
    Integrable (firstVariationDensity L u η) μ ∧
      HasDerivAt (fun ε => action μ L (perturb u η ε))
        (firstVariation μ L u η) 0 := by
  have hdiff : ∀ᵐ x ∂μ, ∀ ε ∈ s,
      HasDerivAt (fun t => density L (perturb u η t) x)
        (firstVariationDensity L (perturb u η ε) η x) ε := by
    filter_upwards [hu, hη, hL] with x hux hηx hLx
    exact fun ε hε => hasDerivAt_density_perturb ε hux hηx (hLx ε hε)
  simpa only [perturb_zero, action, firstVariation] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := fun ε x => density L (perturb u η ε) x)
      (F' := fun ε x => firstVariationDensity L (perturb u η ε) η x)
      hs hmeas (by simpa using hint) (by simpa using hdmeas)
      hbound hbound_int hdiff)

end ProjectAInos.Variational
