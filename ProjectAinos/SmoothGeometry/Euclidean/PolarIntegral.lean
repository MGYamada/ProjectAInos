/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-! # Separation of radial and angular factors in polar coordinates -/

@[expose] public section
open MeasureTheory Set Metric
namespace ProjectAinos.SmoothGeometry.Sphere

/-- Polar integration of a product of angular and radial factors for additive Haar measure. -/
theorem integral_polar_mul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (F : E → ℝ)
    (f : sphere (0 : E) 1 → ℝ) (h : ℝ → ℝ)
    (hF : ∀ (n : sphere (0 : E) 1) (r : ℝ), 0 < r → F (r • n.val) = f n * h r) :
    ∫ x, F x ∂μ = (∫ n, f n ∂μ.toSphere) *
      ∫ r in Ioi (0 : ℝ), r ^ (Module.finrank ℝ E - 1) * h r := by
  have h1 : ∫ x, F x ∂μ =
      ∫ x : ({(0 : E)}ᶜ : Set E), F x ∂(μ.comap (↑)) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl fun x ↦ F x,
      restrict_compl_singleton]
  have h2 := (Measure.measurePreserving_homeomorphUnitSphereProd
    μ).integral_comp (Homeomorph.measurableEmbedding _)
    (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f p.1 * h p.2.1)
  have h3 : ∫ x : ({(0 : E)}ᶜ : Set E), F x ∂(μ.comap (↑)) =
      ∫ x : ({(0 : E)}ᶜ : Set E), (fun p : sphere (0 : E) 1 × Ioi (0 : ℝ) => f p.1 * h p.2.1)
        (homeomorphUnitSphereProd E x) ∂(μ.comap (↑)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← hF _ _ (homeomorphUnitSphereProd E x).2.2]
    have hx0 : (x : E) ≠ 0 := x.2
    have hx : 0 < ‖(x : E)‖ := norm_pos_iff.mpr hx0
    congr 1
    simp [smul_smul, hx.ne']
  rw [h1, h3, h2, integral_prod_mul f (fun r : Ioi (0 : ℝ) => h r)]
  congr 1
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul
      ((measurable_subtype_coe.pow_const _).real_toNNReal),
    integral_subtype_comap measurableSet_Ioi
      (fun a => Real.toNNReal (a ^ (Module.finrank ℝ E - 1)) • h a)]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hr) _), smul_eq_mul]

end ProjectAinos.SmoothGeometry.Sphere
