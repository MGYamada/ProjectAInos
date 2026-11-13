/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.HodgeSquare

/-! # Smooth Hodge on the curved conformal Lorentz plane -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianHodgeCurvedExamples
open LorentzMetric DifferentialForm LorentzianConformalExample

/-- The local inverse-metric preprocessing is multiplication by `exp(-2x²)`. -/
theorem conformal_chartMap (p v : Plane) :
    metric.hodgeChartMap (OpenPartialHomeomorph.refl Plane) p v = Real.exp (-(2 * (p 1)^2)) • v := by
  have he := (OrientedAtlas.standard 2).mem_atlas p
  have hi : (metric.chartMetric (OpenPartialHomeomorph.refl Plane) p).IsInvertible :=
    metric.chartMetric_isInvertible he ((OrientedAtlas.standard 2).mem_source p)
  apply hi.injective
  change metric.chartMetric (OpenPartialHomeomorph.refl Plane) p
    ((metric.chartMetric (OpenPartialHomeomorph.refl Plane) p).inverse (Minkowski.flat .timeNegative v)) = _
  rw [ContinuousLinearMap.IsInvertible.self_apply_inverse hi]
  ext w
  rw [chartMetric_apply, chartField_refl, chartField_refl]
  change minkowskiForm .timeNegative 1 v w =
    Real.exp (2 * (p 1)^2) * minkowskiForm .timeNegative 1 (Real.exp (-(2 * (p 1)^2)) • v) w
  simp only [map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- In two dimensions Hodge on all one-forms is unchanged by this nonconstant conformal factor. -/
theorem conformal_one (p : Plane) (α : Plane [⋀^Fin 1]→L[ℝ] ℝ) :
    metric.hodgeFiber (OrientedAtlas.standard 2) p (by decide : 1 + 1 = 1 + 1) α =
      Minkowski.hodgeFiber .timeNegative .standard (by decide : 1 + 1 = 1 + 1) α := by
  rw [metric.hodgeFiber_standard, LorentzianVolumeExamples.conformal_density]
  have hα : α.compContinuousLinearMap (metric.hodgeChartMap (OpenPartialHomeomorph.refl Plane) p) =
      Real.exp (-(2 * (p 1)^2)) • α := by
    ext v
    change α (fun i => metric.hodgeChartMap (OpenPartialHomeomorph.refl Plane) p (v i)) = _
    simp only [conformal_chartMap]
    simpa using α.map_smul_univ (fun _ => Real.exp (-(2 * (p 1)^2))) v
  rw [hα, map_smul, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

/-- The curved example also verifies the identity as an equality of smooth native sections. -/
theorem conformal_smooth_one (α : Form Plane 1) (hα : ContDiff ℝ ∞ α) (p : Plane) :
    metric.smoothHodge (OrientedAtlas.standard 2) (by decide : 1 + 1 = 1 + 1) (ofFlat α hα) p =
      Minkowski.hodgeFiber .timeNegative .standard (by decide : 1 + 1 = 1 + 1) (α p) :=
  conformal_one p (α p)

/-- Curvature is nonzero while the one-form Hodge square is positive. -/
theorem conformal_square_and_curvature (p : Plane) (α : Plane [⋀^Fin 1]→L[ℝ] ℝ) :
    metric.hodgeFiber (OrientedAtlas.standard 2) p (by decide : 1 + 1 = 1 + 1)
      (metric.hodgeFiber (OrientedAtlas.standard 2) p (by decide) α) = α ∧
    metric.scalarCurvature p = -4 * Real.exp (-(2 * (p 1)^2)) := by
  constructor
  · rw [metric.hodgeFiber_square]
    norm_num [LorentzConvention.negativeIndex]
  · exact scalarCurvature_eq p

end ProjectAInos.SmoothGeometry.LorentzianHodgeCurvedExamples
