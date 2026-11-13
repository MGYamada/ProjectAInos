/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.LocalInertial
public import ProjectAInos.SmoothGeometry.Lorentzian.ConformalExample
public import ProjectAInos.SmoothGeometry.Lorentzian.ConnectionExamples

/-! # Flat and curved local inertial chart examples -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry

open LorentzMetric

namespace LorentzianCharts

/-- The quadratic correction at the origin of the shear example is exactly
the original nonlinear inertial-coordinate map. This fixes its Hessian sign. -/
theorem quadratic_correction_eq_shear (p : Plane) :
    QuadraticChart.correction (ContinuousLinearEquiv.refl ℝ Plane)
      (metric.chartChristoffelBilinear standardChart 0) 0 p = shear p := by
  ext k
  simp only [QuadraticChart.correction, ContinuousLinearEquiv.refl_apply, sub_zero,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul, chartChristoffelBilinear_apply,
    chartChristoffel_standard]
  fin_cases k <;> norm_num [shear, Fin.sum_univ_succ]
  ring

end LorentzianCharts

namespace LorentzianConformalExample

/-- The ordinary chart is already locally inertial at the origin of this
curved metric, including all first metric derivatives. -/
theorem standardChart_inertial_origin :
    metric.IsInertialChartAt (Homeomorph.refl Plane).toOpenPartialHomeomorph 0 := by
  let e := (Homeomorph.refl Plane).toOpenPartialHomeomorph
  have he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ Plane :=
    IsManifold.chart_mem_maximalAtlas (0 : Plane)
  have hp : (0 : Plane) ∈ e.source := Set.mem_univ _
  have hΓ (k i j : Fin 2) : metric.chartChristoffel e 0 k i j = 0 := by
    rw [chartChristoffel_model, christoffel_origin]
  refine ⟨he, hp, rfl, ?_, hΓ, metric.chartComponent_fderiv_eq_zero he hp hΓ⟩
  intro v w
  have hf (u : Plane) : chartField e u 0 = u := by
    simp [e, chartField, mpullback_apply, modelField, NormedSpace.fromTangentSpace,
      tangentSpaceCastModel]
    rfl
  rw [hf, hf, metric_coordinates]
  simp [minkowskiForm_apply, lorentzSign, Fin.sum_univ_succ]

/-- Local inertial normalization at a point coexists with nonzero curvature.
It does not imply Minkowski coordinates on an open neighborhood. -/
theorem inertial_origin_curved :
    metric.IsInertialChartAt (Homeomorph.refl Plane).toOpenPartialHomeomorph 0 ∧
      metric.curvature 0 ≠ 0 ∧ metric.scalarCurvature 0 = -4 :=
  ⟨standardChart_inertial_origin, curvature_origin_ne_zero, scalarCurvature_origin⟩

end LorentzianConformalExample

end ProjectAInos.SmoothGeometry
