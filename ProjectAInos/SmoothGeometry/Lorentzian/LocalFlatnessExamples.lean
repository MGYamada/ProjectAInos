/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.LocalFlatness
public import ProjectAInos.SmoothGeometry.Lorentzian.LocalFlatnessConverse
public import ProjectAInos.SmoothGeometry.Lorentzian.FlatTransport
public import ProjectAInos.SmoothGeometry.Lorentzian.LocalInertialExamples
public import ProjectAInos.SmoothGeometry.Lorentzian.ParallelCoframe

/-! # Pointwise inertia does not imply local flatness -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianConformalExample

/-- The conformal plane has no local Minkowski presentation at every point:
its nonzero curvature at the origin obstructs that property. -/
theorem not_isLocallyMinkowski : ¬ metric.IsLocallyMinkowski := by
  intro h
  exact curvature_origin_ne_zero (h.curvature_eq_zero 0)

/-- Even the existence of an inertial chart at every point does not imply
local Minkowski geometry on open neighborhoods. -/
theorem pointwise_inertial_not_locallyMinkowski :
    (∀ p : Plane, ∃ e : OpenPartialHomeomorph Plane Plane, metric.IsInertialChartAt e p) ∧
      ¬ metric.IsLocallyMinkowski :=
  ⟨metric.exists_inertialChart, not_isLocallyMinkowski⟩

end ProjectAInos.SmoothGeometry.LorentzianConformalExample

namespace ProjectAInos.SmoothGeometry.LorentzianCharts

open LorentzMetric

/-- The native curvature criterion constructs local Minkowski geometry for
the nonlinear shear metric without supplying its known coframe as input. -/
theorem isLocallyMinkowski_via_curvature : metric.IsLocallyMinkowski :=
  metric.isLocallyMinkowski_of_curvature_eq_zero curvature_shear

/-- The nonlinear shear presentation has path-independent transport even
for arbitrary finite piecewise regular paths with corners. -/
theorem piecewise_transport_path_independent {x y : Plane}
    (p q : PiecewisePath 1 Plane x y) : p.transport metric = q.transport metric := by
  apply p.transport_eq_of_same_endpoints_in_flatChart metric inertialChart_mem_maximalAtlas
    (fun z _ k i j => chartChristoffel_inertial z k i j) q
  · exact Set.subset_univ _
  · exact Set.subset_univ _

theorem shearCoframe_contDiff : ContDiff ℝ ∞ (fderiv ℝ shear) := by
  change ContDiff ℝ ∞ (fun p => fderiv ℝ shear p)
  simp_rw [(hasFDerivAt_shear _).fderiv]
  exact shearLinear_contDiff.comp (contDiff_const.mul (contDiff_apply ℝ _ 0))

/-- The shear Jacobian is a nonconstant smooth invertible parallel coframe
for the nonlinear Minkowski presentation. -/
theorem shearCoframe_parallel :
    metric.IsParallelChartCoframeOn standardChart Set.univ (fderiv ℝ shear) := by
  intro p _ u v
  change fderiv ℝ (fderiv ℝ shear) p u v =
    fderiv ℝ shear p (metric.chartChristoffelBilinear standardChart p u v)
  have hd : DifferentiableAt ℝ (fderiv ℝ shear) p :=
    shearCoframe_contDiff.differentiable (by simp) p
  have he := congrArg (fun A : Plane →L[ℝ] Plane => A u)
    ((ContinuousLinearMap.apply ℝ Plane v).hasFDerivAt.comp p hd.hasFDerivAt).fderiv
  change fderiv ℝ (fun q => fderiv ℝ shear q v) p u = fderiv ℝ (fderiv ℝ shear) p u v at he
  have hG : metric.chartChristoffelBilinear standardChart p u v = ![0, 2 * u 0 * v 0] := by
    ext k
    simp only [chartChristoffelBilinear_apply, chartChristoffel_standard]
    fin_cases k <;> simp [Fin.sum_univ_succ]
  rw [← he, shear_hessian, hG, (hasFDerivAt_shear p).fderiv]
  ext k
  fin_cases k <;> simp

/-- Integrating this nonconstant parallel coframe supplies actual local
Minkowski coordinates through the general construction, at every point. -/
theorem isLocallyMinkowski_via_parallelCoframe : metric.IsLocallyMinkowski := by
  apply metric.isLocallyMinkowski_of_charts
  intro p
  apply metric.exists_minkowskiChart_of_parallelCoframe standardChart_mem_maximalAtlas
    isOpen_univ convex_univ (by intro q _; trivial)
    shearCoframe_contDiff.contDiffOn shearCoframe_parallel
    (fun q _ => ?_) (Set.mem_univ p) (Set.mem_univ (standardChart p))
  · intro v w
    have hf (u : Plane) : chartField standardChart u p = u := by
      simp [standardChart, chartField, VectorField.mpullback_apply, modelField,
        NormedSpace.fromTangentSpace, tangentSpaceCastModel]
      rfl
    rw [hf, hf]
    change metric.form p v w =
      minkowskiForm .timeNegative 1 (fderiv ℝ shear p v) (fderiv ℝ shear p w)
    rw [(hasFDerivAt_shear p).fderiv]
    rfl
  · exact ⟨shearLinear (2 * q 0), (hasFDerivAt_shear q).fderiv.symm⟩

end ProjectAInos.SmoothGeometry.LorentzianCharts
