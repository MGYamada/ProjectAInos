/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Christoffel
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartConnection
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartExamples
public import ProjectAInos.SmoothGeometry.Lorentzian.Naturality

/-! # Native connection checks in nonlinear Minkowski coordinates

The metric and both charts are the objects constructed in `ChartExamples`.
Here the coefficients are derived from the Lorentz Levi-Civita connection.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianCharts

open LorentzMetric

/-- Exact derivative of the nonlinear metric on constant coordinate fields. -/
theorem hasFDerivAt_metric_pair (p v w : Plane) :
    HasFDerivAt (fun q => metric.form q (modelField v q) (modelField w q))
      ((2 * v 0 * (w 1 + 2 * p 0 * w 0) +
        2 * w 0 * (v 1 + 2 * p 0 * v 0)) • (proj 0 : Plane →L[ℝ] ℝ)) p := by
  change HasFDerivAt (fun q : Plane => metric.form q v w) _ p
  simp_rw [metric_coordinates]
  have hp := (proj 0 : Plane →L[ℝ] ℝ).hasFDerivAt (x := p)
  have hv := ((hp.const_mul 2).mul_const (v 0)).const_add (v 1)
  have hw := ((hp.const_mul 2).mul_const (w 0)).const_add (w 1)
  convert! (hv.mul hw).const_add (-(v 0 * w 0)) using 1
  ext u
  simp
  ring

/-- The only connection term in the nonlinear shear coordinates is spatial:
`∇_v w = (0, 2 vᵗ wᵗ)` for constant coordinate fields. -/
theorem leviCivita_modelField (p v w : Plane) :
    metric.leviCivita (modelField w) p (modelField v p) =
      modelField ![0, 2 * v 0 * w 0] p := by
  apply (metric.flat p).injective
  ext z
  change metric.form p (metric.leviCivita (modelField w) p (modelField v p)) z =
    metric.form p ![0, 2 * v 0 * w 0] z
  have hz : modelField (NormedSpace.fromTangentSpace p z) p = z :=
    (NormedSpace.fromTangentSpace p).symm_apply_apply z
  have h := metric.modelField_leviCivita_pairing p v w (NormedSpace.fromTangentSpace p z)
  rw [hz] at h
  rw [h, (hasFDerivAt_metric_pair p w _).fderiv,
    (hasFDerivAt_metric_pair p _ v).fderiv, (hasFDerivAt_metric_pair p v w).fderiv]
  simp [metric_coordinates, NormedSpace.fromTangentSpace, tangentSpaceCastModel]
  ring

/-- All eight coefficients, including `Γˣ_tt = 2`, of the actual connection. -/
theorem christoffel_shear (p : Plane) (k i j : Fin 2) :
    metric.christoffel p k i j = if k = 1 ∧ i = 0 ∧ j = 0 then 2 else 0 := by
  rw [christoffel, leviCivita_modelField]
  simp only [modelField, ContinuousLinearEquiv.apply_symm_apply]
  fin_cases k <;> fin_cases i <;> fin_cases j <;> norm_num [Pi.single_apply]

/-- Differentiate the actual transition Jacobian, with the second direction fixed. -/
theorem hasFDerivAt_shear_direction (p w : Plane) :
    HasFDerivAt (fun q => fderiv ℝ shear q w)
      ((proj 0 : Plane →L[ℝ] ℝ).smulRight ![0, 2 * w 0]) p := by
  simp_rw [(hasFDerivAt_shear _).fderiv]
  apply hasFDerivAt_pi''
  intro i
  fin_cases i
  · convert! hasFDerivAt_const (𝕜 := ℝ) (w 0) p using 1
    ext u
    simp
  · have hp := (proj 0 : Plane →L[ℝ] ℝ).hasFDerivAt (x := p)
    have h := (hp.const_mul 2).mul_const (w 0)
    convert! h.const_add (w 1) using 1
    ext u
    simp
    ring

/-- The second derivative is nonzero although the inertial coefficients vanish. -/
theorem shear_hessian (p v w : Plane) :
    fderiv ℝ (fun q => fderiv ℝ shear q w) p v = ![0, 2 * v 0 * w 0] := by
  rw [(hasFDerivAt_shear_direction p w).fderiv]
  ext i
  fin_cases i <;> simp
  ring

/-- The flat specialization of the connection transformation law. The Jacobian
maps the nonlinear-chart connection term to the actual Hessian of the transition. -/
theorem connection_shear_transformation (p v w : Plane) :
    fderiv ℝ shear p
      (NormedSpace.fromTangentSpace p
        (metric.leviCivita (modelField w) p (modelField v p))) =
      fderiv ℝ (fun q => fderiv ℝ shear q w) p v := by
  rw [leviCivita_modelField, modelField, ContinuousLinearEquiv.apply_symm_apply,
    (hasFDerivAt_shear p).fderiv, shear_hessian]
  ext i
  fin_cases i <;> simp

/-- The earlier concrete metric agrees with the general pullback construction. -/
theorem metric_eq_pullback :
    metric = (minkowskiMetric .timeNegative 1).pullback shearDiffeomorph
      shearDiffeomorph.contMDiff (fun x =>
        shearDiffeomorph.isInvertible_mfderiv (x := x) (by simp)) := by
  apply LorentzMetric.ext
  intro p v w
  rw [pullback_form]
  exact metric_covariance p v w

/-- The general connection naturality theorem applies to this actual nonlinear
chart for every target field differentiable at the evaluation point. -/
theorem leviCivita_shear_naturality
    {Y : ∀ y : Plane, TangentSpace 𝓘(ℝ, Plane) y} {p : Plane}
    (hY : MDifferentiableAt 𝓘(ℝ, Plane) (𝓘(ℝ, Plane).prod 𝓘(ℝ, Plane))
      (T% Y) (shear p)) (v : TangentSpace 𝓘(ℝ, Plane) p) :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p
      (metric.leviCivita (VectorField.mpullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear Y) p v) =
      (minkowskiMetric .timeNegative 1).leviCivita Y (shear p)
        (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p v) :=
  metric.leviCivita_naturality_of_metric (minkowskiMetric .timeNegative 1)
    shear_contDiff.contMDiff metric_covariance hY v

/-- The manifold-chart interface recovers the nonzero coefficients in the
standard `(t,x)` chart of the nonlinear metric. -/
theorem chartChristoffel_standard (p : Plane) (k i j : Fin 2) :
    metric.chartChristoffel standardChart p k i j =
      if k = 1 ∧ i = 0 ∧ j = 0 then 2 else 0 := by
  rw [standardChart, chartChristoffel_model, christoffel_shear]

/-- The coefficients of this same metric vanish in its actual inertial chart. -/
theorem chartChristoffel_inertial (p : Plane) (k i j : Fin 2) :
    metric.chartChristoffel inertialChart p k i j = 0 := by
  have hv : mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p
      (chartField inertialChart (Pi.single i 1) p) = modelField (Pi.single i 1) (shear p) := by
    change mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p
      (VectorField.mpullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear (modelField (Pi.single i 1)) p) = _
    have hinv : (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p).IsInvertible :=
      shearDiffeomorph.isInvertible_mfderiv (x := p) (by simp)
    exact hinv.self_apply_inverse _
  have h := leviCivita_shear_naturality
    ((modelField_contMDiff (Pi.single j 1)).mdifferentiableAt (by simp))
    (chartField inertialChart (Pi.single i 1) p)
  rw [hv] at h
  change NormedSpace.fromTangentSpace (shear p)
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p
      (metric.leviCivita (VectorField.mpullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane)
        shear (modelField (Pi.single j 1))) p (chartField inertialChart (Pi.single i 1) p))) k = 0
  rw [h]
  simpa using (minkowskiMetric .timeNegative 1).leviCivita_model_coordinates
    (x := shear p) (differentiableAt_const (Pi.single j 1)) (Pi.single i 1) k

/-- Regression of the general overlap law on the two actual nonlinear charts.
The surviving term is the second derivative of their transition map. -/
theorem chart_transformation_shear (p : Plane) (k i j : Fin 2) :
    (∑ l, fderiv ℝ shear p (Pi.single l 1) k * metric.christoffel p l i j) =
      fderiv ℝ (fun z => fderiv ℝ shear z (Pi.single j 1)) p (Pi.single i 1) k := by
  have h := metric.chartChristoffel_transformation standardChart_mem_maximalAtlas
    inertialChart_mem_maximalAtlas (x := p) (by simp [standardChart])
    (by simp [inertialChart]) k i j
  simp only [chartChristoffel_inertial, zero_mul, Finset.sum_const_zero, add_zero] at h
  change (∑ l, fderiv ℝ shear p (Pi.single l 1) k *
      metric.chartChristoffel (Homeomorph.refl Plane).toOpenPartialHomeomorph p l i j) =
    fderiv ℝ (fun z => fderiv ℝ shear z (Pi.single j 1)) p (Pi.single i 1) k at h
  simpa only [chartChristoffel_model] using h

end ProjectAInos.SmoothGeometry.LorentzianCharts
