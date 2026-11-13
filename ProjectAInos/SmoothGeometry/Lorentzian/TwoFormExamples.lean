/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.TwoFormExterior
public import ProjectAInos.SmoothGeometry.Lorentzian.ConformalExample
public import ProjectAInos.SmoothGeometry.DifferentialForm.Coordinates

/-! # A coordinate-constant two-form with nonzero covariant derivative -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianTwoFormExamples
open DifferentialForm LorentzMetric LorentzianConformalExample

/-- The form `dt ∧ dx`, with constant model coefficients. -/
def coordinateArea : SmoothForm 𝓘(ℝ, Plane) Plane 2 :=
  ofFlat (fun _ => coordinateForm ![0, 1]) contDiff_const

/-- Curvature of the background makes the coordinate-constant form nonparallel. -/
theorem conformal_area_derivative (p : Plane) :
    metric.twoFormDerivative coordinateArea p (modelField (Pi.single 0 1) p)
      (modelField (Pi.single 1 1) p) (modelField (Pi.single 1 1) p) = -4 * p 1 := by
  rw [metric.twoFormDerivative_apply coordinateArea
    ((modelField_contMDiff _ p).mdifferentiableAt (by simp))
    ((modelField_contMDiff _ p).mdifferentiableAt (by simp))]
  simp_rw [leviCivita_modelField]
  have hm (q : Plane) (v : Plane) : modelField v q = v := rfl
  simp only [coordinateArea, ofFlat, hm]
  change mvfderiv 𝓘(ℝ, Plane) (fun _ => coordinateForm ![0, 1]
      ![(Pi.single 0 1 : Plane), Pi.single 1 1]) p (Pi.single 1 1) - _ - _ = _
  rw [mvfderiv_const]
  norm_num [Pi.single_apply]
  change -(coordinateForm (n := 2) ![0, 1]) ![![2 * p 1, 0], Pi.single 1 1] -
    (coordinateForm (n := 2) ![0, 1]) ![Pi.single 0 1, ![0, 2 * p 1]] = -(4 * p 1)
  simp [coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply]
  ring

/-- The same form is closed: exterior differentiation alternates the covariant derivative. -/
theorem coordinateArea_closed : smoothExteriorDerivative coordinateArea = 0 := by
  ext x v
  change nativeExteriorDerivative (fun _ : Plane => coordinateForm ![0, 1]) x v = 0
  rw [nativeExteriorDerivative_flat]
  simp [extDeriv]
  change (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := 2) ℝ Plane ℝ) 0 v = 0
  rw [map_zero]
  rfl

theorem conformal_area_cyclic (p : Plane) (u v w : TangentSpace 𝓘(ℝ, Plane) p) :
    metric.twoFormDerivative coordinateArea p v w u +
      metric.twoFormDerivative coordinateArea p w u v +
      metric.twoFormDerivative coordinateArea p u v w = 0 :=
  (metric.exteriorDerivative_zero_iff_covariant coordinateArea).mp coordinateArea_closed p u v w

end ProjectAInos.SmoothGeometry.LorentzianTwoFormExamples
