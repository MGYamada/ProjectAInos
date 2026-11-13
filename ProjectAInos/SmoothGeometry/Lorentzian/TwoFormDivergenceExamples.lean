/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.TwoFormRaised
public import ProjectAInos.SmoothGeometry.Lorentzian.TwoFormExamples

/-! # Nonzero two-form divergence on a curved conformal plane -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianTwoFormExamples
open DifferentialForm LorentzMetric LorentzianConformalExample

theorem conformal_area_derivative_apply (p u v w : Plane) :
    metric.twoFormDerivative coordinateArea p (modelField v p) (modelField w p) (modelField u p) =
      -4 * p 1 * u 1 * (v 0 * w 1 - v 1 * w 0) := by
  rw [metric.twoFormDerivative_apply coordinateArea
    ((modelField_contMDiff _ p).mdifferentiableAt (by simp))
    ((modelField_contMDiff _ p).mdifferentiableAt (by simp))]
  simp_rw [leviCivita_modelField]
  have hm (q : Plane) (v : Plane) : modelField v q = v := rfl
  simp only [coordinateArea, ofFlat, hm]
  change mvfderiv 𝓘(ℝ, Plane) (fun _ => coordinateForm ![0, 1] ![v, w]) p u - _ - _ = _
  rw [mvfderiv_const]
  simp only [zero_apply, zero_sub]
  change -(coordinateForm (n := 2) ![0, 1])
      ![![2 * p 1 * (u 0 * v 1 + u 1 * v 0), 2 * p 1 * (u 0 * v 0 + u 1 * v 1)], w] -
    (coordinateForm (n := 2) ![0, 1])
      ![v, ![2 * p 1 * (u 0 * w 1 + u 1 * w 0), 2 * p 1 * (u 0 * w 0 + u 1 * w 1)]] = _
  simp [coordinateForm_apply, Matrix.det_fin_two]
  ring

/-- A closed, coordinate-constant form has nonzero covariant divergence in the curved metric. -/
theorem conformal_area_divergence (p : Plane) :
    metric.twoFormDivergence coordinateArea p =
      modelField ![-4 * p 1 * Real.exp (-(4 * (p 1)^2)), 0] p := by
  apply (NormedSpace.fromTangentSpace p).injective
  ext j
  rw [metric.twoFormDivergence_components coordinateArea p (NormedSpace.fromTangentSpace p)]
  change (∑ b : Fin 2, ∑ a : Fin 2, ∑ i : Fin 2,
    metric.twoFormDerivative coordinateArea p (modelField (Pi.single a 1) p)
      (modelField (Pi.single b 1) p) (modelField (Pi.single i 1) p) *
      metric.inverseComponent p (NormedSpace.fromTangentSpace p) a i *
      metric.inverseComponent p (NormedSpace.fromTangentSpace p) j b) =
        ![-4 * p 1 * Real.exp (-(4 * (p 1)^2)), 0] j
  simp_rw [conformal_area_derivative_apply, inverseComponent_eq]
  have hexp : Real.exp (-(2 * (p 1)^2)) * Real.exp (-(2 * (p 1)^2)) =
      Real.exp (-(4 * (p 1)^2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  fin_cases j <;> norm_num [Fin.sum_univ_succ, Pi.single_apply]
  nlinarith only [congrArg (fun r => 4 * p 1 * r) hexp]

end ProjectAInos.SmoothGeometry.LorentzianTwoFormExamples
