/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeExamples
public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeNaturality

/-! # A nonzero native exterior derivative in nonlinear charts

The potential `T dX` has derivative `dT ∧ dX`. Its nonlinear shear has
coefficients `t dx + 2t² dt`, whose derivative has the same normalization.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.DifferentialForm.NativeExamples

open LorentzianCharts

def potentialCoefficients : Form Plane 1 := fun p => p 0 • coordinateForm ![1]

theorem potentialCoefficients_contDiff : ContDiff ℝ ∞ potentialCoefficients :=
  ((ContinuousLinearMap.proj 0 : Plane →L[ℝ] ℝ).smulRight (coordinateForm ![1])).contDiff

theorem potentialCoefficients_exteriorDerivative :
    exteriorDerivative potentialCoefficients = fun _ => coordinateForm ![0, 1] := by
  funext x
  have hd : fderiv ℝ potentialCoefficients x =
      (ContinuousLinearMap.proj 0 : Plane →L[ℝ] ℝ).smulRight (coordinateForm ![1]) :=
    ((ContinuousLinearMap.proj 0 : Plane →L[ℝ] ℝ).smulRight (coordinateForm ![1])).fderiv
  ext v
  simp only [exteriorDerivative, extDeriv, hd,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp [coordinateForm_apply, Matrix.det_fin_two, Fin.removeNth, mul_comm, sub_eq_add_neg]
  ring

/-- A nonconstant smooth native potential. -/
def potential : SmoothForm 𝓘(ℝ, Plane) Plane 1 :=
  ofFlat potentialCoefficients potentialCoefficients_contDiff

/-- The native derivative has the standard nonzero normalization. -/
theorem potential_exteriorDerivative : smoothExteriorDerivative potential = area := by
  ext x v
  change nativeExteriorDerivative potentialCoefficients x v = coordinateForm ![0, 1] v
  rw [nativeExteriorDerivative_flat]
  change exteriorDerivative potentialCoefficients x v = _
  rw [potentialCoefficients_exteriorDerivative]

/-- The exact native area form is nonzero. -/
theorem area_nonzero : area ≠ 0 := by
  intro h
  have he := congrArg (fun α : SmoothForm 𝓘(ℝ, Plane) Plane 2 =>
    α 0 ![Pi.single 0 1, Pi.single 1 1]) h
  change coordinateForm ![0, 1] ![Pi.single 0 1, Pi.single 1 1] = 0 at he
  norm_num [coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply] at he

/-- The native exact area form is closed. -/
theorem area_closed : smoothExteriorDerivative area = 0 := by
  rw [← potential_exteriorDerivative]
  exact smoothExteriorDerivative_squared potential

/-- A nonlinear pullback gives the same derivative, including all second-derivative terms. -/
theorem shear_potential_exteriorDerivative (p v w : Plane) :
    smoothExteriorDerivative
      (smoothPullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shearDiffeomorph.toContMDiffMap potential) p ![v, w] =
        v 0 * w 1 - w 0 * v 1 := by
  rw [smoothExteriorDerivative_pullback, potential_exteriorDerivative]
  exact area_shear p v w

/-- The coordinate derivative agrees in the actual nonlinear maximal-atlas chart. -/
theorem inertial_chart_exteriorDerivative (p : Plane) :
    extDeriv (chartCoefficients inertialChart (fun x => potential x)) p =
      chartCoefficients inertialChart (fun x => area x) p := by
  rw [← chartCoefficients_smoothExteriorDerivative potential inertialChart_mem_maximalAtlas
    (show p ∈ inertialChart.target from by simp [inertialChart]), potential_exteriorDerivative]

/-- Naturality also covers the noninvertible tangent map of the time-axis inclusion. -/
theorem timeAxis_potential_exteriorDerivative (t v w : ℝ) :
    smoothExteriorDerivative (smoothPullback 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane)
      (timeAxis : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, Plane), Plane⟯) potential) t ![v, w] = 0 := by
  rw [smoothExteriorDerivative_pullback, potential_exteriorDerivative, smoothPullback_apply]
  change coordinateForm ![0, 1]
    (fun i => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) timeAxis t (![v, w] i)) = 0
  rw [mfderiv_timeAxis]
  simp only [coordinateForm_apply, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  change (v * 1) * (w * 0) - (v * 0) * (w * 1) = 0
  ring

end ProjectAInos.SmoothGeometry.DifferentialForm.NativeExamples
