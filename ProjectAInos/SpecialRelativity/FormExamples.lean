/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ProjectAInos.SpecialRelativity.Spacetime
public import ProjectAInos.SmoothGeometry.DifferentialForm.Coordinates

/-! # A nonzero exact field for the electrodynamics interface

This verifies differential-form calculus without imposing Maxwell's physical laws.
-/
@[expose] public section
noncomputable section
open scoped ContDiff
namespace ProjectAInos.SpecialRelativity
open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm

def coordinatePotential : Form FourVector 1 := fun x => x 0 • coordinateForm ![1]

def coordinateField : Form FourVector 2 := fun _ => coordinateForm ![0,1]

theorem coordinatePotential_contDiff : ContDiff ℝ ∞ coordinatePotential :=
  ((ContinuousLinearMap.proj 0 : FourVector →L[ℝ] ℝ).smulRight (coordinateForm ![1])).contDiff

theorem coordinatePotential_derivative (x : FourVector) :
    fderiv ℝ coordinatePotential x =
      (ContinuousLinearMap.proj 0 : FourVector →L[ℝ] ℝ).smulRight (coordinateForm ![1]) :=
  ((ContinuousLinearMap.proj 0 : FourVector →L[ℝ] ℝ).smulRight (coordinateForm ![1])).fderiv

theorem coordinatePotential_exteriorDerivative : exteriorDerivative coordinatePotential = coordinateField := by
  funext x
  ext v
  simp only [exteriorDerivative, extDeriv, coordinatePotential_derivative,
    ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  simp [coordinateField, coordinateForm_apply, Matrix.det_fin_two,
    Fin.removeNth, mul_comm, sub_eq_add_neg]

theorem coordinateField_nonzero : coordinateField ≠ 0 := by
  intro h
  have he := congrArg (fun F : Form FourVector 2 => F 0 ![Pi.single 0 1, Pi.single 1 1]) h
  norm_num [coordinateField, coordinateForm_apply, Matrix.det_fin_two, Pi.single_apply] at he

theorem coordinateField_closed : exteriorDerivative coordinateField = 0 := by
  rw [← coordinatePotential_exteriorDerivative]
  exact exteriorDerivative_squared coordinatePotential (coordinatePotential_contDiff.of_le (by simp))

theorem coordinatePotential_gauge (χ : Form FourVector 0) (hχ : ContDiff ℝ 2 χ) :
    extDeriv (coordinatePotential + extDeriv χ) = coordinateField := by
  rw [gauge_exteriorDerivative coordinatePotential χ (coordinatePotential_contDiff.differentiable (by simp)) hχ]
  exact coordinatePotential_exteriorDerivative

end ProjectAInos.SpecialRelativity
