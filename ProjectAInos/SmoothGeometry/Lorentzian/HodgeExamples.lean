/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.HodgeFlat

/-! # Native Hodge normalization and nonlinear-chart examples -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianHodgeExamples
open LorentzMetric DifferentialForm

theorem flat_dt_dx (σ : LorentzConvention) (x : MinkowskiModel 3) :
    (minkowskiMetric σ 3).hodgeFiber (OrientedAtlas.standard 4) x (by decide : 2 + 2 = 3 + 1)
      (coordinateForm ![0, 1]) = -coordinateForm ![2, 3] := by
  rw [minkowskiMetric_hodgeFiber]
  exact Minkowski.hodge_dt_dx σ

theorem flat_dt_dy (σ : LorentzConvention) (x : MinkowskiModel 3) :
    (minkowskiMetric σ 3).hodgeFiber (OrientedAtlas.standard 4) x (by decide : 2 + 2 = 3 + 1)
      (coordinateForm ![0, 2]) = coordinateForm ![1, 3] := by
  rw [minkowskiMetric_hodgeFiber]
  exact Minkowski.hodge_dt_dy σ

theorem flat_dt_dz (σ : LorentzConvention) (x : MinkowskiModel 3) :
    (minkowskiMetric σ 3).hodgeFiber (OrientedAtlas.standard 4) x (by decide : 2 + 2 = 3 + 1)
      (coordinateForm ![0, 3]) = -coordinateForm ![1, 2] := by
  rw [minkowskiMetric_hodgeFiber]
  exact Minkowski.hodge_dt_dz σ

theorem flat_dy_dz (σ : LorentzConvention) (x : MinkowskiModel 3) :
    (minkowskiMetric σ 3).hodgeFiber (OrientedAtlas.standard 4) x (by decide : 2 + 2 = 3 + 1)
      (coordinateForm ![2, 3]) = coordinateForm ![0, 1] := by
  rw [minkowskiMetric_hodgeFiber]
  exact Minkowski.hodge_dy_dz σ

theorem flat_dx_dz (σ : LorentzConvention) (x : MinkowskiModel 3) :
    (minkowskiMetric σ 3).hodgeFiber (OrientedAtlas.standard 4) x (by decide : 2 + 2 = 3 + 1)
      (coordinateForm ![1, 3]) = -coordinateForm ![0, 2] := by
  rw [minkowskiMetric_hodgeFiber]
  exact Minkowski.hodge_dx_dz σ

theorem flat_dx_dy (σ : LorentzConvention) (x : MinkowskiModel 3) :
    (minkowskiMetric σ 3).hodgeFiber (OrientedAtlas.standard 4) x (by decide : 2 + 2 = 3 + 1)
      (coordinateForm ![1, 2]) = coordinateForm ![0, 3] := by
  rw [minkowskiMetric_hodgeFiber]
  exact Minkowski.hodge_dx_dy σ

/-- Four-dimensional two-forms have square `-1` in either metric convention. -/
theorem flat_two_square (σ : LorentzConvention) (x : MinkowskiModel 3)
    (α : MinkowskiModel 3 [⋀^Fin 2]→L[ℝ] ℝ) :
    (minkowskiMetric σ 3).hodgeFiber (OrientedAtlas.standard 4) x (by decide : 2 + 2 = 3 + 1)
      ((minkowskiMetric σ 3).hodgeFiber (OrientedAtlas.standard 4) x (by decide) α) = -α := by
  rw [minkowskiMetric_hodgeFiber, minkowskiMetric_hodgeFiber]
  exact Minkowski.hodgeFiber_two_square σ .standard α

open LorentzianCharts

/-- The native oriented volume is preserved by the derivative of the nonlinear shear. -/
theorem shear_volume_preserved (x : Plane) :
    ((minkowskiMetric .timeNegative 1).volumeForm (OrientedAtlas.standard 2) (shear x)).compContinuousLinearMap
        (shearLinear (2 * x 0)).toContinuousLinearMap =
      metric.volumeForm (OrientedAtlas.standard 2) x := by
  rw [LorentzianVolumeExamples.minkowski_volume, LorentzianVolumeExamples.shear_volume]
  ext v
  change coordinateForm (n := 2) (k := 2) id (fun i => shearLinear (2 * x 0) (v i)) =
    coordinateForm ![0, 1] v
  simp only [coordinateForm_apply, Matrix.det_fin_two, Matrix.of_apply]
  simp [shearLinear]
  ring

/-- Hodge in the nonconstant shear metric is the actual pulled-back Minkowski Hodge. -/
theorem shear_hodge (x : Plane) {k l : ℕ} (hkl : k + l = 2)
    (β : Plane [⋀^Fin k]→L[ℝ] ℝ) :
    metric.hodgeFiber (OrientedAtlas.standard 2) x hkl
      (β.compContinuousLinearMap (shearLinear (2 * x 0)).toContinuousLinearMap) =
    (Minkowski.hodgeFiber .timeNegative .standard hkl β).compContinuousLinearMap
      (shearLinear (2 * x 0)).toContinuousLinearMap := by
  have h := metric.hodgeFiber_naturality (minkowskiMetric .timeNegative 1)
    (OrientedAtlas.standard 2) (OrientedAtlas.standard 2) x (shear x)
    (shearLinear (2 * x 0)) (fun _ _ => rfl) (shear_volume_preserved x) hkl β
  rw [minkowskiMetric_hodgeFiber] at h
  exact h.symm

end ProjectAInos.SmoothGeometry.LorentzianHodgeExamples
