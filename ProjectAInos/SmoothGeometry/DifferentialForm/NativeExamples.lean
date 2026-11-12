/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeFlat
public import ProjectAInos.SmoothGeometry.DifferentialForm.Coordinates
public import ProjectAInos.SmoothGeometry.Lorentzian.PullbackExamples

/-! # Nonlinear and dimension-changing native form examples -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.DifferentialForm.NativeExamples

open LorentzianCharts

/-- The standard spatial covector as a smooth native form. -/
def spatial : SmoothForm 𝓘(ℝ, Plane) Plane 1 :=
  ofFlat (fun _ => coordinateForm ![1]) contDiff_const

/-- The normalized coordinate area form. -/
def area : SmoothForm 𝓘(ℝ, Plane) Plane 2 :=
  ofFlat (fun _ => coordinateForm ![0, 1]) contDiff_const

/-- A nonlinear coordinate change produces the expected nonconstant one-form. -/
theorem spatial_shear (p v : Plane) :
    smoothPullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shearDiffeomorph.toContMDiffMap spatial p ![v] =
      v 1 + 2 * p 0 * v 0 := by
  rw [smoothPullback_apply]
  change coordinateForm ![1] (fun i => mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p (![v] i)) = _
  rw [mfderiv_shear]
  simp only [coordinateForm_apply, Matrix.det_fin_one, Matrix.of_apply]
  rfl

/-- The same nonlinear shear preserves the normalized two-form. -/
theorem area_shear (p v w : Plane) :
    smoothPullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shearDiffeomorph.toContMDiffMap area p ![v, w] =
      v 0 * w 1 - w 0 * v 1 := by
  rw [smoothPullback_apply]
  change coordinateForm ![0, 1]
    (fun i => mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p (![v, w] i)) = _
  rw [mfderiv_shear]
  simp only [coordinateForm_apply, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  change v 0 * (w 1 + 2 * p 0 * w 0) - (v 1 + 2 * p 0 * v 0) * w 0 = _
  ring

/-- Pullback from a plane to a line needs no inverse derivative. -/
theorem spatial_shear_timeAxis (t v : ℝ) :
    smoothPullback 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane)
      (timeAxis : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, Plane), Plane⟯)
      (smoothPullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shearDiffeomorph.toContMDiffMap spatial) t ![v] =
      2 * t * v := by
  rw [smoothPullback_apply]
  change smoothPullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shearDiffeomorph.toContMDiffMap spatial
    (timeAxis t) (fun i => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) timeAxis t (![v] i)) = _
  rw [mfderiv_timeAxis]
  change smoothPullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shearDiffeomorph.toContMDiffMap spatial
    (timeAxis t) ![timeAxis v] = _
  rw [spatial_shear]
  change v * 0 + 2 * (t * 1) * (v * 1) = _
  ring

/-- A nonconstant singular map annihilates the area form. -/
theorem area_timeProjection (p v w : Plane) :
    smoothPullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane)
      (timeProjection : C^∞⟮𝓘(ℝ, Plane), Plane; 𝓘(ℝ, Plane), Plane⟯) area p ![v, w] = 0 := by
  rw [smoothPullback_apply]
  change coordinateForm ![0, 1]
    (fun i => mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) timeProjection p (![v, w] i)) = _
  have hd : mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) timeProjection p = timeProjection := by
    rw [mfderiv_eq_fderiv, timeProjection.fderiv]
    rfl
  rw [hd]
  simp only [coordinateForm_apply, Matrix.det_fin_two, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  change (v 0 * 1) * (w 0 * 0) - (v 0 * 0) * (w 0 * 1) = 0
  ring

end ProjectAInos.SmoothGeometry.DifferentialForm.NativeExamples
