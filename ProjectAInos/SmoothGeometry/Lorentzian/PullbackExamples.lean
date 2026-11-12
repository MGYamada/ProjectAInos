/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.CovariantPullback
public import ProjectAInos.SmoothGeometry.Lorentzian.ChartExamples

/-! # Dimension-changing and singular covariant pullback examples

The time axis pulls a two-dimensional metric back to a one-dimensional
tensor. The nonlinear-chart metric gives `(-1 + 4t²) dt²`, including its
degenerate points. Thus tensor pullback does not require an isometry or
a nondegenerate induced metric.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzianCharts

open Tensor.Shape

/-- The time axis as a smooth map from a line into spacetime. -/
def timeAxis : ℝ →L[ℝ] Plane := (ContinuousLinearMap.id ℝ ℝ).smulRight ![1, 0]

theorem timeAxis_apply (t : ℝ) : timeAxis t = ![t, 0] := by
  ext i
  fin_cases i <;> simp [timeAxis]

theorem mfderiv_timeAxis (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) timeAxis t = timeAxis := by
  rw [mfderiv_eq_fderiv, timeAxis.fderiv]
  rfl

/-- The induced tensor is computed using the actual tangent derivative. -/
theorem metric_timeAxis_pullback (t v w : ℝ) :
    covariantPullbackField 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) 2
      (timeAxis : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, Plane), Plane⟯) metric.toTensor t v w =
      (-1 + 4 * t ^ 2) * v * w := by
  rw [covariantPullbackField_two_apply]
  change metric.form (timeAxis t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) timeAxis t v)
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) timeAxis t w) = _
  rw [mfderiv_timeAxis, metric_coordinates]
  change -((v * 1) * (w * 1)) +
    (v * 0 + 2 * (t * 1) * (v * 1)) * (w * 0 + 2 * (t * 1) * (w * 1)) = _
  ring

/-- Minkowski restriction has the expected negative time component. -/
theorem minkowski_timeAxis_pullback (t v w : ℝ) :
    covariantPullbackField 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) 2
      (timeAxis : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, Plane), Plane⟯)
      (minkowskiMetric .timeNegative 1).toTensor t v w = -(v * w) := by
  rw [covariantPullbackField_two_apply]
  change minkowskiForm .timeNegative 1
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) timeAxis t v)
    (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) timeAxis t w) = _
  rw [mfderiv_timeAxis]
  simp [minkowskiForm_apply, lorentzSign, Fin.sum_univ_succ]
  change -((v * 1) * (w * 1)) + ((v * 0) * (w * 0)) = _
  ring

/-- The induced tensor may vanish even though the ambient metric is Lorentz. -/
theorem metric_timeAxis_pullback_degenerate (v w : ℝ) :
    covariantPullbackField 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) 2
      (timeAxis : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, Plane), Plane⟯)
      metric.toTensor (1 / 2 : ℝ) v w = 0 := by
  rw [metric_timeAxis_pullback]
  norm_num

/-- A rank-zero derivative annihilates the ambient metric at every point. -/
theorem metric_constant_pullback (p q v w : Plane) :
    covariantPullbackField 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) 2
      (ContMDiffMap.const p) metric.toTensor q v w = 0 := by
  rw [covariantPullbackField_two_apply]
  change metric.form p (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (fun _ : Plane => p) q v)
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) (fun _ : Plane => p) q w) = 0
  rw [mfderiv_const]
  simp

/-- A nonconstant map with a singular derivative between equal-dimensional spaces. -/
def timeProjection : Plane →L[ℝ] Plane := timeAxis.comp (proj 0)

/-- The projection kills the spatial slot but retains the nonconstant time coefficient. -/
theorem metric_timeProjection_pullback (p v w : Plane) :
    covariantPullbackField 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) 2
      (timeProjection : C^∞⟮𝓘(ℝ, Plane), Plane; 𝓘(ℝ, Plane), Plane⟯)
      metric.toTensor p v w = (-1 + 4 * (p 0) ^ 2) * v 0 * w 0 := by
  rw [covariantPullbackField_two_apply]
  change metric.form (timeProjection p)
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) timeProjection p v)
    (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) timeProjection p w) = _
  have hd : mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) timeProjection p = timeProjection := by
    rw [mfderiv_eq_fderiv, timeProjection.fderiv]
    rfl
  rw [hd, metric_coordinates]
  change -((v 0 * 1) * (w 0 * 1)) +
    (v 0 * 0 + 2 * (p 0 * 1) * (v 0 * 1)) *
      (w 0 * 0 + 2 * (p 0 * 1) * (w 0 * 1)) = _
  ring

end ProjectAInos.SmoothGeometry.LorentzianCharts
