/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.ParticleAction
public import ProjectAInos.SmoothGeometry.Lorentzian.MotionExamples
public import ProjectAInos.SmoothGeometry.Lorentzian.ConformalExample

/-! # Intrinsic clocks in nonlinear flat coordinates and a curved metric -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace ProjectAInos.GeneralRelativity.ClockExamples

open SmoothGeometry LorentzMetric LorentzianCharts

/-- The nonlinear-chart parabola still has unit proper-time rate. -/
theorem shear_speed (t : ℝ) : speedAlong metric inertialTimePath t = 1 := by
  unfold speedAlong properSpeed
  rw [curveVelocity_model, (inertialTimePath_hasDerivAt t).deriv]
  change Real.sqrt (-metric.form (inertialTimePath t) ![1, -2 * t] ![1, -2 * t]) = 1
  rw [metric_coordinates]
  simp [inertialTimePath]

theorem shear_properTime (a b : ℝ) : properTime metric inertialTimePath a b = b - a := by
  unfold properTime
  simp_rw [shear_speed]
  simp

theorem shear_freeAction (m a b : ℝ) :
    freeAction metric m inertialTimePath a b = -m * (b - a) := by
  rw [freeAction, shear_properTime]

/-- A clock at a fixed spatial coordinate in the curved conformal example. -/
def stationaryClock (x : ℝ) (t : ℝ) : Plane := ![t, x]

theorem stationaryClock_hasDerivAt (x t : ℝ) :
    HasDerivAt (stationaryClock x) ![1, 0] t := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_id t
  · exact hasDerivAt_const t x

theorem conformal_clock_norm (x t : ℝ) :
    LorentzianConformalExample.metric.form (stationaryClock x t)
      (curveVelocity (stationaryClock x) t) (curveVelocity (stationaryClock x) t) =
      -Real.exp (2 * x ^ 2) := by
  rw [curveVelocity_model, (stationaryClock_hasDerivAt x t).deriv]
  change LorentzianConformalExample.metric.form (stationaryClock x t) ![1, 0] ![1, 0] = _
  rw [LorentzianConformalExample.metric_coordinates]
  simp [stationaryClock]

theorem conformal_clock_timelike (x t : ℝ) :
    Timelike LorentzianConformalExample.metric (curveVelocity (stationaryClock x) t) := by
  unfold Timelike
  rw [conformal_clock_norm]
  exact neg_neg_of_pos (Real.exp_pos _)

/-- The exact rate is computed from the native metric, including at curved points. -/
theorem conformal_clock_speed (x t : ℝ) :
    speedAlong LorentzianConformalExample.metric (stationaryClock x) t = Real.exp (x ^ 2) := by
  unfold speedAlong properSpeed
  rw [conformal_clock_norm, neg_neg, two_mul, Real.exp_add,
    ← pow_two, Real.sqrt_sq (Real.exp_nonneg _)]

theorem conformal_clock_properTime (x a b : ℝ) :
    properTime LorentzianConformalExample.metric (stationaryClock x) a b =
      (b - a) * Real.exp (x ^ 2) := by
  unfold properTime
  simp_rw [conformal_clock_speed]
  simp

theorem conformal_clock_quadraticAction (x a b : ℝ) :
    quadraticAction LorentzianConformalExample.metric (stationaryClock x) a b =
      -(b - a) / 2 * Real.exp (2 * x ^ 2) := by
  unfold quadraticAction
  simp_rw [conformal_clock_norm]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  ring

end ProjectAInos.GeneralRelativity.ClockExamples
