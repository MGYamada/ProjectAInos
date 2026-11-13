/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.ParticleAction
public import ProjectAInos.SpecialRelativity.ParticleAction
public import ProjectAInos.SmoothGeometry.Lorentzian.MotionExamples

/-! # Minkowski specialization of intrinsic proper time and particle action -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace ProjectAInos.GeneralRelativity

open SmoothGeometry LorentzMetric

variable {d : ℕ}

/-- The curved definition uses exactly the existing SR clock rate in Minkowski space. -/
theorem speedAlong_minkowski (γ : ℝ → MinkowskiModel d) (t : ℝ) :
    speedAlong (minkowskiMetric .timeNegative d) γ t =
      SpecialRelativity.properSpeed (deriv γ t) := by
  unfold speedAlong properSpeed
  rw [curveVelocity_model]
  change Real.sqrt (-minkowskiForm .timeNegative d (deriv γ t) (deriv γ t)) = _
  simpa using SpecialRelativity.properSpeed_convention .timeNegative (deriv γ t)

/-- Equality with the SR functional, not merely an agreement on inertial lines. -/
theorem properTime_minkowski (γ : ℝ → MinkowskiModel d) (a b : ℝ) :
    properTime (minkowskiMetric .timeNegative d) γ a b = SpecialRelativity.properTime γ a b := by
  unfold properTime SpecialRelativity.properTime
  simp_rw [speedAlong_minkowski]

theorem freeAction_minkowski (m : ℝ) (γ : ℝ → SpecialRelativity.Spacetime) (a b : ℝ) :
    freeAction (minkowskiMetric .timeNegative 3) m γ a b =
      SpecialRelativity.freeAction m γ a b := by
  rw [freeAction, SpecialRelativity.freeAction, properTime_minkowski]

/-- The SR specialization also agrees with the existing open-domain mechanics action. -/
theorem freeAction_minkowski_eq_mechanics (m : ℝ)
    (γ : ℝ → SpecialRelativity.Spacetime) (a b : ℝ) :
    freeAction (minkowskiMetric .timeNegative 3) m γ a b =
      Mechanics.action a b (SpecialRelativity.freeLagrangian m) γ := by
  rw [freeAction_minkowski, SpecialRelativity.freeAction_eq_action]

theorem properTime_minkowski_inertial (p v : MinkowskiModel d) (a b : ℝ) :
    properTime (minkowskiMetric .timeNegative d) (fun t => p + t • v) a b =
      (b - a) * SpecialRelativity.properSpeed v := by
  rw [properTime_minkowski, SpecialRelativity.properTime_inertial]

end ProjectAInos.GeneralRelativity
