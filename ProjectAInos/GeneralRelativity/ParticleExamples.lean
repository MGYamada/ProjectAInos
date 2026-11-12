/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.GeneralRelativity.FreeGeodesic
public import ProjectAInos.GeneralRelativity.ClockExamples

/-! # A non-affine stationary massive worldline

The nonlinear flat chart and exponential parameter both contribute nonzero
coordinate acceleration. The square-root action is stationary; the quadratic
action is not stationary in this parameter.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace ProjectAInos.GeneralRelativity.ParticleExamples

open SmoothGeometry LorentzMetric LorentzianCharts

def exponentialClock : ℝ → Plane := inertialTimePath ∘ Real.exp

theorem exponentialClock_contDiff : ContDiff ℝ ∞ exponentialClock :=
  inertialTimePath_contDiff.comp Real.contDiff_exp

theorem exponentialClock_speed (t : ℝ) : speedAlong metric exponentialClock t = Real.exp t := by
  rw [exponentialClock, speedAlong_comp metric
    (inertialTimePath_contDiff.contMDiff.mdifferentiable (by simp) _)
    Real.differentiable_exp.differentiableAt, Real.deriv_exp,
    abs_of_pos (Real.exp_pos t), ClockExamples.shear_speed, mul_one]

theorem exponentialClock_timelike (t : ℝ) : Timelike metric (curveVelocity exponentialClock t) := by
  apply (properSpeed_pos_iff metric _).mp
  change 0 < speedAlong metric exponentialClock t
  rw [exponentialClock_speed]
  exact Real.exp_pos t

/-- Its nonzero covariant acceleration is exactly its velocity. -/
theorem exponentialClock_acceleration (t : ℝ) :
    metric.covariantAlong (curveVelocity exponentialClock) t = curveVelocity exponentialClock t := by
  rw [exponentialClock, metric.covariantAcceleration_reparam
    ((inertialTimePath_contDiff.of_le (by simp)).contMDiff.contMDiffAt)
    ((Real.contDiff_exp : ContDiff ℝ 2 Real.exp).contDiffAt),
    curveVelocity_comp (inertialTimePath_contDiff.contMDiff.mdifferentiable (by simp) _)
      Real.differentiable_exp.differentiableAt,
    (inertialTimePath_geodesic (Real.exp t) (mem_univ _)).2]
  simp only [Real.deriv_exp, smul_zero, add_zero]

theorem exponentialClock_free_stationary {m a b : ℝ} (hm : 0 < m) (hab : a < b) :
    ∀ η : ℝ → Plane, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => freeAction metric m (Variational.perturb exponentialClock η ε) a b) 0 0 := by
  apply (freeAction_stationary_iff_tangential metric hm hab
    (exponentialClock_contDiff.of_le (by simp)) (fun t _ => exponentialClock_timelike t)).mpr
  intro t _
  exact ⟨1, by simpa only [one_smul] using exponentialClock_acceleration t⟩

theorem exponentialClock_not_quadratic_stationary {a b : ℝ} (hab : a < b) :
    ¬(∀ η : ℝ → Plane, Mechanics.FixedEndpointVariation a b η →
      HasDerivAt (fun ε => quadraticAction metric (Variational.perturb exponentialClock η ε) a b)
        0 0) := by
  intro hs
  have hg := (quadraticAction_stationary_iff_geodesic metric hab
    (exponentialClock_contDiff.of_le (by simp))).mp hs
  have ht : (a + b) / 2 ∈ Ioo a b := by constructor <;> linarith
  have hz := (hg _ ht).2
  rw [exponentialClock_acceleration] at hz
  have hv := exponentialClock_timelike ((a + b) / 2)
  unfold Timelike at hv
  simp only [hz, map_zero, lt_self_iff_false] at hv

theorem exponentialClock_properTime (a b : ℝ) :
    properTime metric exponentialClock a b = Real.exp b - Real.exp a := by
  rw [exponentialClock, properTime_reparametrize metric inertialTimePath Real.exp a b
    (fun _ _ => (inertialTimePath_contDiff.of_le (by simp)).contMDiff.contMDiffAt)
    (fun _ _ => (Real.contDiff_exp : ContDiff ℝ 1 Real.exp).contDiffAt)
    (fun t _ => by rw [Real.deriv_exp]; exact (Real.exp_pos t).le),
    ClockExamples.shear_properTime]

end ProjectAInos.GeneralRelativity.ParticleExamples
