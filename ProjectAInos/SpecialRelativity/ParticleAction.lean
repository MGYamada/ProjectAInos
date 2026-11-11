module
public import ProjectAInos.SpecialRelativity.ProperTime
public import ProjectAInos.SpecialRelativity.Spacetime
public import ProjectAInos.Mechanics.OpenDomain
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Free massive particle action

The square-root Lagrangian is smooth on the open timelike cone. Its extension
to other velocities is not assumed to be differentiable. Units are c = 1.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped ContDiff
namespace ProjectAInos.SpecialRelativity
open SmoothGeometry SmoothGeometry.Minkowski Mechanics

theorem contDiff_intervalQuadratic {n : ℕ∞ω} :
    ContDiff ℝ n (intervalQuadratic : Spacetime → ℝ) :=
  (pair.contDiff.clm_apply contDiff_id)

theorem hasFDerivAt_intervalQuadratic (v : Spacetime) :
    HasFDerivAt (intervalQuadratic : Spacetime → ℝ) ((2 : ℝ) • pair v) v := by
  have h := (pair.hasFDerivAt (x := v)).clm_apply (hasFDerivAt_id v)
  have he : (pair v).comp (ContinuousLinearMap.id ℝ Spacetime) + pair.flip v = (2 : ℝ) • pair v := by
    ext w
    simp only [add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.flip_apply, smul_apply, smul_eq_mul]
    rw [Minkowski.pair_comm w v]
    ring
  simp only [id_eq] at h
  rw [he] at h
  exact h

theorem contDiffAt_properSpeed {v : Spacetime} (hv : Timelike v) {n : ℕ∞ω} :
    ContDiffAt ℝ n properSpeed v :=
  contDiff_intervalQuadratic.contDiffAt.sqrt (ne_of_gt hv)

theorem hasFDerivAt_properSpeed {v : Spacetime} (hv : Timelike v) :
    HasFDerivAt properSpeed ((properSpeed v)⁻¹ • pair v) v := by
  have h := (hasFDerivAt_intervalQuadratic v).sqrt (ne_of_gt hv)
  have he : (1 / (2 * Real.sqrt (intervalQuadratic v))) • ((2 : ℝ) • pair v) =
      (properSpeed v)⁻¹ • pair v := by
    rw [smul_smul]
    congr 1
    simp only [properSpeed]
    ring
  rw [he] at h
  exact h

theorem contDiffAt_fourVelocity {v : Spacetime} (hv : Timelike v) {n : ℕ∞ω} :
    ContDiffAt ℝ n fourVelocity v :=
  ((contDiffAt_properSpeed hv).inv (ne_of_gt (Real.sqrt_pos.mpr hv))).smul contDiffAt_id

def freeLagrangian (m : ℝ) : Lagrangian Spacetime := fun _ z => -m * properSpeed z.2
def freeAction (m : ℝ) (γ : ℝ → Spacetime) (a b : ℝ) : ℝ := -m * properTime γ a b
def timelikeJets : Set (ℝ × (Spacetime × Spacetime)) := {z | Timelike z.2.2}

theorem isOpen_timelikeJets : IsOpen timelikeJets :=
  isOpen_lt continuous_const ((contDiff_intervalQuadratic (n := 0)).continuous.comp
    (continuous_snd.comp continuous_snd))

theorem freeLagrangian_contDiffOn (m : ℝ) :
    ContDiffOn ℝ 2 (Function.uncurry (freeLagrangian m)) timelikeJets := by
  intro z hz
  exact (contDiffAt_const.mul ((contDiffAt_properSpeed hz).comp z
    (contDiff_snd.comp contDiff_snd).contDiffAt)).contDiffWithinAt

theorem freeAction_eq_action (m : ℝ) (γ : ℝ → Spacetime) (a b : ℝ) :
    freeAction m γ a b = action a b (freeLagrangian m) γ := by
  simp only [freeAction, properTime, action, freeLagrangian, intervalIntegral.integral_const_mul]

/-- The kinetic momentum covector is m times the lowered unit four-velocity. -/
def kineticMomentum (m : ℝ) (v : Spacetime) : FourCovector :=
  m • flat .timeNegative (fourVelocity v)

theorem kineticMomentum_eq (m : ℝ) (v : Spacetime) :
    kineticMomentum m v = (-m * (properSpeed v)⁻¹) • pair v := by
  ext w
  simp [kineticMomentum, fourVelocity, flat_apply, metric_eq]
  ring

theorem hasFDerivAt_freeLagrangian (m : ℝ) {z : Spacetime × Spacetime}
    (hz : Timelike z.2) (t : ℝ) :
    HasFDerivAt (freeLagrangian m t)
      ((kineticMomentum m z.2).comp (ContinuousLinearMap.snd ℝ Spacetime Spacetime)) z := by
  have h := ((hasFDerivAt_properSpeed hz).comp z (hasFDerivAt_snd)).const_mul (-m)
  have he : ((kineticMomentum m z.2).comp (ContinuousLinearMap.snd ℝ Spacetime Spacetime)) =
      -m • (((properSpeed z.2)⁻¹ • pair z.2).comp (ContinuousLinearMap.snd ℝ Spacetime Spacetime)) := by
    rw [kineticMomentum_eq, ← smul_smul, ContinuousLinearMap.smul_comp,
      ContinuousLinearMap.smul_comp]
  rw [← he] at h
  exact h

theorem free_force (m : ℝ) {γ : ℝ → Spacetime} {t : ℝ}
    (hv : Timelike (deriv γ t)) : force (freeLagrangian m) γ t = 0 := by
  rw [force, (hasFDerivAt_freeLagrangian m (z := (γ t, deriv γ t)) hv t).fderiv]
  ext w
  simp

theorem free_momentum (m : ℝ) {γ : ℝ → Spacetime} {t : ℝ}
    (hv : Timelike (deriv γ t)) :
    momentum (freeLagrangian m) γ t = kineticMomentum m (deriv γ t) := by
  rw [momentum, (hasFDerivAt_freeLagrangian m (z := (γ t, deriv γ t)) hv t).fderiv]
  ext w
  simp

theorem free_stationary_iff (m : ℝ) {γ : ℝ → Spacetime} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hv : ∀ t ∈ Icc a b, Timelike (deriv γ t)) :
    Stationary a b (freeLagrangian m) γ ↔
      ∀ t ∈ Ioo a b, eulerLagrange (freeLagrangian m) γ t = 0 :=
  stationary_iff_eulerLagrange_on hab hγ isOpen_timelikeJets
    (freeLagrangian_contDiffOn m) hv

end ProjectAInos.SpecialRelativity
