/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SpecialRelativity.Boost
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Proper time of parametrized flat-spacetime curves

The scalar functional is total; physical use requires explicit causal and
regularity hypotheses. Null curves are never normalized to four-velocity.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
namespace ProjectAInos.SpecialRelativity
open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ}

def properSpeed (v : MinkowskiModel d) : ℝ := Real.sqrt (intervalQuadratic v)

@[simp] theorem properSpeed_smul (a : ℝ) (v : MinkowskiModel d) :
    properSpeed (a • v) = |a| * properSpeed v := by
  simp only [properSpeed, QuadraticMap.map_smul, smul_eq_mul, ← pow_two]
  rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]

theorem properSpeed_continuous : Continuous (properSpeed (d := d)) := by
  unfold properSpeed
  simp_rw [intervalQuadratic_coordinates]
  exact Real.continuous_sqrt.comp ((time.continuous.pow 2).sub (space.continuous.norm.pow 2))

/-- Physical hypotheses on a directed timelike segment, with regularity on a
neighbourhood of each point of the closed parameter interval. -/
structure TimelikeSegment (γ : ℝ → MinkowskiModel d) (a b : ℝ) : Prop where
  ordered : a ≤ b
  regular : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 γ t
  future : ∀ t ∈ uIcc a b, FutureTimelike (deriv γ t)

def properTime (γ : ℝ → MinkowskiModel d) (a b : ℝ) : ℝ :=
  ∫ t in a..b, properSpeed (deriv γ t)

theorem properTime_integrable (γ : ℝ → MinkowskiModel d) (a b : ℝ)
    (hγ : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 γ t) :
    IntervalIntegrable (fun t => properSpeed (deriv γ t)) volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  exact properSpeed_continuous.continuousAt.comp_continuousWithinAt
    ((hγ t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

theorem properTime_nonneg (γ : ℝ → MinkowskiModel d) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ properTime γ a b :=
  intervalIntegral.integral_nonneg hab (fun _ _ => Real.sqrt_nonneg _)

theorem properTime_null (γ : ℝ → MinkowskiModel d) (a b : ℝ)
    (h : ∀ t ∈ uIcc a b, intervalQuadratic (deriv γ t) = 0) : properTime γ a b = 0 := by
  unfold properTime
  calc
    (∫ t in a..b, properSpeed (deriv γ t)) = ∫ _t in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp [properSpeed, h t ht]
    _ = 0 := by simp

def fourVelocity (v : MinkowskiModel d) : MinkowskiModel d := (properSpeed v)⁻¹ • v

theorem fourVelocity_unit {v : MinkowskiModel d} (hv : Timelike v) :
    intervalQuadratic (fourVelocity v) = 1 := by
  have hpos : 0 < properSpeed v := Real.sqrt_pos.mpr hv
  have hsq : properSpeed v ^ 2 = intervalQuadratic v := Real.sq_sqrt (le_of_lt hv)
  simp only [fourVelocity, QuadraticMap.map_smul, smul_eq_mul]
  rw [← mul_inv, ← pow_two, hsq, inv_mul_cancel₀ (ne_of_gt hv)]

theorem fourVelocity_metric {v : MinkowskiModel d} (hv : Timelike v) :
    minkowskiForm .timeNegative d (fourVelocity v) (fourVelocity v) = -1 := by
  have h := intervalQuadratic_convention .timeNegative (fourVelocity v)
  rw [fourVelocity_unit hv] at h
  simpa using congrArg Neg.neg h

theorem properTime_reparametrize (γ : ℝ → MinkowskiModel d) (f : ℝ → ℝ) (a b : ℝ)
    (hγ : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 γ (f t))
    (hf : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 f t)
    (hpos : ∀ t ∈ uIcc a b, 0 ≤ deriv f t) :
    properTime (γ ∘ f) a b = properTime γ (f a) (f b) := by
  unfold properTime
  calc
    (∫ t in a..b, properSpeed (deriv (γ ∘ f) t)) =
        ∫ t in a..b, properSpeed (deriv γ (f t)) * deriv f t := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      have hd : deriv (γ ∘ f) t = deriv f t • deriv γ (f t) :=
        (((hγ t ht).differentiableAt (by norm_num)).hasDerivAt.scomp t
          ((hf t ht).differentiableAt (by norm_num)).hasDerivAt).deriv
      rw [hd]
      rw [properSpeed_smul, abs_of_nonneg (hpos t ht), mul_comm]
    _ = _ := by
      apply intervalIntegral.integral_comp_mul_deriv' (f := f) (f' := deriv f)
        (g := fun t => properSpeed (deriv γ t))
      · intro t ht
        exact ((hf t ht).differentiableAt (by norm_num)).hasDerivAt
      · intro t ht
        exact ((hf t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt
      · rintro y ⟨t, ht, rfl⟩
        exact properSpeed_continuous.continuousAt.comp_continuousWithinAt
          ((hγ t ht).derivWithin (m := 0) (by norm_num)).continuousAt.continuousWithinAt

theorem properTime_poincare (γ : ℝ → MinkowskiModel d) (f : PoincareGroup d) (a b : ℝ)
    (hγ : ∀ t ∈ uIcc a b, DifferentiableAt ℝ γ t) :
    properTime (fun t => f.val (γ t)) a b = properTime γ a b := by
  apply intervalIntegral.integral_congr
  intro t ht
  have hd : HasDerivAt (fun t => f.val (γ t))
      (f.val.linear (deriv γ t)) t := by
    have h := ((LorentzGroup.toContinuousLinearEquiv (PoincareGroup.linear f)).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t
      (hγ t ht).hasDerivAt).add_const (f.val 0)
    convert h using 1
    · funext z
      exact PoincareGroup.apply_eq f (γ z)
    · rfl
  dsimp only
  rw [hd.deriv]
  unfold properSpeed
  exact congrArg Real.sqrt (LorentzGroup.preserves_interval (PoincareGroup.linear f) (deriv γ t))

theorem properTime_inertial (p v : MinkowskiModel d) (a b : ℝ) :
    properTime (fun t : ℝ => p + t • v) a b = (b-a) * properSpeed v := by
  unfold properTime
  have hd (t : ℝ) : deriv (fun t : ℝ => p + t • v) t = v := by
    simpa using (((hasDerivAt_id t).smul_const v).const_add p).deriv
  simp_rw [hd]
  simp

/-- The same proper speed is obtained from either explicitly signed metric. -/
theorem properSpeed_convention (σ : LorentzConvention) (v : MinkowskiModel d) :
    Real.sqrt (σ.timeSign * minkowskiForm σ d v v) = properSpeed v := by
  rw [intervalQuadratic_convention]
  rfl

def fourVelocityObserver (v : MinkowskiModel d) (hv : FutureTimelike v) : Observer d where
  velocity := fourVelocity v
  unit := fourVelocity_unit (futureTimelike_iff v |>.mp hv).1
  future := by
    rw [fourVelocity, map_smul, smul_eq_mul]
    have ht := (futureTimelike_iff v |>.mp hv).2
    have hs : 0 < properSpeed v := Real.sqrt_pos.mpr (futureTimelike_iff v |>.mp hv).1
    positivity

theorem properTime_timeDilation (p : MinkowskiModel d) (β : Velocity d) (a b : ℝ) :
    properTime (fun t : ℝ => p + t • vector 1 β.val) a b = (b-a) / β.gamma := by
  rw [properTime_inertial]
  simp [properSpeed, intervalQuadratic_coordinates, Velocity.gamma, div_eq_mul_inv]

end ProjectAInos.SpecialRelativity
