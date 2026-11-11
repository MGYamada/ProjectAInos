/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ProjectAInos.SpecialRelativity.Rapidity
public import ProjectAInos.SpecialRelativity.ProperTime
public import ProjectAInos.SpecialRelativity.FormExamples
public import ProjectAInos.SmoothGeometry.Minkowski.TwoForm
import Mathlib.Tactic.NormNum.RealSqrt

/-! # Exact causal, boost, clock, and field examples

The nonzero velocity 3/5 has Lorentz factor 5/4 and clock rate 4/5.
No numerical approximations or experimental premises enter these proofs.
-/
@[expose] public section
noncomputable section
namespace ProjectAInos.SpecialRelativity.Examples
open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm

theorem timelike_example : Timelike (![1,0] : MinkowskiModel 1) := by
  norm_num [Timelike, intervalQuadratic_apply, pair, minkowskiForm_apply, lorentzSign, Fin.sum_univ_succ]

theorem spacelike_example : Spacelike (![0,1] : MinkowskiModel 1) := by
  norm_num [Spacelike, intervalQuadratic_apply, pair, minkowskiForm_apply, lorentzSign, Fin.sum_univ_succ]

theorem lightlike_example : Lightlike (![1,1] : MinkowskiModel 1) := by
  constructor
  · intro h
    have := congrFun h 0
    norm_num at this
  · norm_num [intervalQuadratic_apply, pair, minkowskiForm_apply, lorentzSign, Fin.sum_univ_succ]

theorem zero_causal_not_lightlike :
    FutureCausal (0 : MinkowskiModel 3) ∧ ¬ Lightlike (0 : MinkowskiModel 3) ∧
      ¬ Timelike (0 : MinkowskiModel 3) ∧ ¬ Spacelike (0 : MinkowskiModel 3) := by
  simp [Lightlike, Timelike, Spacelike]

def beta : Velocity 1 := ⟨WithLp.toLp 2 (fun _ : Fin 1 => (3/5 : ℝ)), by
  norm_num [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_lt']⟩

theorem beta_norm : ‖beta.val‖ = (3/5 : ℝ) := by
  norm_num [beta, EuclideanSpace.norm_eq, Fin.sum_univ_one]

theorem beta_nonzero : beta.val ≠ 0 := by
  intro h
  have hn := beta_norm
  rw [h, norm_zero] at hn
  norm_num at hn

theorem beta_gamma : beta.gamma = (5/4 : ℝ) := by
  rw [Velocity.gamma, beta_norm]
  norm_num

theorem boosted_time : time ((boost beta).val (timeAxis 1)) = (5/4 : ℝ) := by
  rw [boost_time, beta_gamma]
  simp [timeAxis]

theorem boosted_space : space ((boost beta).val (timeAxis 1)) 0 = (-3/4 : ℝ) := by
  rw [boost_space, beta_gamma]
  norm_num [timeAxis, beta]

theorem inverse_boost (v : MinkowskiModel 1) :
    (boost beta.neg).val ((boost beta).val v) = v := by
  rw [boost_neg_inverse]
  exact (boost beta).val.symm_apply_apply v

theorem boosted_speed_lt_one :
    ‖(Velocity.transform (boostOrthochronous beta) beta.neg).val‖ < 1 :=
  Velocity.norm_transform_lt_one _ _

theorem time_dilation :
    properTime (fun t : ℝ => (0 : MinkowskiModel 1) + t • vector 1 beta.val) 0 1 = 4/5 := by
  rw [properTime_timeDilation, beta_gamma]
  norm_num

theorem same_clock_both_signs (σ : LorentzConvention) :
    Real.sqrt (σ.timeSign * minkowskiForm σ 1 (vector 1 beta.val) (vector 1 beta.val)) = 4/5 := by
  rw [properSpeed_convention]
  norm_num [properSpeed, intervalQuadratic_coordinates, beta_norm]

theorem same_boost_both_signs (σ : LorentzConvention) (v w : MinkowskiModel 1) :
    minkowskiForm σ 1 ((boost beta).val v) ((boost beta).val w) = minkowskiForm σ 1 v w :=
  LorentzGroup.preserves_metric _ _ _ _

/-- The nonzero field d(t dx) is recovered by any future unit observer. -/
theorem coordinateField_reconstruction (σ : LorentzConvention) (o : SpacetimeOrientation)
    (u : Observer 3) (x : FourVector) :
    reconstructTwoForm σ o u ((coordinateField x).curryLeft u.velocity)
      ((hodgeFiber σ o (by decide : 2+2=3+1) (coordinateField x)).curryLeft u.velocity) =
      coordinateField x := reconstructTwoForm_contractions σ o u _

end ProjectAInos.SpecialRelativity.Examples
