/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.RadialReparam
public import ProjectAInos.SmoothGeometry.ODE.VolterraExamples
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # A nonconstant coordinate connection and its radial endpoint

For the real coefficient `Γ(q)(u,v) = -(q/2)uv`, radial vector transport from
zero to `x` has endpoint `exp(x²/4)v`. The proof identifies the unit segment
with the nonconstant Volterra example and uses radial reparametrization.
-/

@[expose] public section
noncomputable section

open ContinuousLinearMap
open scoped ContDiff

namespace ProjectAInos.SmoothGeometry.LinearODE

/-- A nonconstant one-dimensional connection coefficient. -/
def quadraticConnection (q : ℝ) : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  (-(q / 2)) • ContinuousLinearMap.mul ℝ ℝ

theorem quadraticConnection_contDiff : ContDiff ℝ ∞ quadraticConnection := by
  apply contDiff_clm_apply_iff.mpr
  intro u
  apply contDiff_clm_apply_iff.mpr
  intro v
  change ContDiff ℝ ∞ (fun q : ℝ => -(q / 2) * (u * v))
  fun_prop

theorem quadratic_radialCoefficient (x : ℝ) (t : unitInterval) :
    radialCoefficient quadraticConnection quadraticConnection_contDiff 0 x t =
      ((t : ℝ) * x ^ 2 / 2) • ContinuousLinearMap.id ℝ ℝ := by
  ext
  simp [radialCoefficient_apply, quadraticConnection]
  ring

theorem quadratic_radialCoefficient_small (x : unitInterval) :
    ‖radialCoefficient quadraticConnection quadraticConnection_contDiff 0 (x : ℝ)‖ < 1 := by
  apply lt_of_le_of_lt (b := (1 : ℝ) / 2) ?_ (by norm_num)
  apply (ContinuousMap.norm_le _ (by norm_num)).mpr
  intro t
  rw [quadratic_radialCoefficient, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (mul_nonneg t.property.1 (sq_nonneg (x : ℝ))) (by norm_num))]
  calc
    (t : ℝ) * (x : ℝ) ^ 2 / 2 * ‖ContinuousLinearMap.id ℝ ℝ‖ ≤
        (t : ℝ) * (x : ℝ) ^ 2 / 2 * 1 :=
      mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le
        (div_nonneg (mul_nonneg t.property.1 (sq_nonneg (x : ℝ))) (by norm_num))
    _ ≤ 1 / 2 := by
      have ht0 := t.property.1
      have ht1 := t.property.2
      have hx0 := x.property.1
      have hx1 := x.property.2
      have hx2 : (x : ℝ) ^ 2 ≤ 1 := by nlinarith
      have htx := mul_le_mul_of_nonneg_left hx2 ht0
      nlinarith

/-- Exact endpoints on all prefixes of the unit ray. -/
theorem quadratic_radialEndpoint (x : unitInterval) (v : ℝ) :
    radialEndpoint quadraticConnection quadraticConnection_contDiff 0 (x : ℝ) v =
      Real.exp ((x : ℝ) ^ 2 / 4) * v := by
  have hcoeff : radialCoefficient quadraticConnection quadraticConnection_contDiff 0 1 =
      rampCoefficient (E := ℝ) := by
    apply ContinuousMap.ext
    intro t
    rw [quadratic_radialCoefficient]
    simp [rampCoefficient]
  have h := radialEndpoint_on_ray quadraticConnection quadraticConnection_contDiff 0 1 v x
    (quadratic_radialCoefficient_small 1) (by simpa using quadratic_radialCoefficient_small x)
  simpa [hcoeff, solution_ramp] using h

end ProjectAInos.SmoothGeometry.LinearODE
