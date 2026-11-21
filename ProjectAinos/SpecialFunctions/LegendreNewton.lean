/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.LegendreGenerating
public import ProjectAinos.SmoothGeometry.Potential.NewtonKernel
import Mathlib.Tactic

/-! # Legendre expansion of the three-dimensional Newton kernel -/

@[expose] public section

open ProjectAinos.SmoothGeometry.Potential
namespace ProjectAinos.SpecialFunctions.Legendre

/-- The convergent exterior expansion, including a source at the origin. The prefactor
uses the project's normalization of the Green function for the negative Laplacian. -/
theorem hasSum_newtonKernel (x y : EuclideanSpace ℝ (Fin 3)) (hy : ‖y‖ < ‖x‖) :
    HasSum (fun n => newtonKernel x * ((polynomial n).eval (inner ℝ x y / (‖x‖ * ‖y‖)) *
      (‖y‖ / ‖x‖) ^ n)) (newtonKernel (x - y)) := by
  have hx : 0 < ‖x‖ := (norm_nonneg y).trans_lt hy
  let c := inner ℝ x y / (‖x‖ * ‖y‖)
  let t := ‖y‖ / ‖x‖
  have hc : |c| ≤ 1 := abs_real_inner_div_norm_mul_norm_le_one x y
  have ht : |t| < 1 := by
    rw [abs_of_nonneg (by dsimp [t]; positivity : 0 ≤ t)]
    exact (div_lt_one hx).mpr hy
  have hrad : 1 - 2 * c * t + t ^ 2 = (‖x - y‖ / ‖x‖) ^ 2 := by
    by_cases hzero : y = 0
    · simp [hzero, c, t, hx.ne']
    · dsimp [c, t]
      simp only [div_pow, norm_sub_sq_real]
      field_simp [hx.ne', norm_ne_zero_iff.mpr hzero]
  have hs := (hasSum_generating hc ht).mul_left (newtonKernel x)
  rw [hrad, Real.sqrt_sq (by positivity)] at hs
  have heq : newtonKernel x * (‖x - y‖ / ‖x‖)⁻¹ = newtonKernel (x - y) := by
    simp [newtonKernel, div_eq_mul_inv, mul_inv_rev, hx.ne', mul_assoc, mul_left_comm, mul_comm]
  rw [heq] at hs
  exact hs

end ProjectAinos.SpecialFunctions.Legendre
