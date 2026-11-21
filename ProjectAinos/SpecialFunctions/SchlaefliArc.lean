/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic

/-! # The finite arc of the outgoing Schläfli contour -/

@[expose] public section
noncomputable section

open Complex MeasureTheory Set Filter
open scoped Real Topology

namespace ProjectAinos.SpecialFunctions.Bessel.Schlaefli

private def kernel (a z : ℂ) (t : ℝ) := exp ((z * Real.sin t - a * t) * I)

/-- Angular part of the outgoing contour, parametrized by the angle from zero to π. -/
def arc (a z : ℂ) : ℂ := ∫ t in 0..π, exp ((z * Real.sin t - a * t) * I)

private theorem int (a z : ℂ) : IntervalIntegrable (kernel a z) volume 0 π :=
  Continuous.intervalIntegrable (by unfold kernel; fun_prop) ..

private theorem shift (a z : ℂ) (t : ℝ) :
    kernel (a - 1) z t = (↑(Real.cos t) + ↑(Real.sin t) * I) * kernel a z t ∧
    kernel (a + 1) z t = (↑(Real.cos t) - ↑(Real.sin t) * I) * kernel a z t := by
  have hm : kernel (a - 1) z t = exp (t * I) * kernel a z t := by
    unfold kernel
    rw [← exp_add]
    congr 1
    ring
  have hp : kernel (a + 1) z t = exp (-(t : ℂ) * I) * kernel a z t := by
    unfold kernel
    rw [← exp_add]
    congr 1
    ring
  rw [hm, hp, exp_mul_I, exp_mul_I, cos_neg, sin_neg, ← ofReal_cos, ← ofReal_sin]
  constructor <;> ring

private def dz (a z : ℂ) (t : ℝ) := (kernel (a - 1) z t - kernel (a + 1) z t) / 2

private theorem deriv_z (a z : ℂ) (t : ℝ) :
    HasDerivAt (fun w => kernel a w t) (dz a z t) z := by
  have h := ((((hasDerivAt_id z).mul_const (Real.sin t : ℂ)).sub_const (a * t)).mul_const I).cexp
  convert h using 1
  · rfl
  change _ = kernel a z t * (1 * (Real.sin t : ℂ) * I)
  rw [dz, (shift a z t).1, (shift a z t).2]
  ring

/-- The argument derivative of the entire arc integral. -/
theorem hasDerivAt_arc (a z : ℂ) :
    HasDerivAt (arc a) ((arc (a - 1) z - arc (a + 1) z) / 2) z := by
  have hc : Continuous (fun p : ℂ × ℝ => dz a p.1 p.2) := by unfold dz kernel; fun_prop
  obtain ⟨C,hC⟩ := ((isCompact_closedBall z 1).prod (isCompact_uIcc (a := 0) (b := π)))
    |>.exists_bound_of_continuousOn hc.continuousOn
  have h := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := π) (F := kernel a) (F' := dz a) (bound := fun _ => C)
    (Metric.closedBall_mem_nhds z zero_lt_one)
    (Eventually.of_forall fun _ => by unfold kernel; fun_prop) (int a z)
    (by unfold dz kernel; fun_prop)
    (Eventually.of_forall fun t ht w hw => hC (w,t) ⟨hw, uIoc_subset_uIcc ht⟩)
    intervalIntegrable_const (Eventually.of_forall fun t _ w _ => deriv_z a w t)
  convert h.2 using 1
  · rfl
  unfold dz
  rw [intervalIntegral.integral_div, intervalIntegral.integral_sub (int _ _) (int _ _)]
  rfl

private def dt (a z : ℂ) (t : ℝ) :=
  I * (z / 2 * (kernel (a + 1) z t + kernel (a - 1) z t) - a * kernel a z t)

private theorem deriv_t (a z : ℂ) (t : ℝ) : HasDerivAt (kernel a z) (dt a z t) t := by
  have h := ((((Real.hasDerivAt_sin t).ofReal_comp.const_mul z).sub
    ((hasDerivAt_id t).ofReal_comp.const_mul a)).mul_const I).cexp
  convert h using 1
  · rfl
  change _ = kernel a z t * ((z * (Real.cos t : ℂ) - a * (1 : ℝ)) * I)
  rw [dt, (shift a z t).1, (shift a z t).2, ofReal_one]
  ring

/-- Integrating the angle derivative retains both endpoints of the arc. -/
theorem arc_recurrence (a z : ℂ) :
    I * (z / 2 * (arc (a + 1) z + arc (a - 1) z) - a * arc a z) =
      exp (-(a * π) * I) - 1 := by
  have hi : IntervalIntegrable (dt a z) volume 0 π :=
    Continuous.intervalIntegrable (by unfold dt kernel; fun_prop) ..
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => deriv_t a z t) hi
  have hs : IntervalIntegrable (fun t => kernel (a + 1) z t + kernel (a - 1) z t) volume 0 π :=
    (int _ _).add (int _ _)
  unfold dt at he
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hs.const_mul _)
    ((int _ _).const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (int _ _) (int _ _)] at he
  simpa only [arc, kernel, Real.sin_zero, Real.sin_pi, ofReal_zero, mul_zero, sub_zero, zero_mul,
    zero_sub, exp_zero] using he

end ProjectAinos.SpecialFunctions.Bessel.Schlaefli
