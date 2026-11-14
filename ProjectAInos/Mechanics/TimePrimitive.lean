/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.TimeFunction
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Primitives of smooth functions of time

The fundamental theorem of calculus for the ring of smooth functions of time:
the increment of a function is the integral of its derivative, and every
function `f` has a primitive `∫₀ᵗ f`, which is again a smooth function of time.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.TimeFunction

open SmoothAlgebra SmoothRing
open scoped ContDiff

/-- A smooth function of time, read as a function of a real variable, has the
derivative `timeDerivative f`. -/
theorem hasDerivAt_apply_const (f : TimeFunction) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f fun _ => s) (timeDerivative f fun _ => t) t := by
  rw [timeDerivative_apply]
  exact ((f.contDiff_apply_const.differentiable (by simp)) t).hasDerivAt

/-- A smooth function of time, read as a function of a real variable, is
continuous. -/
theorem continuous_apply_const (f : TimeFunction) : Continuous fun s : ℝ => f fun _ => s :=
  f.contDiff_apply_const.continuous

/-- The increment of a smooth function of time is the integral of its
derivative. -/
theorem apply_sub_apply_eq_integral (f : TimeFunction) (a b : ℝ) :
    f (fun _ => b) - f (fun _ => a) = ∫ s in a..b, timeDerivative f fun _ => s :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_apply_const f s)
    ((timeDerivative f).continuous_apply_const.intervalIntegrable a b)).symm

/-- The primitive `t ↦ ∫₀ᵗ f` of a smooth function of time. -/
def primitive (f : TimeFunction) : TimeFunction :=
  SmoothOperation.ofContDiff (fun x => ∫ s in (0 : ℝ)..x 0, f fun _ => s) (by
    have hd (t : ℝ) : HasDerivAt (fun u : ℝ => ∫ s in (0 : ℝ)..u, f fun _ => s)
        (f fun _ => t) t :=
      (f.continuous_apply_const.integral_hasStrictDerivAt 0 t).hasDerivAt
    have hF : ContDiff ℝ ∞ (fun u : ℝ => ∫ s in (0 : ℝ)..u, f fun _ => s) := by
      refine contDiff_infty_iff_deriv.mpr ⟨fun t => (hd t).differentiableAt, ?_⟩
      have h : deriv (fun u : ℝ => ∫ s in (0 : ℝ)..u, f fun _ => s) = fun t => f fun _ => t :=
        funext fun t => (hd t).deriv
      rw [h]
      exact f.contDiff_apply_const
    exact hF.comp (contDiff_apply ℝ (fun _ => ℝ) 0))

theorem primitive_apply (f : TimeFunction) (t : ℝ) :
    primitive f (fun _ => t) = ∫ s in (0 : ℝ)..t, f fun _ => s := rfl

@[simp] theorem primitive_apply_zero (f : TimeFunction) : primitive f (fun _ => 0) = 0 := by
  rw [primitive_apply, intervalIntegral.integral_same]

/-- The derivative of the primitive is the function. -/
theorem timeDerivative_primitive (f : TimeFunction) : timeDerivative (primitive f) = f := by
  refine ext_apply_const fun t => ?_
  rw [timeDerivative_apply]
  exact (f.continuous_apply_const.integral_hasStrictDerivAt 0 t).hasDerivAt.deriv

end ProjectAInos.Mechanics.TimeFunction
