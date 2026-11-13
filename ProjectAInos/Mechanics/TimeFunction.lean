/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Derivation
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# Smooth functions of time

The C-infinity ring of smooth functions of one real variable, with its
coordinate vector field `d/dt`. Paths and trajectories take values in this
ring. A function with zero derivative is constant; this is the one place where
the trajectory statements of mechanics use calculus.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing

/-- Smooth functions of time. -/
abbrev TimeFunction := SmoothOperation 1

/-- The derivative `d/dt` of a smooth function of time. -/
def timeDerivative : SmoothDerivation TimeFunction TimeFunction :=
  SmoothDerivation.partialDerivation 0

/-- `timeDerivative` is the ordinary derivative of the function `s ↦ f s` of a
real variable. -/
theorem TimeFunction.timeDerivative_apply (f : TimeFunction) (t : ℝ) :
    timeDerivative f (fun _ => t) = deriv (fun s : ℝ => f (fun _ => s)) t := by
  have hf : HasFDerivAt f (fderiv ℝ f (fun _ => t)) (fun _ => t) :=
    (f.contMDiff.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hc : HasDerivAt (fun s : ℝ => (fun _ : Fin 1 => s)) (fun _ => (1 : ℝ)) t :=
    hasDerivAt_pi.mpr fun _ => hasDerivAt_id t
  have h : HasDerivAt (fun s : ℝ => f (fun _ => s)) (fderiv ℝ f (fun _ => t) fun _ => 1) t :=
    hf.comp_hasDerivAt t hc
  rw [h.deriv, SmoothOperation.fderiv_apply_eq_sum_partialDeriv, Fin.sum_univ_one, one_mul]
  rfl

/-- A smooth function of time with zero derivative is constant. -/
theorem TimeFunction.eq_of_timeDerivative_eq_zero {f : TimeFunction}
    (h : timeDerivative f = 0) (s t : Fin 1 → ℝ) : f s = f t := by
  refine is_const_of_fderiv_eq_zero (𝕜 := ℝ) (f.contMDiff.contDiff.differentiable (by simp))
    (fun x => ?_) s t
  ext v
  rw [SmoothOperation.fderiv_apply_eq_sum_partialDeriv, Fin.sum_univ_one]
  have h0 : SmoothOperation.partialDeriv 0 f x = 0 := congrArg (fun g : TimeFunction => g x) h
  rw [h0, mul_zero]
  rfl

end ProjectAInos.Mechanics
