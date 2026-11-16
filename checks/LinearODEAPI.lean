/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.SmoothGeometry.ODE.Propagator

/-! Typed contracts for linear differential equations: the Volterra operator
without a bound on the coefficient, and the propagator on the real line. These
examples use default elaborator options. -/

open ProjectAInos.SmoothGeometry ProjectAInos.SmoothGeometry.LinearODE
open scoped ContDiff Nat

noncomputable section

section Volterra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (A : Curve (E →L[ℝ] E)) (y : E)

example (n : ℕ) (f : Curve E) (t : unitInterval) :
    ‖(volterra A ^ n) f t‖ ≤ ‖A‖ ^ n * (t : ℝ) ^ n / n ! * ‖f‖ :=
  volterra_pow_apply_norm_le A n f t

/-- The Volterra operator is quasi-nilpotent. -/
example (n : ℕ) : ‖volterra A ^ n‖ ≤ ‖A‖ ^ n / n ! := volterra_pow_norm_le A n

/-- Invertibility with no bound on the coefficient. -/
example : (equationOperator A).IsInvertible := isInvertible_equationOperator A

example (t : unitInterval) : solutionOperator A y t = y +
    ∫ s in 0..(t : ℝ), extend A s (extend (solutionOperator A y) s) :=
  solutionOperator_integral_eq A y t

example : solutionOperator A y 0 = y := solutionOperator_zero A y

example (f : Curve E)
    (hf : ∀ t : unitInterval, f t = y + ∫ s in 0..(t : ℝ), extend A s (extend f s)) :
    f = solutionOperator A y :=
  eq_solutionOperator_of_integral_eq A y f hf

example (t : unitInterval) :
    HasDerivWithinAt (extend (solutionOperator A y)) (A t (solutionOperator A y t))
      (Set.Icc (0 : ℝ) 1) t :=
  solutionOperator_hasDerivWithinAt A y t

example (f : Curve E) (h0 : f 0 = y)
    (hf : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (extend f) (extend A t (extend f t)) t) :
    f = solutionOperator A y :=
  eq_solutionOperator_of_hasDerivAt A y f h0 hf

example : ContDiff ℝ ∞ (solutionOperator (E := E)) := solutionOperator_contDiff

example : ContDiff ℝ ∞ (fun p : Curve (E →L[ℝ] E) × E => solutionOperator p.1 p.2) :=
  solutionOperator_apply_contDiff

end Volterra

section Propagator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (A : C(ℝ, E →L[ℝ] E))

example (s t : ℝ) (σ : unitInterval) :
    segmentCoefficient A s t σ = (t - s) • A (s + (σ : ℝ) * (t - s)) :=
  segmentCoefficient_apply A s t σ

example (t s : ℝ) (y : E) :
    propagator A t s y = solutionOperator (segmentCoefficient A s t) y 1 :=
  propagator_apply A t s y

example (s : ℝ) : propagator A s s = ContinuousLinearMap.id ℝ E := propagator_self A s

example (s t : ℝ) (y : E) (σ : unitInterval) :
    solutionOperator (segmentCoefficient A s t) y σ =
      propagator A (s + (σ : ℝ) * (t - s)) s y :=
  solutionOperator_segmentCoefficient_apply A s t y σ

example (t s : ℝ) (y : E) :
    propagator A t s y = y + ∫ r in s..t, A r (propagator A r s y) :=
  propagator_apply_eq_add_integral A t s y

example : Continuous fun q : ℝ × ℝ => propagator A q.1 q.2 := continuous_propagator A

/-- The differential equation, for all real times. -/
example (t s : ℝ) (y : E) :
    HasDerivAt (fun r => propagator A r s y) (A t (propagator A t s y)) t :=
  hasDerivAt_propagator_apply A t s y

example (t s : ℝ) :
    HasDerivAt (fun r => propagator A r s) (A t ∘L propagator A t s) t :=
  hasDerivAt_propagator A t s

/-- Uniqueness of the solution between two times. -/
example {f : ℝ → E} {s t : ℝ} (hc : ContinuousOn f (Set.uIcc s t))
    (hf : ∀ r ∈ Set.Ioo (min s t) (max s t), HasDerivAt f (A r (f r)) r) :
    f t = propagator A t s (f s) :=
  eq_propagator_apply_of_hasDerivAt A hc hf

/-- The composition law. -/
example (t s r : ℝ) : propagator A t s ∘L propagator A s r = propagator A t r :=
  propagator_comp A t s r

example (t s : ℝ) (y : E) : propagator A t s (propagator A s t y) = y :=
  propagator_apply_self_apply A t s y

example (t s : ℝ) : (propagator A t s).IsInvertible := propagator_isInvertible A t s

/-- Constant coefficients: the exponential. -/
example (A₀ : E →L[ℝ] E) (t s : ℝ) :
    propagator (ContinuousMap.const ℝ A₀) t s = NormedSpace.exp ((t - s) • A₀) :=
  propagator_const A₀ t s

example {B : C(ℝ, E →L[ℝ] E)} (hB : ContDiff ℝ ∞ B) :
    ContDiff ℝ ∞ fun q : ℝ × ℝ => propagator B q.1 q.2 :=
  propagator_contDiff_of_contDiff hB

end Propagator

section Parameter

universe u

variable {P V : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Smooth dependence on a parameter and the two times. -/
example {A : P × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ fun q : P × ℝ × ℝ =>
      propagator (coefficientCurve A hA.continuous q.1) q.2.1 q.2.2 :=
  propagator_contDiff hA

example {A : P × ℝ → V →L[ℝ] V} (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ fun q : (P × ℝ × ℝ) × V =>
      propagator (coefficientCurve A hA.continuous q.1.1) q.1.2.1 q.1.2.2 q.2 :=
  propagator_apply_contDiff hA

end Parameter
