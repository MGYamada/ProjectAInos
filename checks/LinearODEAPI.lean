/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.SmoothGeometry.ODE.PropagatorExpansion

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

example (f : Curve E) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : extend f t = f ⟨t, ht⟩ :=
  extend_of_mem f ht

example (s : ℝ) : segmentCoefficient A s s = 0 := segmentCoefficient_self A s

example : Continuous fun q : ℝ × ℝ => segmentCoefficient A q.2 q.1 :=
  continuous_segmentCoefficient A

example (s : ℝ) : Continuous fun r : ℝ => propagator A r s := continuous_propagator_left A s

example (t s r : ℝ) (y : E) :
    propagator A t s (propagator A s r y) = propagator A t r y :=
  propagator_comp_apply A t s r y

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

example (A : P × ℝ → V →L[ℝ] V) (hA : Continuous A) (p : P) (t : ℝ) :
    coefficientCurve A hA p t = A (p, t) := coefficientCurve_apply A hA p t

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

section Expansion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  (A : C(ℝ, E →L[ℝ] E))

/-- Growth of a solution under a bound on the coefficient. -/
example {s t g : ℝ} (hst : s ≤ t) (hg : ∀ r ∈ Set.Icc s t, ‖A r‖ ≤ g) (y : E) :
    ‖propagator A t s y‖ ≤ ‖y‖ * Real.exp (g * (t - s)) :=
  norm_propagator_apply_le A hst hg y

example {s t g c : ℝ} {k : ℕ} (hg : ∀ r ∈ Set.Icc s t, ‖A r‖ ≤ g) (hg0 : 0 ≤ g) {u : ℝ → E}
    (hu : ∀ r ∈ Set.Icc s t, ‖u r‖ ≤ c * (r - s) ^ k) {τ : ℝ} (hτ : τ ∈ Set.Icc s t) :
    ‖∫ r in s..τ, A r (u r)‖ ≤ g * c * (τ - s) ^ (k + 1) / (k + 1) :=
  norm_integral_apply_le A hg hg0 hu hτ

example (s : ℝ) (y : E) (r : ℝ) : firstOrder A s y r = ∫ x in s..r, A x y := rfl

example (s : ℝ) (y : E) (r : ℝ) :
    secondOrder A s y r = ∫ x in s..r, A x (firstOrder A s y x) := rfl

example (y : E) : Continuous fun r : ℝ => A r y := continuous_apply_const A y

example (s : ℝ) (y : E) (r : ℝ) : HasDerivAt (firstOrder A s y) (A r y) r :=
  hasDerivAt_firstOrder A s y r

example (s : ℝ) (y : E) : Continuous (firstOrder A s y) := continuous_firstOrder A s y

example {s t g : ℝ} (hg : ∀ r ∈ Set.Icc s t, ‖A r‖ ≤ g) (hg0 : 0 ≤ g) (y : E) {τ : ℝ}
    (hτ : τ ∈ Set.Icc s t) :
    ‖propagator A τ s y - y‖ ≤ ‖y‖ * Real.exp (g * (t - s)) * g * (τ - s) :=
  norm_propagator_apply_sub_le hg hg0 y hτ

example {s t g : ℝ} (hg : ∀ r ∈ Set.Icc s t, ‖A r‖ ≤ g) (hg0 : 0 ≤ g) (y : E) {τ : ℝ}
    (hτ : τ ∈ Set.Icc s t) :
    ‖propagator A τ s y - y - firstOrder A s y τ‖ ≤
      ‖y‖ * Real.exp (g * (t - s)) * g ^ 2 * (τ - s) ^ 2 / 2 :=
  norm_propagator_apply_sub_firstOrder_le hg hg0 y hτ

/-- The expansion to second order with a remainder of third order. -/
example {s t g : ℝ} (hst : s ≤ t) (hg : ∀ r ∈ Set.Icc s t, ‖A r‖ ≤ g) (hg0 : 0 ≤ g)
    (y : E) :
    ‖propagator A t s y - y - firstOrder A s y t - secondOrder A s y t‖ ≤
      ‖y‖ * Real.exp (g * (t - s)) * (g * (t - s)) ^ 3 / 6 :=
  norm_propagator_apply_sub_secondOrder_le hst hg hg0 y

example (s r : ℝ) : integralCoefficient A s r = ∫ x in s..r, A x := rfl

example (s r : ℝ) : HasDerivAt (integralCoefficient A s) (A r) r :=
  hasDerivAt_integralCoefficient A s r

example (s : ℝ) : Continuous (integralCoefficient A s) := continuous_integralCoefficient A s

example (s : ℝ) : integralCoefficient A s s = 0 := integralCoefficient_self A s

example (s : ℝ) (y : E) (r : ℝ) : firstOrder A s y r = integralCoefficient A s r y :=
  firstOrder_eq A s y r

example (s r : ℝ) :
    secondOrderOperator A s r = ∫ x in s..r, A x ∘L integralCoefficient A s x := rfl

example (s : ℝ) : Continuous fun x : ℝ => A x ∘L integralCoefficient A s x :=
  continuous_comp_integralCoefficient A s

example (s r : ℝ) :
    HasDerivAt (secondOrderOperator A s) (A r ∘L integralCoefficient A s r) r :=
  hasDerivAt_secondOrderOperator A s r

example (s : ℝ) : secondOrderOperator A s s = 0 := secondOrderOperator_self A s

example (s : ℝ) (y : E) (r : ℝ) : secondOrder A s y r = secondOrderOperator A s r y :=
  secondOrder_eq A s y r

example [FiniteDimensional ℝ E] (L : E →L[ℝ] E) :
    traceCLM L = LinearMap.trace ℝ E (L : E →ₗ[ℝ] E) := traceCLM_apply L

example [FiniteDimensional ℝ E] (L L' : E →L[ℝ] E) :
    traceCLM (L ∘L L') = traceCLM (L' ∘L L) := traceCLM_comp_comm L L'

/-- The trace of the term of second order. -/
example [FiniteDimensional ℝ E] (s t : ℝ) :
    traceCLM (secondOrderOperator A s t) =
      1 / 2 * traceCLM (integralCoefficient A s t ∘L integralCoefficient A s t) :=
  traceCLM_secondOrderOperator A s t

end Expansion
