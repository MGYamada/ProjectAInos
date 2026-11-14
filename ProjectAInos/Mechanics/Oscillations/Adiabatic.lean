/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Parametric
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The action variable of an oscillator with a variable frequency

Landau–Lifshitz §49. For `ẍ + ω(t)² x = 0` the action variable is
`I = E/ω = (ẋ² + ω² x²)/2ω`. Its derivative along a solution is

`İ = (ω̇/2ω²) (ω² x² − ẋ²)`,

exactly. It is proportional to `ω̇`, and its second factor oscillates about
zero; the adiabatic theorem is the statement that the integral of this
expression stays small when `ω` varies slowly, and it is not proved here.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.Parametric

open SmoothAlgebra

/-- The action variable `I = (ẋ² + ω² x²)/2ω` of an oscillator with the
frequency `ω`, where `ωinv` is the inverse of `ω`. -/
def action (ω ωinv x : TimeFunction) : TimeFunction :=
  algebraMap ℝ TimeFunction (1 / 2) * ωinv *
    (timeDerivative x * timeDerivative x + ω * ω * (x * x))

/-- The derivative of the inverse: `d(1/ω)/dt = −ω̇/ω²`. -/
theorem timeDerivative_inv {ω ωinv : TimeFunction} (hω : ω * ωinv = 1) :
    timeDerivative ωinv = -(timeDerivative ω * (ωinv * ωinv)) := by
  have h := congrArg timeDerivative hω
  rw [SmoothDerivation.map_mul, SmoothDerivation.map_one, smul_eq_mul, smul_eq_mul] at h
  linear_combination ωinv * h - timeDerivative ωinv * hω

/-- The derivative of the action variable along a solution of
`ẍ + ω(t)² x = 0`: `İ = (ω̇/2ω²) (ω² x² − ẋ²)` (Landau–Lifshitz §49). -/
theorem timeDerivative_action {ω ωinv x : TimeFunction} (hω : ω * ωinv = 1)
    (hx : IsHill (ω * ω) x) :
    timeDerivative (action ω ωinv x) =
      algebraMap ℝ TimeFunction (1 / 2) * (timeDerivative ω * (ωinv * ωinv)) *
        (ω * ω * (x * x) - timeDerivative x * timeDerivative x) := by
  have hinv := timeDerivative_inv hω
  unfold IsHill at hx
  rw [action, SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap_mul, map_add,
    SmoothDerivation.map_mul, SmoothDerivation.map_mul, SmoothDerivation.map_mul,
    SmoothDerivation.map_mul, hx, hinv]
  simp only [smul_eq_mul]
  linear_combination
    (-(2 * algebraMap ℝ TimeFunction (1 / 2) * timeDerivative ω * (x * x) * (ω * ωinv))) * hω

/-- If the frequency is constant, the action variable is constant. -/
theorem timeDerivative_action_of_const {ω ωinv x : TimeFunction} (hω : ω * ωinv = 1)
    (hx : IsHill (ω * ω) x) (hconst : timeDerivative ω = 0) :
    timeDerivative (action ω ωinv x) = 0 := by
  rw [timeDerivative_action hω hx, hconst, zero_mul, mul_zero, zero_mul]

end ProjectAInos.Mechanics.Parametric
