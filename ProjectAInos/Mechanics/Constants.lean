/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Linearization
public import ProjectAInos.Mechanics.Oscillations.Damped
public import ProjectAInos.SmoothAlgebra.FreeChainRule
public import ProjectAInos.SmoothAlgebra.Point

/-!
# The constants of a free C-infinity ring

An element of a free C-infinity ring whose partial derivatives all vanish is a
constant. The proof joins two points by a segment: along the curve
`t ↦ x + t (y − x)` the element is a function of time with zero derivative.

This is the step "a function of `v` that is also a function of `(t, q)` is a
constant" in the characterization of the Lagrangian of a free particle
(Landau–Lifshitz §4).
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing

variable {κ : Type*} [DecidableEq κ]

/-- An element of a free C-infinity ring whose partial derivatives all vanish
takes the same value at all points. -/
theorem lift_eq_of_partialDerivation_eq_zero {s : FreeSmoothRing κ}
    (h : ∀ a, partialDerivation a s = 0) (x y : κ → ℝ) :
    FreeSmoothRing.lift x s = FreeSmoothRing.lift y s := by
  have hD : timeDerivative (FreeSmoothRing.lift (fun a => algebraMap ℝ TimeFunction (x a) +
      algebraMap ℝ TimeFunction (y a - x a) * TimeFunction.time) s) = 0 := by
    rw [← FreeSmoothRing.map_derivation_eq _
      (FreeSmoothRing.derivation fun a => algebraMap ℝ (FreeSmoothRing κ) (y a - x a))
      timeDerivative (fun a => by
        rw [derivation_generator, SmoothRingHom.map_algebraMap, lift_generator, map_add,
          SmoothDerivation.map_algebraMap, SmoothDerivation.map_algebraMap_mul,
          TimeFunction.timeDerivative_time, zero_add, smul_eq_mul, mul_one]) s,
      apply_eq_zero_of_partialDerivation_eq_zero _ h, SmoothRingHom.map_zero]
  have h01 := TimeFunction.eq_of_timeDerivative_eq_zero hD (fun _ => 0) (fun _ => 1)
  rw [lift_curve_apply, lift_curve_apply] at h01
  simpa only [TimeFunction.add_apply, TimeFunction.mul_apply, TimeFunction.algebraMap_apply,
    TimeFunction.time_apply, mul_zero, add_zero, mul_one, add_sub_cancel] using h01

/-- An element of a free C-infinity ring whose partial derivatives all vanish
is a constant. -/
theorem eq_algebraMap_of_partialDerivation_eq_zero {s : FreeSmoothRing κ}
    (h : ∀ a, partialDerivation a s = 0) (x₀ : κ → ℝ) :
    s = algebraMap ℝ (FreeSmoothRing κ) (FreeSmoothRing.lift x₀ s) :=
  FreeSmoothRing.ext_lift fun x => by
    rw [SmoothRingHom.map_algebraMap, lift_eq_of_partialDerivation_eq_zero h x x₀]
    rfl

end ProjectAInos.Mechanics
