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
The same proof shows that an element annihilated by a constant vector field is
invariant under the translations along it, and that an element does not depend
on the co-ordinates in which its partial derivatives vanish.

This is the step "a function of `v` that is also a function of `(t, q)` is a
constant" in the characterization of the Lagrangian of a free particle
(Landau–Lifshitz §4).
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing

variable {κ : Type*} [DecidableEq κ]

omit [DecidableEq κ] in
/-- An element annihilated by the constant vector field `y − x` takes the same
value at the points `x` and `y`. -/
theorem lift_eq_of_derivation_eq_zero {s : FreeSmoothRing κ} {x y : κ → ℝ}
    (h : FreeSmoothRing.derivation
      (fun a => algebraMap ℝ (FreeSmoothRing κ) (y a - x a)) s = 0) :
    FreeSmoothRing.lift x s = FreeSmoothRing.lift y s := by
  have hD : timeDerivative (FreeSmoothRing.lift (fun a => algebraMap ℝ TimeFunction (x a) +
      algebraMap ℝ TimeFunction (y a - x a) * TimeFunction.time) s) = 0 := by
    rw [← FreeSmoothRing.map_derivation_eq _
      (FreeSmoothRing.derivation fun a => algebraMap ℝ (FreeSmoothRing κ) (y a - x a))
      timeDerivative (fun a => by
        rw [derivation_generator, SmoothRingHom.map_algebraMap, lift_generator, map_add,
          SmoothDerivation.map_algebraMap, SmoothDerivation.map_algebraMap_mul,
          TimeFunction.timeDerivative_time, zero_add, smul_eq_mul, mul_one]) s,
      h, SmoothRingHom.map_zero]
  have h01 := TimeFunction.eq_of_timeDerivative_eq_zero hD (fun _ => 0) (fun _ => 1)
  rw [lift_curve_apply, lift_curve_apply] at h01
  simpa only [TimeFunction.add_apply, TimeFunction.mul_apply, TimeFunction.algebraMap_apply,
    TimeFunction.time_apply, mul_zero, add_zero, mul_one, add_sub_cancel] using h01

/-- An element takes the same value at two points when its partial derivatives
vanish in the co-ordinates in which the points differ. -/
theorem lift_eq_of_partialDerivation_eq_zero_of_ne {s : FreeSmoothRing κ} {x y : κ → ℝ}
    (h : ∀ a, x a ≠ y a → partialDerivation a s = 0) :
    FreeSmoothRing.lift x s = FreeSmoothRing.lift y s := by
  refine lift_eq_of_derivation_eq_zero ?_
  rw [apply_eq_sum_partialDerivation]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [derivation_generator]
  by_cases hxy : x a = y a
  · rw [hxy, sub_self, map_zero, smul_zero]
  · rw [h a hxy, zero_smul]

/-- An element of a free C-infinity ring whose partial derivatives all vanish
takes the same value at all points. -/
theorem lift_eq_of_partialDerivation_eq_zero {s : FreeSmoothRing κ}
    (h : ∀ a, partialDerivation a s = 0) (x y : κ → ℝ) :
    FreeSmoothRing.lift x s = FreeSmoothRing.lift y s :=
  lift_eq_of_partialDerivation_eq_zero_of_ne fun a _ => h a

/-- A substitution fixes an element when the partial derivatives of the
element vanish in the co-ordinates that the substitution changes. -/
theorem lift_eq_self_of_partialDerivation_eq_zero {s : FreeSmoothRing κ}
    {y : κ → FreeSmoothRing κ} (h : ∀ a, y a ≠ generator a → partialDerivation a s = 0) :
    FreeSmoothRing.lift y s = s :=
  FreeSmoothRing.ext_lift fun x => by
    have hcomp : FreeSmoothRing.lift x (FreeSmoothRing.lift y s) =
        FreeSmoothRing.lift (fun a => FreeSmoothRing.lift x (y a)) s :=
      congrArg (fun χ : SmoothRingHom (FreeSmoothRing κ) ℝ => χ s)
        (FreeSmoothRing.hom_ext (f := (FreeSmoothRing.lift x).comp (FreeSmoothRing.lift y))
          (g := FreeSmoothRing.lift fun a => FreeSmoothRing.lift x (y a)) fun a => by
            rw [SmoothRingHom.comp_apply, lift_generator, lift_generator])
    rw [hcomp]
    refine lift_eq_of_partialDerivation_eq_zero_of_ne fun a ha => h a fun hy => ha ?_
    rw [hy, lift_generator]

/-- An element of a free C-infinity ring whose partial derivatives all vanish
is a constant. -/
theorem eq_algebraMap_of_partialDerivation_eq_zero {s : FreeSmoothRing κ}
    (h : ∀ a, partialDerivation a s = 0) (x₀ : κ → ℝ) :
    s = algebraMap ℝ (FreeSmoothRing κ) (FreeSmoothRing.lift x₀ s) :=
  FreeSmoothRing.ext_lift fun x => by
    rw [SmoothRingHom.map_algebraMap, lift_eq_of_partialDerivation_eq_zero h x x₀]
    rfl

end ProjectAInos.Mechanics
