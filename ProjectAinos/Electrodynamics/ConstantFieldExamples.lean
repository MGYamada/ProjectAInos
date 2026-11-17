/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.ConstantField
public import ProjectAinos.Electrodynamics.Examples
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Uniform fields: the electric, the magnetic, the null and the parallel case

The field `uniformField E B = −E dt ∧ dx¹ + B dx² ∧ dx³` has an electric and a magnetic part
along the first axis of space (Landau–Lifshitz, *The Classical Theory of Fields*, §§20–22).

* `isSimple_electric`, `generatorInvariant_electric`: the electric part is `dt ∧ (−E dx¹)` with
  the invariant `E²`, so the motion is hyperbolic with `Ω = e E/m` (`velocity_electric`).
* `isSimple_magnetic`, `generatorInvariant_magnetic`: the magnetic part is `dx² ∧ (B dx³)` with
  the invariant `−B²`, so the motion is circular with `Ω = e B/m` (`velocity_magnetic`).
* `nullField E = E (dt ∧ dx¹ + dx¹ ∧ dx²)` is `(dt − dx²) ∧ (E dx¹)` with the invariant zero:
  an electric and a magnetic field of the same size at a right angle
  (`isSimple_nullField`, `velocity_nullField`).
* `velocity_uniformField`: for parallel fields the four-velocity is the sum of the hyperbolic
  and the circular one minus the initial value.
* `motion_eq_hyperbola`: the hyperbola of the earlier example is the motion with its initial
  data.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Electrodynamics.ConstantField

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity
open Examples

/-- The co-ordinate covector `dx^μ`. -/
def coordinateCovector (μ : Fin 4) : FourCovector := ContinuousLinearMap.proj μ

@[simp] theorem coordinateCovector_apply (μ : Fin 4) (v : Spacetime) :
    coordinateCovector μ v = v μ := rfl

/-! ### The electric field -/

theorem isSimple_electric (E : ℝ) :
    IsSimple (uniformField E 0) (coordinateCovector 0) (-E • coordinateCovector 1) := by
  intro v w
  simp [uniformField, coordinateForm_apply, Matrix.det_fin_two]
  ring

theorem generatorInvariant_electric (E : ℝ) :
    generatorInvariant .timeNegative (coordinateCovector 0) (-E • coordinateCovector 1) =
      E ^ 2 := by
  simp [generatorInvariant, sharp_apply, lorentzSign]
  ring

/-- In an electric field the four-velocity is hyperbolic with `Ω = e E/m`. -/
theorem velocity_electric {m e E : ℝ} (hΩ : e * E / m ≠ 0) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (uniformField E 0) u₀ τ =
      u₀ + (Real.sinh (e * E / m * τ) / (e * E / m)) • generator m e (uniformField E 0) u₀ +
        ((Real.cosh (e * E / m * τ) - 1) / (e * E / m) ^ 2) •
          generator m e (uniformField E 0) (generator m e (uniformField E 0) u₀) :=
  velocity_of_pos (isSimple_electric E) hΩ (by rw [generatorInvariant_electric]; ring) u₀ τ

/-! ### The magnetic field -/

theorem isSimple_magnetic (B : ℝ) :
    IsSimple (uniformField 0 B) (coordinateCovector 2) (B • coordinateCovector 3) := by
  intro v w
  simp [uniformField, coordinateForm_apply, Matrix.det_fin_two]
  ring

theorem generatorInvariant_magnetic (B : ℝ) :
    generatorInvariant .timeNegative (coordinateCovector 2) (B • coordinateCovector 3) =
      -B ^ 2 := by
  simp [generatorInvariant, sharp_apply, lorentzSign]
  ring

/-- In a magnetic field the four-velocity turns with `Ω = e B/m`. -/
theorem velocity_magnetic {m e B : ℝ} (hΩ : e * B / m ≠ 0) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (uniformField 0 B) u₀ τ =
      u₀ + (Real.sin (e * B / m * τ) / (e * B / m)) • generator m e (uniformField 0 B) u₀ +
        ((1 - Real.cos (e * B / m * τ)) / (e * B / m) ^ 2) •
          generator m e (uniformField 0 B) (generator m e (uniformField 0 B) u₀) :=
  velocity_of_neg (isSimple_magnetic B) hΩ (by rw [generatorInvariant_magnetic]; ring) u₀ τ

/-! ### The null field -/

/-- An electric field along the first axis and a magnetic field of the same size along the
third axis: `E (dt ∧ dx¹ + dx¹ ∧ dx²)`. -/
def nullField (E : ℝ) : TwoForm := E • (coordinateForm ![0, 1] + coordinateForm ![1, 2])

theorem isSimple_nullField (E : ℝ) :
    IsSimple (nullField E) (coordinateCovector 0 - coordinateCovector 2)
      (E • coordinateCovector 1) := by
  intro v w
  simp [nullField, coordinateForm_apply, Matrix.det_fin_two]
  ring

theorem generatorInvariant_nullField (E : ℝ) :
    generatorInvariant .timeNegative (coordinateCovector 0 - coordinateCovector 2)
      (E • coordinateCovector 1) = 0 := by
  simp [generatorInvariant, sharp_apply, lorentzSign]

/-- The null field is not zero for `E ≠ 0`. -/
theorem nullField_ne_zero {E : ℝ} (hE : E ≠ 0) : nullField E ≠ 0 := by
  intro h
  have h1 := isSimple_nullField E (Pi.single 0 1) (Pi.single 1 1)
  rw [h] at h1
  simp at h1
  exact hE h1.symm

/-- In a null field the four-velocity is a polynomial of degree two in the proper time. -/
theorem velocity_nullField (m e E : ℝ) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (nullField E) u₀ τ = u₀ + τ • generator m e (nullField E) u₀ +
      (τ ^ 2 / 2) • generator m e (nullField E) (generator m e (nullField E) u₀) :=
  velocity_of_zero (isSimple_nullField E) (by rw [generatorInvariant_nullField, mul_zero]) u₀ τ

/-! ### Parallel fields -/

theorem uniformField_eq_add (E B : ℝ) :
    uniformField E B = uniformField E 0 + uniformField 0 B := by
  simp [uniformField]

theorem generator_electric_apply (m e E : ℝ) (v : Spacetime) :
    generator m e (uniformField E 0) v = (e * E / m) • ![v 1, v 0, 0, 0] := by
  rw [generator_of_isSimple (isSimple_electric E), lorentzGenerator_apply]
  ext i
  fin_cases i <;> simp [sharp_apply, lorentzSign] <;> ring

theorem generator_magnetic_apply (m e B : ℝ) (v : Spacetime) :
    generator m e (uniformField 0 B) v = (e * B / m) • ![0, 0, v 3, -v 2] := by
  rw [generator_of_isSimple (isSimple_magnetic B), lorentzGenerator_apply]
  ext i
  fin_cases i <;> simp [sharp_apply, lorentzSign] <;> ring

/-- For parallel fields the four-velocity is the sum of the hyperbolic and the circular one
minus the initial value. -/
theorem velocity_uniformField (m e E B : ℝ) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (uniformField E B) u₀ τ =
      velocity m e (uniformField E 0) u₀ τ + velocity m e (uniformField 0 B) u₀ τ - u₀ := by
  rw [uniformField_eq_add]
  refine velocity_add m e (fun v => ?_) (fun v => ?_) u₀ τ
  · rw [generator_electric_apply, generator_magnetic_apply]
    simp
  · rw [generator_magnetic_apply, generator_electric_apply]
    simp

/-! ### The hyperbola -/

/-- The hyperbola `(sinh τ, cosh τ, 0, 0)` is the motion of the unit charge of unit mass in
the unit electric field, with its initial event and four-velocity. -/
theorem motion_eq_hyperbola (τ : ℝ) :
    motion 1 1 (uniformField 1 0) (hyperbola 0) (hyperbolaVelocity 0) τ = hyperbola τ := by
  rw [motion_of_pos (Ω := 1) (isSimple_electric 1) one_ne_zero
    (by rw [generatorInvariant_electric]; norm_num)]
  simp only [generator_electric_apply]
  ext i
  fin_cases i <;> simp [hyperbola, hyperbolaVelocity]

end ProjectAinos.Electrodynamics.ConstantField
