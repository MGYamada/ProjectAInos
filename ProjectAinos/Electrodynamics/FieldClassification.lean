/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.FieldTransformation
public import ProjectAinos.Electrodynamics.ConstantFieldExamples
public import ProjectAinos.Electrodynamics.StaticField
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The classification of a constant field by its invariants

A field `F` has the invariants `I₁ = B² − E²` and `I₂ = E · B`. The generator `A = (e/m) F♯`
of the motion of a charge is the linear map `v ↦ (e/m) (E · v, v⁰ E + v × B)`
(Landau–Lifshitz, *The Classical Theory of Fields*, §§22, 25).

* `lorentzForce_vectors`: the force in terms of the electric and the magnetic components.
* `generator_cube_eq`, `generator_dualGenerator`: `A³ = −(e/m)² I₁ A − (e/m)³ I₂ D` and
  `A D = −(e/m) I₂`, where `D` is the force map of the triples `−B` and `E`.
* `generator_quartic`: the equation of Cayley and Hamilton
  `A⁴ = −(e/m)² I₁ A² + (e/m)⁴ I₂²`.

The invariants give four kinds of a field, and the motion in the proper time for each.

* `I₂ = 0`, `I₁ < 0` (`velocity_of_scalarInvariant_neg`): `A³ = Ω² A`, a hyperbolic motion.
* `I₂ = 0`, `I₁ > 0` (`velocity_of_scalarInvariant_pos`): `A³ = −Ω² A`, a circular motion.
* `I₁ = I₂ = 0` (`velocity_of_invariants_zero`): `A³ = 0`, a polynomial motion. The field
  `nullField E` is of this kind and is not zero.
* `I₂ ≠ 0` (`velocity_of_quartic`, `exists_rates`): there are `a, b > 0` with
  `a² − b² = (e/m)² (E² − B²)` and `a² b² = (e/m)⁴ (E · B)²`; the space is the sum of the range
  of the projection `(A² + b²)/(a² + b²)`, where `A² = a²`, and its kernel, where `A² = −b²`,
  and the motion is the sum of a hyperbolic and a circular motion.

A field of two covectors has `I₂ = 0` (`pseudoscalarInvariant_of_isSimple`), and parallel
fields `uniformField E B` have `I₁ = B² − E²`, `I₂ = E B` and the rates `e E/m`, `e B/m`
(`velocity_uniformField_closed`). The kinds are stated for the generator. A frame in which the
electric and the magnetic field are parallel is not constructed.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Electrodynamics

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

/-! ### The force in components -/

theorem single_zero_eq : (Pi.single 0 1 : Spacetime) = ![1, 0, 0, 0] := by
  ext i
  fin_cases i <;> rfl

theorem single_one_eq : (Pi.single 1 1 : Spacetime) = ![0, 1, 0, 0] := by
  ext i
  fin_cases i <;> rfl

theorem single_two_eq : (Pi.single 2 1 : Spacetime) = ![0, 0, 1, 0] := by
  ext i
  fin_cases i <;> rfl

theorem single_three_eq : (Pi.single 3 1 : Spacetime) = ![0, 0, 0, 1] := by
  ext i
  fin_cases i <;> rfl

/-- The force on a vector `v` in terms of the electric and the magnetic components:
`e (E · v, v⁰ E + v × B)`. -/
theorem lorentzForce_vectors (e : ℝ) (F : TwoForm) (v : Spacetime) :
    lorentzForce e F v = e •
      ![electricVector F 0 * v 1 + electricVector F 1 * v 2 + electricVector F 2 * v 3,
        v 0 * electricVector F 0 + (v 2 * magneticVector F 2 - v 3 * magneticVector F 1),
        v 0 * electricVector F 1 + (v 3 * magneticVector F 0 - v 1 * magneticVector F 2),
        v 0 * electricVector F 2 + (v 1 * magneticVector F 1 - v 2 * magneticVector F 0)] := by
  have h0 := ChargedParticle.lorentzForce_zero e F v
  have h1 : lorentzForce e F v 1 = -e * F ![v, Pi.single 1 1] :=
    ChargedParticle.lorentzForce_succ e F v 0
  have h2 : lorentzForce e F v 2 = -e * F ![v, Pi.single 2 1] :=
    ChargedParticle.lorentzForce_succ e F v 1
  have h3 : lorentzForce e F v 3 = -e * F ![v, Pi.single 3 1] :=
    ChargedParticle.lorentzForce_succ e F v 2
  rw [single_zero_eq, twoForm_apply_vectors] at h0
  rw [single_one_eq, twoForm_apply_vectors] at h1
  rw [single_two_eq, twoForm_apply_vectors] at h2
  rw [single_three_eq, twoForm_apply_vectors] at h3
  simp only [Matrix.cons_val] at h0 h1 h2 h3
  ext μ
  fin_cases μ
  · refine h0.trans ?_
    change _ = e * (electricVector F 0 * v 1 + electricVector F 1 * v 2 +
      electricVector F 2 * v 3)
    ring
  · refine h1.trans ?_
    change _ = e * (v 0 * electricVector F 0 +
      (v 2 * magneticVector F 2 - v 3 * magneticVector F 1))
    ring
  · refine h2.trans ?_
    change _ = e * (v 0 * electricVector F 1 +
      (v 3 * magneticVector F 0 - v 1 * magneticVector F 2))
    ring
  · refine h3.trans ?_
    change _ = e * (v 0 * electricVector F 2 +
      (v 1 * magneticVector F 1 - v 2 * magneticVector F 0))
    ring

/-- The linear map `v ↦ (E · v, v⁰ E + v × B)` of two triples `E` and `B`. -/
def forceVector (E B : Fin 3 → ℝ) (v : Spacetime) : Spacetime :=
  ![E 0 * v 1 + E 1 * v 2 + E 2 * v 3,
    v 0 * E 0 + (v 2 * B 2 - v 3 * B 1),
    v 0 * E 1 + (v 3 * B 0 - v 1 * B 2),
    v 0 * E 2 + (v 1 * B 1 - v 2 * B 0)]

theorem lorentzForce_eq_forceVector (e : ℝ) (F : TwoForm) (v : Spacetime) :
    lorentzForce e F v = e • forceVector (electricVector F) (magneticVector F) v :=
  lorentzForce_vectors e F v

/-- The cube of the force map: `G³ = −(B² − E²) G − (E · B) D`, where `D` is the force map of
the triples `−B` and `E`. -/
theorem forceVector_cube (E B : Fin 3 → ℝ) (v : Spacetime) :
    forceVector E B (forceVector E B (forceVector E B v)) =
      (-(∑ i, B i ^ 2 - ∑ i, E i ^ 2)) • forceVector E B v -
        (∑ i, E i * B i) • forceVector (-B) E v := by
  ext μ
  fin_cases μ <;> simp [forceVector, Fin.sum_univ_three] <;> ring

/-- The product with the dual force map: `G D = −(E · B)`. -/
theorem forceVector_dual (E B : Fin 3 → ℝ) (v : Spacetime) :
    forceVector E B (forceVector (-B) E v) = (-(∑ i, E i * B i)) • v := by
  ext μ
  fin_cases μ <;> simp [forceVector, Fin.sum_univ_three] <;> ring

theorem forceVector_smul (E B : Fin 3 → ℝ) (c : ℝ) (v : Spacetime) :
    forceVector E B (c • v) = c • forceVector E B v := by
  ext μ
  fin_cases μ <;> simp [forceVector] <;> ring

end ProjectAinos.Electrodynamics

namespace ProjectAinos.Electrodynamics.ConstantField

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.LinearODE SpecialRelativity
open SmoothGeometry.DifferentialForm Examples

variable {m e : ℝ} (F : TwoForm)

/-! ### The identities of the generator -/

/-- The dual of the generator: the force map of the triples `−B` and `E`. -/
def dualGenerator (F : TwoForm) (v : Spacetime) : Spacetime :=
  forceVector (-magneticVector F) (electricVector F) v

theorem generator_eq_forceVector (m e : ℝ) (v : Spacetime) :
    generator m e F v = (e / m) • forceVector (electricVector F) (magneticVector F) v := by
  rw [generator_apply, lorentzForce_eq_forceVector, smul_smul]
  congr 1
  ring

/-- The cube of the generator `A = (e/m) F♯`:
`A³ = −(e/m)² (B² − E²) A − (e/m)³ (E · B) D` with the dual `D`. -/
theorem generator_cube_eq (m e : ℝ) (v : Spacetime) :
    generator m e F (generator m e F (generator m e F v)) =
      (-((e / m) ^ 2 * scalarInvariant F)) • generator m e F v -
        ((e / m) ^ 3 * pseudoscalarInvariant F) • dualGenerator F v := by
  simp only [generator_eq_forceVector, forceVector_smul, forceVector_cube, dualGenerator,
    scalarInvariant_vectors, pseudoscalarInvariant_vectors]
  module

/-- The product of the generator and its dual: `A D = −(e/m) (E · B)`. -/
theorem generator_dualGenerator (m e : ℝ) (v : Spacetime) :
    generator m e F (dualGenerator F v) = (-(e / m * pseudoscalarInvariant F)) • v := by
  rw [generator_eq_forceVector, dualGenerator, forceVector_dual, pseudoscalarInvariant_vectors]
  module

/-- The equation of Cayley and Hamilton for the generator:
`A⁴ = −(e/m)² (B² − E²) A² + (e/m)⁴ (E · B)²`. -/
theorem generator_quartic (m e : ℝ) (v : Spacetime) :
    generator m e F (generator m e F (generator m e F (generator m e F v))) =
      (-((e / m) ^ 2 * scalarInvariant F)) • generator m e F (generator m e F v) +
        ((e / m) ^ 4 * pseudoscalarInvariant F ^ 2) • v := by
  rw [generator_cube_eq F m e v, map_sub, map_smul, map_smul, generator_dualGenerator]
  module

/-- For a field with `E · B = 0` the cube of the generator is a multiple of the generator. -/
theorem generator_cube_of_pseudoscalarInvariant (hI : pseudoscalarInvariant F = 0) (m e : ℝ)
    (v : Spacetime) :
    generator m e F (generator m e F (generator m e F v)) =
      (-((e / m) ^ 2 * scalarInvariant F)) • generator m e F v := by
  rw [generator_cube_eq, hI, mul_zero, zero_smul, sub_zero]

variable {F}

/-- A field of two covectors has `E · B = 0`. -/
theorem pseudoscalarInvariant_of_isSimple {α β : FourCovector} (h : IsSimple F α β) :
    pseudoscalarInvariant F = 0 := by
  have h' : ∀ v w, F ![v, w] = α v * β w - α w * β v := h
  rw [pseudoscalarInvariant_vectors]
  simp only [Fin.sum_univ_three, electricVector, magneticVector, component, h', Matrix.cons_val]
  ring

/-! ### The four kinds of a constant field -/

/-- `E · B = 0` and `E² > B²`: the motion is hyperbolic. -/
theorem velocity_of_scalarInvariant_neg (hI : pseudoscalarInvariant F = 0) {Ω : ℝ} (hΩ : Ω ≠ 0)
    (hκ : -((e / m) ^ 2 * scalarInvariant F) = Ω ^ 2) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + (Real.sinh (Ω * τ) / Ω) • generator m e F u₀ +
      ((Real.cosh (Ω * τ) - 1) / Ω ^ 2) • generator m e F (generator m e F u₀) :=
  linearVelocity_eq_of_cube
    (fun v => by rw [generator_cube_of_pseudoscalarInvariant F hI, hκ])
    (hasDerivAt_sinh_div hΩ) (hasDerivAt_cosh_sub_div hΩ) (by simp) (by simp) u₀ τ

/-- `E · B = 0` and `E² < B²`: the motion is circular. -/
theorem velocity_of_scalarInvariant_pos (hI : pseudoscalarInvariant F = 0) {Ω : ℝ} (hΩ : Ω ≠ 0)
    (hκ : -((e / m) ^ 2 * scalarInvariant F) = -Ω ^ 2) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + (Real.sin (Ω * τ) / Ω) • generator m e F u₀ +
      ((1 - Real.cos (Ω * τ)) / Ω ^ 2) • generator m e F (generator m e F u₀) :=
  linearVelocity_eq_of_cube
    (fun v => by rw [generator_cube_of_pseudoscalarInvariant F hI, hκ])
    (hasDerivAt_sin_div hΩ) (hasDerivAt_one_sub_cos_div hΩ) (by simp) (by simp) u₀ τ

/-- `E · B = 0` and `E² = B²`, a null field: the cube of the generator is zero, and the
four-velocity is a polynomial of degree two. -/
theorem velocity_of_invariants_zero (hI₁ : scalarInvariant F = 0)
    (hI₂ : pseudoscalarInvariant F = 0) (m e : ℝ) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + τ • generator m e F u₀ +
      (τ ^ 2 / 2) • generator m e F (generator m e F u₀) := by
  refine linearVelocity_eq_of_cube (κ := 0) (s := fun t => t) (c := fun t => t ^ 2 / 2)
    (fun v => by rw [generator_cube_of_pseudoscalarInvariant F hI₂, hI₁, mul_zero, neg_zero])
    (fun t => ?_) (fun t => ?_) rfl (by simp) u₀ τ
  · exact (hasDerivAt_id' t).congr_deriv (by simp)
  · have h2 := ((hasDerivAt_id t).pow 2).div_const 2
    refine h2.congr_deriv ?_
    simp

/-- `E · B ≠ 0`: with `a² − b² = (e/m)² (E² − B²)` and `a b = ±(e/m)² E · B`, the motion is the
sum of a hyperbolic motion with the rate `a` and a circular motion with the rate `b`, on the
range and on the kernel of the projection `(A² + b²)/(a² + b²)`. -/
theorem velocity_of_quartic {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a ^ 2 - b ^ 2 = -((e / m) ^ 2 * scalarInvariant F))
    (hab' : a ^ 2 * b ^ 2 = (e / m) ^ 4 * pseudoscalarInvariant F ^ 2) (u₀ : Spacetime)
    (τ : ℝ) :
    velocity m e F u₀ τ =
      u₀ + (Real.sinh (a * τ) / a) •
          generator m e F (hyperbolicProjection (generator m e F) a b u₀) +
        ((Real.cosh (a * τ) - 1) / a ^ 2) • generator m e F
          (generator m e F (hyperbolicProjection (generator m e F) a b u₀)) +
        (Real.sin (b * τ) / b) •
          generator m e F (u₀ - hyperbolicProjection (generator m e F) a b u₀) +
        ((1 - Real.cos (b * τ)) / b ^ 2) • generator m e F
          (generator m e F (u₀ - hyperbolicProjection (generator m e F) a b u₀)) :=
  linearVelocity_eq_of_quartic (fun v => by rw [generator_quartic, hab, hab'])
    (by positivity) (hasDerivAt_sinh_div ha) (hasDerivAt_cosh_sub_div ha) (by simp) (by simp)
    (hasDerivAt_sin_div hb) (hasDerivAt_one_sub_cos_div hb) (by simp) (by simp) u₀ τ

/-- The two rates exist: for real `p` and `q ≠ 0` there are positive `a` and `b` with
`a² − b² = p` and `a² b² = q²`. -/
theorem exists_rates (p : ℝ) {q : ℝ} (hq : q ≠ 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ^ 2 - b ^ 2 = p ∧ a ^ 2 * b ^ 2 = q ^ 2 := by
  have hq2 : 0 < q ^ 2 := by positivity
  have hD : 0 < p ^ 2 + 4 * q ^ 2 := by positivity
  have hs := Real.sq_sqrt hD.le
  have hsp : |p| < Real.sqrt (p ^ 2 + 4 * q ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg p) (by linarith)
  have h1 : 0 < (Real.sqrt (p ^ 2 + 4 * q ^ 2) + p) / 2 := by
    have := neg_abs_le p
    linarith
  have h2 : 0 < (Real.sqrt (p ^ 2 + 4 * q ^ 2) - p) / 2 := by
    have := le_abs_self p
    linarith
  refine ⟨Real.sqrt ((Real.sqrt (p ^ 2 + 4 * q ^ 2) + p) / 2),
    Real.sqrt ((Real.sqrt (p ^ 2 + 4 * q ^ 2) - p) / 2), Real.sqrt_pos.mpr h1,
    Real.sqrt_pos.mpr h2, ?_, ?_⟩
  · rw [Real.sq_sqrt h1.le, Real.sq_sqrt h2.le]
    ring
  · rw [Real.sq_sqrt h1.le, Real.sq_sqrt h2.le]
    linear_combination (1 / 4 : ℝ) * hs

/-! ### The invariants of the examples -/

theorem electricVector_uniformField (E B : ℝ) :
    electricVector (uniformField E B) = ![E, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [electricVector, component, uniformField, coordinateForm_apply, Matrix.det_fin_two]

theorem magneticVector_uniformField (E B : ℝ) :
    magneticVector (uniformField E B) = ![B, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [magneticVector, component, uniformField, coordinateForm_apply, Matrix.det_fin_two]

/-- Parallel fields have the invariants `B² − E²` and `E B`. -/
theorem scalarInvariant_uniformField (E B : ℝ) :
    scalarInvariant (uniformField E B) = B ^ 2 - E ^ 2 := by
  rw [scalarInvariant_vectors, electricVector_uniformField, magneticVector_uniformField]
  simp [Fin.sum_univ_three]

theorem pseudoscalarInvariant_uniformField (E B : ℝ) :
    pseudoscalarInvariant (uniformField E B) = E * B := by
  rw [pseudoscalarInvariant_vectors, electricVector_uniformField, magneticVector_uniformField]
  simp [Fin.sum_univ_three]

/-- Both invariants of the null field are zero. -/
theorem pseudoscalarInvariant_nullField (E : ℝ) : pseudoscalarInvariant (nullField E) = 0 :=
  pseudoscalarInvariant_of_isSimple (isSimple_nullField E)

theorem scalarInvariant_nullField (E : ℝ) : scalarInvariant (nullField E) = 0 := by
  rw [scalarInvariant_vectors]
  simp [Fin.sum_univ_three, electricVector, magneticVector, component, nullField,
    coordinateForm_apply, Matrix.det_fin_two]

/-- Parallel fields that are not zero: the motion with the rates `e E/m` and `e B/m`. -/
theorem velocity_uniformField_closed {m e E B : ℝ} (hE : e * E / m ≠ 0) (hB : e * B / m ≠ 0)
    (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (uniformField E B) u₀ τ =
      u₀ + (Real.sinh (e * E / m * τ) / (e * E / m)) • generator m e (uniformField E B)
          (hyperbolicProjection (generator m e (uniformField E B)) (e * E / m) (e * B / m)
            u₀) +
        ((Real.cosh (e * E / m * τ) - 1) / (e * E / m) ^ 2) • generator m e (uniformField E B)
          (generator m e (uniformField E B)
            (hyperbolicProjection (generator m e (uniformField E B)) (e * E / m) (e * B / m)
              u₀)) +
        (Real.sin (e * B / m * τ) / (e * B / m)) • generator m e (uniformField E B)
          (u₀ - hyperbolicProjection (generator m e (uniformField E B)) (e * E / m)
            (e * B / m) u₀) +
        ((1 - Real.cos (e * B / m * τ)) / (e * B / m) ^ 2) • generator m e (uniformField E B)
          (generator m e (uniformField E B)
            (u₀ - hyperbolicProjection (generator m e (uniformField E B)) (e * E / m)
              (e * B / m) u₀)) :=
  velocity_of_quartic hE hB
    (by rw [scalarInvariant_uniformField]; ring)
    (by rw [pseudoscalarInvariant_uniformField]; ring) u₀ τ

end ProjectAinos.Electrodynamics.ConstantField
