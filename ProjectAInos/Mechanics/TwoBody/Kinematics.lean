/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Two bodies: the centre of mass and the reduced mass

For two particles of masses `m₁`, `m₂` and velocities `v₁`, `v₂`, the kinetic
energy is the kinetic energy of the centre of mass plus that of the relative
motion with the reduced mass `μ = m₁ m₂ / (m₁ + m₂)` (Landau–Lifshitz §13):

`½ m₁ |v₁|² + ½ m₂ |v₂|² = ½ (m₁ + m₂) |V|² + ½ μ |v₁ − v₂|²`.

The division-free form
`(m₁ + m₂) (m₁ |v₁|² + m₂ |v₂|²) = |m₁ v₁ + m₂ v₂|² + m₁ m₂ |v₁ − v₂|²` holds for
all masses and is the identity used for collisions. In the centre-of-mass frame
the momenta are `± μ (v₁ − v₂)`. Vectors are elements of `Fin 3 → ℝ` and `⬝ᵥ` is
the scalar product.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.TwoBody

open Matrix

/-- The reduced mass `m₁ m₂ / (m₁ + m₂)`. -/
def reducedMass (m₁ m₂ : ℝ) : ℝ := m₁ * m₂ / (m₁ + m₂)

/-- The velocity of the centre of mass. -/
def centreOfMassVelocity (m₁ m₂ : ℝ) (v₁ v₂ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (m₁ + m₂)⁻¹ • (m₁ • v₁ + m₂ • v₂)

/-- The division-free form of the splitting of the kinetic energy:
`(m₁ + m₂) (m₁ |v₁|² + m₂ |v₂|²) = |m₁ v₁ + m₂ v₂|² + m₁ m₂ |v₁ − v₂|²`. -/
theorem total_mass_mul_kinetic (m₁ m₂ : ℝ) (v₁ v₂ : Fin 3 → ℝ) :
    (m₁ + m₂) * (m₁ * (v₁ ⬝ᵥ v₁) + m₂ * (v₂ ⬝ᵥ v₂)) =
      (m₁ • v₁ + m₂ • v₂) ⬝ᵥ (m₁ • v₁ + m₂ • v₂) + m₁ * m₂ * ((v₁ - v₂) ⬝ᵥ (v₁ - v₂)) := by
  simp only [dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  ring

/-- The kinetic energy of two particles is the kinetic energy of the centre of
mass plus that of the relative motion with the reduced mass. -/
theorem kineticEnergy_eq {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v₁ v₂ : Fin 3 → ℝ) :
    m₁ / 2 * (v₁ ⬝ᵥ v₁) + m₂ / 2 * (v₂ ⬝ᵥ v₂) =
      (m₁ + m₂) / 2 *
          (centreOfMassVelocity m₁ m₂ v₁ v₂ ⬝ᵥ centreOfMassVelocity m₁ m₂ v₁ v₂) +
        reducedMass m₁ m₂ / 2 * ((v₁ - v₂) ⬝ᵥ (v₁ - v₂)) := by
  simp only [centreOfMassVelocity, reducedMass, dotProduct, Fin.sum_univ_three, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The velocity of the first particle: the centre of mass plus its share of
the relative velocity. -/
theorem velocity_one_eq {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v₁ v₂ : Fin 3 → ℝ) :
    v₁ = centreOfMassVelocity m₁ m₂ v₁ v₂ + (m₂ / (m₁ + m₂)) • (v₁ - v₂) := by
  ext i
  simp only [centreOfMassVelocity, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- The velocity of the second particle. -/
theorem velocity_two_eq {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v₁ v₂ : Fin 3 → ℝ) :
    v₂ = centreOfMassVelocity m₁ m₂ v₁ v₂ - (m₁ / (m₁ + m₂)) • (v₁ - v₂) := by
  ext i
  simp only [centreOfMassVelocity, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- In the centre-of-mass frame the momentum of the first particle is
`μ (v₁ − v₂)`. -/
theorem momentum_one_centreOfMass {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v₁ v₂ : Fin 3 → ℝ) :
    m₁ • (v₁ - centreOfMassVelocity m₁ m₂ v₁ v₂) = reducedMass m₁ m₂ • (v₁ - v₂) := by
  ext i
  simp only [centreOfMassVelocity, reducedMass, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]
  field_simp
  ring

/-- In the centre-of-mass frame the momenta are opposite. -/
theorem momentum_two_centreOfMass {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v₁ v₂ : Fin 3 → ℝ) :
    m₂ • (v₂ - centreOfMassVelocity m₁ m₂ v₁ v₂) = -(reducedMass m₁ m₂ • (v₁ - v₂)) := by
  ext i
  simp only [centreOfMassVelocity, reducedMass, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.neg_apply, smul_eq_mul]
  field_simp
  ring

end ProjectAInos.Mechanics.TwoBody
