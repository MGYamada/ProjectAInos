/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the two-body API: the reduced mass, disintegration,
elastic collisions and the canonical variables of the centre of mass. Default
elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its
type. -/
noncomputable section
open ProjectAInos.SmoothAlgebra ProjectAInos.Mechanics ProjectAInos.Mechanics.TwoBody
open Matrix

section Kinematics

example (m₁ m₂ : ℝ) : reducedMass m₁ m₂ = m₁ * m₂ / (m₁ + m₂) := rfl

example (m₁ m₂ : ℝ) (v₁ v₂ : Fin 3 → ℝ) :
    centreOfMassVelocity m₁ m₂ v₁ v₂ = (m₁ + m₂)⁻¹ • (m₁ • v₁ + m₂ • v₂) := rfl

/-- The kinetic energy splits into the centre of mass and the relative motion. -/
example {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v₁ v₂ : Fin 3 → ℝ) :
    m₁ / 2 * (v₁ ⬝ᵥ v₁) + m₂ / 2 * (v₂ ⬝ᵥ v₂) =
      (m₁ + m₂) / 2 *
          (centreOfMassVelocity m₁ m₂ v₁ v₂ ⬝ᵥ centreOfMassVelocity m₁ m₂ v₁ v₂) +
        reducedMass m₁ m₂ / 2 * ((v₁ - v₂) ⬝ᵥ (v₁ - v₂)) :=
  kineticEnergy_eq hM v₁ v₂

example (m₁ m₂ : ℝ) (v₁ v₂ : Fin 3 → ℝ) :
    (m₁ + m₂) * (m₁ * (v₁ ⬝ᵥ v₁) + m₂ * (v₂ ⬝ᵥ v₂)) =
      (m₁ • v₁ + m₂ • v₂) ⬝ᵥ (m₁ • v₁ + m₂ • v₂) + m₁ * m₂ * ((v₁ - v₂) ⬝ᵥ (v₁ - v₂)) :=
  total_mass_mul_kinetic m₁ m₂ v₁ v₂

example {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v₁ v₂ : Fin 3 → ℝ) :
    m₁ • (v₁ - centreOfMassVelocity m₁ m₂ v₁ v₂) = reducedMass m₁ m₂ • (v₁ - v₂) :=
  momentum_one_centreOfMass hM v₁ v₂

end Kinematics

section Disintegration

/-- `|p|² = 2 μ ε`. -/
example {m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0) {p₁ p₂ : Fin 3 → ℝ}
    {E E₁ E₂ : ℝ} (hp : p₁ + p₂ = 0)
    (hE : E = E₁ + E₂ + p₁ ⬝ᵥ p₁ / (2 * m₁) + p₂ ⬝ᵥ p₂ / (2 * m₂)) :
    p₁ ⬝ᵥ p₁ = 2 * reducedMass m₁ m₂ * (E - E₁ - E₂) :=
  disintegration_momentum_sq h₁ h₂ hM hp hE

/-- The fragments share the energy in inverse proportion to their masses. -/
example {m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0) {p₁ p₂ : Fin 3 → ℝ}
    {E E₁ E₂ : ℝ} (hp : p₁ + p₂ = 0)
    (hE : E = E₁ + E₂ + p₁ ⬝ᵥ p₁ / (2 * m₁) + p₂ ⬝ᵥ p₂ / (2 * m₂)) :
    p₁ ⬝ᵥ p₁ / (2 * m₁) = m₂ / (m₁ + m₂) * (E - E₁ - E₂) ∧
      p₂ ⬝ᵥ p₂ / (2 * m₂) = m₁ / (m₁ + m₂) * (E - E₁ - E₂) :=
  ⟨disintegration_kinetic_one h₁ h₂ hM hp hE, disintegration_kinetic_two h₁ h₂ hM hp hE⟩

example {m₁ m₂ : ℝ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) {p₁ p₂ : Fin 3 → ℝ} {E E₁ E₂ : ℝ}
    (hE : E = E₁ + E₂ + p₁ ⬝ᵥ p₁ / (2 * m₁) + p₂ ⬝ᵥ p₂ / (2 * m₂)) : 0 ≤ E - E₁ - E₂ :=
  disintegration_energy_nonneg h₁ h₂ hE

end Disintegration

section Elastic

example (m₁ m₂ : ℝ) (v₁ v₂ v₁' v₂' : Fin 3 → ℝ) :
    IsElastic m₁ m₂ v₁ v₂ v₁' v₂' ↔
      m₁ • v₁ + m₂ • v₂ = m₁ • v₁' + m₂ • v₂' ∧
        m₁ * (v₁ ⬝ᵥ v₁) + m₂ * (v₂ ⬝ᵥ v₂) = m₁ * (v₁' ⬝ᵥ v₁') + m₂ * (v₂' ⬝ᵥ v₂') :=
  ⟨fun h => ⟨h.momentum, h.energy⟩, fun h => ⟨h.1, h.2⟩⟩

example (m₁ m₂ : ℝ) (v₁ v₂ w : Fin 3 → ℝ) :
    outgoingOne m₁ m₂ v₁ v₂ w = centreOfMassVelocity m₁ m₂ v₁ v₂ + (m₂ / (m₁ + m₂)) • w ∧
      outgoingTwo m₁ m₂ v₁ v₂ w = centreOfMassVelocity m₁ m₂ v₁ v₂ - (m₁ / (m₁ + m₂)) • w :=
  ⟨rfl, rfl⟩

/-- The relative velocity keeps its length. -/
example {m₁ m₂ : ℝ} {v₁ v₂ v₁' v₂' : Fin 3 → ℝ} (h : IsElastic m₁ m₂ v₁ v₂ v₁' v₂')
    (hm : m₁ * m₂ ≠ 0) : (v₁' - v₂') ⬝ᵥ (v₁' - v₂') = (v₁ - v₂) ⬝ᵥ (v₁ - v₂) :=
  h.relative_speed hm

/-- An elastic collision is determined up to the direction of the relative
velocity after the collision. -/
example {m₁ m₂ : ℝ} (hm : m₁ * m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0) (v₁ v₂ v₁' v₂' : Fin 3 → ℝ) :
    IsElastic m₁ m₂ v₁ v₂ v₁' v₂' ↔
      ∃ w : Fin 3 → ℝ, w ⬝ᵥ w = (v₁ - v₂) ⬝ᵥ (v₁ - v₂) ∧
        v₁' = outgoingOne m₁ m₂ v₁ v₂ w ∧ v₂' = outgoingTwo m₁ m₂ v₁ v₂ w :=
  isElastic_iff hm hM v₁ v₂ v₁' v₂'

/-- Speeds after a collision with a target at rest. -/
example {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v : ℝ) {n n₀ : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1)
    (hn₀ : n₀ ⬝ᵥ n₀ = 1) :
    outgoingOne m₁ m₂ (v • n) 0 (v • n₀) ⬝ᵥ outgoingOne m₁ m₂ (v • n) 0 (v • n₀) =
        v ^ 2 * (m₁ ^ 2 + m₂ ^ 2 + 2 * m₁ * m₂ * (n ⬝ᵥ n₀)) / (m₁ + m₂) ^ 2 ∧
      outgoingTwo m₁ m₂ (v • n) 0 (v • n₀) ⬝ᵥ outgoingTwo m₁ m₂ (v • n) 0 (v • n₀) =
        2 * m₁ ^ 2 * v ^ 2 * (1 - n ⬝ᵥ n₀) / (m₁ + m₂) ^ 2 :=
  ⟨outgoingOne_rest_dotProduct_self hM v hn hn₀, outgoingTwo_rest_dotProduct_self hM v hn hn₀⟩

/-- A head-on collision. -/
example {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v : ℝ) (n : Fin 3 → ℝ) :
    outgoingOne m₁ m₂ (v • n) 0 (v • -n) = ((m₁ - m₂) / (m₁ + m₂) * v) • n ∧
      outgoingTwo m₁ m₂ (v • n) 0 (v • -n) = (2 * m₁ / (m₁ + m₂) * v) • n :=
  ⟨outgoingOne_headOn hM v n, outgoingTwo_headOn hM v n⟩

/-- The bound on the transferred energy. -/
example {m₁ m₂ : ℝ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) (v : ℝ) {n n₀ : Fin 3 → ℝ}
    (hn : n ⬝ᵥ n = 1) (hn₀ : n₀ ⬝ᵥ n₀ = 1) :
    m₂ / 2 * (outgoingTwo m₁ m₂ (v • n) 0 (v • n₀) ⬝ᵥ outgoingTwo m₁ m₂ (v • n) 0 (v • n₀)) ≤
      4 * m₁ * m₂ / (m₁ + m₂) ^ 2 * (m₁ / 2 * v ^ 2) :=
  energy_transfer_le h₁ h₂ v hn hn₀

/-- Equal masses separate at a right angle. -/
example {m : ℝ} (hm : m ≠ 0) (v : ℝ) {n n₀ : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1)
    (hn₀ : n₀ ⬝ᵥ n₀ = 1) :
    outgoingOne m m (v • n) 0 (v • n₀) ⬝ᵥ outgoingTwo m m (v • n) 0 (v • n₀) = 0 :=
  outgoing_rest_dotProduct_eq_zero hm v hn hn₀

end Elastic

section CanonicalVariables

example (m₁ m₂ : ℝ) (i : Fin 3) :
    centre m₁ m₂ i =
      algebraMap ℝ Space (m₁ / (m₁ + m₂)) * q₁ i + algebraMap ℝ Space (m₂ / (m₁ + m₂)) * q₂ i :=
  rfl

example (m₁ m₂ : ℝ) (i : Fin 3) :
    relativeMomentum m₁ m₂ i =
      algebraMap ℝ Space (m₂ / (m₁ + m₂)) * p₁ i - algebraMap ℝ Space (m₁ / (m₁ + m₂)) * p₂ i :=
  rfl

/-- The centre-of-mass variables are canonical. -/
example {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (i j : Fin 3) :
    canonical.bracket (centre m₁ m₂ i) (totalMomentum j) = (if i = j then 1 else 0) ∧
      canonical.bracket (relative i) (relativeMomentum m₁ m₂ j) = (if i = j then 1 else 0) ∧
      canonical.bracket (centre m₁ m₂ i) (relativeMomentum m₁ m₂ j) = 0 ∧
      canonical.bracket (relative i) (totalMomentum j) = 0 :=
  ⟨canonical_centre_totalMomentum hM i j, canonical_relative_relativeMomentum hM i j,
    canonical_centre_relativeMomentum m₁ m₂ i j, canonical_relative_totalMomentum i j⟩

/-- The kinetic energy in the centre-of-mass variables. -/
example {m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0) :
    kineticEnergy m₁ m₂ =
      algebraMap ℝ Space ((m₁ + m₂)⁻¹ / 2) * (totalMomentum ⬝ᵥ totalMomentum) +
        algebraMap ℝ Space ((reducedMass m₁ m₂)⁻¹ / 2) *
          (relativeMomentum m₁ m₂ ⬝ᵥ relativeMomentum m₁ m₂) :=
  kineticEnergy_eq_centre h₁ h₂ hM

end CanonicalVariables
