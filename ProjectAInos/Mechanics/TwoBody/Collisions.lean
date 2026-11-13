/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.TwoBody.Kinematics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Disintegration and elastic collisions

Both are algebra on the level sets of the momentum and the energy.

*Disintegration* (Landau–Lifshitz §16). In the centre-of-mass frame the two
fragments have opposite momenta, and the energy balance gives
`|p|² = 2 μ ε` with `ε` the disintegration energy. The fragments share `ε` in
inverse proportion to their masses.

*Elastic collisions* (Landau–Lifshitz §17). Conservation of momentum and of
kinetic energy holds exactly when the centre of mass keeps its velocity and the
relative velocity keeps its length. The velocities after the collision are
`V + (m₂ / M) w` and `V − (m₁ / M) w`, where `w` is any vector with the length of
the initial relative velocity: the collision is determined up to the direction
of `w`. For a target at rest the speeds after the collision, the head-on case,
the bound on the transferred energy and the right angle for equal masses
follow.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.TwoBody

open Matrix

/-! ### Disintegration -/

/-- In the centre-of-mass frame the fragments have momenta of equal length. -/
theorem disintegration_momentum_sq_eq {p₁ p₂ : Fin 3 → ℝ} (hp : p₁ + p₂ = 0) :
    p₂ ⬝ᵥ p₂ = p₁ ⬝ᵥ p₁ := by
  have h : p₂ = -p₁ := (neg_eq_of_add_eq_zero_right hp).symm
  rw [h, neg_dotProduct_neg]

/-- The momentum of the fragments: `|p|² = 2 μ ε`, where `ε = E − E₁ − E₂` is
the disintegration energy. -/
theorem disintegration_momentum_sq {m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0)
    (hM : m₁ + m₂ ≠ 0) {p₁ p₂ : Fin 3 → ℝ} {E E₁ E₂ : ℝ} (hp : p₁ + p₂ = 0)
    (hE : E = E₁ + E₂ + p₁ ⬝ᵥ p₁ / (2 * m₁) + p₂ ⬝ᵥ p₂ / (2 * m₂)) :
    p₁ ⬝ᵥ p₁ = 2 * reducedMass m₁ m₂ * (E - E₁ - E₂) := by
  rw [disintegration_momentum_sq_eq hp] at hE
  rw [hE, reducedMass]
  field_simp
  ring

/-- The first fragment carries the fraction `m₂ / (m₁ + m₂)` of the
disintegration energy. -/
theorem disintegration_kinetic_one {m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0)
    (hM : m₁ + m₂ ≠ 0) {p₁ p₂ : Fin 3 → ℝ} {E E₁ E₂ : ℝ} (hp : p₁ + p₂ = 0)
    (hE : E = E₁ + E₂ + p₁ ⬝ᵥ p₁ / (2 * m₁) + p₂ ⬝ᵥ p₂ / (2 * m₂)) :
    p₁ ⬝ᵥ p₁ / (2 * m₁) = m₂ / (m₁ + m₂) * (E - E₁ - E₂) := by
  rw [disintegration_momentum_sq h₁ h₂ hM hp hE, reducedMass]
  field_simp

/-- The second fragment carries the fraction `m₁ / (m₁ + m₂)` of the
disintegration energy. -/
theorem disintegration_kinetic_two {m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0)
    (hM : m₁ + m₂ ≠ 0) {p₁ p₂ : Fin 3 → ℝ} {E E₁ E₂ : ℝ} (hp : p₁ + p₂ = 0)
    (hE : E = E₁ + E₂ + p₁ ⬝ᵥ p₁ / (2 * m₁) + p₂ ⬝ᵥ p₂ / (2 * m₂)) :
    p₂ ⬝ᵥ p₂ / (2 * m₂) = m₁ / (m₁ + m₂) * (E - E₁ - E₂) := by
  rw [disintegration_momentum_sq_eq hp, disintegration_momentum_sq h₁ h₂ hM hp hE, reducedMass]
  field_simp

/-- A disintegration into fragments of positive mass needs a non-negative
disintegration energy. -/
theorem disintegration_energy_nonneg {m₁ m₂ : ℝ} (h₁ : 0 < m₁) (h₂ : 0 < m₂)
    {p₁ p₂ : Fin 3 → ℝ} {E E₁ E₂ : ℝ}
    (hE : E = E₁ + E₂ + p₁ ⬝ᵥ p₁ / (2 * m₁) + p₂ ⬝ᵥ p₂ / (2 * m₂)) : 0 ≤ E - E₁ - E₂ := by
  have hp₁ : 0 ≤ p₁ ⬝ᵥ p₁ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hp₂ : 0 ≤ p₂ ⬝ᵥ p₂ := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hk₁ : 0 ≤ p₁ ⬝ᵥ p₁ / (2 * m₁) := div_nonneg hp₁ (by linarith)
  have hk₂ : 0 ≤ p₂ ⬝ᵥ p₂ / (2 * m₂) := div_nonneg hp₂ (by linarith)
  linarith

/-- The velocity of a fragment in the laboratory frame: if `v = V + v₀`, then
`|v₀|² = |v|² + |V|² − 2 v · V`. -/
theorem disintegration_laboratory {v V v₀ : Fin 3 → ℝ} (h : v = V + v₀) :
    v₀ ⬝ᵥ v₀ = v ⬝ᵥ v + V ⬝ᵥ V - 2 * (v ⬝ᵥ V) := by
  rw [h]
  simp only [dotProduct, Fin.sum_univ_three, Pi.add_apply]
  ring

/-! ### Elastic collisions -/

/-- An elastic collision: momentum and kinetic energy are conserved. -/
structure IsElastic (m₁ m₂ : ℝ) (v₁ v₂ v₁' v₂' : Fin 3 → ℝ) : Prop where
  momentum : m₁ • v₁ + m₂ • v₂ = m₁ • v₁' + m₂ • v₂'
  energy : m₁ * (v₁ ⬝ᵥ v₁) + m₂ * (v₂ ⬝ᵥ v₂) = m₁ * (v₁' ⬝ᵥ v₁') + m₂ * (v₂' ⬝ᵥ v₂')

/-- The velocity of the first particle after a collision with relative velocity
`w`: `V + (m₂ / M) w`. -/
def outgoingOne (m₁ m₂ : ℝ) (v₁ v₂ w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  centreOfMassVelocity m₁ m₂ v₁ v₂ + (m₂ / (m₁ + m₂)) • w

/-- The velocity of the second particle after a collision with relative velocity
`w`: `V − (m₁ / M) w`. -/
def outgoingTwo (m₁ m₂ : ℝ) (v₁ v₂ w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  centreOfMassVelocity m₁ m₂ v₁ v₂ - (m₁ / (m₁ + m₂)) • w

namespace IsElastic

variable {m₁ m₂ : ℝ} {v₁ v₂ v₁' v₂' : Fin 3 → ℝ}

/-- The centre of mass keeps its velocity. -/
theorem centreOfMassVelocity_eq (h : IsElastic m₁ m₂ v₁ v₂ v₁' v₂') :
    centreOfMassVelocity m₁ m₂ v₁' v₂' = centreOfMassVelocity m₁ m₂ v₁ v₂ := by
  rw [centreOfMassVelocity, centreOfMassVelocity, h.momentum]

/-- The relative velocity keeps its length. -/
theorem relative_speed (h : IsElastic m₁ m₂ v₁ v₂ v₁' v₂') (hm : m₁ * m₂ ≠ 0) :
    (v₁' - v₂') ⬝ᵥ (v₁' - v₂') = (v₁ - v₂) ⬝ᵥ (v₁ - v₂) := by
  have h1 := total_mass_mul_kinetic m₁ m₂ v₁ v₂
  have h2 := total_mass_mul_kinetic m₁ m₂ v₁' v₂'
  rw [h.energy, h.momentum] at h1
  have h3 : m₁ * m₂ * ((v₁' - v₂') ⬝ᵥ (v₁' - v₂')) =
      m₁ * m₂ * ((v₁ - v₂) ⬝ᵥ (v₁ - v₂)) := by linarith
  exact mul_left_cancel₀ hm h3

/-- The velocity of the first particle after the collision. -/
theorem velocity_one (h : IsElastic m₁ m₂ v₁ v₂ v₁' v₂') (hM : m₁ + m₂ ≠ 0) :
    v₁' = outgoingOne m₁ m₂ v₁ v₂ (v₁' - v₂') := by
  rw [outgoingOne, ← h.centreOfMassVelocity_eq]
  exact velocity_one_eq hM v₁' v₂'

/-- The velocity of the second particle after the collision. -/
theorem velocity_two (h : IsElastic m₁ m₂ v₁ v₂ v₁' v₂') (hM : m₁ + m₂ ≠ 0) :
    v₂' = outgoingTwo m₁ m₂ v₁ v₂ (v₁' - v₂') := by
  rw [outgoingTwo, ← h.centreOfMassVelocity_eq]
  exact velocity_two_eq hM v₁' v₂'

end IsElastic

theorem outgoingOne_sub_outgoingTwo {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v₁ v₂ w : Fin 3 → ℝ) :
    outgoingOne m₁ m₂ v₁ v₂ w - outgoingTwo m₁ m₂ v₁ v₂ w = w := by
  ext i
  simp only [outgoingOne, outgoingTwo, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

theorem momentum_outgoing {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v₁ v₂ w : Fin 3 → ℝ) :
    m₁ • outgoingOne m₁ m₂ v₁ v₂ w + m₂ • outgoingTwo m₁ m₂ v₁ v₂ w = m₁ • v₁ + m₂ • v₂ := by
  ext i
  simp only [outgoingOne, outgoingTwo, centreOfMassVelocity, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

/-- Every vector with the length of the initial relative velocity is the
relative velocity after an elastic collision. -/
theorem isElastic_outgoing {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v₁ v₂ : Fin 3 → ℝ)
    {w : Fin 3 → ℝ} (hw : w ⬝ᵥ w = (v₁ - v₂) ⬝ᵥ (v₁ - v₂)) :
    IsElastic m₁ m₂ v₁ v₂ (outgoingOne m₁ m₂ v₁ v₂ w) (outgoingTwo m₁ m₂ v₁ v₂ w) where
  momentum := (momentum_outgoing hM v₁ v₂ w).symm
  energy := by
    have h1 := total_mass_mul_kinetic m₁ m₂ v₁ v₂
    have h2 := total_mass_mul_kinetic m₁ m₂ (outgoingOne m₁ m₂ v₁ v₂ w)
      (outgoingTwo m₁ m₂ v₁ v₂ w)
    rw [momentum_outgoing hM, outgoingOne_sub_outgoingTwo hM, hw, ← h1] at h2
    exact (mul_left_cancel₀ hM h2).symm

/-- An elastic collision is determined up to the direction of the relative
velocity after the collision (Landau–Lifshitz §17). -/
theorem isElastic_iff {m₁ m₂ : ℝ} (hm : m₁ * m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0)
    (v₁ v₂ v₁' v₂' : Fin 3 → ℝ) :
    IsElastic m₁ m₂ v₁ v₂ v₁' v₂' ↔
      ∃ w : Fin 3 → ℝ, w ⬝ᵥ w = (v₁ - v₂) ⬝ᵥ (v₁ - v₂) ∧
        v₁' = outgoingOne m₁ m₂ v₁ v₂ w ∧ v₂' = outgoingTwo m₁ m₂ v₁ v₂ w := by
  constructor
  · intro h
    exact ⟨v₁' - v₂', h.relative_speed hm, h.velocity_one hM, h.velocity_two hM⟩
  · rintro ⟨w, hw, rfl, rfl⟩
    exact isElastic_outgoing hM v₁ v₂ hw

/-! ### A target at rest

The first particle has velocity `v n` with `n` a unit vector, the second is at
rest, and the relative velocity after the collision is `v n₀` with `n₀` a unit
vector. The scalar product `n · n₀` is the cosine of the angle of deflection in
the centre-of-mass frame. -/

theorem outgoingOne_rest {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v : ℝ) (n n₀ : Fin 3 → ℝ) :
    outgoingOne m₁ m₂ (v • n) 0 (v • n₀) = (v / (m₁ + m₂)) • (m₁ • n + m₂ • n₀) := by
  ext i
  simp only [outgoingOne, centreOfMassVelocity, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
    smul_eq_mul, mul_zero, add_zero]
  field_simp

theorem outgoingTwo_rest {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v : ℝ) (n n₀ : Fin 3 → ℝ) :
    outgoingTwo m₁ m₂ (v • n) 0 (v • n₀) = (m₁ * v / (m₁ + m₂)) • (n - n₀) := by
  ext i
  simp only [outgoingTwo, centreOfMassVelocity, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.zero_apply, smul_eq_mul, mul_zero, add_zero]
  field_simp

/-- The speed of the incident particle after the collision:
`|v₁'|² = v² (m₁² + m₂² + 2 m₁ m₂ n · n₀) / (m₁ + m₂)²`. -/
theorem outgoingOne_rest_dotProduct_self {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v : ℝ)
    {n n₀ : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (hn₀ : n₀ ⬝ᵥ n₀ = 1) :
    outgoingOne m₁ m₂ (v • n) 0 (v • n₀) ⬝ᵥ outgoingOne m₁ m₂ (v • n) 0 (v • n₀) =
      v ^ 2 * (m₁ ^ 2 + m₂ ^ 2 + 2 * m₁ * m₂ * (n ⬝ᵥ n₀)) / (m₁ + m₂) ^ 2 := by
  rw [outgoingOne_rest hM]
  simp only [smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_add, smul_eq_mul, hn,
    hn₀, dotProduct_comm n₀ n]
  field_simp
  ring

/-- The speed of the target after the collision:
`|v₂'|² = 2 m₁² v² (1 − n · n₀) / (m₁ + m₂)²`. -/
theorem outgoingTwo_rest_dotProduct_self {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v : ℝ)
    {n n₀ : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (hn₀ : n₀ ⬝ᵥ n₀ = 1) :
    outgoingTwo m₁ m₂ (v • n) 0 (v • n₀) ⬝ᵥ outgoingTwo m₁ m₂ (v • n) 0 (v • n₀) =
      2 * m₁ ^ 2 * v ^ 2 * (1 - n ⬝ᵥ n₀) / (m₁ + m₂) ^ 2 := by
  rw [outgoingTwo_rest hM]
  simp only [smul_dotProduct, dotProduct_smul, sub_dotProduct, dotProduct_sub, smul_eq_mul, hn,
    hn₀, dotProduct_comm n₀ n]
  field_simp
  ring

/-- A head-on collision: the incident particle keeps the velocity
`(m₁ − m₂) / (m₁ + m₂) · v`. -/
theorem outgoingOne_headOn {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v : ℝ) (n : Fin 3 → ℝ) :
    outgoingOne m₁ m₂ (v • n) 0 (v • -n) = ((m₁ - m₂) / (m₁ + m₂) * v) • n := by
  rw [outgoingOne_rest hM]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  field_simp
  ring

/-- A head-on collision: the target acquires the velocity
`2 m₁ / (m₁ + m₂) · v`. -/
theorem outgoingTwo_headOn {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (v : ℝ) (n : Fin 3 → ℝ) :
    outgoingTwo m₁ m₂ (v • n) 0 (v • -n) = (2 * m₁ / (m₁ + m₂) * v) • n := by
  rw [outgoingTwo_rest hM]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  field_simp
  ring

/-- The scalar product of two unit vectors is at least `−1`. -/
theorem neg_one_le_dotProduct {n n₀ : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (hn₀ : n₀ ⬝ᵥ n₀ = 1) :
    -1 ≤ n ⬝ᵥ n₀ := by
  have h0 : 0 ≤ (n + n₀) ⬝ᵥ (n + n₀) := Finset.sum_nonneg fun i _ => mul_self_nonneg _
  simp only [add_dotProduct, dotProduct_add, hn, hn₀, dotProduct_comm n₀ n] at h0
  linarith

/-- The energy transferred to a target at rest is at most
`4 m₁ m₂ / (m₁ + m₂)²` times the energy of the incident particle
(Landau–Lifshitz §17). -/
theorem energy_transfer_le {m₁ m₂ : ℝ} (h₁ : 0 < m₁) (h₂ : 0 < m₂) (v : ℝ)
    {n n₀ : Fin 3 → ℝ} (hn : n ⬝ᵥ n = 1) (hn₀ : n₀ ⬝ᵥ n₀ = 1) :
    m₂ / 2 * (outgoingTwo m₁ m₂ (v • n) 0 (v • n₀) ⬝ᵥ outgoingTwo m₁ m₂ (v • n) 0 (v • n₀)) ≤
      4 * m₁ * m₂ / (m₁ + m₂) ^ 2 * (m₁ / 2 * v ^ 2) := by
  have hM : m₁ + m₂ ≠ 0 := by positivity
  have hK : 0 ≤ m₁ ^ 2 * m₂ * v ^ 2 / (m₁ + m₂) ^ 2 := by positivity
  have hc := neg_one_le_dotProduct hn hn₀
  have e1 : m₂ / 2 * (2 * m₁ ^ 2 * v ^ 2 * (1 - n ⬝ᵥ n₀) / (m₁ + m₂) ^ 2) =
      m₁ ^ 2 * m₂ * v ^ 2 / (m₁ + m₂) ^ 2 * (1 - n ⬝ᵥ n₀) := by
    field_simp
  have e2 : 4 * m₁ * m₂ / (m₁ + m₂) ^ 2 * (m₁ / 2 * v ^ 2) =
      m₁ ^ 2 * m₂ * v ^ 2 / (m₁ + m₂) ^ 2 * 2 := by
    field_simp
    ring
  rw [outgoingTwo_rest_dotProduct_self hM v hn hn₀, e1, e2]
  exact mul_le_mul_of_nonneg_left (by linarith) hK

/-- For equal masses and a target at rest, the two particles separate at a
right angle. -/
theorem outgoing_rest_dotProduct_eq_zero {m : ℝ} (hm : m ≠ 0) (v : ℝ) {n n₀ : Fin 3 → ℝ}
    (hn : n ⬝ᵥ n = 1) (hn₀ : n₀ ⬝ᵥ n₀ = 1) :
    outgoingOne m m (v • n) 0 (v • n₀) ⬝ᵥ outgoingTwo m m (v • n) 0 (v • n₀) = 0 := by
  have hM : m + m ≠ 0 := by
    intro h
    exact hm (by linarith)
  rw [outgoingOne_rest hM, outgoingTwo_rest hM]
  simp only [smul_dotProduct, dotProduct_smul, add_dotProduct, dotProduct_sub, smul_eq_mul, hn,
    hn₀, dotProduct_comm n₀ n]
  ring

end ProjectAInos.Mechanics.TwoBody
