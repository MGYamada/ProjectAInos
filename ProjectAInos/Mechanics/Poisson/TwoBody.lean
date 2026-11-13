/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.TwoBody.Kinematics
public import ProjectAInos.SmoothAlgebra.Poisson.Canonical
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Canonical variables for two bodies

On the canonical phase space of two particles in space, the centre of mass
`R = (m₁ q₁ + m₂ q₂) / M`, the relative position `r = q₁ − q₂`, the total
momentum `P = p₁ + p₂` and the relative momentum `p = (m₂ p₁ − m₁ p₂) / M` are
canonical: `{Rᵢ, Pⱼ} = {rᵢ, pⱼ} = δᵢⱼ` and all other brackets vanish. In these
variables the kinetic energy is `|P|² / 2M + |p|² / 2μ` with the reduced mass
`μ` (Landau–Lifshitz §13). This is the linear canonical change of variables that
separates the motion of the centre of mass.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.TwoBody

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

/-- The canonical phase space of two particles in space. -/
abbrev Space := SmoothAlgebra.PhaseSpace (Fin 2 × Fin 3)

/-- The canonical Poisson structure of two particles. -/
abbrev canonical : PoissonStructure Space := PhaseSpace.canonical (Fin 2 × Fin 3)

/-- The position of the first particle. -/
def q₁ (i : Fin 3) : Space := PhaseSpace.q (0, i)

/-- The position of the second particle. -/
def q₂ (i : Fin 3) : Space := PhaseSpace.q (1, i)

/-- The momentum of the first particle. -/
def p₁ (i : Fin 3) : Space := PhaseSpace.p (0, i)

/-- The momentum of the second particle. -/
def p₂ (i : Fin 3) : Space := PhaseSpace.p (1, i)

theorem canonical_q₁_p₁ (i j : Fin 3) :
    canonical.bracket (q₁ i) (p₁ j) = if i = j then 1 else 0 := by
  rw [q₁, p₁, PhaseSpace.canonical_q_p]
  simp

theorem canonical_q₂_p₂ (i j : Fin 3) :
    canonical.bracket (q₂ i) (p₂ j) = if i = j then 1 else 0 := by
  rw [q₂, p₂, PhaseSpace.canonical_q_p]
  simp

theorem canonical_q₁_p₂ (i j : Fin 3) : canonical.bracket (q₁ i) (p₂ j) = 0 := by
  rw [q₁, p₂, PhaseSpace.canonical_q_p]
  simp

theorem canonical_q₂_p₁ (i j : Fin 3) : canonical.bracket (q₂ i) (p₁ j) = 0 := by
  rw [q₂, p₁, PhaseSpace.canonical_q_p]
  simp

/-- The centre of mass `R = (m₁ q₁ + m₂ q₂) / M`. -/
def centre (m₁ m₂ : ℝ) (i : Fin 3) : Space :=
  algebraMap ℝ Space (m₁ / (m₁ + m₂)) * q₁ i + algebraMap ℝ Space (m₂ / (m₁ + m₂)) * q₂ i

/-- The relative position `r = q₁ − q₂`. -/
def relative (i : Fin 3) : Space := q₁ i - q₂ i

/-- The total momentum `P = p₁ + p₂`. -/
def totalMomentum (i : Fin 3) : Space := p₁ i + p₂ i

/-- The relative momentum `p = (m₂ p₁ − m₁ p₂) / M`. -/
def relativeMomentum (m₁ m₂ : ℝ) (i : Fin 3) : Space :=
  algebraMap ℝ Space (m₂ / (m₁ + m₂)) * p₁ i - algebraMap ℝ Space (m₁ / (m₁ + m₂)) * p₂ i

theorem algebraMap_fraction_add {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) :
    algebraMap ℝ Space (m₁ / (m₁ + m₂)) + algebraMap ℝ Space (m₂ / (m₁ + m₂)) = 1 := by
  rw [← map_add, ← map_one (algebraMap ℝ Space)]
  congr 1
  field_simp

/-- `{Rᵢ, Pⱼ} = δᵢⱼ`. -/
theorem canonical_centre_totalMomentum {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (i j : Fin 3) :
    canonical.bracket (centre m₁ m₂ i) (totalMomentum j) = if i = j then 1 else 0 := by
  have hsum := algebraMap_fraction_add hM
  simp only [centre, totalMomentum, AlmostPoissonStructure.bracket_add_left,
    AlmostPoissonStructure.bracket_add_right, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_algebraMap_left, canonical_q₁_p₁, canonical_q₂_p₂,
    canonical_q₁_p₂, canonical_q₂_p₁, mul_zero, add_zero, zero_add]
  split_ifs
  · linear_combination hsum
  · ring

/-- `{rᵢ, pⱼ} = δᵢⱼ`. -/
theorem canonical_relative_relativeMomentum {m₁ m₂ : ℝ} (hM : m₁ + m₂ ≠ 0) (i j : Fin 3) :
    canonical.bracket (relative i) (relativeMomentum m₁ m₂ j) = if i = j then 1 else 0 := by
  have hsum := algebraMap_fraction_add hM
  simp only [relative, relativeMomentum, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_sub_right, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_algebraMap_right, canonical_q₁_p₁, canonical_q₂_p₂,
    canonical_q₁_p₂, canonical_q₂_p₁, mul_zero, add_zero, sub_zero, zero_sub]
  split_ifs
  · linear_combination hsum
  · ring

/-- `{Rᵢ, pⱼ} = 0`: the centre of mass commutes with the relative momentum. -/
theorem canonical_centre_relativeMomentum (m₁ m₂ : ℝ) (i j : Fin 3) :
    canonical.bracket (centre m₁ m₂ i) (relativeMomentum m₁ m₂ j) = 0 := by
  simp only [centre, relativeMomentum, AlmostPoissonStructure.bracket_add_left,
    AlmostPoissonStructure.bracket_sub_right, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_left,
    AlmostPoissonStructure.bracket_algebraMap_right, canonical_q₁_p₁, canonical_q₂_p₂,
    canonical_q₁_p₂, canonical_q₂_p₁, mul_zero, add_zero]
  split_ifs <;> ring

/-- `{rᵢ, Pⱼ} = 0`: the relative position commutes with the total momentum. -/
theorem canonical_relative_totalMomentum (i j : Fin 3) :
    canonical.bracket (relative i) (totalMomentum j) = 0 := by
  simp only [relative, totalMomentum, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_add_right, canonical_q₁_p₁, canonical_q₂_p₂,
    canonical_q₁_p₂, canonical_q₂_p₁]
  ring

/-- `{Rᵢ, rⱼ} = 0`. -/
theorem canonical_centre_relative (m₁ m₂ : ℝ) (i j : Fin 3) :
    canonical.bracket (centre m₁ m₂ i) (relative j) = 0 := by
  simp only [centre, relative, q₁, q₂, AlmostPoissonStructure.bracket_add_left,
    AlmostPoissonStructure.bracket_sub_right, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_algebraMap_left, PhaseSpace.canonical_q_q, mul_zero,
    add_zero, sub_zero]

/-- `{Pᵢ, pⱼ} = 0`. -/
theorem canonical_totalMomentum_relativeMomentum (m₁ m₂ : ℝ) (i j : Fin 3) :
    canonical.bracket (totalMomentum i) (relativeMomentum m₁ m₂ j) = 0 := by
  simp only [totalMomentum, relativeMomentum, p₁, p₂, AlmostPoissonStructure.bracket_add_left,
    AlmostPoissonStructure.bracket_sub_right, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_algebraMap_right, PhaseSpace.canonical_p_p, mul_zero,
    add_zero, sub_zero]

/-- The kinetic energy `|p₁|² / 2m₁ + |p₂|² / 2m₂` of two particles. -/
def kineticEnergy (m₁ m₂ : ℝ) : Space :=
  algebraMap ℝ Space (m₁⁻¹ / 2) * (p₁ ⬝ᵥ p₁) + algebraMap ℝ Space (m₂⁻¹ / 2) * (p₂ ⬝ᵥ p₂)

/-- In the canonical variables of the centre of mass the kinetic energy is
`|P|² / 2M + |p|² / 2μ` (Landau–Lifshitz §13). -/
theorem kineticEnergy_eq_centre {m₁ m₂ : ℝ} (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0)
    (hM : m₁ + m₂ ≠ 0) :
    kineticEnergy m₁ m₂ =
      algebraMap ℝ Space ((m₁ + m₂)⁻¹ / 2) * (totalMomentum ⬝ᵥ totalMomentum) +
        algebraMap ℝ Space ((reducedMass m₁ m₂)⁻¹ / 2) *
          (relativeMomentum m₁ m₂ ⬝ᵥ relativeMomentum m₁ m₂) := by
  have e1 : algebraMap ℝ Space ((m₁ + m₂)⁻¹ / 2) + algebraMap ℝ Space ((reducedMass m₁ m₂)⁻¹ / 2) *
      (algebraMap ℝ Space (m₂ / (m₁ + m₂)) * algebraMap ℝ Space (m₂ / (m₁ + m₂))) =
      algebraMap ℝ Space (m₁⁻¹ / 2) := by
    rw [← map_mul, ← map_mul, ← map_add]
    congr 1
    rw [reducedMass]
    field_simp
  have e2 : algebraMap ℝ Space ((m₁ + m₂)⁻¹ / 2) + algebraMap ℝ Space ((reducedMass m₁ m₂)⁻¹ / 2) *
      (algebraMap ℝ Space (m₁ / (m₁ + m₂)) * algebraMap ℝ Space (m₁ / (m₁ + m₂))) =
      algebraMap ℝ Space (m₂⁻¹ / 2) := by
    rw [← map_mul, ← map_mul, ← map_add]
    congr 1
    rw [reducedMass]
    field_simp
    ring
  have e3 : algebraMap ℝ Space ((m₁ + m₂)⁻¹ / 2) - algebraMap ℝ Space ((reducedMass m₁ m₂)⁻¹ / 2) *
      (algebraMap ℝ Space (m₁ / (m₁ + m₂)) * algebraMap ℝ Space (m₂ / (m₁ + m₂))) = 0 := by
    rw [← map_mul, ← map_mul, ← map_sub, ← map_zero (algebraMap ℝ Space)]
    congr 1
    rw [reducedMass]
    field_simp
    ring
  simp only [kineticEnergy, totalMomentum, relativeMomentum, dotProduct, Fin.sum_univ_three]
  linear_combination (-(p₁ 0 * p₁ 0 + p₁ 1 * p₁ 1 + p₁ 2 * p₁ 2)) * e1 +
    (-(p₂ 0 * p₂ 0 + p₂ 1 * p₂ 1 + p₂ 2 * p₂ 2)) * e2 +
    (-2 * (p₁ 0 * p₂ 0 + p₁ 1 * p₂ 1 + p₁ 2 * p₂ 2)) * e3

end ProjectAInos.Mechanics.TwoBody
