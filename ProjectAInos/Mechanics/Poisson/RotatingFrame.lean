/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.Galilei
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Motion in a rotating frame

In a frame rotating with constant angular velocity `Ω`, a particle of mass `m`
in a potential `U` has the Hamiltonian `H = |p|² / 2m + U − Ω · M` with
`M = q × p` (Landau–Lifshitz §39). Its equations of motion are

`{q, H} = p / m − Ω × q` and `{p, H} = −∇U − Ω × p`.

With the velocity `v = p / m − Ω × q`, the acceleration is

`{v, H} = −∇U / m − 2 Ω × v − Ω × (Ω × q)`:

the Coriolis term `−2 Ω × v` and the centrifugal term `−Ω × (Ω × q)`. No
hypothesis on the mass is needed for these identities.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.RotatingFrame

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix AngularMomentum

/-- The constant angular velocity as a vector of constants of the phase space. -/
def angularVelocity (Ω : Fin 3 → ℝ) : Fin 3 → Space := fun a => algebraMap ℝ Space (Ω a)

/-- For a vector `x` that transforms as a vector under rotations,
`{xₐ, Ω · M} = (Ω × x)ₐ`. -/
theorem canonical_bracket_dot_M {x : Fin 3 → Space}
    (hx : ∀ a b, canonical.bracket (M a) (x b) = epsilon x a b) (Ω : Fin 3 → ℝ) (a : Fin 3) :
    canonical.bracket (x a) (angularVelocity Ω ⬝ᵥ M) = (angularVelocity Ω ⨯₃ x) a := by
  have hxM (c b : Fin 3) : canonical.bracket (x c) (M b) = -epsilon x b c := by
    rw [canonical.antisymm, hx]
  simp only [dotProduct, Fin.sum_univ_three, angularVelocity,
    AlmostPoissonStructure.bracket_add_right, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_algebraMap_right, mul_zero, add_zero, hxM]
  fin_cases a <;> simp [epsilon, cross_apply, angularVelocity] <;> ring

/-- `{qₐ, Ω · M} = (Ω × q)ₐ`. -/
theorem canonical_q_dot_M (Ω : Fin 3 → ℝ) (a : Fin 3) :
    canonical.bracket (q a) (angularVelocity Ω ⬝ᵥ M) = (angularVelocity Ω ⨯₃ q) a :=
  canonical_bracket_dot_M canonical_M_q Ω a

/-- `{pₐ, Ω · M} = (Ω × p)ₐ`. -/
theorem canonical_p_dot_M (Ω : Fin 3 → ℝ) (a : Fin 3) :
    canonical.bracket (p a) (angularVelocity Ω ⬝ᵥ M) = (angularVelocity Ω ⨯₃ p) a :=
  canonical_bracket_dot_M canonical_M_p Ω a

/-- The Hamiltonian `|p|² / 2m + U − Ω · M` in the rotating frame. -/
def hamiltonian (m : ℝ) (U : Space) (Ω : Fin 3 → ℝ) : Space :=
  Galilei.freeHamiltonian m + U - angularVelocity Ω ⬝ᵥ M

/-- The velocity `v = p / m − Ω × q` in the rotating frame. -/
def velocity (m : ℝ) (Ω : Fin 3 → ℝ) : Fin 3 → Space :=
  fun a => algebraMap ℝ Space m⁻¹ * p a - (angularVelocity Ω ⨯₃ q) a

/-- `{q, H} = p / m − Ω × q` for a potential that does not depend on the momenta. -/
theorem canonical_q_hamiltonian (m : ℝ) {U : Space}
    (hU : ∀ a, partialDerivation (Sum.inr a) U = 0) (Ω : Fin 3 → ℝ) (a : Fin 3) :
    canonical.bracket (q a) (hamiltonian m U Ω) = velocity m Ω a := by
  have hqU : canonical.bracket (q a) U = 0 := by
    have h : canonical.bracket (q a) U = partialDerivation (Sum.inr a) U :=
      PhaseSpace.canonical_q_bracket a U
    rw [h, hU]
  rw [hamiltonian, AlmostPoissonStructure.bracket_sub_right,
    AlmostPoissonStructure.bracket_add_right, Galilei.canonical_q_freeHamiltonian, hqU,
    canonical_q_dot_M, add_zero, velocity]

/-- `{p, H} = −∇U − Ω × p`. -/
theorem canonical_p_hamiltonian (m : ℝ) (U : Space) (Ω : Fin 3 → ℝ) (a : Fin 3) :
    canonical.bracket (p a) (hamiltonian m U Ω) =
      -partialDerivation (Sum.inl a) U - (angularVelocity Ω ⨯₃ p) a := by
  have hpU : canonical.bracket (p a) U = -partialDerivation (Sum.inl a) U :=
    PhaseSpace.canonical_p_bracket a U
  rw [hamiltonian, AlmostPoissonStructure.bracket_sub_right,
    AlmostPoissonStructure.bracket_add_right, Galilei.canonical_p_freeHamiltonian, hpU,
    canonical_p_dot_M, zero_add]

/-- The equation of motion in the rotating frame (Landau–Lifshitz §39):
`{v, H} = −∇U / m − 2 Ω × v − Ω × (Ω × q)`. The second term is the Coriolis
acceleration and the third the centrifugal acceleration. -/
theorem canonical_velocity_hamiltonian (m : ℝ) {U : Space}
    (hU : ∀ a, partialDerivation (Sum.inr a) U = 0) (Ω : Fin 3 → ℝ) (a : Fin 3) :
    canonical.bracket (velocity m Ω a) (hamiltonian m U Ω) =
      -(algebraMap ℝ Space m⁻¹ * partialDerivation (Sum.inl a) U) -
        2 * (angularVelocity Ω ⨯₃ velocity m Ω) a -
        (angularVelocity Ω ⨯₃ (angularVelocity Ω ⨯₃ q)) a := by
  have hq (c : Fin 3) : canonical.bracket (q c) (hamiltonian m U Ω) = velocity m Ω c :=
    canonical_q_hamiltonian m hU Ω c
  have hp (c : Fin 3) : canonical.bracket (p c) (hamiltonian m U Ω) =
      -partialDerivation (Sum.inl c) U - (angularVelocity Ω ⨯₃ p) c :=
    canonical_p_hamiltonian m U Ω c
  have hv : canonical.bracket (velocity m Ω a) (hamiltonian m U Ω) =
      canonical.bracket (algebraMap ℝ Space m⁻¹ * p a - (angularVelocity Ω ⨯₃ q) a)
        (hamiltonian m U Ω) := rfl
  rw [hv]
  fin_cases a <;>
    simp only [cross_apply, angularVelocity, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one,
      Fin.reduceFinMk, AlmostPoissonStructure.bracket_sub_left,
      AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_algebraMap_left,
      hq, hp, mul_zero, add_zero] <;>
    simp only [velocity, cross_apply, angularVelocity, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    ring

/-- The energy in the rotating frame, for a nonzero mass:
`H = m |v|² / 2 − m |Ω × q|² / 2 + U`. The second term is the centrifugal
potential energy; the Coriolis force does not contribute. -/
theorem hamiltonian_eq_velocity {m : ℝ} (hm : m ≠ 0) (U : Space) (Ω : Fin 3 → ℝ) :
    hamiltonian m U Ω =
      algebraMap ℝ Space (m / 2) * (velocity m Ω ⬝ᵥ velocity m Ω) -
        algebraMap ℝ Space (m / 2) *
          ((angularVelocity Ω ⨯₃ q) ⬝ᵥ (angularVelocity Ω ⨯₃ q)) + U := by
  have c1 : algebraMap ℝ Space (m / 2) * (algebraMap ℝ Space m⁻¹ * algebraMap ℝ Space m⁻¹) =
      algebraMap ℝ Space (m⁻¹ / 2) := by
    rw [← map_mul, ← map_mul]
    congr 1
    field_simp
  have c2 : algebraMap ℝ Space (m / 2) * (2 * algebraMap ℝ Space m⁻¹) = 1 := by
    have h2 : (2 : Space) = algebraMap ℝ Space 2 := (map_ofNat _ 2).symm
    rw [h2, ← map_mul, ← map_mul, ← map_one (algebraMap ℝ Space)]
    congr 1
    field_simp
  simp only [hamiltonian, Galilei.freeHamiltonian, velocity, M, dotProduct, Fin.sum_univ_three,
    cross_apply, angularVelocity, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  linear_combination (-(p 0 * p 0 + p 1 * p 1 + p 2 * p 2)) * c1 +
    (p 0 * (algebraMap ℝ Space (Ω 1) * q 2 - algebraMap ℝ Space (Ω 2) * q 1) +
      p 1 * (algebraMap ℝ Space (Ω 2) * q 0 - algebraMap ℝ Space (Ω 0) * q 2) +
      p 2 * (algebraMap ℝ Space (Ω 0) * q 1 - algebraMap ℝ Space (Ω 1) * q 0)) * c2

end ProjectAInos.Mechanics.RotatingFrame
