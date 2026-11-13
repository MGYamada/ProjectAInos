/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.Epsilon
public import ProjectAInos.Mechanics.Poisson.RigidBody
public import ProjectAInos.SmoothAlgebra.Poisson.Canonical
public import ProjectAInos.SmoothAlgebra.Poisson.Hom
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Angular momentum of a particle in space

On the canonical phase space of one particle in space, the angular momentum is
`M = q × p`. Its brackets are `{Mₐ, q_b} = εₐ_bc q_c`, `{Mₐ, p_b} = εₐ_bc p_c`
and `{Mₐ, M_b} = εₐ_bc M_c` (Landau–Lifshitz §§9, 42). The scalars `|q|²`, `|p|²`
and `q · p` are invariant, so every smooth function of them has `M` as an
integral of the motion: this is conservation of angular momentum in a central
field, in Hamiltonian form.

The generator relations say that `L ↦ −M` is a Poisson morphism from the phase
space of the rigid body, the free C-infinity ring on `so(3)`, to the canonical
phase space. This morphism is the momentum map of the rotations.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.AngularMomentum

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

/-- The canonical phase space of one particle in space. -/
abbrev Space := SmoothAlgebra.PhaseSpace (Fin 3)

/-- The position vector. -/
def q : Fin 3 → Space := PhaseSpace.q

/-- The momentum vector. -/
def p : Fin 3 → Space := PhaseSpace.p

/-- The canonical Poisson structure. -/
abbrev canonical : PoissonStructure Space := PhaseSpace.canonical (Fin 3)

/-- The angular momentum `M = q × p`. -/
def M : Fin 3 → Space := q ⨯₃ p

theorem canonical_q_q (a b : Fin 3) : canonical.bracket (q a) (q b) = 0 :=
  PhaseSpace.canonical_q_q a b

theorem canonical_p_p (a b : Fin 3) : canonical.bracket (p a) (p b) = 0 :=
  PhaseSpace.canonical_p_p a b

theorem canonical_q_p (a b : Fin 3) : canonical.bracket (q a) (p b) = if a = b then 1 else 0 :=
  PhaseSpace.canonical_q_p a b

theorem canonical_p_q (a b : Fin 3) : canonical.bracket (p a) (q b) = if a = b then -1 else 0 :=
  PhaseSpace.canonical_p_q a b

/-- `{Mₐ, q_b} = εₐ_bc q_c`. -/
theorem canonical_M_q (a b : Fin 3) : canonical.bracket (M a) (q b) = epsilon q a b := by
  fin_cases a <;> fin_cases b <;>
    simp [M, epsilon, cross_apply, AlmostPoissonStructure.bracket_sub_left,
      AlmostPoissonStructure.bracket_mul_left, canonical_q_q, canonical_p_q] <;>
    ring

/-- `{Mₐ, p_b} = εₐ_bc p_c`. -/
theorem canonical_M_p (a b : Fin 3) : canonical.bracket (M a) (p b) = epsilon p a b := by
  fin_cases a <;> fin_cases b <;>
    simp [M, epsilon, cross_apply, AlmostPoissonStructure.bracket_sub_left,
      AlmostPoissonStructure.bracket_mul_left, canonical_p_p, canonical_q_p]

/-- `{Mₐ, M_b} = εₐ_bc M_c`: the components of the angular momentum span `so(3)`. -/
theorem canonical_M_M (a b : Fin 3) : canonical.bracket (M a) (M b) = epsilon M a b := by
  fin_cases a <;> fin_cases b <;>
    simp [M, epsilon, cross_apply, AlmostPoissonStructure.bracket_sub_left,
      AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_sub_right,
      AlmostPoissonStructure.bracket_mul_right, canonical_q_q, canonical_p_p, canonical_q_p,
      canonical_p_q] <;>
    ring

/-- `{M₀, M₁} = M₂`. -/
theorem canonical_M_zero_M_one : canonical.bracket (M 0) (M 1) = M 2 := canonical_M_M 0 1

/-- `{M₁, M₂} = M₀`. -/
theorem canonical_M_one_M_two : canonical.bracket (M 1) (M 2) = M 0 := canonical_M_M 1 2

/-- `{M₂, M₀} = M₁`. -/
theorem canonical_M_two_M_zero : canonical.bracket (M 2) (M 0) = M 1 := canonical_M_M 2 0

/-- The bracket of the angular momentum with a scalar product of two vectors
that transform as vectors vanishes. -/
theorem canonical_M_dotProduct {x y : Fin 3 → Space}
    (hx : ∀ a b, canonical.bracket (M a) (x b) = epsilon x a b)
    (hy : ∀ a b, canonical.bracket (M a) (y b) = epsilon y a b) (a : Fin 3) :
    canonical.bracket (M a) (x ⬝ᵥ y) = 0 := by
  simp only [dotProduct, Fin.sum_univ_three, AlmostPoissonStructure.bracket_add_right,
    AlmostPoissonStructure.bracket_mul_right, hx, hy]
  fin_cases a <;> simp [epsilon] <;> ring

/-- `|q|²` is invariant under rotations. -/
theorem canonical_M_q_sq (a : Fin 3) : canonical.bracket (M a) (q ⬝ᵥ q) = 0 :=
  canonical_M_dotProduct canonical_M_q canonical_M_q a

/-- `|p|²` is invariant under rotations. -/
theorem canonical_M_p_sq (a : Fin 3) : canonical.bracket (M a) (p ⬝ᵥ p) = 0 :=
  canonical_M_dotProduct canonical_M_p canonical_M_p a

/-- `q · p` is invariant under rotations. -/
theorem canonical_M_q_p (a : Fin 3) : canonical.bracket (M a) (q ⬝ᵥ p) = 0 :=
  canonical_M_dotProduct canonical_M_q canonical_M_p a

/-- `|M|²` Poisson-commutes with every component of the angular momentum. -/
theorem canonical_M_M_sq (a : Fin 3) : canonical.bracket (M a) (M ⬝ᵥ M) = 0 :=
  canonical_M_dotProduct canonical_M_M canonical_M_M a

/-- The rotation scalars `|q|²`, `|p|²` and `q · p`. -/
def scalars : Fin 3 → Space := ![q ⬝ᵥ q, p ⬝ᵥ p, q ⬝ᵥ p]

theorem canonical_M_scalars (a : Fin 3) (i : Fin 3) :
    canonical.bracket (M a) (scalars i) = 0 := by
  fin_cases i
  · exact canonical_M_q_sq a
  · exact canonical_M_p_sq a
  · exact canonical_M_q_p a

/-- Conservation of angular momentum (Landau–Lifshitz §§9, 14): for every
Hamiltonian that is a smooth function of `|q|²`, `|p|²` and `q · p`, each
component of the angular momentum is an integral of the motion. -/
theorem isIntegral_M (f : SmoothOperation 3) (a : Fin 3) :
    canonical.IsIntegral (op f scalars) (M a) := by
  unfold PoissonStructure.IsIntegral
  rw [canonical.toAlmostPoissonStructure.chain_right]
  exact Finset.sum_eq_zero fun i _ => by rw [canonical_M_scalars, mul_zero]

/-- `|M|²` is an integral of the motion of every central Hamiltonian. -/
theorem isIntegral_M_sq (f : SmoothOperation 3) :
    canonical.IsIntegral (op f scalars) (M ⬝ᵥ M) := by
  unfold PoissonStructure.IsIntegral
  simp only [dotProduct, Fin.sum_univ_three, AlmostPoissonStructure.bracket_add_left,
    AlmostPoissonStructure.bracket_mul_left]
  have h (a : Fin 3) : canonical.bracket (M a) (op f scalars) = 0 := isIntegral_M f a
  simp only [h, mul_zero, add_zero]

/-- The momentum map of the rotations: the morphism from the phase space of the
rigid body that sends `Lₐ` to `−Mₐ`. -/
def momentumMap : SmoothRingHom RigidBody.PhaseSpace Space :=
  FreeSmoothRing.lift fun a => -M a

@[simp] theorem momentumMap_L (a : Fin 3) : momentumMap (RigidBody.L a) = -M a :=
  lift_generator _ a

/-- The momentum map is a Poisson morphism. -/
theorem isPoissonHom_momentumMap :
    IsPoissonHom RigidBody.poisson.toAlmostPoissonStructure canonical.toAlmostPoissonStructure
      momentumMap :=
  FreeSmoothRing.isPoissonHom_of_generators fun a b => by
    change momentumMap (RigidBody.poisson.bracket (RigidBody.L a) (RigidBody.L b)) =
      canonical.bracket (momentumMap (RigidBody.L a)) (momentumMap (RigidBody.L b))
    rw [RigidBody.poisson_L_L, momentumMap_L, momentumMap_L,
      AlmostPoissonStructure.bracket_neg_left, AlmostPoissonStructure.bracket_neg_right,
      neg_neg, canonical_M_M]
    fin_cases a <;> fin_cases b <;>
      simp [RigidBody.structureMatrix, epsilon, SmoothRingHom.map_neg]

end ProjectAInos.Mechanics.AngularMomentum
