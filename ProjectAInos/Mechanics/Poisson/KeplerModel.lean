/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.Kepler
public import ProjectAInos.SmoothAlgebra.Poisson.Free
import Mathlib.Tactic.Ring

/-!
# A phase space for Kepler's problem

The Hamiltonian `|p|² / 2m − α / r` contains `1 / r`, which is not an element of
the free C-infinity ring on `q` and `p`. Following the remark after
Proposition 69 of the research plan, `ρ = 1 / r` is adjoined as a generator.
The phase space is the free C-infinity ring on `q`, `p` and `ρ`, with the
canonical brackets of `q` and `p` and

`{ρ, pⱼ} = −ρ³ qⱼ`, `{ρ, qⱼ} = 0`,

which is what `ρ = 1 / |q|` satisfies. This bracket is a Poisson structure: the
Jacobi identity is checked on generators. It is a model of the relations of
`Kepler.IsFrame`, so the identities proved there are not vacuous.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.KeplerModel

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

/-- The generators: `none` for `ρ`, `some (Sum.inl i)` for `qᵢ` and
`some (Sum.inr i)` for `pᵢ`. -/
abbrev Index := Option (Fin 3 ⊕ Fin 3)

/-- The phase space of Kepler's problem: smooth functions of `q`, `p` and `ρ`. -/
abbrev PhaseSpace := FreeSmoothRing Index

/-- The position. -/
def q (i : Fin 3) : PhaseSpace := generator (some (Sum.inl i))

/-- The momentum. -/
def p (i : Fin 3) : PhaseSpace := generator (some (Sum.inr i))

/-- The inverse distance `ρ = 1 / r`, as an independent generator. -/
def ρ : PhaseSpace := generator none

/-- The brackets of the generators. -/
def structureMatrix : Index → Index → PhaseSpace
  | some (Sum.inl i), some (Sum.inr j) => if i = j then 1 else 0
  | some (Sum.inr i), some (Sum.inl j) => if i = j then -1 else 0
  | none, some (Sum.inr j) => -(ρ * ρ * ρ * q j)
  | some (Sum.inr j), none => ρ * ρ * ρ * q j
  | some (Sum.inl _), some (Sum.inl _) => 0
  | some (Sum.inr _), some (Sum.inr _) => 0
  | none, some (Sum.inl _) => 0
  | some (Sum.inl _), none => 0
  | none, none => 0

theorem structureMatrix_skew (a b : Index) : structureMatrix a b = -structureMatrix b a := by
  rcases a with _ | i | i <;> rcases b with _ | j | j <;>
    simp only [structureMatrix, neg_zero, neg_neg]
  · split_ifs with h1 h2 h2
    · exact (neg_neg _).symm
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact neg_zero.symm
  · split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · exact neg_zero.symm

/-- The almost-Poisson structure of Kepler's problem, before the Jacobi identity. -/
def almostPoisson : AlmostPoissonStructure PhaseSpace :=
  FreeSmoothRing.almostPoisson structureMatrix structureMatrix_skew

theorem almostPoisson_generator (a b : Index) :
    almostPoisson.bracket (generator a) (generator b) = structureMatrix a b :=
  almostPoisson_bracket_generator structureMatrix structureMatrix_skew a b

theorem almostPoisson_q_q (i j : Fin 3) : almostPoisson.bracket (q i) (q j) = 0 :=
  almostPoisson_generator _ _

theorem almostPoisson_p_p (i j : Fin 3) : almostPoisson.bracket (p i) (p j) = 0 :=
  almostPoisson_generator _ _

theorem almostPoisson_q_p (i j : Fin 3) :
    almostPoisson.bracket (q i) (p j) = if i = j then 1 else 0 :=
  almostPoisson_generator _ _

theorem almostPoisson_ρ_ρ : almostPoisson.bracket ρ ρ = 0 := almostPoisson_generator _ _

theorem almostPoisson_ρ_q (j : Fin 3) : almostPoisson.bracket ρ (q j) = 0 :=
  almostPoisson_generator _ _

theorem almostPoisson_q_ρ (j : Fin 3) : almostPoisson.bracket (q j) ρ = 0 :=
  almostPoisson_generator _ _

theorem almostPoisson_ρ_p (j : Fin 3) :
    almostPoisson.bracket ρ (p j) = -(ρ * ρ * ρ * q j) :=
  almostPoisson_generator _ _

/-- The bracket `{ρ³ qⱼ, pₖ} = ρ³ δⱼₖ − 3 ρ⁵ qⱼ qₖ`. -/
theorem almostPoisson_ρ_cube_q_p (j k : Fin 3) :
    almostPoisson.bracket (ρ * ρ * ρ * q j) (p k) =
      ρ * ρ * ρ * (if j = k then 1 else 0) - 3 * (ρ * ρ * ρ * ρ * ρ) * q j * q k := by
  simp only [AlmostPoissonStructure.bracket_mul_left, almostPoisson_ρ_p, almostPoisson_q_p]
  ring

/-- The Jacobi identity on the generators `ρ, pⱼ, pₖ`. -/
theorem jacobi_ρ_p_p (j k : Fin 3) :
    almostPoisson.bracket (structureMatrix none (some (Sum.inr j)))
        (generator (some (Sum.inr k))) +
      almostPoisson.bracket (structureMatrix (some (Sum.inr j)) (some (Sum.inr k)))
        (generator none) +
      almostPoisson.bracket (structureMatrix (some (Sum.inr k)) none)
        (generator (some (Sum.inr j))) = 0 := by
  change almostPoisson.bracket (-(ρ * ρ * ρ * q j)) (p k) + almostPoisson.bracket 0 ρ +
    almostPoisson.bracket (ρ * ρ * ρ * q k) (p j) = 0
  rw [AlmostPoissonStructure.bracket_neg_left, almostPoisson_ρ_cube_q_p,
    almostPoisson_ρ_cube_q_p, AlmostPoissonStructure.bracket_zero_left]
  rw [show (if k = j then (1 : PhaseSpace) else 0) = if j = k then 1 else 0 by
    simp only [eq_comm]]
  ring

theorem almostPoisson_ite_one (c : Prop) [Decidable c] (z : PhaseSpace) :
    almostPoisson.bracket (if c then 1 else 0) z = 0 := by
  split_ifs
  · exact almostPoisson.bracket_one_left z
  · exact almostPoisson.bracket_zero_left z

theorem almostPoisson_ite_neg_one (c : Prop) [Decidable c] (z : PhaseSpace) :
    almostPoisson.bracket (if c then -1 else 0) z = 0 := by
  split_ifs
  · rw [AlmostPoissonStructure.bracket_neg_left, almostPoisson.bracket_one_left, neg_zero]
  · exact almostPoisson.bracket_zero_left z

theorem almostPoisson_ρ_cube_q_generator_none (j : Fin 3) :
    almostPoisson.bracket (ρ * ρ * ρ * q j) (generator none) = 0 := by
  change almostPoisson.bracket (ρ * ρ * ρ * q j) ρ = 0
  simp only [AlmostPoissonStructure.bracket_mul_left, almostPoisson_ρ_ρ, almostPoisson_q_ρ,
    mul_zero, add_zero]

theorem almostPoisson_ρ_cube_q_generator_inl (j k : Fin 3) :
    almostPoisson.bracket (ρ * ρ * ρ * q j) (generator (some (Sum.inl k))) = 0 := by
  change almostPoisson.bracket (ρ * ρ * ρ * q j) (q k) = 0
  simp only [AlmostPoissonStructure.bracket_mul_left, almostPoisson_ρ_q, almostPoisson_q_q,
    mul_zero, add_zero]

/-- The Jacobi identity on generators. The only nontrivial case is `ρ, pⱼ, pₖ`
and its rotations. -/
theorem jacobi_generators (a b c : Index) :
    almostPoisson.bracket (structureMatrix a b) (generator c) +
      almostPoisson.bracket (structureMatrix b c) (generator a) +
      almostPoisson.bracket (structureMatrix c a) (generator b) = 0 := by
  rcases a with _ | a | a <;> rcases b with _ | b | b <;> rcases c with _ | c | c
  all_goals try
    (simp only [structureMatrix, almostPoisson_ite_one, almostPoisson_ite_neg_one,
      AlmostPoissonStructure.bracket_zero_left, AlmostPoissonStructure.bracket_neg_left,
      almostPoisson_ρ_cube_q_generator_none, almostPoisson_ρ_cube_q_generator_inl, neg_zero,
      add_zero]
     done)
  · exact jacobi_ρ_p_p b c
  · rw [add_assoc, add_comm]
    exact jacobi_ρ_p_p c a
  · rw [add_comm, ← add_assoc]
    exact jacobi_ρ_p_p a b

/-- The Poisson structure of Kepler's problem. -/
def poisson : PoissonStructure PhaseSpace :=
  poissonOfCoordinates structureMatrix structureMatrix_skew jacobi_generators

/-- The generators of the model form a Kepler frame. -/
theorem isFrame : Kepler.IsFrame poisson q p ρ where
  q_q := almostPoisson_q_q
  p_p := almostPoisson_p_p
  q_p := almostPoisson_q_p
  ρ_q := almostPoisson_ρ_q
  ρ_p := almostPoisson_ρ_p

/-- The constraint ideal `(ρ² |q|² − 1)`: the functions that vanish where `ρ` is
the inverse distance. -/
def constraintIdeal : Ideal PhaseSpace := Ideal.span {Kepler.constraint q ρ}

theorem bracket_constraint_mem (g : PhaseSpace) :
    poisson.bracket (Kepler.constraint q ρ) g ∈ constraintIdeal := by
  have hsum : poisson.bracket g (Kepler.constraint q ρ) =
      ∑ a, partialDerivation a g * poisson.bracket (generator a) (Kepler.constraint q ρ) :=
    almostPoisson_bracket_eq_sum_left structureMatrix structureMatrix_skew g _
  rw [poisson.antisymm, hsum]
  refine neg_mem (sum_mem fun a _ => Ideal.mul_mem_left _ _ ?_)
  rcases a with _ | a | a
  · have h0 : poisson.bracket (generator none) (Kepler.constraint q ρ) = 0 :=
      isFrame.ρ_constraint
    rw [h0]
    exact zero_mem _
  · have h0 : poisson.bracket (generator (some (Sum.inl a))) (Kepler.constraint q ρ) = 0 :=
      isFrame.q_constraint a
    rw [h0]
    exact zero_mem _
  · have h0 : poisson.bracket (generator (some (Sum.inr a))) (Kepler.constraint q ρ) =
        2 * (ρ * ρ) * q a * Kepler.constraint q ρ := isFrame.p_constraint a
    rw [h0]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)

/-- The constraint generates a Poisson ideal: identities modulo the constraint
are compatible with the bracket. -/
theorem isPoissonIdeal_constraintIdeal : poisson.IsPoissonIdeal constraintIdeal :=
  PoissonStructure.isPoissonIdeal_span_singleton bracket_constraint_mem

end ProjectAInos.Mechanics.KeplerModel
