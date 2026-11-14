/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.FreeChainRule
public import ProjectAInos.Mechanics.Jet.Prolongation
public import ProjectAInos.Mechanics.Poisson.Trajectory
public import ProjectAInos.Mechanics.Poisson.Virial
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The Legendre transformation of a natural Lagrangian

For the Lagrangian `L = Σᵢ ½ mᵢ q̇ᵢ² − U(q)` with non-zero masses and a smooth
potential `U`, the Legendre transformation is `pᵢ = mᵢ q̇ᵢ` and the Hamiltonian
is `H = Σᵢ pᵢ²/2mᵢ + U(q)` (Landau–Lifshitz §40).

A potential is an element `u` of the free C-infinity ring on the positions. It
is read in the jet ring by `positionsToJet` and on the phase space by
`positionsToPhase`. The Legendre transformation is the morphism `legendre m`
from the phase space to the jet ring with `qᵢ ↦ qᵢ` and `pᵢ ↦ mᵢ q̇ᵢ`. It takes
`H` to the energy of `L`, and the trajectories of `H` are the solutions of the
Euler–Lagrange equations of `L` together with the momenta `pᵢ = mᵢ q̇ᵢ`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace

variable {ι : Type*} [DecidableEq ι]

/-- A function of the positions, as an element of the jet ring. -/
def positionsToJet : SmoothRingHom (FreeSmoothRing ι) (StandardJet ι) :=
  FreeSmoothRing.lift fun i => (StandardJet.jetRing ι).q i 0

/-- A function of the positions, as an element of the phase space. -/
def positionsToPhase : SmoothRingHom (FreeSmoothRing ι) (PhaseSpace ι) :=
  FreeSmoothRing.lift fun i => PhaseSpace.q i

/-- A function of the positions along a path. -/
theorem prolongation_positionsToJet (γ : ι → TimeFunction) (u : FreeSmoothRing ι) :
    StandardJet.prolongation γ (positionsToJet u) = FreeSmoothRing.lift γ u := by
  have h : (StandardJet.prolongation γ).comp positionsToJet = FreeSmoothRing.lift γ :=
    FreeSmoothRing.hom_ext fun i => by
      rw [SmoothRingHom.comp_apply, positionsToJet, lift_generator, lift_generator,
        StandardJet.prolongation_q]
      rfl
  exact congrArg (fun φ : SmoothRingHom (FreeSmoothRing ι) TimeFunction => φ u) h

omit [DecidableEq ι] in
/-- A function of the positions along a curve of the phase space. -/
theorem lift_positionsToPhase (c : ι ⊕ ι → TimeFunction) (u : FreeSmoothRing ι) :
    FreeSmoothRing.lift c (positionsToPhase u) =
      FreeSmoothRing.lift (fun i => c (Sum.inl i)) u := by
  have h : (FreeSmoothRing.lift c).comp positionsToPhase =
      FreeSmoothRing.lift fun i => c (Sum.inl i) :=
    FreeSmoothRing.hom_ext fun i => by
      rw [SmoothRingHom.comp_apply, positionsToPhase, lift_generator, lift_generator,
        PhaseSpace.q, lift_generator]
  exact congrArg (fun φ : SmoothRingHom (FreeSmoothRing ι) TimeFunction => φ u) h

variable [Fintype ι]

/-- The derivative of a function of the positions with respect to a
position. -/
theorem d_zero_positionsToJet (u : FreeSmoothRing ι) (j : ι) :
    (StandardJet.jetRing ι).d j 0 (positionsToJet u) =
      positionsToJet (partialDerivation j u) := by
  rw [positionsToJet, derivation_lift_mul, Finset.sum_eq_single j]
  · rw [(StandardJet.jetRing ι).d_q_self, mul_one]
  · intro a _ haj
    rw [(StandardJet.jetRing ι).d_q_ne a 0 j 0 (fun h => haj (Prod.mk.inj h).1), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- A function of the positions does not depend on the velocities or on the
higher derivatives. -/
theorem d_positionsToJet_of_ne_zero (u : FreeSmoothRing ι) (j : ι) {k : ℕ} (hk : k ≠ 0) :
    (StandardJet.jetRing ι).d j k (positionsToJet u) = 0 := by
  rw [positionsToJet, derivation_lift_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [(StandardJet.jetRing ι).d_q_ne a 0 j k (fun h => hk (Prod.mk.inj h).2.symm), mul_zero]

/-- A function of the positions has order zero. -/
theorem orderLE_positionsToJet (u : FreeSmoothRing ι) :
    (StandardJet.jetRing ι).OrderLE (positionsToJet u) 0 := fun j _ hk =>
  d_positionsToJet_of_ne_zero u j (by omega)

theorem partialDerivation_inl_positionsToPhase (u : FreeSmoothRing ι) (j : ι) :
    partialDerivation (Sum.inl j) (positionsToPhase u) =
      positionsToPhase (partialDerivation j u) := by
  rw [positionsToPhase, derivation_lift_mul, Finset.sum_eq_single j]
  · rw [PhaseSpace.q, partialDerivation_generator_self, mul_one]
  · intro a _ haj
    rw [PhaseSpace.q, partialDerivation_generator_of_ne (c := Sum.inl j) (i := Sum.inl a)
      (fun h => haj (Sum.inl.inj h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem partialDerivation_inr_positionsToPhase (u : FreeSmoothRing ι) (j : ι) :
    partialDerivation (Sum.inr j) (positionsToPhase u) = 0 := by
  rw [positionsToPhase, derivation_lift_mul]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [PhaseSpace.q, partialDerivation_generator_of_ne (c := Sum.inr j) (i := Sum.inl a)
    (by simp), mul_zero]

/-- The Legendre transformation of the natural Lagrangian with the masses
`m`, as a morphism from the phase space to the jet ring: `qᵢ ↦ qᵢ` and
`pᵢ ↦ mᵢ q̇ᵢ`. -/
def legendre (m : ι → ℝ) : SmoothRingHom (PhaseSpace ι) (StandardJet ι) :=
  FreeSmoothRing.lift (Sum.elim (fun i => (StandardJet.jetRing ι).q i 0)
    fun i => algebraMap ℝ (StandardJet ι) (m i) * (StandardJet.jetRing ι).q i 1)

omit [Fintype ι] in
theorem legendre_q (m : ι → ℝ) (i : ι) :
    legendre m (PhaseSpace.q i) = (StandardJet.jetRing ι).q i 0 := by
  rw [legendre, PhaseSpace.q, lift_generator, Sum.elim_inl]

omit [Fintype ι] in
theorem legendre_p (m : ι → ℝ) (i : ι) :
    legendre m (PhaseSpace.p i) =
      algebraMap ℝ (StandardJet ι) (m i) * (StandardJet.jetRing ι).q i 1 := by
  rw [legendre, PhaseSpace.p, lift_generator, Sum.elim_inr]

/-- The Legendre transformation takes the momentum to the momentum
`∂L/∂q̇ᵢ` of the Lagrangian. -/
theorem legendre_p_eq_momentum (m : ι → ℝ) (u : FreeSmoothRing ι) (i : ι) :
    legendre m (PhaseSpace.p i) =
      (StandardJet.jetRing ι).momentum
        ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u)) i := by
  rw [legendre_p, JetRing.momentum_naturalLagrangian m (orderLE_positionsToJet u)]

omit [Fintype ι] in
theorem legendre_positionsToPhase (m : ι → ℝ) (u : FreeSmoothRing ι) :
    legendre m (positionsToPhase u) = positionsToJet u := by
  have h : (legendre m).comp positionsToPhase = positionsToJet :=
    FreeSmoothRing.hom_ext fun i => by
      rw [SmoothRingHom.comp_apply, positionsToPhase, lift_generator, legendre_q, positionsToJet,
        lift_generator]
  exact congrArg (fun φ : SmoothRingHom (FreeSmoothRing ι) (StandardJet ι) => φ u) h

/-- The Legendre transformation takes the Hamiltonian
`Σᵢ pᵢ²/2mᵢ + U` to the energy of the Lagrangian `Σᵢ ½ mᵢ q̇ᵢ² − U`. -/
theorem legendre_hamiltonian {m : ι → ℝ} (hm : ∀ i, m i ≠ 0) (u : FreeSmoothRing ι) :
    legendre m (kineticEnergy m + positionsToPhase u) =
      (StandardJet.jetRing ι).energy
        ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u)) := by
  rw [JetRing.energy_naturalLagrangian m (orderLE_positionsToJet u), SmoothRingHom.map_add,
    legendre_positionsToPhase, kineticEnergy, SmoothRingHom.map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : algebraMap ℝ (StandardJet ι) ((m i)⁻¹ / 2) *
      (algebraMap ℝ (StandardJet ι) (m i) * algebraMap ℝ (StandardJet ι) (m i)) =
      algebraMap ℝ (StandardJet ι) (m i / 2) := by
    rw [← map_mul, ← map_mul]
    congr 1
    field_simp [hm i]
  rw [SmoothRingHom.map_mul, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, legendre_p]
  linear_combination ((StandardJet.jetRing ι).q i 1 * (StandardJet.jetRing ι).q i 1) * hc

/-- Hamilton's equations for `H = Σᵢ pᵢ²/2mᵢ + U(q)` along a curve. -/
theorem isTrajectory_natural_iff (m : ι → ℝ) (u : FreeSmoothRing ι)
    (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (kineticEnergy m + positionsToPhase u) c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) =
        algebraMap ℝ TimeFunction (m i)⁻¹ * c (Sum.inr i)) ∧
      ∀ i, timeDerivative (c (Sum.inr i)) =
        -FreeSmoothRing.lift (fun k => c (Sum.inl k)) (partialDerivation i u) := by
  rw [isTrajectory_canonical_iff]
  simp only [map_add, partialDerivation_inr_kineticEnergy,
    partialDerivation_inr_positionsToPhase, partialDerivation_inl_kineticEnergy,
    partialDerivation_inl_positionsToPhase, add_zero, zero_add, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, PhaseSpace.p, lift_generator, lift_positionsToPhase]

/-- Newton's equations for `L = Σᵢ ½ mᵢ q̇ᵢ² − U(q)` along a path. -/
theorem isSolution_natural_iff (m : ι → ℝ) (u : FreeSmoothRing ι) (γ : ι → TimeFunction) :
    StandardJet.IsSolution
        ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u)) γ ↔
      ∀ i, algebraMap ℝ TimeFunction (m i) * timeDerivative (timeDerivative (γ i)) =
        -FreeSmoothRing.lift γ (partialDerivation i u) := by
  rw [StandardJet.isSolution_naturalLagrangian_iff m (orderLE_positionsToJet u)]
  refine forall_congr' fun i => ?_
  rw [d_zero_positionsToJet, prolongation_positionsToJet, Function.iterate_succ_apply',
    Function.iterate_one]

/-- The Legendre correspondence (Landau–Lifshitz §40): the trajectories of
`H = Σᵢ pᵢ²/2mᵢ + U(q)` are the solutions of the Euler–Lagrange equations of
`L = Σᵢ ½ mᵢ q̇ᵢ² − U(q)` together with the momenta `pᵢ = mᵢ q̇ᵢ`. -/
theorem isTrajectory_natural_iff_isSolution {m : ι → ℝ} (hm : ∀ i, m i ≠ 0)
    (u : FreeSmoothRing ι) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (kineticEnergy m + positionsToPhase u) c ↔
      StandardJet.IsSolution
          ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u))
          (fun i => c (Sum.inl i)) ∧
        ∀ i, c (Sum.inr i) =
          algebraMap ℝ TimeFunction (m i) * timeDerivative (c (Sum.inl i)) := by
  rw [isTrajectory_natural_iff, isSolution_natural_iff, ← forall_and, ← forall_and]
  refine forall_congr' fun i => ?_
  have hinv : algebraMap ℝ TimeFunction (m i)⁻¹ * algebraMap ℝ TimeFunction (m i) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (hm i), map_one]
  constructor
  · rintro ⟨hq, hp⟩
    have hpq : c (Sum.inr i) =
        algebraMap ℝ TimeFunction (m i) * timeDerivative (c (Sum.inl i)) := by
      rw [hq]
      linear_combination (-c (Sum.inr i)) * hinv
    refine ⟨?_, hpq⟩
    rw [← hp, hpq, SmoothDerivation.map_algebraMap_mul, smul_eq_mul]
  · rintro ⟨hs, hp⟩
    refine ⟨?_, ?_⟩
    · rw [hp]
      linear_combination (-timeDerivative (c (Sum.inl i))) * hinv
    · rw [hp, SmoothDerivation.map_algebraMap_mul, smul_eq_mul]
      exact hs

end ProjectAInos.Mechanics
