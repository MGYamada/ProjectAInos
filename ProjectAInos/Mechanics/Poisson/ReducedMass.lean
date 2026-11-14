/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.CyclicReduction
public import ProjectAInos.Mechanics.Poisson.TwoBody
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The reduced mass as a reduction

The relative position `r`, the centre of mass `R` and their momenta `p`, `P`
are canonical co-ordinates on the phase space of two particles: the change of
variables is an isomorphism of Poisson C-infinity rings
(`TwoBody.centreCoordinates`, `TwoBody.particleCoordinates`).

In these co-ordinates the total momentum is the momentum of the centre of
mass, and the centre of mass is a cyclic co-ordinate of a Hamiltonian whose
interaction depends on the relative position. So the reduction by
translations at total momentum zero is the reduction with respect to cyclic
co-ordinates: the reduced ring `N(I)/I` of the ideal `I = (P₁, P₂, P₃)` is the
phase space of one particle, and the class of the Hamiltonian is
`|p|² / 2μ + U(r)` with the reduced mass `μ` (Landau–Lifshitz §13). Along a
trajectory with total momentum zero, the relative position and the relative
momentum form a trajectory of this Hamiltonian.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.TwoBody

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix CyclicReduction

/-- The phase space of the relative position, the centre of mass and their
momenta: the co-ordinates `Sum.inl i` are relative, `Sum.inr i` of the centre. -/
abbrev CentreSpace := SmoothAlgebra.PhaseSpace (Fin 3 ⊕ Fin 3)

variable {m₁ m₂ : ℝ}

/-- `{rᵢ, rⱼ} = 0`. -/
theorem canonical_relative_relative (i j : Fin 3) :
    canonical.bracket (relative i) (relative j) = 0 := by
  simp only [relative, q₁, q₂, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_sub_right, PhaseSpace.canonical_q_q, sub_zero]

/-- `{Rᵢ, Rⱼ} = 0`. -/
theorem canonical_centre_centre (m₁ m₂ : ℝ) (i j : Fin 3) :
    canonical.bracket (centre m₁ m₂ i) (centre m₁ m₂ j) = 0 := by
  simp only [centre, q₁, q₂, AlmostPoissonStructure.bracket_add_left,
    AlmostPoissonStructure.bracket_add_right, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_left,
    AlmostPoissonStructure.bracket_algebraMap_right, PhaseSpace.canonical_q_q, mul_zero,
    add_zero]

/-- `{pᵢ, pⱼ} = 0` for the relative momentum. -/
theorem canonical_relativeMomentum_relativeMomentum (m₁ m₂ : ℝ) (i j : Fin 3) :
    canonical.bracket (relativeMomentum m₁ m₂ i) (relativeMomentum m₁ m₂ j) = 0 := by
  simp only [relativeMomentum, p₁, p₂, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_sub_right, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_left,
    AlmostPoissonStructure.bracket_algebraMap_right, PhaseSpace.canonical_p_p, mul_zero,
    add_zero, sub_zero]

/-- `{Pᵢ, Pⱼ} = 0`. -/
theorem canonical_totalMomentum_totalMomentum (i j : Fin 3) :
    canonical.bracket (totalMomentum i) (totalMomentum j) = 0 := by
  simp only [totalMomentum, p₁, p₂, AlmostPoissonStructure.bracket_add_left,
    AlmostPoissonStructure.bracket_add_right, PhaseSpace.canonical_p_p, add_zero]

/-! ### The canonical co-ordinates of the centre of mass -/

/-- The canonical co-ordinates of the centre of mass, as functions of the
positions and the momenta of the particles. -/
def centreCoordinates (m₁ m₂ : ℝ) : SmoothRingHom CentreSpace Space :=
  FreeSmoothRing.lift (Sum.elim (Sum.elim relative (centre m₁ m₂))
    (Sum.elim (relativeMomentum m₁ m₂) totalMomentum))

theorem centreCoordinates_q_inl (m₁ m₂ : ℝ) (i : Fin 3) :
    centreCoordinates m₁ m₂ (PhaseSpace.q (Sum.inl i)) = relative i := lift_generator _ _

theorem centreCoordinates_q_inr (m₁ m₂ : ℝ) (i : Fin 3) :
    centreCoordinates m₁ m₂ (PhaseSpace.q (Sum.inr i)) = centre m₁ m₂ i := lift_generator _ _

theorem centreCoordinates_p_inl (m₁ m₂ : ℝ) (i : Fin 3) :
    centreCoordinates m₁ m₂ (PhaseSpace.p (Sum.inl i)) = relativeMomentum m₁ m₂ i :=
  lift_generator _ _

theorem centreCoordinates_p_inr (m₁ m₂ : ℝ) (i : Fin 3) :
    centreCoordinates m₁ m₂ (PhaseSpace.p (Sum.inr i)) = totalMomentum i := lift_generator _ _

/-- The positions and the momenta of the particles, as functions of the
co-ordinates of the centre of mass: `q₁ = R + (m₂/M) r`, `q₂ = R − (m₁/M) r`,
`p₁ = (m₁/M) P + p`, `p₂ = (m₂/M) P − p`. -/
def particleCoordinates (m₁ m₂ : ℝ) : SmoothRingHom Space CentreSpace :=
  FreeSmoothRing.lift (Sum.elim
    (fun a => ![PhaseSpace.q (Sum.inr a.2) +
        algebraMap ℝ CentreSpace (m₂ / (m₁ + m₂)) * PhaseSpace.q (Sum.inl a.2),
      PhaseSpace.q (Sum.inr a.2) -
        algebraMap ℝ CentreSpace (m₁ / (m₁ + m₂)) * PhaseSpace.q (Sum.inl a.2)] a.1)
    fun a => ![algebraMap ℝ CentreSpace (m₁ / (m₁ + m₂)) * PhaseSpace.p (Sum.inr a.2) +
        PhaseSpace.p (Sum.inl a.2),
      algebraMap ℝ CentreSpace (m₂ / (m₁ + m₂)) * PhaseSpace.p (Sum.inr a.2) -
        PhaseSpace.p (Sum.inl a.2)] a.1)

theorem particleCoordinates_q₁ (m₁ m₂ : ℝ) (i : Fin 3) :
    particleCoordinates m₁ m₂ (q₁ i) = PhaseSpace.q (Sum.inr i) +
      algebraMap ℝ CentreSpace (m₂ / (m₁ + m₂)) * PhaseSpace.q (Sum.inl i) :=
  lift_generator _ _

theorem particleCoordinates_q₂ (m₁ m₂ : ℝ) (i : Fin 3) :
    particleCoordinates m₁ m₂ (q₂ i) = PhaseSpace.q (Sum.inr i) -
      algebraMap ℝ CentreSpace (m₁ / (m₁ + m₂)) * PhaseSpace.q (Sum.inl i) :=
  lift_generator _ _

theorem particleCoordinates_p₁ (m₁ m₂ : ℝ) (i : Fin 3) :
    particleCoordinates m₁ m₂ (p₁ i) =
      algebraMap ℝ CentreSpace (m₁ / (m₁ + m₂)) * PhaseSpace.p (Sum.inr i) +
        PhaseSpace.p (Sum.inl i) :=
  lift_generator _ _

theorem particleCoordinates_p₂ (m₁ m₂ : ℝ) (i : Fin 3) :
    particleCoordinates m₁ m₂ (p₂ i) =
      algebraMap ℝ CentreSpace (m₂ / (m₁ + m₂)) * PhaseSpace.p (Sum.inr i) -
        PhaseSpace.p (Sum.inl i) :=
  lift_generator _ _

/-- The two changes of variables are inverse to each other. -/
theorem centreCoordinates_particleCoordinates (hM : m₁ + m₂ ≠ 0) (f : Space) :
    centreCoordinates m₁ m₂ (particleCoordinates m₁ m₂ f) = f := by
  have h : (centreCoordinates m₁ m₂).comp (particleCoordinates m₁ m₂) = SmoothRingHom.id Space :=
    FreeSmoothRing.hom_ext fun a => by
      have hsum := algebraMap_fraction_add hM
      rw [SmoothRingHom.comp_apply, SmoothRingHom.id_apply]
      rcases a with ⟨b, i⟩ | ⟨b, i⟩ <;> fin_cases b
      · change centreCoordinates m₁ m₂ (particleCoordinates m₁ m₂ (q₁ i)) = q₁ i
        rw [particleCoordinates_q₁, SmoothRingHom.map_add, SmoothRingHom.map_mul,
          SmoothRingHom.map_algebraMap, centreCoordinates_q_inr, centreCoordinates_q_inl, centre,
          relative]
        linear_combination q₁ i * hsum
      · change centreCoordinates m₁ m₂ (particleCoordinates m₁ m₂ (q₂ i)) = q₂ i
        rw [particleCoordinates_q₂, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
          SmoothRingHom.map_algebraMap, centreCoordinates_q_inr, centreCoordinates_q_inl, centre,
          relative]
        linear_combination q₂ i * hsum
      · change centreCoordinates m₁ m₂ (particleCoordinates m₁ m₂ (p₁ i)) = p₁ i
        rw [particleCoordinates_p₁, SmoothRingHom.map_add, SmoothRingHom.map_mul,
          SmoothRingHom.map_algebraMap, centreCoordinates_p_inr, centreCoordinates_p_inl,
          totalMomentum, relativeMomentum]
        linear_combination p₁ i * hsum
      · change centreCoordinates m₁ m₂ (particleCoordinates m₁ m₂ (p₂ i)) = p₂ i
        rw [particleCoordinates_p₂, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
          SmoothRingHom.map_algebraMap, centreCoordinates_p_inr, centreCoordinates_p_inl,
          totalMomentum, relativeMomentum]
        linear_combination p₂ i * hsum
  exact congrArg (fun χ : SmoothRingHom Space Space => χ f) h

/-- The two changes of variables are inverse to each other. -/
theorem particleCoordinates_centreCoordinates (hM : m₁ + m₂ ≠ 0) (g : CentreSpace) :
    particleCoordinates m₁ m₂ (centreCoordinates m₁ m₂ g) = g := by
  have h : (particleCoordinates m₁ m₂).comp (centreCoordinates m₁ m₂) =
      SmoothRingHom.id CentreSpace :=
    FreeSmoothRing.hom_ext fun a => by
      have hsum : algebraMap ℝ CentreSpace (m₁ / (m₁ + m₂)) +
          algebraMap ℝ CentreSpace (m₂ / (m₁ + m₂)) = 1 := by
        rw [← map_add, ← map_one (algebraMap ℝ CentreSpace)]
        congr 1
        field_simp
      rw [SmoothRingHom.comp_apply, SmoothRingHom.id_apply]
      rcases a with (i | i) | (i | i)
      · change particleCoordinates m₁ m₂ (centreCoordinates m₁ m₂ (PhaseSpace.q (Sum.inl i))) =
          PhaseSpace.q (Sum.inl i)
        rw [centreCoordinates_q_inl, relative, SmoothRingHom.map_sub, particleCoordinates_q₁,
          particleCoordinates_q₂]
        linear_combination PhaseSpace.q (Sum.inl i) * hsum
      · change particleCoordinates m₁ m₂ (centreCoordinates m₁ m₂ (PhaseSpace.q (Sum.inr i))) =
          PhaseSpace.q (Sum.inr i)
        rw [centreCoordinates_q_inr, centre, SmoothRingHom.map_add, SmoothRingHom.map_mul,
          SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, SmoothRingHom.map_algebraMap,
          particleCoordinates_q₁, particleCoordinates_q₂]
        linear_combination PhaseSpace.q (Sum.inr i) * hsum
      · change particleCoordinates m₁ m₂ (centreCoordinates m₁ m₂ (PhaseSpace.p (Sum.inl i))) =
          PhaseSpace.p (Sum.inl i)
        rw [centreCoordinates_p_inl, relativeMomentum, SmoothRingHom.map_sub,
          SmoothRingHom.map_mul, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
          SmoothRingHom.map_algebraMap, particleCoordinates_p₁, particleCoordinates_p₂]
        linear_combination PhaseSpace.p (Sum.inl i) * hsum
      · change particleCoordinates m₁ m₂ (centreCoordinates m₁ m₂ (PhaseSpace.p (Sum.inr i))) =
          PhaseSpace.p (Sum.inr i)
        rw [centreCoordinates_p_inr, totalMomentum, SmoothRingHom.map_add,
          particleCoordinates_p₁, particleCoordinates_p₂]
        linear_combination PhaseSpace.p (Sum.inr i) * hsum
  exact congrArg (fun χ : SmoothRingHom CentreSpace CentreSpace => χ g) h

/-- The change of variables to the centre of mass is canonical (Landau–Lifshitz
§13). -/
theorem isPoissonHom_centreCoordinates (hM : m₁ + m₂ ≠ 0) :
    IsPoissonHom (PhaseSpace.canonical (Fin 3 ⊕ Fin 3)).toAlmostPoissonStructure
      canonical.toAlmostPoissonStructure (centreCoordinates m₁ m₂) := by
  refine PhaseSpace.isPoissonHom_of_canonical ?_ ?_ ?_
  · rintro (i | i) (j | j)
    · rw [centreCoordinates_q_inl, centreCoordinates_q_inl]
      exact canonical_relative_relative i j
    · rw [centreCoordinates_q_inl, centreCoordinates_q_inr, canonical.antisymm,
        canonical_centre_relative, neg_zero]
    · rw [centreCoordinates_q_inr, centreCoordinates_q_inl]
      exact canonical_centre_relative m₁ m₂ i j
    · rw [centreCoordinates_q_inr, centreCoordinates_q_inr]
      exact canonical_centre_centre m₁ m₂ i j
  · rintro (i | i) (j | j)
    · rw [centreCoordinates_p_inl, centreCoordinates_p_inl]
      exact canonical_relativeMomentum_relativeMomentum m₁ m₂ i j
    · rw [centreCoordinates_p_inl, centreCoordinates_p_inr, canonical.antisymm,
        canonical_totalMomentum_relativeMomentum, neg_zero]
    · rw [centreCoordinates_p_inr, centreCoordinates_p_inl]
      exact canonical_totalMomentum_relativeMomentum m₁ m₂ i j
    · rw [centreCoordinates_p_inr, centreCoordinates_p_inr]
      exact canonical_totalMomentum_totalMomentum i j
  · rintro (i | i) (j | j)
    · rw [centreCoordinates_q_inl, centreCoordinates_p_inl,
        canonical_relative_relativeMomentum hM]
      simp only [Sum.inl.injEq]
    · rw [centreCoordinates_q_inl, centreCoordinates_p_inr, canonical_relative_totalMomentum]
      simp only [reduceCtorEq, ↓reduceIte]
    · rw [centreCoordinates_q_inr, centreCoordinates_p_inl, canonical_centre_relativeMomentum]
      simp only [reduceCtorEq, ↓reduceIte]
    · rw [centreCoordinates_q_inr, centreCoordinates_p_inr, canonical_centre_totalMomentum hM]
      simp only [Sum.inr.injEq]

/-! ### Reduction by translations -/

/-- The ideal of the equations `P = 0`: total momentum zero. -/
def totalMomentumIdeal : Ideal Space := Ideal.span (Set.range totalMomentum)

theorem totalMomentumIdeal_eq (m₁ m₂ : ℝ) :
    totalMomentumIdeal = Ideal.span (Set.range fun k =>
      centreCoordinates m₁ m₂ (momentumEquation (Fin 3) (0 : Fin 3 → ℝ) k)) := by
  have h : (fun k => centreCoordinates m₁ m₂ (momentumEquation (Fin 3) (0 : Fin 3 → ℝ) k)) =
      totalMomentum := funext fun k => by
    rw [momentumEquation, SmoothRingHom.map_sub, centreCoordinates_p_inr,
      SmoothRingHom.map_algebraMap, Pi.zero_apply, map_zero, sub_zero]
  rw [h, totalMomentumIdeal]

/-- The morphism from the phase space of one particle to the reduced ring of
two particles at total momentum zero: `q ↦ r`, `p ↦` the relative momentum. -/
def reducedMassHom (hM : m₁ + m₂ ≠ 0) :
    SmoothRingHom (SmoothAlgebra.PhaseSpace (Fin 3)) (canonical.Reduction totalMomentumIdeal) :=
  canonicalReductionHom (isPoissonHom_centreCoordinates hM) (totalMomentumIdeal_eq m₁ m₂)

/-- The reduced ring of two particles by translations at total momentum zero is
the phase space of one particle. -/
theorem reducedMassHom_bijective (hM : m₁ + m₂ ≠ 0) :
    Function.Bijective (reducedMassHom hM) :=
  canonicalReductionHom_bijective _ (centreCoordinates_particleCoordinates hM)
    (particleCoordinates_centreCoordinates hM) _

/-- The identification of the reduced ring with the phase space of one particle
preserves the bracket. -/
theorem isPoissonHom_reducedMassHom (hM : m₁ + m₂ ≠ 0) :
    IsPoissonHom (PhaseSpace.canonical (Fin 3)).toAlmostPoissonStructure
      (canonical.reduction totalMomentumIdeal).toAlmostPoissonStructure (reducedMassHom hM) :=
  isPoissonHom_canonicalReductionHom _ _

/-! ### The Hamiltonian -/

/-- The Hamiltonian of two particles whose interaction depends on the relative
position. -/
def hamiltonian (m₁ m₂ : ℝ) (U : FreeSmoothRing (Fin 3)) : Space :=
  kineticEnergy m₁ m₂ + FreeSmoothRing.lift relative U

/-- The Hamiltonian `|p|² / 2μ + U(q)` of one particle of mass `μ` in the field
`U`. -/
def relativeHamiltonian (μ : ℝ) (U : FreeSmoothRing (Fin 3)) : SmoothAlgebra.PhaseSpace (Fin 3) :=
  algebraMap ℝ (SmoothAlgebra.PhaseSpace (Fin 3)) (μ⁻¹ / 2) * (PhaseSpace.p ⬝ᵥ PhaseSpace.p) +
    FreeSmoothRing.lift PhaseSpace.q U

/-- In the co-ordinates of the centre of mass the Hamiltonian is
`|P|² / 2M + |p|² / 2μ + U(r)`. -/
theorem particleCoordinates_hamiltonian (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0)
    (U : FreeSmoothRing (Fin 3)) :
    particleCoordinates m₁ m₂ (hamiltonian m₁ m₂ U) =
      algebraMap ℝ CentreSpace ((m₁ + m₂)⁻¹ / 2) *
          ((fun i => PhaseSpace.p (Sum.inr i)) ⬝ᵥ fun i => PhaseSpace.p (Sum.inr i)) +
        algebraMap ℝ CentreSpace ((reducedMass m₁ m₂)⁻¹ / 2) *
          ((fun i => PhaseSpace.p (Sum.inl i)) ⬝ᵥ fun i => PhaseSpace.p (Sum.inl i)) +
        FreeSmoothRing.lift (fun i => PhaseSpace.q (Sum.inl i)) U := by
  have hP (i : Fin 3) : particleCoordinates m₁ m₂ (totalMomentum i) = PhaseSpace.p (Sum.inr i) := by
    rw [← centreCoordinates_p_inr m₁ m₂, particleCoordinates_centreCoordinates hM]
  have hp (i : Fin 3) :
      particleCoordinates m₁ m₂ (relativeMomentum m₁ m₂ i) = PhaseSpace.p (Sum.inl i) := by
    rw [← centreCoordinates_p_inl m₁ m₂, particleCoordinates_centreCoordinates hM]
  have hr (i : Fin 3) : particleCoordinates m₁ m₂ (relative i) = PhaseSpace.q (Sum.inl i) := by
    rw [← centreCoordinates_q_inl m₁ m₂, particleCoordinates_centreCoordinates hM]
  rw [hamiltonian, SmoothRingHom.map_add, kineticEnergy_eq_centre h₁ h₂ hM, map_lift]
  simp only [SmoothRingHom.map_add, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
    dotProduct, SmoothRingHom.map_sum, hP, hp, hr]

/-- The centre of mass is a cyclic co-ordinate of the Hamiltonian. -/
theorem partialDerivation_particleCoordinates_hamiltonian (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0)
    (hM : m₁ + m₂ ≠ 0) (U : FreeSmoothRing (Fin 3)) (k : Fin 3) :
    partialDerivation (Sum.inl (Sum.inr k))
      (particleCoordinates m₁ m₂ (hamiltonian m₁ m₂ U)) = 0 := by
  rw [particleCoordinates_hamiltonian h₁ h₂ hM, map_add, map_add,
    SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_algebraMap_mul,
    derivation_lift_mul]
  simp [dotProduct, PhaseSpace.p, PhaseSpace.q, SmoothDerivation.map_mul,
    partialDerivation_generator]

/-- At total momentum zero and with the centre of mass at the origin, the
Hamiltonian is that of one particle with the reduced mass. -/
theorem restriction_particleCoordinates_hamiltonian (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0)
    (hM : m₁ + m₂ ≠ 0) (U : FreeSmoothRing (Fin 3)) :
    restriction (Fin 3) (0 : Fin 3 → ℝ) (particleCoordinates m₁ m₂ (hamiltonian m₁ m₂ U)) =
      relativeHamiltonian (reducedMass m₁ m₂) U := by
  have hP (i : Fin 3) : restriction (Fin 3) (0 : Fin 3 → ℝ) (PhaseSpace.p (Sum.inr i)) = 0 := by
    rw [PhaseSpace.p, restriction, lift_generator]
    exact map_zero _
  have hp (i : Fin 3) :
      restriction (Fin 3) (0 : Fin 3 → ℝ) (PhaseSpace.p (Sum.inl i)) = PhaseSpace.p i := by
    rw [PhaseSpace.p, restriction, lift_generator]
    rfl
  have hq (i : Fin 3) :
      restriction (Fin 3) (0 : Fin 3 → ℝ) (PhaseSpace.q (Sum.inl i)) = PhaseSpace.q i := by
    rw [PhaseSpace.q, restriction, lift_generator]
    rfl
  rw [particleCoordinates_hamiltonian h₁ h₂ hM, relativeHamiltonian, SmoothRingHom.map_add,
    SmoothRingHom.map_add, map_lift]
  simp only [SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, dotProduct,
    SmoothRingHom.map_sum, hP, hp, hq, mul_zero, Finset.sum_const_zero, zero_add]

/-- The Hamiltonian is in the normalizer of the ideal of total momentum zero. -/
theorem hamiltonian_mem_normalizer (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0)
    (U : FreeSmoothRing (Fin 3)) :
    hamiltonian m₁ m₂ U ∈ canonical.normalizer totalMomentumIdeal := by
  have h := map_mem_normalizer (isPoissonHom_centreCoordinates hM) (totalMomentumIdeal_eq m₁ m₂)
    (mem_normalizer_of_cyclic (partialDerivation_particleCoordinates_hamiltonian h₁ h₂ hM U) 0)
  rwa [centreCoordinates_particleCoordinates hM] at h

/-- The reduced mass (Landau–Lifshitz §13): in the reduced ring of two
particles at total momentum zero, the class of the Hamiltonian is the
Hamiltonian `|p|² / 2μ + U(q)` of one particle with the reduced mass. -/
theorem reducedMassHom_relativeHamiltonian (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0)
    (U : FreeSmoothRing (Fin 3)) :
    reducedMassHom hM (relativeHamiltonian (reducedMass m₁ m₂) U) =
      canonical.reductionMap totalMomentumIdeal
        ⟨hamiltonian m₁ m₂ U, hamiltonian_mem_normalizer h₁ h₂ hM U⟩ := by
  rw [← restriction_particleCoordinates_hamiltonian h₁ h₂ hM]
  exact canonicalReductionHom_restriction _ (centreCoordinates_particleCoordinates hM)
    (particleCoordinates_centreCoordinates hM) _ _

/-! ### Trajectories -/

/-- The total momentum is an integral of the motion. -/
theorem isIntegral_totalMomentum (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0)
    (U : FreeSmoothRing (Fin 3)) (i : Fin 3) :
    canonical.IsIntegral (hamiltonian m₁ m₂ U) (totalMomentum i) := by
  have h := isPoissonHom_centreCoordinates hM (PhaseSpace.p (Sum.inr i))
    (particleCoordinates m₁ m₂ (hamiltonian m₁ m₂ U))
  rw [centreCoordinates_p_inr, centreCoordinates_particleCoordinates hM,
    PhaseSpace.canonical_p_bracket,
    partialDerivation_particleCoordinates_hamiltonian h₁ h₂ hM, neg_zero,
    SmoothRingHom.map_zero] at h
  exact h.symm

/-- The motion of two bodies reduces to the motion of one body with the
reduced mass (Landau–Lifshitz §13): along a trajectory with total momentum
zero, the relative position and the relative momentum form a trajectory of the
Hamiltonian `|p|² / 2μ + U(q)`. -/
theorem isTrajectory_relative (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0)
    {U : FreeSmoothRing (Fin 3)} {x : (Fin 2 × Fin 3) ⊕ (Fin 2 × Fin 3) → TimeFunction}
    (hx : IsTrajectory canonical (hamiltonian m₁ m₂ U) x)
    (hP : ∀ i, FreeSmoothRing.lift x (totalMomentum i) = 0) :
    IsTrajectory (PhaseSpace.canonical (Fin 3)) (relativeHamiltonian (reducedMass m₁ m₂) U)
      (Sum.elim (fun i => FreeSmoothRing.lift x (relative i))
        fun i => FreeSmoothRing.lift x (relativeMomentum m₁ m₂ i)) := by
  have hy : IsTrajectory (PhaseSpace.canonical (Fin 3 ⊕ Fin 3))
      (particleCoordinates m₁ m₂ (hamiltonian m₁ m₂ U))
      fun a => FreeSmoothRing.lift x (centreCoordinates m₁ m₂ (generator a)) :=
    IsTrajectory.of_isPoissonHom (isPoissonHom_centreCoordinates hM)
      (by rwa [centreCoordinates_particleCoordinates hM])
  have h := isTrajectory_restriction (c := 0)
    (partialDerivation_particleCoordinates_hamiltonian h₁ h₂ hM U) hy fun k => by
      change FreeSmoothRing.lift x (centreCoordinates m₁ m₂ (PhaseSpace.p (Sum.inr k))) = _
      rw [centreCoordinates_p_inr, hP, Pi.zero_apply, map_zero]
  rw [restriction_particleCoordinates_hamiltonian h₁ h₂ hM] at h
  have hcurve : (Sum.elim (fun i => FreeSmoothRing.lift x (relative i))
      fun i => FreeSmoothRing.lift x (relativeMomentum m₁ m₂ i)) =
      fun a => FreeSmoothRing.lift x
        (centreCoordinates m₁ m₂ (generator (Sum.map Sum.inl Sum.inl a))) := by
    funext a
    rcases a with i | i
    · exact congrArg (FreeSmoothRing.lift x) (centreCoordinates_q_inl m₁ m₂ i).symm
    · exact congrArg (FreeSmoothRing.lift x) (centreCoordinates_p_inl m₁ m₂ i).symm
  rw [hcurve]
  exact h

end ProjectAInos.Mechanics.TwoBody
