/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.HamiltonianField
public import ProjectAinos.SmoothAlgebra.Poisson.Position
public import ProjectAinos.SmoothAlgebra.RelEnergy
public import ProjectAinos.SmoothGeometry.ODE.FlowBounded
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The Hamiltonian of a charge in a static field

Fix an inertial observer, and let the scalar potential `φ` and the vector potential `a` be
smooth functions of the position on all of space that do not depend on the time. For a mass
`m ≠ 0` and a charge `e`,

`H = √(m² + Σ (pᵢ − e aᵢ)²) + e φ`

is the element `ChargedParticle.hamiltonian m e φ a` of the canonical phase space of `d` space
co-ordinates (Landau–Lifshitz, *The Classical Theory of Fields*, §§16–19). The units have
`c = 1`. The fields are `Eᵢ = −∂ᵢφ` and the antisymmetric tensor `Fᵢⱼ = ∂ᵢaⱼ − ∂ⱼaᵢ`; in three
dimensions `Σⱼ Fᵢⱼ vⱼ = (v × B)ᵢ` with `B = ∇ × a`.

* `canonical_q_hamiltonian`: the velocity is `vᵢ = πᵢ/√(m² + Σ πⱼ²)` with the kinetic momentum
  `π = p − e a`, and `sum_velocity_mul_self`: `Σ vᵢ² = 1 − m²/(m² + Σ πⱼ²)`.
* `canonical_kineticMomentum_kineticMomentum`: `{πᵢ, πⱼ} = e Fᵢⱼ`.
* `canonical_kineticMomentum_hamiltonian`: the equation of motion `{πᵢ, H} = e (Eᵢ + Σⱼ Fᵢⱼ vⱼ)`,
  the Lorentz force.
* `canonical_kineticEnergy_hamiltonian`: the kinetic energy changes by the work of the electric
  field, `{√(m² + Σ πⱼ²), H} = e Σᵢ Eᵢ vᵢ`; the energy `H` is an integral of the motion.
* `isIntegral_p_of_cyclic`: the canonical momentum of a co-ordinate on which the potentials do
  not depend is an integral of the motion.
* `momentumShift_hamiltonian`: the gauge change `a ↦ a + ∇χ` is the canonical transformation
  `p ↦ p + e ∇χ`; it does not change the fields (`magneticTensor_gaugeShift`), and it maps
  trajectories to trajectories (`isTrajectory_gaugeShift`).
* `isTrajectory_iff_lorentzForce`: Hamilton's equations are the equation of the Lorentz force
  together with the relation between the velocity and the kinetic momentum.
* `flowDomain_hamiltonianField`: the flow is defined for all times and points, for all smooth
  static potentials: the speed is less than one, and the force is bounded where the position
  is bounded. `measurePreserving_hamiltonianFlow` is Liouville's theorem for it.

A potential that depends on the time is outside this module.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SmoothAlgebra

/-- The bracket with the relativistic energy of a family `w`:
`{g, √(m² + Σ wⱼ²)} = (1/√(m² + Σ wⱼ²)) Σⱼ wⱼ {g, wⱼ}`. -/
theorem AlmostPoissonStructure.bracket_relEnergy_right {P : Type*} [CommRing P] [Algebra ℝ P]
    [SmoothRing P] (ρ : AlmostPoissonStructure P) {m : ℝ} (hm : m ≠ 0) {d : ℕ} (g : P)
    (w : Fin d → P) :
    ρ.bracket g (relEnergy m w) = relEnergyInv m w * ∑ j, w j * ρ.bracket g (w j) := by
  have h : ρ.bracket (relEnergy m w) g = relEnergyInv m w * ∑ j, w j * ρ.bracket (w j) g :=
    SmoothDerivation.apply_relEnergy hm (ρ.hamiltonian g) w
  rw [ρ.antisymm, h, ← mul_neg, ← Finset.sum_neg_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  rw [ρ.antisymm (w j) g, mul_neg, neg_neg]

end ProjectAinos.SmoothAlgebra

namespace ProjectAinos.Electrodynamics.ChargedParticle

open Set MeasureTheory
open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics
open SmoothGeometry SmoothGeometry.NonlinearODE

variable {d : ℕ} {m : ℝ}

/-! ### The fields of static potentials -/

/-- The electric field `Eᵢ = −∂ᵢφ` of a static scalar potential. -/
def electricField (φ : FreeSmoothRing (Fin d)) (i : Fin d) : FreeSmoothRing (Fin d) :=
  -partialDerivation i φ

/-- The magnetic field of a static vector potential, as the antisymmetric tensor
`Fᵢⱼ = ∂ᵢaⱼ − ∂ⱼaᵢ`. -/
def magneticTensor (a : Fin d → FreeSmoothRing (Fin d)) (i j : Fin d) : FreeSmoothRing (Fin d) :=
  partialDerivation i (a j) - partialDerivation j (a i)

theorem magneticTensor_antisymm (a : Fin d → FreeSmoothRing (Fin d)) (i j : Fin d) :
    magneticTensor a i j = -magneticTensor a j i := by
  rw [magneticTensor, magneticTensor, neg_sub]

@[simp] theorem magneticTensor_self (a : Fin d → FreeSmoothRing (Fin d)) (i : Fin d) :
    magneticTensor a i i = 0 := by
  rw [magneticTensor, sub_self]

/-- The gauge change `a ↦ a + ∇χ` of the vector potential by a function `χ` of the
position. -/
def gaugeShift (a : Fin d → FreeSmoothRing (Fin d)) (χ : FreeSmoothRing (Fin d)) (i : Fin d) :
    FreeSmoothRing (Fin d) :=
  a i + partialDerivation i χ

/-- The gauge change does not change the magnetic field. -/
theorem magneticTensor_gaugeShift (a : Fin d → FreeSmoothRing (Fin d))
    (χ : FreeSmoothRing (Fin d)) (i j : Fin d) :
    magneticTensor (gaugeShift a χ) i j = magneticTensor a i j := by
  simp only [magneticTensor, gaugeShift, map_add]
  rw [partialDerivation_comm i j χ]
  ring

/-! ### The Hamiltonian -/

/-- The kinetic momentum `πᵢ = pᵢ − e aᵢ`. -/
def kineticMomentum (e : ℝ) (a : Fin d → FreeSmoothRing (Fin d)) (i : Fin d) :
    PhaseSpace (Fin d) :=
  p i - algebraMap ℝ (PhaseSpace (Fin d)) e * ofPosition (a i)

/-- The Hamiltonian `√(m² + Σ (pᵢ − e aᵢ)²) + e φ` of a charge in a static field. -/
def hamiltonian (m e : ℝ) (φ : FreeSmoothRing (Fin d)) (a : Fin d → FreeSmoothRing (Fin d)) :
    PhaseSpace (Fin d) :=
  relEnergy m (kineticMomentum e a) + algebraMap ℝ (PhaseSpace (Fin d)) e * ofPosition φ

/-- The velocity `πᵢ/√(m² + Σ πⱼ²)` as a function on the phase space. -/
def velocity (m e : ℝ) (a : Fin d → FreeSmoothRing (Fin d)) (i : Fin d) : PhaseSpace (Fin d) :=
  relEnergyInv m (kineticMomentum e a) * kineticMomentum e a i

variable (e : ℝ) (φ : FreeSmoothRing (Fin d)) (a : Fin d → FreeSmoothRing (Fin d))

/-- Without a charge the Hamiltonian is that of the free particle. -/
theorem hamiltonian_zero_charge (m : ℝ) :
    hamiltonian m 0 φ a = relEnergy m (p : Fin d → PhaseSpace (Fin d)) := by
  have h : kineticMomentum 0 a = (p : Fin d → PhaseSpace (Fin d)) := by
    funext i
    rw [kineticMomentum, map_zero, zero_mul, sub_zero]
  rw [hamiltonian, h, map_zero, zero_mul, add_zero]

/-! ### The brackets of the kinetic momentum -/

/-- `{qᵢ, πⱼ} = δᵢⱼ`. -/
theorem canonical_q_kineticMomentum (i j : Fin d) :
    (canonical (Fin d)).bracket (q i) (kineticMomentum e a j) = if i = j then 1 else 0 := by
  simp only [kineticMomentum, AlmostPoissonStructure.bracket_sub_right,
    AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_right,
    canonical_q_ofPosition, canonical_q_p, mul_zero, add_zero, sub_zero]

/-- `{pᵢ, πⱼ} = e ∂ᵢaⱼ`. -/
theorem canonical_p_kineticMomentum (i j : Fin d) :
    (canonical (Fin d)).bracket (p i) (kineticMomentum e a j) =
      algebraMap ℝ (PhaseSpace (Fin d)) e * ofPosition (partialDerivation i (a j)) := by
  simp only [kineticMomentum, AlmostPoissonStructure.bracket_sub_right,
    AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_right,
    canonical_p_ofPosition, canonical_p_p, mul_zero, add_zero]
  ring

/-- `{πᵢ, f} = −∂ᵢf` for a function `f` of the position. -/
theorem canonical_kineticMomentum_ofPosition (i : Fin d) (f : FreeSmoothRing (Fin d)) :
    (canonical (Fin d)).bracket (kineticMomentum e a i) (ofPosition f) =
      -ofPosition (partialDerivation i f) := by
  simp only [kineticMomentum, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_algebraMap_left,
    canonical_ofPosition_ofPosition, canonical_p_ofPosition, mul_zero, add_zero, sub_zero]

/-- `{πᵢ, πⱼ} = e Fᵢⱼ`: the components of the kinetic momentum do not commute in a magnetic
field. -/
theorem canonical_kineticMomentum_kineticMomentum (i j : Fin d) :
    (canonical (Fin d)).bracket (kineticMomentum e a i) (kineticMomentum e a j) =
      algebraMap ℝ (PhaseSpace (Fin d)) e * ofPosition (magneticTensor a i j) := by
  have h1 := canonical_kineticMomentum_ofPosition e a i (a j)
  have h2 : (canonical (Fin d)).bracket (kineticMomentum e a i) (p j) =
      -(algebraMap ℝ (PhaseSpace (Fin d)) e * ofPosition (partialDerivation j (a i))) := by
    rw [(canonical (Fin d)).antisymm, canonical_p_kineticMomentum]
  have h : (canonical (Fin d)).bracket (kineticMomentum e a i) (kineticMomentum e a j) =
      (canonical (Fin d)).bracket (kineticMomentum e a i) (p j) -
        algebraMap ℝ (PhaseSpace (Fin d)) e *
          (canonical (Fin d)).bracket (kineticMomentum e a i) (ofPosition (a j)) := by
    conv_lhs => rw [kineticMomentum.eq_1 e a j]
    simp only [AlmostPoissonStructure.bracket_sub_right,
      AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_right,
      mul_zero, add_zero]
  rw [h, h1, h2, magneticTensor, SmoothRingHom.map_sub]
  ring

/-! ### Hamilton's equations -/

/-- `{qᵢ, H} = vᵢ`. -/
theorem canonical_q_hamiltonian (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (q i) (hamiltonian m e φ a) = velocity m e a i := by
  rw [hamiltonian, AlmostPoissonStructure.bracket_add_right,
    AlmostPoissonStructure.bracket_relEnergy_right _ hm, Finset.sum_eq_single i]
  · simp only [canonical_q_kineticMomentum, ↓reduceIte, mul_one,
      AlmostPoissonStructure.bracket_mul_right, AlmostPoissonStructure.bracket_algebraMap_right,
      canonical_q_ofPosition, mul_zero, add_zero, velocity]
  · intro j _ hj
    simp only [canonical_q_kineticMomentum, Ne.symm hj, ↓reduceIte, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- `{pᵢ, H} = e (Σⱼ ∂ᵢaⱼ vⱼ − ∂ᵢφ)`. -/
theorem canonical_p_hamiltonian (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (p i) (hamiltonian m e φ a) =
      algebraMap ℝ (PhaseSpace (Fin d)) e *
        (∑ j, ofPosition (partialDerivation i (a j)) * velocity m e a j -
          ofPosition (partialDerivation i φ)) := by
  have hsum : relEnergyInv m (kineticMomentum e a) *
      ∑ j, kineticMomentum e a j * (algebraMap ℝ (PhaseSpace (Fin d)) e *
        ofPosition (partialDerivation i (a j))) =
      algebraMap ℝ (PhaseSpace (Fin d)) e *
        ∑ j, ofPosition (partialDerivation i (a j)) * velocity m e a j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [velocity]
    ring
  rw [hamiltonian, AlmostPoissonStructure.bracket_add_right,
    AlmostPoissonStructure.bracket_relEnergy_right _ hm]
  simp only [canonical_p_kineticMomentum, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_algebraMap_right, canonical_p_ofPosition, mul_zero, add_zero]
  rw [hsum]
  ring

/-- The equation of motion of a charge: `{πᵢ, H} = e (Eᵢ + Σⱼ Fᵢⱼ vⱼ)`. In three dimensions the
second term is `(v × B)ᵢ`. -/
theorem canonical_kineticMomentum_hamiltonian (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (kineticMomentum e a i) (hamiltonian m e φ a) =
      algebraMap ℝ (PhaseSpace (Fin d)) e * (ofPosition (electricField φ i) +
        ∑ j, ofPosition (magneticTensor a i j) * velocity m e a j) := by
  have hsum : relEnergyInv m (kineticMomentum e a) *
      ∑ j, kineticMomentum e a j * (algebraMap ℝ (PhaseSpace (Fin d)) e *
        ofPosition (magneticTensor a i j)) =
      algebraMap ℝ (PhaseSpace (Fin d)) e *
        ∑ j, ofPosition (magneticTensor a i j) * velocity m e a j := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [velocity]
    ring
  rw [hamiltonian, AlmostPoissonStructure.bracket_add_right,
    AlmostPoissonStructure.bracket_relEnergy_right _ hm]
  simp only [canonical_kineticMomentum_kineticMomentum, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_algebraMap_right, canonical_kineticMomentum_ofPosition,
    mul_zero, add_zero]
  rw [hsum, electricField, SmoothRingHom.map_neg]
  ring

/-- The kinetic energy changes by the work of the electric field:
`{√(m² + Σ πⱼ²), H} = e Σᵢ Eᵢ vᵢ`. The magnetic field does no work. -/
theorem canonical_kineticEnergy_hamiltonian (hm : m ≠ 0) :
    (canonical (Fin d)).bracket (relEnergy m (kineticMomentum e a)) (hamiltonian m e φ a) =
      algebraMap ℝ (PhaseSpace (Fin d)) e *
        ∑ i, ofPosition (electricField φ i) * velocity m e a i := by
  have hφ : (canonical (Fin d)).bracket (relEnergy m (kineticMomentum e a)) (ofPosition φ) =
      ∑ i, ofPosition (electricField φ i) * velocity m e a i := by
    rw [(canonical (Fin d)).antisymm, AlmostPoissonStructure.bracket_relEnergy_right _ hm,
      Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [(canonical (Fin d)).antisymm, canonical_kineticMomentum_ofPosition, velocity,
      electricField, SmoothRingHom.map_neg]
    ring
  rw [hamiltonian, AlmostPoissonStructure.bracket_add_right,
    AlmostPoissonStructure.bracket_self, zero_add, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_algebraMap_right, hφ, mul_zero, add_zero]

/-- `Σ vᵢ² = 1 − m²/(m² + Σ πⱼ²)`. -/
theorem sum_velocity_mul_self (hm : m ≠ 0) :
    ∑ i, velocity m e a i * velocity m e a i =
      1 - algebraMap ℝ (PhaseSpace (Fin d)) (m ^ 2) *
        (relEnergyInv m (kineticMomentum e a) * relEnergyInv m (kineticMomentum e a)) :=
  sum_relEnergyInv_mul_sq hm _

/-! ### Integrals of the motion -/

/-- The energy is an integral of the motion. -/
theorem isIntegral_hamiltonian (m : ℝ) :
    (canonical (Fin d)).IsIntegral (hamiltonian m e φ a) (hamiltonian m e φ a) :=
  PoissonStructure.isIntegral_self _

/-- The canonical momentum of a co-ordinate on which the potentials do not depend is an
integral of the motion. -/
theorem isIntegral_p_of_cyclic (hm : m ≠ 0) {k : Fin d} (hφ : partialDerivation k φ = 0)
    (ha : ∀ j, partialDerivation k (a j) = 0) :
    (canonical (Fin d)).IsIntegral (hamiltonian m e φ a) (p k) := by
  change (canonical (Fin d)).bracket (p k) (hamiltonian m e φ a) = 0
  rw [canonical_p_hamiltonian e φ a hm, hφ, SmoothRingHom.map_zero, sub_zero,
    Finset.sum_eq_zero, mul_zero]
  intro j _
  rw [ha j, SmoothRingHom.map_zero, zero_mul]

/-! ### The gauge change -/

/-- The canonical transformation `p ↦ p + e ∇χ` maps the kinetic momentum of `a + ∇χ` to that
of `a`. -/
theorem momentumShift_kineticMomentum (χ : FreeSmoothRing (Fin d)) (i : Fin d) :
    momentumShift e χ (kineticMomentum e (gaugeShift a χ) i) = kineticMomentum e a i := by
  rw [kineticMomentum, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, momentumShift_p, momentumShift_ofPosition, gaugeShift,
    SmoothRingHom.map_add, kineticMomentum]
  ring

/-- The gauge change `a ↦ a + ∇χ` is the canonical transformation `p ↦ p + e ∇χ`. -/
theorem momentumShift_hamiltonian (m : ℝ) (χ : FreeSmoothRing (Fin d)) :
    momentumShift e χ (hamiltonian m e φ (gaugeShift a χ)) = hamiltonian m e φ a := by
  rw [hamiltonian, SmoothRingHom.map_add, SmoothRingHom.map_relEnergy, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, momentumShift_ofPosition, hamiltonian]
  simp only [momentumShift_kineticMomentum]

/-- A trajectory in the potential `a` is a trajectory in the potential `a + ∇χ`, with the same
positions and the momenta `p + e ∇χ`. -/
theorem isTrajectory_gaugeShift {c : Fin d ⊕ Fin d → TimeFunction}
    (h : IsTrajectory (canonical (Fin d)) (hamiltonian m e φ a) c) (χ : FreeSmoothRing (Fin d)) :
    IsTrajectory (canonical (Fin d)) (hamiltonian m e φ (gaugeShift a χ))
      fun s => FreeSmoothRing.lift c (momentumShift e χ (generator s)) := by
  refine IsTrajectory.of_isPoissonHom (isPoissonHom_momentumShift e χ) ?_
  rw [momentumShift_hamiltonian]
  exact h

/-! ### The equations along a trajectory -/

/-- Along a trajectory the position moves with the velocity `π/√(m² + Σ πⱼ²)`. -/
theorem timeDerivative_q (hm : m ≠ 0) {c : Fin d ⊕ Fin d → TimeFunction}
    (h : IsTrajectory (canonical (Fin d)) (hamiltonian m e φ a) c) (i : Fin d) :
    timeDerivative (c (Sum.inl i)) = FreeSmoothRing.lift c (velocity m e a i) := by
  have h1 := h.timeDerivative_lift (q i)
  rw [canonical_q_hamiltonian e φ a hm, q, lift_generator] at h1
  exact h1

/-- Along a trajectory the kinetic momentum satisfies the equation of the Lorentz force. -/
theorem timeDerivative_kineticMomentum (hm : m ≠ 0) {c : Fin d ⊕ Fin d → TimeFunction}
    (h : IsTrajectory (canonical (Fin d)) (hamiltonian m e φ a) c) (i : Fin d) :
    timeDerivative (FreeSmoothRing.lift c (kineticMomentum e a i)) =
      FreeSmoothRing.lift c (algebraMap ℝ (PhaseSpace (Fin d)) e *
        (ofPosition (electricField φ i) +
          ∑ j, ofPosition (magneticTensor a i j) * velocity m e a j)) := by
  rw [h.timeDerivative_lift, canonical_kineticMomentum_hamiltonian e φ a hm]

/-- The momentum changes by the change of the kinetic momentum and of the vector potential
along the motion: `{pᵢ, H} = {πᵢ, H} + e Σⱼ ∂ⱼaᵢ vⱼ`. -/
theorem canonical_p_hamiltonian_eq (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (p i) (hamiltonian m e φ a) =
      (canonical (Fin d)).bracket (kineticMomentum e a i) (hamiltonian m e φ a) +
        algebraMap ℝ (PhaseSpace (Fin d)) e *
          ∑ j, ofPosition (partialDerivation j (a i)) * velocity m e a j := by
  have hp : p i =
      kineticMomentum e a i + algebraMap ℝ (PhaseSpace (Fin d)) e * ofPosition (a i) := by
    rw [kineticMomentum]
    ring
  have h : (canonical (Fin d)).bracket (p i) (hamiltonian m e φ a) =
      (canonical (Fin d)).bracket
        (kineticMomentum e a i + algebraMap ℝ (PhaseSpace (Fin d)) e * ofPosition (a i))
        (hamiltonian m e φ a) :=
    congrArg (fun f => (canonical (Fin d)).bracket f (hamiltonian m e φ a)) hp
  rw [h, AlmostPoissonStructure.bracket_add_left, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_algebraMap_left, mul_zero, add_zero,
    canonical_ofPosition_bracket]
  simp only [← canonical_q_bracket, canonical_q_hamiltonian e φ a hm]

/-- Along any curve the momentum is the kinetic momentum plus `e a`, differentiated by the
chain rule. -/
theorem timeDerivative_p_eq (c : Fin d ⊕ Fin d → TimeFunction) (i : Fin d) :
    timeDerivative (c (Sum.inr i)) =
      timeDerivative (FreeSmoothRing.lift c (kineticMomentum e a i)) +
        algebraMap ℝ TimeFunction e * ∑ j, FreeSmoothRing.lift c
          (ofPosition (partialDerivation j (a i))) * timeDerivative (c (Sum.inl j)) := by
  have hpos (f : FreeSmoothRing (Fin d)) :
      FreeSmoothRing.lift c (ofPosition f) = FreeSmoothRing.lift (fun j => c (Sum.inl j)) f := by
    rw [ofPosition, map_lift]
    simp only [q, lift_generator]
  have h1 : c (Sum.inr i) = FreeSmoothRing.lift c (kineticMomentum e a i) +
      algebraMap ℝ TimeFunction e * FreeSmoothRing.lift (fun j => c (Sum.inl j)) (a i) := by
    rw [kineticMomentum, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
      SmoothRingHom.map_algebraMap, p, lift_generator, hpos]
    ring
  conv_lhs => rw [h1]
  rw [map_add, SmoothDerivation.map_algebraMap_mul,
    derivation_lift_mul (fun j => c (Sum.inl j)) timeDerivative (a i), smul_eq_mul]
  simp only [hpos]

/-- Hamilton's equations are the equation of the Lorentz force: a curve in the phase space is
a trajectory if and only if its position moves with the velocity `π/√(m² + Σ πⱼ²)` and its
kinetic momentum satisfies `π̇ᵢ = e (Eᵢ + Σⱼ Fᵢⱼ vⱼ)`. -/
theorem isTrajectory_iff_lorentzForce (hm : m ≠ 0) (c : Fin d ⊕ Fin d → TimeFunction) :
    IsTrajectory (canonical (Fin d)) (hamiltonian m e φ a) c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) = FreeSmoothRing.lift c (velocity m e a i)) ∧
      ∀ i, timeDerivative (FreeSmoothRing.lift c (kineticMomentum e a i)) =
        FreeSmoothRing.lift c (algebraMap ℝ (PhaseSpace (Fin d)) e *
          (ofPosition (electricField φ i) +
            ∑ j, ofPosition (magneticTensor a i j) * velocity m e a j)) := by
  constructor
  · intro h
    exact ⟨timeDerivative_q e φ a hm h, timeDerivative_kineticMomentum e φ a hm h⟩
  · rintro ⟨hq, hπ⟩ (i | i)
    · change timeDerivative (c (Sum.inl i)) =
        FreeSmoothRing.lift c ((canonical (Fin d)).bracket (q i) (hamiltonian m e φ a))
      rw [canonical_q_hamiltonian e φ a hm]
      exact hq i
    · change timeDerivative (c (Sum.inr i)) =
        FreeSmoothRing.lift c ((canonical (Fin d)).bracket (p i) (hamiltonian m e φ a))
      rw [timeDerivative_p_eq e a c i, hπ i, canonical_p_hamiltonian_eq e φ a hm,
        canonical_kineticMomentum_hamiltonian e φ a hm]
      simp only [hq, SmoothRingHom.map_add, SmoothRingHom.map_mul, SmoothRingHom.map_sum,
        SmoothRingHom.map_algebraMap]

/-! ### Values at a point of the phase space -/

/-- The kinetic momentum `p − e a(x)` at a point of the phase space. -/
def realKineticMomentum (e : ℝ) (a : Fin d → FreeSmoothRing (Fin d)) (z : Fin d ⊕ Fin d → ℝ) :
    Fin d → ℝ :=
  fun i => z (Sum.inr i) - e * (a i).val fun j => z (Sum.inl j)

theorem lift_kineticMomentum (z : Fin d ⊕ Fin d → ℝ) (i : Fin d) :
    FreeSmoothRing.lift z (kineticMomentum e a i) = realKineticMomentum e a z i := by
  rw [kineticMomentum, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, p, lift_generator, lift_ofPosition, lift_real]
  rfl

/-- The value of the Hamiltonian at a point: `E(π) + e φ(x)`. -/
theorem lift_hamiltonian (m : ℝ) (z : Fin d ⊕ Fin d → ℝ) :
    FreeSmoothRing.lift z (hamiltonian m e φ a) =
      relEnergy m (realKineticMomentum e a z) + e * φ.val fun j => z (Sum.inl j) := by
  rw [hamiltonian, SmoothRingHom.map_add, SmoothRingHom.map_relEnergy, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, lift_ofPosition, lift_real]
  simp only [lift_kineticMomentum]
  rfl

/-- The Hamiltonian field: `ẋᵢ = πᵢ/√(m² + Σ πⱼ²)`. -/
theorem hamiltonianField_inl (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) (i : Fin d) :
    hamiltonianField (hamiltonian m e φ a) z (Sum.inl i) =
      relEnergyInv m (realKineticMomentum e a z) * realKineticMomentum e a z i := by
  change ((canonical (Fin d)).bracket (q i) (hamiltonian m e φ a)).val z = _
  rw [canonical_q_hamiltonian e φ a hm, ← lift_real, velocity, SmoothRingHom.map_mul,
    SmoothRingHom.map_relEnergyInv]
  simp only [lift_kineticMomentum]

/-- The Hamiltonian field: `ṗᵢ = e (Σⱼ ∂ᵢaⱼ(x) ẋⱼ − ∂ᵢφ(x))`. -/
theorem hamiltonianField_inr (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) (i : Fin d) :
    hamiltonianField (hamiltonian m e φ a) z (Sum.inr i) =
      e * (∑ j, (partialDerivation i (a j)).val (fun k => z (Sum.inl k)) *
          hamiltonianField (hamiltonian m e φ a) z (Sum.inl j) -
        (partialDerivation i φ).val fun k => z (Sum.inl k)) := by
  simp only [hamiltonianField_inl e φ a hm]
  change ((canonical (Fin d)).bracket (p i) (hamiltonian m e φ a)).val z = _
  rw [canonical_p_hamiltonian e φ a hm, ← lift_real]
  simp only [SmoothRingHom.map_mul, SmoothRingHom.map_sub, SmoothRingHom.map_sum,
    SmoothRingHom.map_algebraMap, lift_ofPosition, velocity, SmoothRingHom.map_relEnergyInv,
    lift_kineticMomentum]
  simp only [lift_real]
  rfl

/-- At every point of the phase space the speed is less than the speed of light. -/
theorem sum_sq_hamiltonianField_lt_one (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) :
    ∑ i, hamiltonianField (hamiltonian m e φ a) z (Sum.inl i) ^ 2 < 1 := by
  simp only [hamiltonianField_inl e φ a hm]
  exact sum_sq_relEnergyInv_mul_lt_one hm _

/-! ### The flow -/

/-- The flow of a charge in a smooth static field is defined for all times and points: the
speed is less than one, and the force is bounded where the position is bounded. -/
theorem flowDomain_hamiltonianField (hm : m ≠ 0) :
    flowDomain (hamiltonianField (hamiltonian m e φ a)) = univ := by
  have hv : ∀ z j, |hamiltonianField (hamiltonian m e φ a) z (Sum.inl j)| ≤ 1 := fun z j => by
    rw [hamiltonianField_inl e φ a hm]
    exact (abs_relEnergyInv_mul_lt_one hm _ j).le
  refine flowDomain_eq_univ_of_bounded_inl (contDiff_hamiltonianField _) hv fun R => ?_
  let G : (Fin d → ℝ) → ℝ := fun x =>
    ∑ k, (∑ j, |(partialDerivation k (a j)).val x| + |(partialDerivation k φ).val x|)
  have hG : Continuous G :=
    continuous_finsetSum _ fun k _ =>
      (continuous_finsetSum _ fun j _ => (contDiff_val _).continuous.abs).add
        (contDiff_val _).continuous.abs
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : Fin d → ℝ) R).exists_bound_of_continuousOn
    hG.continuousOn
  refine ⟨|e| * B, fun z hz k => ?_⟩
  have hR : 0 ≤ R := (abs_nonneg _).trans (hz k)
  have hx : (fun j => z (Sum.inl j)) ∈ Metric.closedBall (0 : Fin d → ℝ) R :=
    mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg hR).mpr fun j => by
      rw [Real.norm_eq_abs]
      exact hz j)
  have hGx : G (fun j => z (Sum.inl j)) ≤ B := (le_abs_self _).trans (hB _ hx)
  rw [hamiltonianField_inr e φ a hm, abs_mul]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg e)
  have hsum : |∑ j, (partialDerivation k (a j)).val (fun i => z (Sum.inl i)) *
      hamiltonianField (hamiltonian m e φ a) z (Sum.inl j)| ≤
      ∑ j, |(partialDerivation k (a j)).val fun i => z (Sum.inl i)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (hv z j)
  have hk : ∑ j, |(partialDerivation k (a j)).val fun i => z (Sum.inl i)| +
      |(partialDerivation k φ).val fun i => z (Sum.inl i)| ≤ G fun j => z (Sum.inl j) :=
    Finset.single_le_sum (f := fun k => ∑ j, |(partialDerivation k (a j)).val
      fun i => z (Sum.inl i)| + |(partialDerivation k φ).val fun i => z (Sum.inl i)|)
      (fun k _ => add_nonneg (Finset.sum_nonneg fun j _ => abs_nonneg _) (abs_nonneg _))
      (Finset.mem_univ k)
  have habs := abs_sub (∑ j, (partialDerivation k (a j)).val (fun i => z (Sum.inl i)) *
      hamiltonianField (hamiltonian m e φ a) z (Sum.inl j))
    ((partialDerivation k φ).val fun i => z (Sum.inl i))
  linarith

/-- Liouville's theorem for a charge in a static field. -/
theorem measurePreserving_hamiltonianFlow (hm : m ≠ 0) (t : ℝ) :
    MeasurePreserving (fun z => flow (hamiltonianField (hamiltonian m e φ a)) (t, z))
      volume volume :=
  Mechanics.measurePreserving_hamiltonianFlow _ (flowDomain_hamiltonianField e φ a hm) t

/-- Through every point of the phase space there is a trajectory for all times. -/
theorem exists_isTrajectory (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) :
    ∃ c : Fin d ⊕ Fin d → TimeFunction,
      IsTrajectory (canonical (Fin d)) (hamiltonian m e φ a) c ∧ realCurve c 0 = z :=
  Mechanics.exists_isTrajectory _ (flowDomain_hamiltonianField e φ a hm) z

end ProjectAinos.Electrodynamics.ChargedParticle
