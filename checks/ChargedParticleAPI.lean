/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAinos.Electrodynamics.HamiltonianExamples
import ProjectAinos.Electrodynamics.StaticField
import ProjectAinos.Electrodynamics.ConstantFieldExamples

/-! Public consumers of the motion of a charge: functions of the positions on a phase space
and the shift of the momenta by a gradient, the completeness of a flow with bounded velocities,
the motion with a linear equation for the velocity, the Hamiltonian of a charge in a static
field with its equations, integrals, gauge change and flow, the comparison with the action of
space-time on a graph, and the motion in a constant field with the electric, the magnetic, the
null and the parallel case.
Default elaborator options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace ProjectAinos.SmoothAlgebra

open SmoothRing FreeSmoothRing

namespace PhaseSpace

variable {ι : Type*}

example (i : ι) : ofPosition ι (generator i) = q i :=
  ofPosition_generator i

example (z : ι ⊕ ι → ℝ) (f : FreeSmoothRing ι) :
    lift z (ofPosition ι f) = lift (fun i => z (Sum.inl i)) f :=
  lift_ofPosition z f

example {B : Type*} [CommRing B] [Algebra ℝ B] [SmoothRing B] (y : ι ⊕ ι → B)
    (f : FreeSmoothRing ι) :
    lift y (ofPosition ι f) = lift (fun i => y (Sum.inl i)) f :=
  lift_ofPosition y f

example : Function.Injective (ofPosition ι) :=
  ofPosition_injective

variable [Fintype ι] [DecidableEq ι]

example (i : ι) (f : FreeSmoothRing ι) :
    partialDerivation (Sum.inl i) (ofPosition ι f) = ofPosition ι (partialDerivation i f) :=
  partialDerivation_inl_ofPosition i f

example (i : ι) (f : FreeSmoothRing ι) :
    partialDerivation (Sum.inr i) (ofPosition ι f) = 0 :=
  partialDerivation_inr_ofPosition i f

example (f : FreeSmoothRing ι) (H : PhaseSpace ι) :
    (canonical ι).bracket (ofPosition ι f) H =
      ∑ i, ofPosition ι (partialDerivation i f) * partialDerivation (Sum.inr i) H :=
  canonical_ofPosition_bracket f H

example (i : ι) (f : FreeSmoothRing ι) :
    (canonical ι).bracket (p i) (ofPosition ι f) = -ofPosition ι (partialDerivation i f) :=
  canonical_p_ofPosition i f

example (i : ι) (f : FreeSmoothRing ι) :
    (canonical ι).bracket (ofPosition ι f) (p i) = ofPosition ι (partialDerivation i f) :=
  canonical_ofPosition_p i f

example (i : ι) (f : FreeSmoothRing ι) :
    (canonical ι).bracket (q i) (ofPosition ι f) = 0 :=
  canonical_q_ofPosition i f

example (f g : FreeSmoothRing ι) :
    (canonical ι).bracket (ofPosition ι f) (ofPosition ι g) = 0 :=
  canonical_ofPosition_ofPosition f g

omit [Fintype ι] in
example (c : ℝ) (χ : FreeSmoothRing ι) (i : ι) :
    momentumShift c χ (q i) = q i :=
  momentumShift_q c χ i

omit [Fintype ι] in
example (c : ℝ) (χ : FreeSmoothRing ι) (i : ι) :
    momentumShift c χ (p i) =
      p i + algebraMap ℝ (PhaseSpace ι) c * ofPosition ι (partialDerivation i χ) :=
  momentumShift_p c χ i

omit [Fintype ι] in
example (c : ℝ) (χ f : FreeSmoothRing ι) :
    momentumShift c χ (ofPosition ι f) = ofPosition ι f :=
  momentumShift_ofPosition c χ f

example (c : ℝ) (χ : FreeSmoothRing ι) :
    IsPoissonHom (canonical ι).toAlmostPoissonStructure (canonical ι).toAlmostPoissonStructure
      (momentumShift c χ) :=
  isPoissonHom_momentumShift c χ

omit [Fintype ι] in
example (c : ℝ) (χ : FreeSmoothRing ι) (s : PhaseSpace ι) :
    momentumShift (-c) χ (momentumShift c χ s) = s :=
  momentumShift_neg_momentumShift c χ s

end PhaseSpace

end ProjectAinos.SmoothAlgebra

open Set Metric
open scoped ContDiff
namespace ProjectAinos.SmoothGeometry.NonlinearODE

example {ι κ : Type*} [Fintype ι] [Fintype κ]
    {X : (ι ⊕ κ → ℝ) → ι ⊕ κ → ℝ} (hX : ContDiff ℝ ∞ X) {V : ℝ}
    (hV : ∀ z i, |X z (Sum.inl i)| ≤ V)
    (hF : ∀ R : ℝ, ∃ M : ℝ, ∀ z, (∀ i, |z (Sum.inl i)| ≤ R) → ∀ k, |X z (Sum.inr k)| ≤ M) :
    flowDomain X = univ :=
  flowDomain_eq_univ_of_bounded_inl hX hV hF

end ProjectAinos.SmoothGeometry.NonlinearODE

open Set
open scoped ContDiff
namespace ProjectAinos.SmoothGeometry.LinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

example (A : E →L[ℝ] E) (u₀ : E) : linearVelocity A u₀ 0 = u₀ :=
  linearVelocity_zero A u₀

example (A : E →L[ℝ] E) (u₀ : E) (τ : ℝ) :
    HasDerivAt (linearVelocity A u₀) (A (linearVelocity A u₀ τ)) τ :=
  hasDerivAt_linearVelocity A u₀ τ

example (A : E →L[ℝ] E) (u₀ : E) :
    ContDiff ℝ ∞ (linearVelocity A u₀) :=
  contDiff_linearVelocity A u₀

example (A : E →L[ℝ] E) {f : ℝ → E}
    (hf : ∀ r, HasDerivAt f (A (f r)) r) (τ : ℝ) : f τ = linearVelocity A (f 0) τ :=
  eq_linearVelocity_of_hasDerivAt A hf τ

example (A : E →L[ℝ] E) (x₀ u₀ : E) : linearMotion A x₀ u₀ 0 = x₀ :=
  linearMotion_zero A x₀ u₀

example (A : E →L[ℝ] E) (x₀ u₀ : E) (τ : ℝ) :
    HasDerivAt (linearMotion A x₀ u₀) (linearVelocity A u₀ τ) τ :=
  hasDerivAt_linearMotion A x₀ u₀ τ

example (A : E →L[ℝ] E) (x₀ u₀ : E) :
    deriv (linearMotion A x₀ u₀) = linearVelocity A u₀ :=
  deriv_linearMotion A x₀ u₀

example (A : E →L[ℝ] E) (x₀ u₀ : E) :
    ContDiff ℝ ∞ (linearMotion A x₀ u₀) :=
  contDiff_linearMotion A x₀ u₀

section Cube

variable {A : E →L[ℝ] E} {κ : ℝ} {s c C : ℝ → ℝ}

example (hA : ∀ v, A (A (A v)) = κ • A v)
    (hs : ∀ τ, HasDerivAt s (1 + κ * c τ) τ) (hc : ∀ τ, HasDerivAt c (s τ) τ)
    (hs0 : s 0 = 0) (hc0 : c 0 = 0) (u₀ : E) (τ : ℝ) :
    linearVelocity A u₀ τ = u₀ + s τ • A u₀ + c τ • A (A u₀) :=
  linearVelocity_eq_of_cube hA hs hc hs0 hc0 u₀ τ

example (hA : ∀ v, A (A (A v)) = κ • A v)
    (hs : ∀ τ, HasDerivAt s (1 + κ * c τ) τ) (hc : ∀ τ, HasDerivAt c (s τ) τ)
    (hs0 : s 0 = 0) (hc0 : c 0 = 0) (hC : ∀ τ, HasDerivAt C (c τ) τ) (hC0 : C 0 = 0)
    (x₀ u₀ : E) (τ : ℝ) :
    linearMotion A x₀ u₀ τ = x₀ + τ • u₀ + c τ • A u₀ + C τ • A (A u₀) :=
  linearMotion_eq_of_cube hA hs hc hs0 hc0 hC hC0 x₀ u₀ τ

end Cube

example {A₁ A₂ : E →L[ℝ] E} (h12 : ∀ v, A₁ (A₂ v) = 0)
    (h21 : ∀ v, A₂ (A₁ v) = 0) (u₀ : E) (τ : ℝ) :
    linearVelocity (A₁ + A₂) u₀ τ =
      linearVelocity A₁ u₀ τ + linearVelocity A₂ u₀ τ - u₀ :=
  linearVelocity_add h12 h21 u₀ τ

end ProjectAinos.SmoothGeometry.LinearODE

namespace ProjectAinos.SmoothAlgebra

example {P : Type*} [CommRing P] [Algebra ℝ P]
    [SmoothRing P] (ρ : AlmostPoissonStructure P) {m : ℝ} (hm : m ≠ 0) {d : ℕ} (g : P)
    (w : Fin d → P) :
    ρ.bracket g (relEnergy m w) = relEnergyInv m w * ∑ j, w j * ρ.bracket g (w j) :=
  AlmostPoissonStructure.bracket_relEnergy_right ρ hm g w

end ProjectAinos.SmoothAlgebra

namespace ProjectAinos.Electrodynamics.ChargedParticle

open Set MeasureTheory

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics

open SmoothGeometry SmoothGeometry.NonlinearODE

variable {d : ℕ} {m : ℝ}

example (a : Fin d → FreeSmoothRing (Fin d)) (i j : Fin d) :
    magneticTensor a i j = -magneticTensor a j i :=
  magneticTensor_antisymm a i j

example (a : Fin d → FreeSmoothRing (Fin d)) (i : Fin d) :
    magneticTensor a i i = 0 :=
  magneticTensor_self a i

example (a : Fin d → FreeSmoothRing (Fin d))
    (χ : FreeSmoothRing (Fin d)) (i j : Fin d) :
    magneticTensor (gaugeShift a χ) i j = magneticTensor a i j :=
  magneticTensor_gaugeShift a χ i j

variable (e : ℝ) (φ : FreeSmoothRing (Fin d)) (a : Fin d → FreeSmoothRing (Fin d))

example (m : ℝ) :
    hamiltonian m 0 φ a = relEnergy m (p : Fin d → PhaseSpace (Fin d)) :=
  hamiltonian_zero_charge φ a m

example (i j : Fin d) :
    (canonical (Fin d)).bracket (q i) (kineticMomentum e a j) = if i = j then 1 else 0 :=
  canonical_q_kineticMomentum e a i j

example (i j : Fin d) :
    (canonical (Fin d)).bracket (p i) (kineticMomentum e a j) =
      algebraMap ℝ (PhaseSpace (Fin d)) e * ofPosition (Fin d) (partialDerivation i (a j)) :=
  canonical_p_kineticMomentum e a i j

example (i : Fin d) (f : FreeSmoothRing (Fin d)) :
    (canonical (Fin d)).bracket (kineticMomentum e a i) (ofPosition (Fin d) f) =
      -ofPosition (Fin d) (partialDerivation i f) :=
  canonical_kineticMomentum_ofPosition e a i f

example (i j : Fin d) :
    (canonical (Fin d)).bracket (kineticMomentum e a i) (kineticMomentum e a j) =
      algebraMap ℝ (PhaseSpace (Fin d)) e * ofPosition (Fin d) (magneticTensor a i j) :=
  canonical_kineticMomentum_kineticMomentum e a i j

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (q i) (hamiltonian m e φ a) = velocity m e a i :=
  canonical_q_hamiltonian e φ a hm i

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (p i) (hamiltonian m e φ a) =
      algebraMap ℝ (PhaseSpace (Fin d)) e *
        (∑ j, ofPosition (Fin d) (partialDerivation i (a j)) * velocity m e a j -
          ofPosition (Fin d) (partialDerivation i φ)) :=
  canonical_p_hamiltonian e φ a hm i

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (kineticMomentum e a i) (hamiltonian m e φ a) =
      algebraMap ℝ (PhaseSpace (Fin d)) e * (ofPosition (Fin d) (electricField φ i) +
        ∑ j, ofPosition (Fin d) (magneticTensor a i j) * velocity m e a j) :=
  canonical_kineticMomentum_hamiltonian e φ a hm i

example (hm : m ≠ 0) :
    (canonical (Fin d)).bracket (relEnergy m (kineticMomentum e a)) (hamiltonian m e φ a) =
      algebraMap ℝ (PhaseSpace (Fin d)) e *
        ∑ i, ofPosition (Fin d) (electricField φ i) * velocity m e a i :=
  canonical_kineticEnergy_hamiltonian e φ a hm

example (hm : m ≠ 0) :
    ∑ i, velocity m e a i * velocity m e a i =
      1 - algebraMap ℝ (PhaseSpace (Fin d)) (m ^ 2) *
        (relEnergyInv m (kineticMomentum e a) * relEnergyInv m (kineticMomentum e a)) :=
  sum_velocity_mul_self e a hm

example (m : ℝ) :
    (canonical (Fin d)).IsIntegral (hamiltonian m e φ a) (hamiltonian m e φ a) :=
  isIntegral_hamiltonian e φ a m

example (hm : m ≠ 0) {k : Fin d} (hφ : partialDerivation k φ = 0)
    (ha : ∀ j, partialDerivation k (a j) = 0) :
    (canonical (Fin d)).IsIntegral (hamiltonian m e φ a) (p k) :=
  isIntegral_p_of_cyclic e φ a hm hφ ha

example (χ : FreeSmoothRing (Fin d)) (i : Fin d) :
    momentumShift e χ (kineticMomentum e (gaugeShift a χ) i) = kineticMomentum e a i :=
  momentumShift_kineticMomentum e a χ i

example (m : ℝ) (χ : FreeSmoothRing (Fin d)) :
    momentumShift e χ (hamiltonian m e φ (gaugeShift a χ)) = hamiltonian m e φ a :=
  momentumShift_hamiltonian e φ a m χ

example {c : Fin d ⊕ Fin d → TimeFunction}
    (h : IsTrajectory (canonical (Fin d)) (hamiltonian m e φ a) c) (χ : FreeSmoothRing (Fin d)) :
    IsTrajectory (canonical (Fin d)) (hamiltonian m e φ (gaugeShift a χ))
      fun s => FreeSmoothRing.lift c (momentumShift e χ (generator s)) :=
  isTrajectory_gaugeShift e φ a h χ

example (hm : m ≠ 0) {c : Fin d ⊕ Fin d → TimeFunction}
    (h : IsTrajectory (canonical (Fin d)) (hamiltonian m e φ a) c) (i : Fin d) :
    timeDerivative (c (Sum.inl i)) = FreeSmoothRing.lift c (velocity m e a i) :=
  timeDerivative_q e φ a hm h i

example (hm : m ≠ 0) {c : Fin d ⊕ Fin d → TimeFunction}
    (h : IsTrajectory (canonical (Fin d)) (hamiltonian m e φ a) c) (i : Fin d) :
    timeDerivative (FreeSmoothRing.lift c (kineticMomentum e a i)) =
      FreeSmoothRing.lift c (algebraMap ℝ (PhaseSpace (Fin d)) e *
        (ofPosition (Fin d) (electricField φ i) +
          ∑ j, ofPosition (Fin d) (magneticTensor a i j) * velocity m e a j)) :=
  timeDerivative_kineticMomentum e φ a hm h i

example (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (p i) (hamiltonian m e φ a) =
      (canonical (Fin d)).bracket (kineticMomentum e a i) (hamiltonian m e φ a) +
        algebraMap ℝ (PhaseSpace (Fin d)) e *
          ∑ j, ofPosition (Fin d) (partialDerivation j (a i)) * velocity m e a j :=
  canonical_p_hamiltonian_eq e φ a hm i

example (c : Fin d ⊕ Fin d → TimeFunction) (i : Fin d) :
    timeDerivative (c (Sum.inr i)) =
      timeDerivative (FreeSmoothRing.lift c (kineticMomentum e a i)) +
        algebraMap ℝ TimeFunction e * ∑ j, FreeSmoothRing.lift c
          (ofPosition (Fin d) (partialDerivation j (a i))) * timeDerivative (c (Sum.inl j)) :=
  timeDerivative_p_eq e a c i

example (hm : m ≠ 0) (c : Fin d ⊕ Fin d → TimeFunction) :
    IsTrajectory (canonical (Fin d)) (hamiltonian m e φ a) c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) = FreeSmoothRing.lift c (velocity m e a i)) ∧
      ∀ i, timeDerivative (FreeSmoothRing.lift c (kineticMomentum e a i)) =
        FreeSmoothRing.lift c (algebraMap ℝ (PhaseSpace (Fin d)) e *
          (ofPosition (Fin d) (electricField φ i) +
            ∑ j, ofPosition (Fin d) (magneticTensor a i j) * velocity m e a j)) :=
  isTrajectory_iff_lorentzForce e φ a hm c

example (z : Fin d ⊕ Fin d → ℝ) (i : Fin d) :
    FreeSmoothRing.lift z (kineticMomentum e a i) = realKineticMomentum e a z i :=
  lift_kineticMomentum e a z i

example (m : ℝ) (z : Fin d ⊕ Fin d → ℝ) :
    FreeSmoothRing.lift z (hamiltonian m e φ a) =
      relEnergy m (realKineticMomentum e a z) + e * φ.val fun j => z (Sum.inl j) :=
  lift_hamiltonian e φ a m z

example (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) (i : Fin d) :
    hamiltonianField (hamiltonian m e φ a) z (Sum.inl i) =
      relEnergyInv m (realKineticMomentum e a z) * realKineticMomentum e a z i :=
  hamiltonianField_inl e φ a hm z i

example (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) (i : Fin d) :
    hamiltonianField (hamiltonian m e φ a) z (Sum.inr i) =
      e * (∑ j, (partialDerivation i (a j)).val (fun k => z (Sum.inl k)) *
          hamiltonianField (hamiltonian m e φ a) z (Sum.inl j) -
        (partialDerivation i φ).val fun k => z (Sum.inl k)) :=
  hamiltonianField_inr e φ a hm z i

example (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) :
    ∑ i, hamiltonianField (hamiltonian m e φ a) z (Sum.inl i) ^ 2 < 1 :=
  sum_sq_hamiltonianField_lt_one e φ a hm z

example (hm : m ≠ 0) :
    flowDomain (hamiltonianField (hamiltonian m e φ a)) = univ :=
  flowDomain_hamiltonianField e φ a hm

example (hm : m ≠ 0) (t : ℝ) :
    MeasurePreserving (fun z => flow (hamiltonianField (hamiltonian m e φ a)) (t, z))
      volume volume :=
  measurePreserving_hamiltonianFlow e φ a hm t

example (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) :
    ∃ c : Fin d ⊕ Fin d → TimeFunction,
      IsTrajectory (canonical (Fin d)) (hamiltonian m e φ a) c ∧ realCurve c 0 = z :=
  exists_isTrajectory e φ a hm z

end ProjectAinos.Electrodynamics.ChargedParticle

namespace ProjectAinos.Electrodynamics.ChargedParticle

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace

variable {m : ℝ}

example (E : ℝ) (k : Fin 3) :
    partialDerivation k (uniformScalar E) =
      if k = 0 then algebraMap ℝ (FreeSmoothRing (Fin 3)) (-E) else 0 :=
  partialDerivation_uniformScalar E k

example (E : ℝ) (k : Fin 3) :
    electricField (uniformScalar E) k =
      if k = 0 then algebraMap ℝ (FreeSmoothRing (Fin 3)) E else 0 :=
  electricField_uniformScalar E k

example (hm : m ≠ 0) (e E : ℝ) (k : Fin 2) :
    (canonical (Fin 3)).IsIntegral (hamiltonian m e (uniformScalar E) 0) (p k.succ) :=
  isIntegral_p_uniformScalar hm e E k

example (hm : m ≠ 0) (e E : ℝ) (k : Fin 3) :
    (canonical (Fin 3)).bracket (kineticMomentum e 0 k) (hamiltonian m e (uniformScalar E) 0) =
      if k = 0 then algebraMap ℝ (PhaseSpace (Fin 3)) (e * E) else 0 :=
  canonical_kineticMomentum_uniformScalar hm e E k

example (B : ℝ) (k : Fin 2) (j : Fin 3) :
    partialDerivation k.succ (landauPotential B j) = 0 :=
  partialDerivation_landauPotential_succ B k j

example (B : ℝ) :
    magneticTensor (landauPotential B) 0 1 = algebraMap ℝ (FreeSmoothRing (Fin 3)) B :=
  magneticTensor_landauPotential B

example (hm : m ≠ 0) (e B : ℝ) (k : Fin 2) :
    (canonical (Fin 3)).IsIntegral (hamiltonian m e 0 (landauPotential B)) (p k.succ) :=
  isIntegral_p_landauPotential hm e B k

end ProjectAinos.Electrodynamics.ChargedParticle

open Set Filter
open scoped Topology ContDiff
namespace ProjectAinos.Electrodynamics.ChargedParticle

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics

open SmoothGeometry SmoothGeometry.Minkowski SpecialRelativity SpecialRelativity.FreeParticle

variable {m e : ℝ} (φ : FreeSmoothRing (Fin 3)) (a : Fin 3 → FreeSmoothRing (Fin 3))

example (x : Spacetime) (i : Fin 3) :
    spaceCoordinates x i = x i.succ :=
  spaceCoordinates_apply x i

example (τ : ℝ) (w : Fin 3 → ℝ) :
    spaceCoordinates (Fin.cons τ w : Spacetime) = w :=
  spaceCoordinates_cons τ w

example (x w : Spacetime) :
    oneCovector (staticPotential φ a x) w =
      -φ.val (spaceCoordinates x) * w 0 + ∑ i, (a i).val (spaceCoordinates x) * w i.succ :=
  staticPotential_apply φ a x w

example : ContDiff ℝ ∞ (staticPotential φ a) :=
  contDiff_staticPotential φ a

example (f : FreeSmoothRing (Fin 3)) (x : Spacetime) :
    HasFDerivAt (fun y : Spacetime => f.val (spaceCoordinates y))
      ((fderiv ℝ (f.val : (Fin 3 → ℝ) → ℝ) (spaceCoordinates x)).comp spaceCoordinates) x :=
  hasFDerivAt_val_spaceCoordinates f x

example (f : FreeSmoothRing (Fin 3)) (x v : Spacetime) :
    ((fderiv ℝ (f.val : (Fin 3 → ℝ) → ℝ) (spaceCoordinates x)).comp spaceCoordinates) v =
      spaceDerivative f x v :=
  comp_spaceCoordinates_apply f x v

example {A : Potential} {x : Spacetime} (hA : DifferentiableAt ℝ A x)
    (v w : Spacetime) :
    oneCovector (fderiv ℝ A x v) w = fderiv ℝ (fun y => oneCovector (A y) w) x v :=
  oneCovector_fderiv_apply hA v w

example (x v w : Spacetime) :
    oneCovector (fderiv ℝ (staticPotential φ a) x v) w =
      -(w 0 * spaceDerivative φ x v) + ∑ i, w i.succ * spaceDerivative (a i) x v :=
  fderiv_staticPotential_apply φ a x v w

example (x v w : Spacetime) :
    fieldTensor (staticPotential φ a) x ![v, w] =
      v 0 * spaceDerivative φ x w - w 0 * spaceDerivative φ x v +
        ∑ i, (w i.succ * spaceDerivative (a i) x v - v i.succ * spaceDerivative (a i) x w) :=
  fieldTensor_staticPotential φ a x v w

example (f : FreeSmoothRing (Fin 3)) (x : Spacetime) (k : Fin 3) :
    spaceDerivative f x (Pi.single k.succ 1) =
      (partialDerivation k f).val (spaceCoordinates x) :=
  spaceDerivative_single_succ f x k

example (f : FreeSmoothRing (Fin 3)) (x : Spacetime) :
    spaceDerivative f x (Pi.single 0 1) = 0 :=
  spaceDerivative_single_zero f x

example (f : FreeSmoothRing (Fin 3)) (x : Spacetime) (τ : ℝ)
    (u : Fin 3 → ℝ) :
    spaceDerivative f x (Fin.cons τ u) =
      ∑ j, (partialDerivation j f).val (spaceCoordinates x) * u j :=
  spaceDerivative_cons f x τ u

example (e : ℝ) (F : TwoForm) (v : Spacetime) (k : Fin 3) :
    lorentzForce e F v k.succ = -e * F ![v, Pi.single k.succ 1] :=
  lorentzForce_succ e F v k

example (e : ℝ) (F : TwoForm) (v : Spacetime) :
    lorentzForce e F v 0 = e * F ![v, Pi.single 0 1] :=
  lorentzForce_zero e F v

example (k : Fin 3) (y : Fin 3 → ℝ) :
    (electricField φ k).val y = -(partialDerivation k φ).val y :=
  val_electricField φ k y

example (k j : Fin 3) (y : Fin 3 → ℝ) :
    (magneticTensor a k j).val y =
      (partialDerivation k (a j)).val y - (partialDerivation j (a k)).val y :=
  val_magneticTensor a k j y

example (e : ℝ) (x : Spacetime) (u : Fin 3 → ℝ) (k : Fin 3) :
    lorentzForce e (fieldTensor (staticPotential φ a) x) (Fin.cons 1 u) k.succ =
      e * ((electricField φ k).val (spaceCoordinates x) +
        ∑ j, (magneticTensor a k j).val (spaceCoordinates x) * u j) :=
  lorentzForce_staticPotential_succ φ a e x u k

example (e : ℝ) (x : Spacetime) (u : Fin 3 → ℝ) :
    lorentzForce e (fieldTensor (staticPotential φ a) x) (Fin.cons 1 u) 0 =
      e * ∑ j, (electricField φ j).val (spaceCoordinates x) * u j :=
  lorentzForce_staticPotential_zero φ a e x u

example {w : Spacetime} {u : Fin 3 → ℝ}
    (h : minkowskiForm .timeNegative 3 w (Fin.cons 1 u) = 0) : w 0 = ∑ k, w k.succ * u k :=
  time_eq_of_minkowskiForm_cons_eq_zero h

variable {x : ℝ → Fin 3 → ℝ} {t₀ t₁ : ℝ}

example (m : ℝ) (hx : Differentiable ℝ x) (s : ℝ) (k : Fin 3) :
    m * fourVelocity (deriv (graph x) s) k.succ = legendre m (deriv x s) k :=
  mul_fourVelocity_graph_succ m hx s k

example (m e : ℝ) (h01 : t₀ < t₁) (hx : ContDiff ℝ 2 x)
    (hv : ∀ t ∈ Icc t₀ t₁, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary t₀ t₁ (chargedLagrangian m e (staticPotential φ a)) (graph x) ↔
      ∀ t ∈ Ioo t₀ t₁, ∀ k, deriv (fun s => legendre m (deriv x s) k) t =
        e * ((electricField φ k).val (x t) +
          ∑ j, (magneticTensor a k j).val (x t) * deriv x t j) :=
  stationary_graph_iff_lorentzForce φ a m e h01 hx hv

example (m e : ℝ) (x : ℝ → Fin 3 → ℝ) (s : ℝ) :
    realKineticMomentum e a (phaseCurve m e a x s) = legendre m (deriv x s) :=
  realKineticMomentum_phaseCurve a m e x s

example (f : FreeSmoothRing (Fin 3)) (hx : Differentiable ℝ x) (t : ℝ) :
    HasDerivAt (fun s => f.val (x s))
      (∑ j, (partialDerivation j f).val (x t) * deriv x t j) t :=
  hasDerivAt_val_comp f hx t

example (hm : 0 < m) (e : ℝ) (h01 : t₀ < t₁)
    (hx : ContDiff ℝ 2 x) (hv : ∀ t ∈ Icc t₀ t₁, ∑ i, deriv x t i ^ 2 < 1) :
    Stationary t₀ t₁ (chargedLagrangian m e (staticPotential φ a)) (graph x) ↔
      ∀ t ∈ Ioo t₀ t₁, HasDerivAt (phaseCurve m e a x)
        (hamiltonianField (hamiltonian m e φ a) (phaseCurve m e a x t)) t :=
  stationary_graph_iff_hamilton φ a hm e h01 hx hv

example (hm : 0 < m) (e : ℝ)
    {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory (canonical (Fin 3)) (hamiltonian m e φ a) c) (h01 : t₀ < t₁) :
    Stationary t₀ t₁ (chargedLagrangian m e (staticPotential φ a))
      (graph fun s i => realCurve c s (Sum.inl i)) :=
  stationary_graph_of_isTrajectory φ a hm e h h01

end ProjectAinos.Electrodynamics.ChargedParticle

open Set
open scoped ContDiff
namespace ProjectAinos.SpecialRelativity

open SmoothGeometry SmoothGeometry.Minkowski

variable {d : ℕ}

example (σ : LorentzConvention) (α β : MinkowskiModel d →L[ℝ] ℝ)
    (v : MinkowskiModel d) :
    lorentzGenerator σ α β v = α v • sharp σ β - β v • sharp σ α :=
  lorentzGenerator_apply σ α β v

example (σ : LorentzConvention) (α β : MinkowskiModel d →L[ℝ] ℝ) :
    β (sharp σ α) = α (sharp σ β) :=
  covector_sharp_comm σ α β

example (σ : LorentzConvention) (α β : MinkowskiModel d →L[ℝ] ℝ)
    (v : MinkowskiModel d) :
    lorentzGenerator σ α β (lorentzGenerator σ α β (lorentzGenerator σ α β v)) =
      generatorInvariant σ α β • lorentzGenerator σ α β v :=
  lorentzGenerator_cube σ α β v

end ProjectAinos.SpecialRelativity

namespace ProjectAinos.Electrodynamics.ConstantField

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.LinearODE SpecialRelativity Mechanics

variable {m e : ℝ} (F : TwoForm)

example (x : Spacetime) : fieldTensor (potential F) x = F :=
  fieldTensor_potential F x

example (e : ℝ) (v : Spacetime) :
    forceMap e F v = lorentzForce e F v :=
  forceMap_apply F e v

example (m e : ℝ) (v : Spacetime) :
    generator m e F v = m⁻¹ • lorentzForce e F v :=
  generator_apply F m e v

example (m e : ℝ) (u₀ : Spacetime) : velocity m e F u₀ 0 = u₀ :=
  velocity_zero F m e u₀

example (m e : ℝ) (x₀ u₀ : Spacetime) : motion m e F x₀ u₀ 0 = x₀ :=
  motion_zero F m e x₀ u₀

example (m e : ℝ) (u₀ : Spacetime) (τ : ℝ) :
    HasDerivAt (velocity m e F u₀) (m⁻¹ • lorentzForce e F (velocity m e F u₀ τ)) τ :=
  hasDerivAt_velocity F m e u₀ τ

example (m e : ℝ) (x₀ u₀ : Spacetime) (τ : ℝ) :
    HasDerivAt (motion m e F x₀ u₀) (velocity m e F u₀ τ) τ :=
  hasDerivAt_motion F m e x₀ u₀ τ

example (m e : ℝ) (x₀ u₀ : Spacetime) :
    deriv (motion m e F x₀ u₀) = velocity m e F u₀ :=
  deriv_motion F m e x₀ u₀

example (m e : ℝ) (x₀ u₀ : Spacetime) : ContDiff ℝ ∞ (motion m e F x₀ u₀) :=
  contDiff_motion F m e x₀ u₀

example (m e : ℝ) (u₀ : Spacetime) : ContDiff ℝ ∞ (velocity m e F u₀) :=
  contDiff_velocity F m e u₀

example (e : ℝ) (v : Spacetime) : pair (lorentzForce e F v) v = 0 :=
  pair_lorentzForce F e v

example (m e : ℝ) (u₀ : Spacetime) (τ : ℝ) :
    intervalQuadratic (velocity m e F u₀ τ) = intervalQuadratic u₀ :=
  intervalQuadratic_velocity F m e u₀ τ

example (m e : ℝ) {u₀ : Spacetime} (hu : FutureTimelike u₀) (τ : ℝ) :
    FutureTimelike (velocity m e F u₀ τ) :=
  futureTimelike_velocity F m e hu τ

example (hm : m ≠ 0) (e : ℝ) (x₀ : Spacetime) {u₀ : Spacetime}
    (hu : intervalQuadratic u₀ = 1) {a b : ℝ} (hab : a < b) :
    Stationary a b (chargedLagrangian m e (potential F)) (motion m e F x₀ u₀) :=
  stationary_motion F hm e x₀ hu hab

example (hm : m ≠ 0) (e : ℝ) {γ : ℝ → Spacetime} {a b : ℝ}
    (hab : a < b) (hγ : ContDiff ℝ 2 γ)
    (hunit : ∀ t ∈ Icc a b, intervalQuadratic (deriv γ t) = 1)
    (hs : Stationary a b (chargedLagrangian m e (potential F)) γ) {t : ℝ} (ht : t ∈ Icc a b) :
    deriv γ t = velocity m e F (deriv γ a) (t - a) :=
  deriv_eq_velocity_of_stationary F hm e hab hγ hunit hs ht

variable {F} {α β : FourCovector}

example (h : IsSimple F α β) (m e : ℝ) (v : Spacetime) :
    generator m e F v = (-(e / m)) • lorentzGenerator .timeNegative α β v :=
  generator_of_isSimple h m e v

example (h : IsSimple F α β) (m e : ℝ) (v : Spacetime) :
    generator m e F (generator m e F (generator m e F v)) =
      ((e / m) ^ 2 * generatorInvariant .timeNegative α β) • generator m e F v :=
  generator_cube h m e v

example {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => Real.sinh (Ω * t) / Ω)
      (1 + Ω ^ 2 * ((Real.cosh (Ω * τ) - 1) / Ω ^ 2)) τ :=
  hasDerivAt_sinh_div hΩ τ

example {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => (Real.cosh (Ω * t) - 1) / Ω ^ 2) (Real.sinh (Ω * τ) / Ω) τ :=
  hasDerivAt_cosh_sub_div hΩ τ

example {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => (Real.sinh (Ω * t) - Ω * t) / Ω ^ 3)
      ((Real.cosh (Ω * τ) - 1) / Ω ^ 2) τ :=
  hasDerivAt_sinh_sub_div hΩ τ

example {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => Real.sin (Ω * t) / Ω)
      (1 + -Ω ^ 2 * ((1 - Real.cos (Ω * τ)) / Ω ^ 2)) τ :=
  hasDerivAt_sin_div hΩ τ

example {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => (1 - Real.cos (Ω * t)) / Ω ^ 2) (Real.sin (Ω * τ) / Ω) τ :=
  hasDerivAt_one_sub_cos_div hΩ τ

example {Ω : ℝ} (hΩ : Ω ≠ 0) (τ : ℝ) :
    HasDerivAt (fun t => (Ω * t - Real.sin (Ω * t)) / Ω ^ 3)
      ((1 - Real.cos (Ω * τ)) / Ω ^ 2) τ :=
  hasDerivAt_sub_sin_div hΩ τ

variable (h : IsSimple F α β) {Ω : ℝ}

include h in
example (hΩ : Ω ≠ 0)
    (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = Ω ^ 2) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + (Real.sinh (Ω * τ) / Ω) • generator m e F u₀ +
      ((Real.cosh (Ω * τ) - 1) / Ω ^ 2) • generator m e F (generator m e F u₀) :=
  velocity_of_pos h hΩ hκ u₀ τ

include h in
example (hΩ : Ω ≠ 0)
    (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = Ω ^ 2) (x₀ u₀ : Spacetime)
    (τ : ℝ) :
    motion m e F x₀ u₀ τ = x₀ + τ • u₀ +
      ((Real.cosh (Ω * τ) - 1) / Ω ^ 2) • generator m e F u₀ +
      ((Real.sinh (Ω * τ) - Ω * τ) / Ω ^ 3) • generator m e F (generator m e F u₀) :=
  motion_of_pos h hΩ hκ x₀ u₀ τ

include h in
example (hΩ : Ω ≠ 0)
    (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = -Ω ^ 2) (u₀ : Spacetime)
    (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + (Real.sin (Ω * τ) / Ω) • generator m e F u₀ +
      ((1 - Real.cos (Ω * τ)) / Ω ^ 2) • generator m e F (generator m e F u₀) :=
  velocity_of_neg h hΩ hκ u₀ τ

include h in
example (hΩ : Ω ≠ 0)
    (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = -Ω ^ 2) (x₀ u₀ : Spacetime)
    (τ : ℝ) :
    motion m e F x₀ u₀ τ = x₀ + τ • u₀ +
      ((1 - Real.cos (Ω * τ)) / Ω ^ 2) • generator m e F u₀ +
      ((Ω * τ - Real.sin (Ω * τ)) / Ω ^ 3) • generator m e F (generator m e F u₀) :=
  motion_of_neg h hΩ hκ x₀ u₀ τ

include h in
example (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = 0)
    (u₀ : Spacetime) (τ : ℝ) :
    velocity m e F u₀ τ = u₀ + τ • generator m e F u₀ +
      (τ ^ 2 / 2) • generator m e F (generator m e F u₀) :=
  velocity_of_zero h hκ u₀ τ

include h in
example (hκ : (e / m) ^ 2 * generatorInvariant .timeNegative α β = 0)
    (x₀ u₀ : Spacetime) (τ : ℝ) :
    motion m e F x₀ u₀ τ = x₀ + τ • u₀ + (τ ^ 2 / 2) • generator m e F u₀ +
      (τ ^ 3 / 6) • generator m e F (generator m e F u₀) :=
  motion_of_zero h hκ x₀ u₀ τ

omit h in
example (m e : ℝ) (F₁ F₂ : TwoForm) :
    generator m e (F₁ + F₂) = generator m e F₁ + generator m e F₂ :=
  generator_add m e F₁ F₂

example (m e : ℝ) {F₁ F₂ : TwoForm}
    (h12 : ∀ v, generator m e F₁ (generator m e F₂ v) = 0)
    (h21 : ∀ v, generator m e F₂ (generator m e F₁ v) = 0) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (F₁ + F₂) u₀ τ = velocity m e F₁ u₀ τ + velocity m e F₂ u₀ τ - u₀ :=
  velocity_add m e h12 h21 u₀ τ

end ProjectAinos.Electrodynamics.ConstantField

namespace ProjectAinos.Electrodynamics.ConstantField

open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

open Examples

example (μ : Fin 4) (v : Spacetime) :
    coordinateCovector μ v = v μ :=
  coordinateCovector_apply μ v

example (E : ℝ) :
    IsSimple (uniformField E 0) (coordinateCovector 0) (-E • coordinateCovector 1) :=
  isSimple_electric E

example (E : ℝ) :
    generatorInvariant .timeNegative (coordinateCovector 0) (-E • coordinateCovector 1) =
      E ^ 2 :=
  generatorInvariant_electric E

example {m e E : ℝ} (hΩ : e * E / m ≠ 0) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (uniformField E 0) u₀ τ =
      u₀ + (Real.sinh (e * E / m * τ) / (e * E / m)) • generator m e (uniformField E 0) u₀ +
        ((Real.cosh (e * E / m * τ) - 1) / (e * E / m) ^ 2) •
          generator m e (uniformField E 0) (generator m e (uniformField E 0) u₀) :=
  velocity_electric hΩ u₀ τ

example (B : ℝ) :
    IsSimple (uniformField 0 B) (coordinateCovector 2) (B • coordinateCovector 3) :=
  isSimple_magnetic B

example (B : ℝ) :
    generatorInvariant .timeNegative (coordinateCovector 2) (B • coordinateCovector 3) =
      -B ^ 2 :=
  generatorInvariant_magnetic B

example {m e B : ℝ} (hΩ : e * B / m ≠ 0) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (uniformField 0 B) u₀ τ =
      u₀ + (Real.sin (e * B / m * τ) / (e * B / m)) • generator m e (uniformField 0 B) u₀ +
        ((1 - Real.cos (e * B / m * τ)) / (e * B / m) ^ 2) •
          generator m e (uniformField 0 B) (generator m e (uniformField 0 B) u₀) :=
  velocity_magnetic hΩ u₀ τ

example (E : ℝ) :
    IsSimple (nullField E) (coordinateCovector 0 - coordinateCovector 2)
      (E • coordinateCovector 1) :=
  isSimple_nullField E

example (E : ℝ) :
    generatorInvariant .timeNegative (coordinateCovector 0 - coordinateCovector 2)
      (E • coordinateCovector 1) = 0 :=
  generatorInvariant_nullField E

example {E : ℝ} (hE : E ≠ 0) : nullField E ≠ 0 :=
  nullField_ne_zero hE

example (m e E : ℝ) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (nullField E) u₀ τ = u₀ + τ • generator m e (nullField E) u₀ +
      (τ ^ 2 / 2) • generator m e (nullField E) (generator m e (nullField E) u₀) :=
  velocity_nullField m e E u₀ τ

example (E B : ℝ) :
    uniformField E B = uniformField E 0 + uniformField 0 B :=
  uniformField_eq_add E B

example (m e E : ℝ) (v : Spacetime) :
    generator m e (uniformField E 0) v = (e * E / m) • ![v 1, v 0, 0, 0] :=
  generator_electric_apply m e E v

example (m e B : ℝ) (v : Spacetime) :
    generator m e (uniformField 0 B) v = (e * B / m) • ![0, 0, v 3, -v 2] :=
  generator_magnetic_apply m e B v

example (m e E B : ℝ) (u₀ : Spacetime) (τ : ℝ) :
    velocity m e (uniformField E B) u₀ τ =
      velocity m e (uniformField E 0) u₀ τ + velocity m e (uniformField 0 B) u₀ τ - u₀ :=
  velocity_uniformField m e E B u₀ τ

example (τ : ℝ) :
    motion 1 1 (uniformField 1 0) (hyperbola 0) (hyperbolaVelocity 0) τ = hyperbola τ :=
  motion_eq_hyperbola τ

end ProjectAinos.Electrodynamics.ConstantField
