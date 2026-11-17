/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Hamiltonian
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Uniform fields as static potentials

Two instances of the Hamiltonian of a charge in a static field.

* `uniformScalar E = −E x₀` is the scalar potential of a uniform electric field `E` along the
  first axis (`electricField_uniformScalar`). The other two co-ordinates are cyclic, so their
  momenta are integrals of the motion (`isIntegral_p_uniformScalar`), and the kinetic momentum
  along the field grows at the rate `e E` (`canonical_kineticMomentum_uniformScalar`).
* `landauPotential B = (0, B x₀, 0)` is a vector potential of a uniform magnetic field along
  the third axis (`magneticTensor_landauPotential`). The second and the third co-ordinate are
  cyclic (`isIntegral_p_landauPotential`).

These are the proved instances of `isIntegral_p_of_cyclic`, whose hypotheses are identities in
a free C∞-ring.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Electrodynamics.ChargedParticle

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace

variable {m : ℝ}

/-- The scalar potential `−E x₀` of a uniform electric field along the first axis. -/
def uniformScalar (E : ℝ) : FreeSmoothRing (Fin 3) :=
  algebraMap ℝ (FreeSmoothRing (Fin 3)) (-E) * generator 0

theorem partialDerivation_uniformScalar (E : ℝ) (k : Fin 3) :
    partialDerivation k (uniformScalar E) =
      if k = 0 then algebraMap ℝ (FreeSmoothRing (Fin 3)) (-E) else 0 := by
  rw [uniformScalar, SmoothDerivation.map_algebraMap_mul, partialDerivation_generator,
    smul_eq_mul]
  by_cases hk : k = 0
  · subst hk
    simp only [↓reduceIte, mul_one]
  · simp only [hk, Ne.symm hk, ↓reduceIte, mul_zero]

/-- The electric field of `uniformScalar E` is `E` along the first axis. -/
theorem electricField_uniformScalar (E : ℝ) (k : Fin 3) :
    electricField (uniformScalar E) k =
      if k = 0 then algebraMap ℝ (FreeSmoothRing (Fin 3)) E else 0 := by
  rw [electricField, partialDerivation_uniformScalar]
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte, map_neg, neg_neg]
  · simp only [hk, ↓reduceIte, neg_zero]

/-- In a uniform electric field the momenta across the field are integrals of the motion. -/
theorem isIntegral_p_uniformScalar (hm : m ≠ 0) (e E : ℝ) (k : Fin 2) :
    (canonical (Fin 3)).IsIntegral (hamiltonian m e (uniformScalar E) 0) (p k.succ) :=
  isIntegral_p_of_cyclic e (uniformScalar E) 0 hm
    (by rw [partialDerivation_uniformScalar]; simp only [Fin.succ_ne_zero, ↓reduceIte])
    fun j => by rw [Pi.zero_apply, map_zero]

/-- In a uniform electric field the kinetic momentum along the field grows at the rate
`e E`, and the other components are constant. -/
theorem canonical_kineticMomentum_uniformScalar (hm : m ≠ 0) (e E : ℝ) (k : Fin 3) :
    (canonical (Fin 3)).bracket (kineticMomentum e 0 k) (hamiltonian m e (uniformScalar E) 0) =
      if k = 0 then algebraMap ℝ (PhaseSpace (Fin 3)) (e * E) else 0 := by
  have hF : ∀ j, magneticTensor (0 : Fin 3 → FreeSmoothRing (Fin 3)) k j = 0 := fun j => by
    rw [magneticTensor, Pi.zero_apply, Pi.zero_apply, map_zero, map_zero, sub_zero]
  rw [canonical_kineticMomentum_hamiltonian e (uniformScalar E) 0 hm,
    electricField_uniformScalar]
  simp only [hF, SmoothRingHom.map_zero, zero_mul, Finset.sum_const_zero, add_zero]
  by_cases hk : k = 0
  · simp only [hk, ↓reduceIte, SmoothRingHom.map_algebraMap, ← map_mul]
  · simp only [hk, ↓reduceIte, SmoothRingHom.map_zero, mul_zero]

/-- The vector potential `(0, B x₀, 0)` of a uniform magnetic field along the third axis. -/
def landauPotential (B : ℝ) : Fin 3 → FreeSmoothRing (Fin 3) :=
  ![0, algebraMap ℝ (FreeSmoothRing (Fin 3)) B * generator 0, 0]

theorem partialDerivation_landauPotential_succ (B : ℝ) (k : Fin 2) (j : Fin 3) :
    partialDerivation k.succ (landauPotential B j) = 0 := by
  fin_cases j
  · exact map_zero _
  · change partialDerivation k.succ
      (algebraMap ℝ (FreeSmoothRing (Fin 3)) B * generator 0) = 0
    rw [SmoothDerivation.map_algebraMap_mul,
      partialDerivation_generator_of_ne (Fin.succ_ne_zero k).symm, smul_zero]
  · exact map_zero _

/-- The magnetic field of `landauPotential B` is `F₀₁ = B`. -/
theorem magneticTensor_landauPotential (B : ℝ) :
    magneticTensor (landauPotential B) 0 1 = algebraMap ℝ (FreeSmoothRing (Fin 3)) B := by
  have h1 : partialDerivation (1 : Fin 3) (landauPotential B 0) = 0 := map_zero _
  have h0 : partialDerivation (0 : Fin 3) (landauPotential B 1) =
      algebraMap ℝ (FreeSmoothRing (Fin 3)) B := by
    change partialDerivation (0 : Fin 3)
      (algebraMap ℝ (FreeSmoothRing (Fin 3)) B * generator 0) = _
    rw [SmoothDerivation.map_algebraMap_mul, partialDerivation_generator_self, smul_eq_mul,
      mul_one]
  rw [magneticTensor, h0, h1, sub_zero]

/-- In a uniform magnetic field in this gauge the second and the third momentum are integrals
of the motion. -/
theorem isIntegral_p_landauPotential (hm : m ≠ 0) (e B : ℝ) (k : Fin 2) :
    (canonical (Fin 3)).IsIntegral (hamiltonian m e 0 (landauPotential B)) (p k.succ) :=
  isIntegral_p_of_cyclic e 0 (landauPotential B) hm (map_zero _)
    (partialDerivation_landauPotential_succ B k)

end ProjectAinos.Electrodynamics.ChargedParticle
