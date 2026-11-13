/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Poisson.Canonical
import Mathlib.Tactic.Ring

/-!
# The virial identity

On the canonical phase space the generator of dilations is `G = Σᵢ qᵢ pᵢ`. For
every Hamiltonian

`{G, H} = Σᵢ pᵢ ∂H/∂pᵢ − Σᵢ qᵢ ∂H/∂qᵢ`.

If `H = T + U` with `T` a function of the momenta that is homogeneous of degree
two and `U` a function of the positions that is homogeneous of degree `k`, in
the sense of Euler's relation, then `{G, H} = 2T − kU`
(Landau–Lifshitz §10). The kinetic energy `Σᵢ pᵢ² / 2mᵢ` satisfies the
hypotheses on `T`. The time average that turns this identity into the virial
theorem is not part of this file.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.SmoothAlgebra.PhaseSpace

open SmoothRing FreeSmoothRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The generator of dilations, `Σᵢ qᵢ pᵢ`. -/
def dilation : PhaseSpace ι := ∑ i, q i * p i

/-- `{Σ qᵢ pᵢ, H} = Σᵢ pᵢ ∂H/∂pᵢ − Σᵢ qᵢ ∂H/∂qᵢ` for every Hamiltonian. -/
theorem canonical_dilation_bracket (H : PhaseSpace ι) :
    (canonical ι).bracket dilation H =
      ∑ i, p i * partialDerivation (Sum.inr i) H -
        ∑ i, q i * partialDerivation (Sum.inl i) H := by
  rw [dilation, AlmostPoissonStructure.bracket_sum_left, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlmostPoissonStructure.bracket_mul_left, canonical_p_bracket, canonical_q_bracket]
  ring

/-- The virial identity `{Σ qᵢ pᵢ, T + U} = 2T − kU` (Landau–Lifshitz §10), for
`T` a function of the momenta homogeneous of degree two and `U` a function of
the positions homogeneous of degree `k`. -/
theorem canonical_dilation_bracket_add {T U : PhaseSpace ι} {k : ℝ}
    (hT : ∑ i, p i * partialDerivation (Sum.inr i) T = 2 * T)
    (hTq : ∀ i, partialDerivation (Sum.inl i) T = 0)
    (hU : ∑ i, q i * partialDerivation (Sum.inl i) U = algebraMap ℝ (PhaseSpace ι) k * U)
    (hUp : ∀ i, partialDerivation (Sum.inr i) U = 0) :
    (canonical ι).bracket dilation (T + U) = 2 * T - algebraMap ℝ (PhaseSpace ι) k * U := by
  rw [canonical_dilation_bracket]
  simp only [map_add, hTq, hUp, add_zero, zero_add, hT, hU]

/-- The kinetic energy `Σᵢ pᵢ² / 2mᵢ`. -/
def kineticEnergy (m : ι → ℝ) : PhaseSpace ι :=
  ∑ i, algebraMap ℝ (PhaseSpace ι) ((m i)⁻¹ / 2) * (p i * p i)

theorem partialDerivation_inl_kineticEnergy (m : ι → ℝ) (j : ι) :
    partialDerivation (Sum.inl j) (kineticEnergy m) = 0 := by
  rw [kineticEnergy, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, SmoothDerivation.map_mul, p,
    partialDerivation_generator_of_ne (c := Sum.inl j) (i := Sum.inr i) (by simp)]
  simp

theorem partialDerivation_inr_kineticEnergy (m : ι → ℝ) (j : ι) :
    partialDerivation (Sum.inr j) (kineticEnergy m) =
      algebraMap ℝ (PhaseSpace ι) (m j)⁻¹ * p j := by
  have h2 : (2 : PhaseSpace ι) = algebraMap ℝ (PhaseSpace ι) 2 := (map_ofNat _ 2).symm
  have hj : (m j)⁻¹ / 2 * 2 = (m j)⁻¹ := by ring
  rw [kineticEnergy, map_sum, Finset.sum_eq_single j]
  · rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, SmoothDerivation.map_mul, p,
      partialDerivation_generator_self]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
    rw [← two_mul, h2, ← mul_assoc, ← map_mul, hj]
  · intro i _ hij
    rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, SmoothDerivation.map_mul, p,
      partialDerivation_generator_of_ne (c := Sum.inr j) (i := Sum.inr i)
        (fun h => hij (Sum.inr.inj h))]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Euler's relation for the kinetic energy: `Σᵢ pᵢ ∂T/∂pᵢ = 2T`. -/
theorem sum_p_mul_partialDerivation_kineticEnergy (m : ι → ℝ) :
    ∑ i, p i * partialDerivation (Sum.inr i) (kineticEnergy m) = 2 * kineticEnergy m := by
  have h2 : (2 : PhaseSpace ι) = algebraMap ℝ (PhaseSpace ι) 2 := (map_ofNat _ 2).symm
  rw [kineticEnergy, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : 2 * ((m i)⁻¹ / 2) = (m i)⁻¹ := by ring
  have hi : algebraMap ℝ (PhaseSpace ι) 2 * algebraMap ℝ (PhaseSpace ι) ((m i)⁻¹ / 2) =
      algebraMap ℝ (PhaseSpace ι) (m i)⁻¹ := by
    rw [← map_mul, hr]
  rw [← kineticEnergy, partialDerivation_inr_kineticEnergy, h2,
    ← mul_assoc (algebraMap ℝ (PhaseSpace ι) 2), hi]
  ring

/-- The virial identity for `H = Σᵢ pᵢ² / 2mᵢ + U` with a potential that is a
function of the positions homogeneous of degree `k`: `{Σ qᵢ pᵢ, H} = 2T − kU`. -/
theorem virial (m : ι → ℝ) {U : PhaseSpace ι} {k : ℝ}
    (hU : ∑ i, q i * partialDerivation (Sum.inl i) U = algebraMap ℝ (PhaseSpace ι) k * U)
    (hUp : ∀ i, partialDerivation (Sum.inr i) U = 0) :
    (canonical ι).bracket dilation (kineticEnergy m + U) =
      2 * kineticEnergy m - algebraMap ℝ (PhaseSpace ι) k * U :=
  canonical_dilation_bracket_add (sum_p_mul_partialDerivation_kineticEnergy m)
    (partialDerivation_inl_kineticEnergy m) hU hUp

/-- The isotropic oscillator potential `Σᵢ ½ k qᵢ²`, homogeneous of degree two. -/
def oscillatorPotential (k : ℝ) : PhaseSpace ι :=
  ∑ i, algebraMap ℝ (PhaseSpace ι) (k / 2) * (q i * q i)

theorem partialDerivation_inr_oscillatorPotential (k : ℝ) (j : ι) :
    partialDerivation (Sum.inr j) (oscillatorPotential (ι := ι) k) = 0 := by
  rw [oscillatorPotential, map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, SmoothDerivation.map_mul, q,
    partialDerivation_generator_of_ne (c := Sum.inr j) (i := Sum.inl i) (by simp)]
  simp

theorem partialDerivation_inl_oscillatorPotential (k : ℝ) (j : ι) :
    partialDerivation (Sum.inl j) (oscillatorPotential (ι := ι) k) =
      algebraMap ℝ (PhaseSpace ι) k * q j := by
  have h2 : (2 : PhaseSpace ι) = algebraMap ℝ (PhaseSpace ι) 2 := (map_ofNat _ 2).symm
  have hk : k / 2 * 2 = k := by ring
  rw [oscillatorPotential, map_sum, Finset.sum_eq_single j]
  · rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, SmoothDerivation.map_mul, q,
      partialDerivation_generator_self]
    simp only [smul_eq_mul, mul_one, mul_zero, add_zero]
    rw [← two_mul, h2, ← mul_assoc, ← map_mul, hk]
  · intro i _ hij
    rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, SmoothDerivation.map_mul, q,
      partialDerivation_generator_of_ne (c := Sum.inl j) (i := Sum.inl i)
        (fun h => hij (Sum.inl.inj h))]
    simp
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- Euler's relation for the oscillator potential: `Σᵢ qᵢ ∂U/∂qᵢ = 2U`. -/
theorem sum_q_mul_partialDerivation_oscillatorPotential (k : ℝ) :
    ∑ i, q i * partialDerivation (Sum.inl i) (oscillatorPotential (ι := ι) k) =
      algebraMap ℝ (PhaseSpace ι) 2 * oscillatorPotential k := by
  rw [oscillatorPotential, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : 2 * (k / 2) = k := by ring
  have hi : algebraMap ℝ (PhaseSpace ι) 2 * algebraMap ℝ (PhaseSpace ι) (k / 2) =
      algebraMap ℝ (PhaseSpace ι) k := by
    rw [← map_mul, hr]
  rw [← oscillatorPotential, partialDerivation_inl_oscillatorPotential,
    ← mul_assoc (algebraMap ℝ (PhaseSpace ι) 2), hi]
  ring

/-- The virial identity of the isotropic oscillator: `{Σ qᵢ pᵢ, H} = 2T − 2U`. -/
theorem virial_oscillator (m : ι → ℝ) (k : ℝ) :
    (canonical ι).bracket dilation (kineticEnergy m + oscillatorPotential k) =
      2 * kineticEnergy m - algebraMap ℝ (PhaseSpace ι) 2 * oscillatorPotential k :=
  virial m (sum_q_mul_partialDerivation_oscillatorPotential k)
    (partialDerivation_inr_oscillatorPotential k)

end ProjectAInos.SmoothAlgebra.PhaseSpace
