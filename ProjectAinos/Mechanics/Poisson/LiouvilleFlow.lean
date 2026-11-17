/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.HamiltonianField
public import ProjectAinos.Mechanics.Elementary

/-!
# Flows of Hamiltonians that are defined for all times

Instances of Liouville's theorem (Landau–Lifshitz §46) in which the flow is
defined for all times and points, so that it preserves the Lebesgue measure of
the phase space.

* The oscillator `Σ pᵢ²/2mᵢ + ½ k qᵢ²`: the field is linear.
* The pendulums `Σ pᵢ²/2mᵢ − k Σ cos qᵢ`: the field is not linear, and it has
  linear growth, which gives completeness without an estimate of the energy.
* The oscillator with friction: the divergence is the constant `−Σ aᵢ/mᵢ`, and
  the flow multiplies the phase volume by `exp (−Σ aᵢ/mᵢ · t)`.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace ProjectAinos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace
open SmoothGeometry SmoothGeometry.LinearODE SmoothGeometry.NonlinearODE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- A bound for one co-ordinate by the sum of the absolute values of the
coefficients. -/
theorem abs_mul_le_sum_mul_norm (c : ι → ℝ) (z : ι ⊕ ι → ℝ) (i : ι) (a : ι ⊕ ι) :
    |c i * z a| ≤ (∑ j, |c j|) * ‖z‖ := by
  rw [abs_mul]
  exact mul_le_mul (Finset.single_le_sum (fun j _ => abs_nonneg (c j)) (Finset.mem_univ i))
    (norm_le_pi_norm z a) (abs_nonneg _) (Finset.sum_nonneg fun j _ => abs_nonneg (c j))

namespace Oscillator

/-- The Hamiltonian field of the oscillator: `q̇ᵢ = pᵢ/mᵢ`. -/
theorem hamiltonianField_inl (m : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (hamiltonian m k) z (Sum.inl i) = (m i)⁻¹ * z (Sum.inr i) := by
  rw [Mechanics.hamiltonianField_inl]
  have h := velocity_hamiltonian m k i
  rw [velocity] at h
  rw [h]
  rfl

/-- The Hamiltonian field of the oscillator: `ṗᵢ = −k qᵢ`. -/
theorem hamiltonianField_inr (m : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (hamiltonian m k) z (Sum.inr i) = -(k * z (Sum.inl i)) := by
  rw [Mechanics.hamiltonianField_inr, partialDerivation_inl_hamiltonian]
  rfl

/-- The flow of the oscillator is defined for all times and points. -/
theorem flowDomain_hamiltonianField (m : ι → ℝ) (k : ℝ) :
    flowDomain (hamiltonianField (hamiltonian m k)) = univ := by
  refine flowDomain_eq_univ_of_norm_le (contDiff_hamiltonianField _)
    (a := 0) (b := |k| + ∑ j, |(m j)⁻¹|) fun z => ?_
  rw [zero_add]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  rcases a with i | i
  · rw [hamiltonianField_inl, Real.norm_eq_abs, add_mul]
    exact (abs_mul_le_sum_mul_norm (fun j => (m j)⁻¹) z i (Sum.inr i)).trans
      (le_add_of_nonneg_left (by positivity))
  · rw [hamiltonianField_inr, Real.norm_eq_abs, abs_neg, abs_mul, add_mul]
    exact (mul_le_mul_of_nonneg_left (norm_le_pi_norm z (Sum.inl i)) (abs_nonneg k)).trans
      (le_add_of_nonneg_right (by positivity))

/-- Liouville's theorem for the oscillator with any number of co-ordinates. -/
theorem measurePreserving_hamiltonianFlow (m : ι → ℝ) (k : ℝ) (t : ℝ) :
    MeasurePreserving (fun z => flow (hamiltonianField (hamiltonian m k)) (t, z))
      volume volume :=
  Mechanics.measurePreserving_hamiltonianFlow _ (flowDomain_hamiltonianField m k) t

end Oscillator

/-! ### Pendulums -/

namespace Pendulum

/-- The Hamiltonian `Σ pᵢ²/2mᵢ − k Σ cos qᵢ` of pendulums. -/
def hamiltonian (m : ι → ℝ) (k : ℝ) : PhaseSpace ι :=
  kineticEnergy m - algebraMap ℝ (PhaseSpace ι) k * ∑ i, ringCos (q i)

theorem partialDerivation_inr_hamiltonian (m : ι → ℝ) (k : ℝ) (j : ι) :
    partialDerivation (Sum.inr j) (hamiltonian m k) =
      algebraMap ℝ (PhaseSpace ι) (m j)⁻¹ * p j := by
  have hzero : partialDerivation (Sum.inr j) (∑ i, ringCos (q i) : PhaseSpace ι) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [apply_ringCos, q,
      partialDerivation_generator_of_ne (c := Sum.inr j) (i := Sum.inl i) (by simp), mul_zero,
      neg_zero]
  rw [hamiltonian, map_sub, partialDerivation_inr_kineticEnergy,
    SmoothDerivation.map_algebraMap_mul, hzero, smul_zero, sub_zero]

theorem partialDerivation_inl_hamiltonian (m : ι → ℝ) (k : ℝ) (j : ι) :
    partialDerivation (Sum.inl j) (hamiltonian m k) =
      algebraMap ℝ (PhaseSpace ι) k * ringSin (q j) := by
  have hsum : partialDerivation (Sum.inl j) (∑ i, ringCos (q i) : PhaseSpace ι) =
      -ringSin (q j) := by
    rw [map_sum, Finset.sum_eq_single j]
    · rw [apply_ringCos, q, partialDerivation_generator_self, mul_one]
    · intro i _ hij
      rw [apply_ringCos, q,
        partialDerivation_generator_of_ne (c := Sum.inl j) (i := Sum.inl i) (by simpa using hij),
        mul_zero, neg_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [hamiltonian, map_sub, partialDerivation_inl_kineticEnergy,
    SmoothDerivation.map_algebraMap_mul, hsum, smul_eq_mul]
  ring

/-- The Hamiltonian field of the pendulums: `q̇ᵢ = pᵢ/mᵢ`. -/
theorem hamiltonianField_inl (m : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (hamiltonian m k) z (Sum.inl i) = (m i)⁻¹ * z (Sum.inr i) := by
  rw [Mechanics.hamiltonianField_inl, partialDerivation_inr_hamiltonian]
  rfl

/-- The Hamiltonian field of the pendulums: `ṗᵢ = −k sin qᵢ`. -/
theorem hamiltonianField_inr (m : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    hamiltonianField (hamiltonian m k) z (Sum.inr i) = -(k * Real.sin (z (Sum.inl i))) := by
  rw [Mechanics.hamiltonianField_inr, partialDerivation_inl_hamiltonian]
  rfl

/-- The flow of the pendulums is defined for all times and points. -/
theorem flowDomain_hamiltonianField (m : ι → ℝ) (k : ℝ) :
    flowDomain (hamiltonianField (hamiltonian m k)) = univ := by
  refine flowDomain_eq_univ_of_norm_le (contDiff_hamiltonianField _)
    (a := |k|) (b := ∑ j, |(m j)⁻¹|) fun z => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun a => ?_
  rcases a with i | i
  · rw [hamiltonianField_inl, Real.norm_eq_abs]
    exact (abs_mul_le_sum_mul_norm (fun j => (m j)⁻¹) z i (Sum.inr i)).trans
      (le_add_of_nonneg_left (abs_nonneg k))
  · rw [hamiltonianField_inr, Real.norm_eq_abs, abs_neg, abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg k) (Real.abs_sin_le_one _)).trans
      (le_add_of_nonneg_right (by positivity))

/-- Liouville's theorem for the pendulums. -/
theorem measurePreserving_hamiltonianFlow (m : ι → ℝ) (k : ℝ) (t : ℝ) :
    MeasurePreserving (fun z => flow (hamiltonianField (hamiltonian m k)) (t, z))
      volume volume :=
  Mechanics.measurePreserving_hamiltonianFlow _ (flowDomain_hamiltonianField m k) t

/-- There is a motion of the pendulums through every point of the phase space. -/
theorem exists_isTrajectory (m : ι → ℝ) (k : ℝ) (z₀ : ι ⊕ ι → ℝ) :
    ∃ c : ι ⊕ ι → TimeFunction, IsTrajectory (canonical ι) (hamiltonian m k) c ∧
      realCurve c 0 = z₀ :=
  Mechanics.exists_isTrajectory _ (flowDomain_hamiltonianField m k) z₀

end Pendulum

/-! ### The oscillator with friction -/

namespace Oscillator

/-- The field of the oscillator with friction: `q̇ᵢ = pᵢ/mᵢ`. -/
theorem realField_dissipativeField_inl (m a : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    realField (dissipativeField (Matrix.diagonal a) (hamiltonian m k)) z (Sum.inl i) =
      (m i)⁻¹ * z (Sum.inr i) := by
  change ((dissipativeField (Matrix.diagonal a) (hamiltonian m k)) (q i)).val z = _
  rw [dissipativeField_q, velocity_hamiltonian]
  rfl

/-- The field of the oscillator with friction: `ṗᵢ = −k qᵢ − aᵢ pᵢ/mᵢ`. -/
theorem realField_dissipativeField_inr (m a : ι → ℝ) (k : ℝ) (z : ι ⊕ ι → ℝ) (i : ι) :
    realField (dissipativeField (Matrix.diagonal a) (hamiltonian m k)) z (Sum.inr i) =
      -(k * z (Sum.inl i)) - a i * ((m i)⁻¹ * z (Sum.inr i)) := by
  change ((dissipativeField (Matrix.diagonal a) (hamiltonian m k)) (p i)).val z = _
  rw [dissipativeField_p, partialDerivation_inl_hamiltonian, frictionalForce_diagonal,
    velocity_hamiltonian]
  rfl

/-- The flow of the oscillator with friction is defined for all times and points. -/
theorem flowDomain_dissipativeField (m a : ι → ℝ) (k : ℝ) :
    flowDomain (realField (dissipativeField (Matrix.diagonal a) (hamiltonian m k))) = univ := by
  refine flowDomain_eq_univ_of_norm_le (contDiff_realField _)
    (a := 0) (b := |k| + ∑ j, |(m j)⁻¹| + ∑ j, |a j * (m j)⁻¹|) fun z => ?_
  rw [zero_add]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun b => ?_
  have h1 := fun i : ι => abs_mul_le_sum_mul_norm (fun j => (m j)⁻¹) z i (Sum.inr i)
  have h2 := fun i : ι => abs_mul_le_sum_mul_norm (fun j => a j * (m j)⁻¹) z i (Sum.inr i)
  have h3 := fun i : ι =>
    mul_le_mul_of_nonneg_left (norm_le_pi_norm z (Sum.inl i)) (abs_nonneg k)
  have hs1 : 0 ≤ (∑ j, |(m j)⁻¹|) * ‖z‖ := by positivity
  have hs2 : 0 ≤ (∑ j, |a j * (m j)⁻¹|) * ‖z‖ := by positivity
  have hs3 : 0 ≤ |k| * ‖z‖ := by positivity
  rcases b with i | i
  · rw [realField_dissipativeField_inl, Real.norm_eq_abs]
    nlinarith [h1 i]
  · rw [realField_dissipativeField_inr, Real.norm_eq_abs]
    have hsplit : |-(k * z (Sum.inl i)) - a i * ((m i)⁻¹ * z (Sum.inr i))| ≤
        |k| * ‖z (Sum.inl i)‖ + |a i * (m i)⁻¹ * z (Sum.inr i)| := by
      rw [← mul_assoc]
      refine (abs_sub _ _).trans ?_
      rw [abs_neg, abs_mul, Real.norm_eq_abs]
    nlinarith [h2 i, h3 i]

/-- With friction the flow of the oscillator multiplies the phase volume by
`exp (−Σ aᵢ/mᵢ · t)`. -/
theorem volume_image_dissipativeFlow (m a : ι → ℝ) (k : ℝ) (t : ℝ) {A : Set (ι ⊕ ι → ℝ)}
    (hA : MeasurableSet A) :
    volume ((fun z => flow (realField (dissipativeField (Matrix.diagonal a) (hamiltonian m k)))
        (t, z)) '' A) =
      ENNReal.ofReal (Real.exp (-(∑ i, a i * (m i)⁻¹) * t)) * volume A := by
  refine (isLocalFlowOn_flow (contDiff_realField _)).measure_image_of_trace_eq volume
    ((contDiff_realField _).of_le (by simp)) (fun z => ?_) hA fun z _ => by
      rw [flowDomain_dissipativeField]
      exact mem_univ _
  rw [traceCLM_fderiv_realField, divergence_dissipativeField]
  rfl

end Oscillator

end ProjectAinos.Mechanics
