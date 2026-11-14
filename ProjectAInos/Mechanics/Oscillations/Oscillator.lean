/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Harmonic
public import ProjectAInos.Mechanics.Jet.Prolongation
public import ProjectAInos.Mechanics.Poisson.Trajectory
public import ProjectAInos.Mechanics.Poisson.Virial
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The harmonic oscillator and its flow

The Lagrangian `Σᵢ ½ mᵢ q̇ᵢ² − ½ k qᵢ²` and the Hamiltonian
`Σᵢ pᵢ²/2mᵢ + ½ k qᵢ²` (Landau–Lifshitz §21). With `k = mᵢ ωᵢ²`, the solutions
of the Euler–Lagrange equations are the paths whose components are free
oscillations of frequency `ωᵢ`, and the trajectories of the Hamiltonian are
those paths together with the momenta `pᵢ = mᵢ q̇ᵢ`.

The flow of the Hamiltonian is linear. In each pair `(qᵢ, pᵢ)` it is the matrix
`flowMatrix`, which is a one-parameter group of determinant one.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The solutions of the Euler–Lagrange equations of the oscillator are the
paths whose components are free oscillations (Landau–Lifshitz (21.3), (21.5)). -/
theorem StandardJet.isSolution_oscillator_iff_isHarmonic {m ω : ι → ℝ} {k : ℝ}
    (hm : ∀ i, m i ≠ 0) (hk : ∀ i, k = m i * ω i ^ 2) (γ : ι → TimeFunction) :
    StandardJet.IsSolution
        ((StandardJet.jetRing ι).naturalLagrangian m (StandardJet.oscillatorPotential k)) γ ↔
      ∀ i, IsHarmonic (ω i) (γ i) := by
  rw [StandardJet.isSolution_oscillator_iff]
  refine forall_congr' fun i => ?_
  have hinv : algebraMap ℝ TimeFunction (m i)⁻¹ * algebraMap ℝ TimeFunction (m i) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (hm i), map_one]
  have hK : algebraMap ℝ TimeFunction k =
      algebraMap ℝ TimeFunction (m i) * algebraMap ℝ TimeFunction (ω i ^ 2) := by
    rw [← map_mul, ← hk i]
  rw [hK, Function.iterate_succ_apply', Function.iterate_one]
  unfold IsHarmonic
  constructor
  · intro h
    linear_combination algebraMap ℝ TimeFunction (m i)⁻¹ * h -
      (timeDerivative (timeDerivative (γ i)) + algebraMap ℝ TimeFunction (ω i ^ 2) * γ i) * hinv
  · intro h
    linear_combination algebraMap ℝ TimeFunction (m i) * h

namespace Oscillator

/-- The Hamiltonian `Σᵢ pᵢ²/2mᵢ + ½ k qᵢ²` of the oscillator. -/
def hamiltonian (m : ι → ℝ) (k : ℝ) : PhaseSpace ι := kineticEnergy m + oscillatorPotential k

/-- Hamilton's equations of the oscillator: `q̇ᵢ = pᵢ/mᵢ`, `ṗᵢ = −k qᵢ`. -/
theorem isTrajectory_iff (m : ι → ℝ) (k : ℝ) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (hamiltonian m k) c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) =
        algebraMap ℝ TimeFunction (m i)⁻¹ * c (Sum.inr i)) ∧
      ∀ i, timeDerivative (c (Sum.inr i)) = -(algebraMap ℝ TimeFunction k * c (Sum.inl i)) := by
  rw [isTrajectory_canonical_iff]
  simp only [hamiltonian, map_add, partialDerivation_inr_kineticEnergy,
    partialDerivation_inr_oscillatorPotential, partialDerivation_inl_kineticEnergy,
    partialDerivation_inl_oscillatorPotential, add_zero, zero_add, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, p, q, lift_generator]

/-- The trajectories of the oscillator: every position is a free oscillation of
frequency `ωᵢ = √(k/mᵢ)`, and `pᵢ = mᵢ q̇ᵢ`. -/
theorem isTrajectory_iff_isHarmonic {m ω : ι → ℝ} {k : ℝ} (hm : ∀ i, m i ≠ 0)
    (hk : ∀ i, k = m i * ω i ^ 2) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (hamiltonian m k) c ↔
      ∀ i, IsHarmonic (ω i) (c (Sum.inl i)) ∧
        c (Sum.inr i) = algebraMap ℝ TimeFunction (m i) * timeDerivative (c (Sum.inl i)) := by
  rw [isTrajectory_iff, ← forall_and]
  refine forall_congr' fun i => ?_
  have hinv : algebraMap ℝ TimeFunction (m i)⁻¹ * algebraMap ℝ TimeFunction (m i) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (hm i), map_one]
  have hK : algebraMap ℝ TimeFunction k =
      algebraMap ℝ TimeFunction (m i) * algebraMap ℝ TimeFunction (ω i ^ 2) := by
    rw [← map_mul, ← hk i]
  unfold IsHarmonic
  rw [hK]
  constructor
  · rintro ⟨hq, hp⟩
    refine ⟨?_, ?_⟩
    · rw [hq, SmoothDerivation.map_algebraMap_mul, smul_eq_mul, hp]
      linear_combination (-(algebraMap ℝ TimeFunction (ω i ^ 2) * c (Sum.inl i))) * hinv
    · rw [hq]
      linear_combination (-c (Sum.inr i)) * hinv
  · rintro ⟨hq, hp⟩
    refine ⟨?_, ?_⟩
    · rw [hp]
      linear_combination (-timeDerivative (c (Sum.inl i))) * hinv
    · rw [hp, SmoothDerivation.map_algebraMap_mul, smul_eq_mul, hq]
      ring

/-! ### The flow -/

/-- The flow of `p²/2m + ½ m ω² q²` at time `t`, as a matrix acting on `(q, p)`. -/
def flowMatrix (m ω t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos (ω * t), Real.sin (ω * t) / (m * ω);
    -(m * ω * Real.sin (ω * t)), Real.cos (ω * t)]

theorem flowMatrix_zero (m ω : ℝ) : flowMatrix m ω 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [flowMatrix]

/-- The flow is a one-parameter group. -/
theorem flowMatrix_add {m ω : ℝ} (hm : m ≠ 0) (hω : ω ≠ 0) (s t : ℝ) :
    flowMatrix m ω (s + t) = flowMatrix m ω s * flowMatrix m ω t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [flowMatrix, Matrix.mul_apply, Fin.sum_univ_two, mul_add, Real.cos_add,
      Real.sin_add] <;>
    field_simp <;> ring

/-- The flow preserves the area of the phase plane. -/
theorem det_flowMatrix {m ω : ℝ} (hm : m ≠ 0) (hω : ω ≠ 0) (t : ℝ) :
    (flowMatrix m ω t).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [flowMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h := Real.cos_sq_add_sin_sq (ω * t)
  field_simp
  linear_combination h

/-- The flow has period `2π/ω`. -/
theorem flowMatrix_add_period (m : ℝ) {ω : ℝ} (hω : ω ≠ 0) (t : ℝ) :
    flowMatrix m ω (t + 2 * Real.pi / ω) = flowMatrix m ω t := by
  have hp : ω * (t + 2 * Real.pi / ω) = ω * t + 2 * Real.pi := by
    field_simp
  simp only [flowMatrix, hp, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- Along a trajectory of the oscillator, the point `(qᵢ, pᵢ)` at time `t` is
the flow matrix applied to the point at time zero. -/
theorem apply_eq_flowMatrix_mulVec {m ω : ι → ℝ} {k : ℝ} (hm : ∀ i, m i ≠ 0)
    (hω : ∀ i, ω i ≠ 0) (hk : ∀ i, k = m i * ω i ^ 2) {c : ι ⊕ ι → TimeFunction}
    (h : IsTrajectory (canonical ι) (hamiltonian m k) c) (i : ι) (t : ℝ) :
    ![c (Sum.inl i) fun _ => t, c (Sum.inr i) fun _ => t] =
      flowMatrix (m i) (ω i) t *ᵥ ![c (Sum.inl i) fun _ => 0, c (Sum.inr i) fun _ => 0] := by
  obtain ⟨hq, hp⟩ := (isTrajectory_iff_isHarmonic hm hk c).mp h i
  have hp' (s : ℝ) : c (Sum.inr i) (fun _ => s) =
      m i * timeDerivative (c (Sum.inl i)) fun _ => s :=
    congrArg (fun f : TimeFunction => f fun _ => s) hp
  have hmi := hm i
  have hωi := hω i
  ext j
  fin_cases j
  · simp only [flowMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.zero_eta,
      Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [hq.apply_eq hωi, hp' 0]
    field_simp
  · simp only [flowMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.mk_one,
      Matrix.cons_val_zero, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [hp' t, hq.timeDerivative_apply_eq hωi, hp' 0]
    ring

/-- The curve through `(q₀, p₀)` at time zero. -/
def flowCurve (m ω q₀ p₀ : ι → ℝ) : ι ⊕ ι → TimeFunction
  | Sum.inl i => algebraMap ℝ TimeFunction (q₀ i) * TimeFunction.cosMul (ω i) +
      algebraMap ℝ TimeFunction (p₀ i / (m i * ω i)) * TimeFunction.sinMul (ω i)
  | Sum.inr i => algebraMap ℝ TimeFunction (p₀ i) * TimeFunction.cosMul (ω i) -
      algebraMap ℝ TimeFunction (m i * ω i * q₀ i) * TimeFunction.sinMul (ω i)

/-- Every point of the phase space lies on a trajectory of the oscillator. -/
theorem isTrajectory_flowCurve {m ω : ι → ℝ} {k : ℝ} (hm : ∀ i, m i ≠ 0)
    (hω : ∀ i, ω i ≠ 0) (hk : ∀ i, k = m i * ω i ^ 2) (q₀ p₀ : ι → ℝ) :
    IsTrajectory (canonical ι) (hamiltonian m k) (flowCurve m ω q₀ p₀) := by
  rw [isTrajectory_iff]
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have hmi := hm i
    have hωi := hω i
    simp only [flowCurve, map_add, SmoothDerivation.map_algebraMap_mul,
      TimeFunction.timeDerivative_cosMul, TimeFunction.timeDerivative_sinMul, smul_eq_mul]
    refine TimeFunction.ext_apply_const fun t => ?_
    simp only [TimeFunction.add_apply, TimeFunction.sub_apply, TimeFunction.mul_apply,
      TimeFunction.neg_apply, TimeFunction.algebraMap_apply, TimeFunction.cosMul_apply,
      TimeFunction.sinMul_apply]
    field_simp
    ring
  · have hmi := hm i
    have hωi := hω i
    simp only [flowCurve, map_sub, SmoothDerivation.map_algebraMap_mul,
      TimeFunction.timeDerivative_cosMul, TimeFunction.timeDerivative_sinMul, smul_eq_mul]
    refine TimeFunction.ext_apply_const fun t => ?_
    simp only [TimeFunction.add_apply, TimeFunction.sub_apply, TimeFunction.mul_apply,
      TimeFunction.neg_apply, TimeFunction.algebraMap_apply, TimeFunction.cosMul_apply,
      TimeFunction.sinMul_apply]
    rw [hk i]
    field_simp
    ring

omit [DecidableEq ι] [Fintype ι] in
theorem flowCurve_inl_apply_zero (m ω q₀ p₀ : ι → ℝ) (i : ι) :
    flowCurve m ω q₀ p₀ (Sum.inl i) (fun _ => 0) = q₀ i := by
  simp [flowCurve]

omit [DecidableEq ι] [Fintype ι] in
theorem flowCurve_inr_apply_zero (m ω q₀ p₀ : ι → ℝ) (i : ι) :
    flowCurve m ω q₀ p₀ (Sum.inr i) (fun _ => 0) = p₀ i := by
  simp [flowCurve]

end Oscillator

end ProjectAInos.Mechanics
