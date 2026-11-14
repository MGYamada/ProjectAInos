/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Oscillations.Damped
public import ProjectAInos.Mechanics.Oscillations.Linearization
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# The dissipative function

Friction is not Hamiltonian. On the canonical phase space, the motion with a
frictional force `fᵢ = Σₖ αᵢₖ vₖ` linear in the velocities `vₖ = ∂H/∂pₖ` is the
vector field `X = X_H − Σᵢ fᵢ ∂/∂pᵢ` (Landau–Lifshitz §25). With the dissipative
function `F = ½ Σ αᵢₖ vᵢ vₖ`, the Hamiltonian satisfies `X(H) = −2F`. If the
matrix `α` is positive semidefinite, `F` is non-negative at every point, and the
energy does not increase along the motion.

A curve is an integral curve of a vector field when each generator evolves by
the value of the field on it; a trajectory of a Hamiltonian is an integral
curve of its Hamiltonian vector field.

For the oscillator with the diagonal friction matrix `αᵢᵢ = 2 mᵢ γᵢ`, the
integral curves are the damped oscillations of `Oscillations/Damped`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Matrix

section IntegralCurve

variable {κ : Type*}

/-- `c` is an integral curve of the vector field `X`: each generator evolves by
the value of `X` on it, evaluated along the curve. -/
def IsIntegralCurve (X : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ))
    (c : κ → TimeFunction) : Prop :=
  ∀ a, timeDerivative (c a) = FreeSmoothRing.lift c (X (generator a))

/-- A trajectory of a Hamiltonian is an integral curve of its Hamiltonian
vector field. -/
theorem isIntegralCurve_hamiltonian_iff (π : PoissonStructure (FreeSmoothRing κ))
    (H : FreeSmoothRing κ) (c : κ → TimeFunction) :
    IsIntegralCurve (π.hamiltonian H) c ↔ IsTrajectory π H c :=
  Iff.rfl

/-- Along an integral curve every observable evolves by the vector field:
`d/dt f(c) = X(f)(c)`. -/
theorem IsIntegralCurve.timeDerivative_lift
    {X : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ)} {c : κ → TimeFunction}
    (h : IsIntegralCurve X c) (f : FreeSmoothRing κ) :
    timeDerivative (FreeSmoothRing.lift c f) = FreeSmoothRing.lift c (X f) := by
  refine (FreeSmoothRing.map_derivation_eq (FreeSmoothRing.lift c) X timeDerivative
    (fun a => ?_) f).symm
  rw [lift_generator]
  exact (h a).symm

end IntegralCurve

section Dissipation

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The velocity `vᵢ = ∂H/∂pᵢ`. -/
def velocity (H : PhaseSpace ι) (i : ι) : PhaseSpace ι := partialDerivation (Sum.inr i) H

/-- The frictional force `fᵢ = Σₖ αᵢₖ vₖ`. -/
def frictionalForce (α : Matrix ι ι ℝ) (H : PhaseSpace ι) (i : ι) : PhaseSpace ι :=
  ∑ k, algebraMap ℝ (PhaseSpace ι) (α i k) * velocity H k

/-- The dissipative function `F = ½ Σ αᵢₖ vᵢ vₖ` (Landau–Lifshitz (25.11)). -/
def dissipativeFunction (α : Matrix ι ι ℝ) (H : PhaseSpace ι) : PhaseSpace ι :=
  ∑ i, ∑ k, algebraMap ℝ (PhaseSpace ι) (α i k / 2) * (velocity H i * velocity H k)

/-- `2F = Σᵢ fᵢ vᵢ`. -/
theorem two_mul_dissipativeFunction (α : Matrix ι ι ℝ) (H : PhaseSpace ι) :
    2 * dissipativeFunction α H = ∑ i, frictionalForce α H i * velocity H i := by
  have h2 (r : ℝ) : 2 * algebraMap ℝ (PhaseSpace ι) (r / 2) = algebraMap ℝ (PhaseSpace ι) r := by
    rw [← map_ofNat (algebraMap ℝ (PhaseSpace ι)) 2, ← map_mul, mul_div_cancel₀ r two_ne_zero]
  rw [dissipativeFunction, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [frictionalForce, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, h2]
  ring

/-- The vector field of the motion with friction, `X = X_H − Σᵢ fᵢ ∂/∂pᵢ`. -/
def dissipativeField (α : Matrix ι ι ℝ) (H : PhaseSpace ι) :
    SmoothDerivation (PhaseSpace ι) (PhaseSpace ι) :=
  (canonical ι).hamiltonian H - ∑ i, frictionalForce α H i • partialDerivation (Sum.inr i)

theorem dissipativeField_apply (α : Matrix ι ι ℝ) (H f : PhaseSpace ι) :
    dissipativeField α H f =
      (canonical ι).bracket f H - ∑ i, frictionalForce α H i * partialDerivation (Sum.inr i) f := by
  rw [dissipativeField, SmoothDerivation.sub_apply, AlmostPoissonStructure.hamiltonian_apply,
    SmoothDerivation.sum_apply]
  simp only [SmoothDerivation.smul_apply, smul_eq_mul]

/-- The equation for a position is not changed by friction: `q̇ᵢ = ∂H/∂pᵢ`. -/
theorem dissipativeField_q (α : Matrix ι ι ℝ) (H : PhaseSpace ι) (i : ι) :
    dissipativeField α H (q i) = velocity H i := by
  rw [dissipativeField_apply, canonical_q_bracket, Finset.sum_eq_zero, sub_zero, velocity]
  intro j _
  rw [q, partialDerivation_generator_of_ne (c := Sum.inr j) (i := Sum.inl i) (by simp), mul_zero]

/-- The equation for a momentum: `ṗᵢ = −∂H/∂qᵢ − fᵢ` (Landau–Lifshitz (25.12)). -/
theorem dissipativeField_p (α : Matrix ι ι ℝ) (H : PhaseSpace ι) (i : ι) :
    dissipativeField α H (p i) = -partialDerivation (Sum.inl i) H - frictionalForce α H i := by
  rw [dissipativeField_apply, canonical_p_bracket, Finset.sum_eq_single i]
  · rw [p, partialDerivation_generator_self, mul_one]
  · intro j _ hji
    rw [p, partialDerivation_generator_of_ne (c := Sum.inr j) (i := Sum.inr i)
      (fun h => hji (Sum.inr.inj h).symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The rate of loss of energy (Landau–Lifshitz (25.13)): `X(H) = −2F`. -/
theorem dissipativeField_self (α : Matrix ι ι ℝ) (H : PhaseSpace ι) :
    dissipativeField α H H = -(2 * dissipativeFunction α H) := by
  rw [dissipativeField_apply, AlmostPoissonStructure.bracket_self, zero_sub,
    two_mul_dissipativeFunction]
  rfl

/-- The value of the dissipative function at a point is the quadratic form of
`α` on the velocities, divided by two. -/
theorem lift_dissipativeFunction (α : Matrix ι ι ℝ) (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) :
    FreeSmoothRing.lift x₀ (dissipativeFunction α H) =
      ((fun i => FreeSmoothRing.lift x₀ (velocity H i)) ⬝ᵥ
        α *ᵥ fun i => FreeSmoothRing.lift x₀ (velocity H i)) / 2 := by
  rw [eq_div_iff two_ne_zero]
  simp only [dissipativeFunction, SmoothRingHom.map_sum, SmoothRingHom.map_mul,
    SmoothRingHom.map_algebraMap, dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  change α i k / 2 * (_ * _) * 2 = _
  ring

/-- For a positive semidefinite matrix `α` the dissipative function is
non-negative at every point. -/
theorem lift_dissipativeFunction_nonneg {α : Matrix ι ι ℝ} (hα : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ α *ᵥ v)
    (H : PhaseSpace ι) (x₀ : ι ⊕ ι → ℝ) :
    0 ≤ FreeSmoothRing.lift x₀ (dissipativeFunction α H) := by
  rw [lift_dissipativeFunction]
  exact div_nonneg (hα _) (by norm_num)

/-- The equations of the motion with friction along a curve. -/
theorem isIntegralCurve_dissipativeField_iff (α : Matrix ι ι ℝ) (H : PhaseSpace ι)
    (c : ι ⊕ ι → TimeFunction) :
    IsIntegralCurve (dissipativeField α H) c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) = FreeSmoothRing.lift c (velocity H i)) ∧
      ∀ i, timeDerivative (c (Sum.inr i)) =
        -FreeSmoothRing.lift c (partialDerivation (Sum.inl i) H) -
          FreeSmoothRing.lift c (frictionalForce α H i) := by
  have hq (i : ι) : dissipativeField α H (generator (Sum.inl i)) = velocity H i :=
    dissipativeField_q α H i
  have hp (i : ι) : dissipativeField α H (generator (Sum.inr i)) =
      -partialDerivation (Sum.inl i) H - frictionalForce α H i := dissipativeField_p α H i
  unfold IsIntegralCurve
  rw [Sum.forall]
  simp only [hq, hp, SmoothRingHom.map_sub, SmoothRingHom.map_neg]

/-- Along a motion with friction the energy changes at the rate `−2F`. -/
theorem IsIntegralCurve.timeDerivative_energy {α : Matrix ι ι ℝ} {H : PhaseSpace ι}
    {c : ι ⊕ ι → TimeFunction} (h : IsIntegralCurve (dissipativeField α H) c) :
    timeDerivative (FreeSmoothRing.lift c H) =
      -(2 * FreeSmoothRing.lift c (dissipativeFunction α H)) := by
  rw [h.timeDerivative_lift, dissipativeField_self, two_mul, two_mul, SmoothRingHom.map_neg,
    SmoothRingHom.map_add]

/-- With a positive semidefinite friction matrix the energy does not increase
along the motion. -/
theorem IsIntegralCurve.energy_antitone {α : Matrix ι ι ℝ} (hα : ∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ α *ᵥ v)
    {H : PhaseSpace ι} {c : ι ⊕ ι → TimeFunction}
    (h : IsIntegralCurve (dissipativeField α H) c) :
    Antitone fun t : ℝ => FreeSmoothRing.lift c H fun _ => t := by
  refine TimeFunction.antitone_of_timeDerivative_nonpos fun t => ?_
  have hF := lift_dissipativeFunction_nonneg hα H fun a => c a fun _ => t
  rw [h.timeDerivative_energy, two_mul]
  change -(FreeSmoothRing.lift c (dissipativeFunction α H) (fun _ => t) +
    FreeSmoothRing.lift c (dissipativeFunction α H) fun _ => t) ≤ 0
  rw [lift_curve_apply]
  linarith

end Dissipation

/-! ### The damped oscillator -/

namespace Oscillator

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem velocity_hamiltonian (m : ι → ℝ) (k : ℝ) (i : ι) :
    velocity (hamiltonian m k) i = algebraMap ℝ (PhaseSpace ι) (m i)⁻¹ * p i := by
  rw [velocity, hamiltonian, map_add, partialDerivation_inr_kineticEnergy,
    partialDerivation_inr_oscillatorPotential, add_zero]

theorem partialDerivation_inl_hamiltonian (m : ι → ℝ) (k : ℝ) (i : ι) :
    partialDerivation (Sum.inl i) (hamiltonian m k) = algebraMap ℝ (PhaseSpace ι) k * q i := by
  rw [hamiltonian, map_add, partialDerivation_inl_kineticEnergy,
    partialDerivation_inl_oscillatorPotential, zero_add]

theorem frictionalForce_diagonal (a : ι → ℝ) (H : PhaseSpace ι) (i : ι) :
    frictionalForce (Matrix.diagonal a) H i = algebraMap ℝ (PhaseSpace ι) (a i) * velocity H i := by
  rw [frictionalForce, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro k _ hki
    rw [Matrix.diagonal_apply_ne _ (Ne.symm hki), map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

omit [DecidableEq ι] in
/-- A diagonal matrix with non-negative entries is positive semidefinite. -/
theorem dotProduct_diagonal_mulVec_nonneg [DecidableEq ι] {a : ι → ℝ} (ha : ∀ i, 0 ≤ a i)
    (v : ι → ℝ) : 0 ≤ v ⬝ᵥ Matrix.diagonal a *ᵥ v := by
  rw [dotProduct]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  nlinarith [ha i, mul_self_nonneg (v i)]

/-- The equations of the oscillator with friction: `q̇ᵢ = pᵢ/mᵢ` and
`ṗᵢ = −k qᵢ − aᵢ pᵢ/mᵢ`. -/
theorem isIntegralCurve_dissipativeField_iff (m a : ι → ℝ) (k : ℝ) (c : ι ⊕ ι → TimeFunction) :
    IsIntegralCurve (dissipativeField (Matrix.diagonal a) (hamiltonian m k)) c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) =
        algebraMap ℝ TimeFunction (m i)⁻¹ * c (Sum.inr i)) ∧
      ∀ i, timeDerivative (c (Sum.inr i)) =
        -(algebraMap ℝ TimeFunction k * c (Sum.inl i)) -
          algebraMap ℝ TimeFunction (a i) *
            (algebraMap ℝ TimeFunction (m i)⁻¹ * c (Sum.inr i)) := by
  rw [Mechanics.isIntegralCurve_dissipativeField_iff]
  simp only [frictionalForce_diagonal, velocity_hamiltonian, partialDerivation_inl_hamiltonian,
    SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, p, q, lift_generator]

/-- The motions of the oscillator with the friction `aᵢ = 2 mᵢ γᵢ` are the
damped oscillations: every position satisfies `ẍ + 2γᵢ ẋ + ω₀ᵢ² x = 0`, and
`pᵢ = mᵢ q̇ᵢ` (Landau–Lifshitz (25.1)). -/
theorem isIntegralCurve_dissipativeField_iff_isDamped {m a γ ω₀ : ι → ℝ} {k : ℝ}
    (hm : ∀ i, m i ≠ 0) (hk : ∀ i, k = m i * ω₀ i ^ 2) (ha : ∀ i, a i = 2 * m i * γ i)
    (c : ι ⊕ ι → TimeFunction) :
    IsIntegralCurve (dissipativeField (Matrix.diagonal a) (hamiltonian m k)) c ↔
      ∀ i, IsDamped (γ i) (ω₀ i) (c (Sum.inl i)) ∧
        c (Sum.inr i) = algebraMap ℝ TimeFunction (m i) * timeDerivative (c (Sum.inl i)) := by
  rw [isIntegralCurve_dissipativeField_iff, ← forall_and]
  refine forall_congr' fun i => ?_
  have hinv : algebraMap ℝ TimeFunction (m i)⁻¹ * algebraMap ℝ TimeFunction (m i) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (hm i), map_one]
  have hK : algebraMap ℝ TimeFunction k =
      algebraMap ℝ TimeFunction (m i) * algebraMap ℝ TimeFunction (ω₀ i ^ 2) := by
    rw [← map_mul, ← hk i]
  have hA : algebraMap ℝ TimeFunction (a i) =
      algebraMap ℝ TimeFunction (m i) * algebraMap ℝ TimeFunction (2 * γ i) := by
    rw [← map_mul, ha i]
    congr 1
    ring
  unfold IsDamped
  rw [hK, hA]
  constructor
  · rintro ⟨hq, hp⟩
    refine ⟨?_, ?_⟩
    · rw [hq, SmoothDerivation.map_algebraMap_mul, smul_eq_mul, hp]
      linear_combination (-(algebraMap ℝ TimeFunction (ω₀ i ^ 2) * c (Sum.inl i)) -
        algebraMap ℝ TimeFunction (2 * γ i) *
          (algebraMap ℝ TimeFunction (m i)⁻¹ * c (Sum.inr i))) * hinv
    · rw [hq]
      linear_combination (-c (Sum.inr i)) * hinv
  · rintro ⟨hq, hp⟩
    refine ⟨?_, ?_⟩
    · rw [hp]
      linear_combination (-timeDerivative (c (Sum.inl i))) * hinv
    · rw [hp, SmoothDerivation.map_algebraMap_mul, smul_eq_mul, hq]
      linear_combination (algebraMap ℝ TimeFunction (m i) * algebraMap ℝ TimeFunction (2 * γ i) *
        timeDerivative (c (Sum.inl i))) * hinv

/-- With non-negative friction the energy of the oscillator does not increase
along the motion. -/
theorem energy_antitone {m a : ι → ℝ} {k : ℝ} (ha : ∀ i, 0 ≤ a i) {c : ι ⊕ ι → TimeFunction}
    (h : IsIntegralCurve (dissipativeField (Matrix.diagonal a) (hamiltonian m k)) c) :
    Antitone fun t : ℝ => FreeSmoothRing.lift c (hamiltonian m k) fun _ => t :=
  h.energy_antitone (dotProduct_diagonal_mulVec_nonneg ha)

end Oscillator

end ProjectAInos.Mechanics
