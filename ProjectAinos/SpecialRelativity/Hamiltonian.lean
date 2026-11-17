/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Mechanics.Poisson.HamiltonianField
public import ProjectAinos.SmoothAlgebra.RelEnergy
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# The coordinate-time Hamiltonian of a free relativistic particle

For a mass `m ≠ 0` the energy `H = √(m² + Σ pᵢ²)` is smooth in all momenta, so it is an element
`FreeParticle.hamiltonian d m` of the canonical phase space of `d` space coordinates
(Landau–Lifshitz, *The Classical Theory of Fields*, §9). The units have `c = 1`.

* `canonical_q_hamiltonian`, `canonical_p_hamiltonian`: Hamilton's equations are `q̇ᵢ = pᵢ/H`
  and `ṗᵢ = 0`; `isTrajectory_iff` states them along a curve.
* `sum_velocity_mul_self`: `Σ (pᵢ/H)² = 1 − m²/H²`, and `sum_sq_hamiltonianField_lt_one`: at
  every point of the phase space the speed is less than one.
* `isIntegral_p`, `isIntegral_angularMomentum`: the momentum and the orbital angular momentum
  `qᵢ pⱼ − qⱼ pᵢ` are integrals of the motion, and `canonical_centreOfEnergy_hamiltonian` is
  `{H qᵢ, H} = pᵢ`.
* `isTrajectory_motion`: `q(t) = q₀ + t p₀/H(p₀)`, `p(t) = p₀` is a trajectory, and
  `realCurve_eq_motion` shows that every trajectory has this form.
* `flowDomain_hamiltonianField`: the Hamiltonian field is bounded, so its flow is defined for
  all times and points; `measurePreserving_hamiltonianFlow` is Liouville's theorem for it.

The Hamiltonian is defined on all momenta. The Lagrangian `−m√(1 − Σ vᵢ²)` is defined on the
ball of velocities, and the Legendre transformation between the two is a separate statement.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace ProjectAinos.SpecialRelativity.FreeParticle

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace Mechanics
open SmoothGeometry SmoothGeometry.NonlinearODE

variable {d : ℕ} {m : ℝ}

/-- The Hamiltonian `√(m² + Σ pᵢ²)` of a free particle of mass `m` in `d` space dimensions. -/
def hamiltonian (d : ℕ) (m : ℝ) : PhaseSpace (Fin d) := relEnergy m p

/-- The velocity `pᵢ/H` as a function on the phase space. -/
def velocity (d : ℕ) (m : ℝ) (i : Fin d) : PhaseSpace (Fin d) := relEnergyInv m p * p i

/-! ### Hamilton's equations -/

theorem partialDerivation_inr_hamiltonian (hm : m ≠ 0) (i : Fin d) :
    partialDerivation (Sum.inr i) (hamiltonian d m) = velocity d m i := by
  rw [hamiltonian, SmoothDerivation.apply_relEnergy hm, Finset.sum_eq_single i, velocity]
  · rw [p, partialDerivation_generator_self, mul_one]
  · intro j _ hj
    rw [p, partialDerivation_generator_of_ne (c := Sum.inr i) (i := Sum.inr j) (by simpa using hj),
      mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem partialDerivation_inl_hamiltonian (hm : m ≠ 0) (i : Fin d) :
    partialDerivation (Sum.inl i) (hamiltonian d m) = 0 := by
  rw [hamiltonian, SmoothDerivation.apply_relEnergy hm, Finset.sum_eq_zero, mul_zero]
  intro j _
  rw [p, partialDerivation_generator_of_ne (c := Sum.inl i) (i := Sum.inr j) (by simp), mul_zero]

/-- `{qᵢ, H} = pᵢ/H`. -/
theorem canonical_q_hamiltonian (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (q i) (hamiltonian d m) = velocity d m i := by
  rw [canonical_q_bracket, partialDerivation_inr_hamiltonian hm]

/-- `{pᵢ, H} = 0`. -/
theorem canonical_p_hamiltonian (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (p i) (hamiltonian d m) = 0 := by
  rw [canonical_p_bracket, partialDerivation_inl_hamiltonian hm, neg_zero]

/-- The square of the Hamiltonian is `m² + Σ pᵢ²`. -/
theorem hamiltonian_mul_self (hm : m ≠ 0) :
    hamiltonian d m * hamiltonian d m =
      algebraMap ℝ (PhaseSpace (Fin d)) (m ^ 2) + ∑ i, p i * p i :=
  relEnergy_mul_self hm p

/-- `Σ (pᵢ/H)² = 1 − m²/H²`. -/
theorem sum_velocity_mul_self (hm : m ≠ 0) :
    ∑ i, velocity d m i * velocity d m i =
      1 - algebraMap ℝ (PhaseSpace (Fin d)) (m ^ 2) * (relEnergyInv m p * relEnergyInv m p) :=
  sum_relEnergyInv_mul_sq hm p

/-! ### Integrals of the motion -/

/-- The momentum is conserved. -/
theorem isIntegral_p (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).IsIntegral (hamiltonian d m) (p i) :=
  canonical_p_hamiltonian hm i

/-- The orbital angular momentum `qᵢ pⱼ − qⱼ pᵢ` is conserved. -/
theorem isIntegral_angularMomentum (hm : m ≠ 0) (i j : Fin d) :
    (canonical (Fin d)).IsIntegral (hamiltonian d m) (q i * p j - q j * p i) := by
  change (canonical (Fin d)).bracket (q i * p j - q j * p i) (hamiltonian d m) = 0
  rw [AlmostPoissonStructure.bracket_sub_left, AlmostPoissonStructure.bracket_mul_left,
    AlmostPoissonStructure.bracket_mul_left, canonical_p_hamiltonian hm,
    canonical_p_hamiltonian hm, canonical_q_hamiltonian hm, canonical_q_hamiltonian hm, velocity,
    velocity]
  ring

/-- `{H qᵢ, H} = pᵢ`: the centre of energy moves with the momentum. -/
theorem canonical_centreOfEnergy_hamiltonian (hm : m ≠ 0) (i : Fin d) :
    (canonical (Fin d)).bracket (hamiltonian d m * q i) (hamiltonian d m) = p i := by
  have h : hamiltonian d m * relEnergyInv m p = 1 := relEnergy_mul_relEnergyInv hm p
  rw [AlmostPoissonStructure.bracket_mul_left, canonical_q_hamiltonian hm,
    AlmostPoissonStructure.bracket_self, mul_zero, add_zero, velocity]
  linear_combination p i * h

/-! ### The Hamiltonian field -/

/-- The value of the Hamiltonian at a point is the energy of its momentum. -/
theorem lift_hamiltonian (z : Fin d ⊕ Fin d → ℝ) :
    FreeSmoothRing.lift z (hamiltonian d m) = relEnergy m fun i => z (Sum.inr i) := by
  rw [hamiltonian, SmoothRingHom.map_relEnergy]
  simp only [p, lift_generator]

/-- For a positive mass the value of the Hamiltonian is `√(m² + Σ pᵢ²)`. -/
theorem lift_hamiltonian_eq_sqrt (hm : 0 < m) (z : Fin d ⊕ Fin d → ℝ) :
    FreeSmoothRing.lift z (hamiltonian d m) = Real.sqrt (m ^ 2 + ∑ i, z (Sum.inr i) ^ 2) := by
  rw [lift_hamiltonian, relEnergy_real hm]

/-- The Hamiltonian field: `q̇ᵢ = pᵢ/H`. -/
theorem hamiltonianField_inl (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) (i : Fin d) :
    hamiltonianField (hamiltonian d m) z (Sum.inl i) =
      relEnergyInv m (fun j => z (Sum.inr j)) * z (Sum.inr i) := by
  rw [Mechanics.hamiltonianField_inl, partialDerivation_inr_hamiltonian hm, ← lift_real, velocity,
    SmoothRingHom.map_mul, SmoothRingHom.map_relEnergyInv]
  simp only [p, lift_generator]

/-- The Hamiltonian field: `ṗᵢ = 0`. -/
theorem hamiltonianField_inr (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) (i : Fin d) :
    hamiltonianField (hamiltonian d m) z (Sum.inr i) = 0 := by
  rw [Mechanics.hamiltonianField_inr, partialDerivation_inl_hamiltonian hm]
  exact neg_zero

/-- At every point of the phase space the speed is less than the speed of light. -/
theorem sum_sq_hamiltonianField_lt_one (hm : m ≠ 0) (z : Fin d ⊕ Fin d → ℝ) :
    ∑ i, hamiltonianField (hamiltonian d m) z (Sum.inl i) ^ 2 < 1 := by
  simp only [hamiltonianField_inl hm]
  exact sum_sq_relEnergyInv_mul_lt_one hm _

/-- The flow of the free particle is defined for all times and points. -/
theorem flowDomain_hamiltonianField (hm : m ≠ 0) :
    flowDomain (hamiltonianField (hamiltonian d m)) = univ := by
  refine flowDomain_eq_univ_of_norm_le (contDiff_hamiltonianField _) (a := 1) (b := 0)
    fun z => ?_
  rw [zero_mul, add_zero]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun a => ?_
  rcases a with i | i
  · rw [hamiltonianField_inl hm, Real.norm_eq_abs]
    exact (abs_relEnergyInv_mul_lt_one hm _ i).le
  · rw [hamiltonianField_inr hm, norm_zero]
    exact zero_le_one

/-- Liouville's theorem for the free particle. -/
theorem measurePreserving_hamiltonianFlow (hm : m ≠ 0) (t : ℝ) :
    MeasurePreserving (fun z => flow (hamiltonianField (hamiltonian d m)) (t, z))
      volume volume :=
  Mechanics.measurePreserving_hamiltonianFlow _ (flowDomain_hamiltonianField hm) t

/-! ### Trajectories -/

/-- A curve is a trajectory if and only if its momentum is constant and its velocity is
`p/H`. -/
theorem isTrajectory_iff (hm : m ≠ 0) (c : Fin d ⊕ Fin d → TimeFunction) :
    IsTrajectory (canonical (Fin d)) (hamiltonian d m) c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) =
        relEnergyInv m (fun j => c (Sum.inr j)) * c (Sum.inr i)) ∧
      ∀ i, timeDerivative (c (Sum.inr i)) = 0 := by
  rw [isTrajectory_canonical_iff]
  simp only [partialDerivation_inr_hamiltonian hm, partialDerivation_inl_hamiltonian hm, velocity,
    SmoothRingHom.map_mul, SmoothRingHom.map_relEnergyInv, p, lift_generator,
    SmoothRingHom.map_zero, neg_zero]

/-- Along a trajectory the momentum takes the same value at all times. -/
theorem momentum_eq_of_isTrajectory (hm : m ≠ 0) {c : Fin d ⊕ Fin d → TimeFunction}
    (h : IsTrajectory (canonical (Fin d)) (hamiltonian d m) c) (i : Fin d) (s t : Fin 1 → ℝ) :
    c (Sum.inr i) s = c (Sum.inr i) t :=
  TimeFunction.eq_of_timeDerivative_eq_zero (((isTrajectory_iff hm c).mp h).2 i) s t

/-- The motion with the initial position `q₀` and the momentum `p₀`:
`q(t) = q₀ + t p₀/H(p₀)` and `p(t) = p₀`. -/
def motion (m : ℝ) (q₀ p₀ : Fin d → ℝ) : Fin d ⊕ Fin d → TimeFunction :=
  Sum.elim
    (fun i => SmoothOperation.ofContDiff
      (fun s : Fin 1 → ℝ => q₀ i + s 0 * (relEnergyInv m p₀ * p₀ i))
      (contDiff_const.add ((contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).mul contDiff_const)))
    (fun i => SmoothOperation.const 1 (p₀ i))

theorem realCurve_motion (m : ℝ) (q₀ p₀ : Fin d → ℝ) (t : ℝ) :
    realCurve (motion m q₀ p₀) t =
      Sum.elim (fun i => q₀ i + t * (relEnergyInv m p₀ * p₀ i)) p₀ := by
  funext a
  rcases a with i | i <;> rfl

theorem realCurve_motion_zero (m : ℝ) (q₀ p₀ : Fin d → ℝ) :
    realCurve (motion m q₀ p₀) 0 = Sum.elim q₀ p₀ := by
  rw [realCurve_motion]
  funext a
  rcases a with i | i
  · simp only [Sum.elim_inl, zero_mul, add_zero]
  · rfl

/-- The motion in a straight line with the velocity `p₀/H(p₀)` is a trajectory. -/
theorem isTrajectory_motion (hm : m ≠ 0) (q₀ p₀ : Fin d → ℝ) :
    IsTrajectory (canonical (Fin d)) (hamiltonian d m) (motion m q₀ p₀) := by
  rw [isTrajectory_canonical_iff_hasDerivAt]
  intro t
  rw [hasDerivAt_pi]
  rintro (i | i)
  · rw [hamiltonianField_inl hm, realCurve_motion]
    change HasDerivAt (fun s : ℝ => q₀ i + s * (relEnergyInv m p₀ * p₀ i))
      (relEnergyInv m p₀ * p₀ i) t
    simpa using ((hasDerivAt_id t).mul_const (relEnergyInv m p₀ * p₀ i)).const_add (q₀ i)
  · rw [hamiltonianField_inr hm]
    simp only [realCurve_motion, Sum.elim_inr]
    exact hasDerivAt_const t (p₀ i)

/-- Every trajectory is a motion in a straight line with the velocity `p/H`. -/
theorem realCurve_eq_motion (hm : m ≠ 0) {c : Fin d ⊕ Fin d → TimeFunction}
    (h : IsTrajectory (canonical (Fin d)) (hamiltonian d m) c) (t : ℝ) :
    realCurve c t = realCurve (motion m (fun i => realCurve c 0 (Sum.inl i))
      fun i => realCurve c 0 (Sum.inr i)) t := by
  have h0 : realCurve (motion m (fun i => realCurve c 0 (Sum.inl i))
      fun i => realCurve c 0 (Sum.inr i)) 0 = realCurve c 0 := by
    rw [realCurve_motion_zero]
    funext a
    rcases a with i | i <;> rfl
  have h1 := (h.flow_eq t).2
  have h2 := ((isTrajectory_motion hm (fun i => realCurve c 0 (Sum.inl i))
    fun i => realCurve c 0 (Sum.inr i)).flow_eq t).2
  rw [h0] at h2
  exact h1.symm.trans h2

/-- The flow of the free particle: `(q, p) ↦ (q + t p/H(p), p)`. -/
theorem flow_hamiltonianField (hm : m ≠ 0) (t : ℝ) (q₀ p₀ : Fin d → ℝ) :
    flow (hamiltonianField (hamiltonian d m)) (t, Sum.elim q₀ p₀) =
      Sum.elim (fun i => q₀ i + t * (relEnergyInv m p₀ * p₀ i)) p₀ := by
  have h := ((isTrajectory_motion hm q₀ p₀).flow_eq t).2
  rwa [realCurve_motion_zero, realCurve_motion] at h

end ProjectAinos.SpecialRelativity.FreeParticle
