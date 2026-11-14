/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.FreeChainRule
public import ProjectAInos.Mechanics.Poisson.Trajectory
public import ProjectAInos.Mechanics.Poisson.Virial
public import ProjectAInos.Mechanics.Oscillations.Damped
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Jacobi's theorem on complete integrals

Let `S` be a smooth function of the co-ordinates `q`, of as many parameters
`α`, and of the time `t`, that satisfies the Hamilton–Jacobi equation
`∂S/∂t + H(q, ∂S/∂q) = 0` (Landau–Lifshitz §47). Let `q(t)` be a curve along
which the derivatives `∂S/∂αᵢ` are constant, for fixed values of the
parameters, and suppose that the matrix `∂²S/∂αᵢ∂qₖ` along the curve is
non-degenerate. Then `q(t)` with the momenta `pᵢ = ∂S/∂qᵢ` satisfies Hamilton's
equations.

The functions of `(q, α, t)` are the free C-infinity ring on
`ι ⊕ ι ⊕ Unit`. The Hamiltonian is an element of the canonical phase space,
and `substitution S` is the morphism `qᵢ ↦ qᵢ`, `pᵢ ↦ ∂S/∂qᵢ`.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.CompleteIntegral

open SmoothAlgebra SmoothRing FreeSmoothRing PhaseSpace

variable {ι : Type*} [DecidableEq ι]

/-- The functions of the co-ordinates `q`, the parameters `α` and the time. -/
abbrev ActionSpace (ι : Type*) := FreeSmoothRing (ι ⊕ ι ⊕ Unit)

/-- The index of the co-ordinate `qᵢ`. -/
abbrev qIndex (i : ι) : ι ⊕ ι ⊕ Unit := Sum.inl i

/-- The index of the parameter `αᵢ`. -/
abbrev αIndex (i : ι) : ι ⊕ ι ⊕ Unit := Sum.inr (Sum.inl i)

/-- The index of the time. -/
abbrev tIndex : ι ⊕ ι ⊕ Unit := Sum.inr (Sum.inr ())

/-- The morphism `qᵢ ↦ qᵢ`, `pᵢ ↦ ∂S/∂qᵢ` from the phase space. -/
def substitution (S : ActionSpace ι) : SmoothRingHom (PhaseSpace ι) (ActionSpace ι) :=
  FreeSmoothRing.lift (Sum.elim (fun i => generator (qIndex i))
    fun i => partialDerivation (qIndex i) S)

/-- `S` satisfies the Hamilton–Jacobi equation `∂S/∂t + H(q, ∂S/∂q) = 0`. -/
def IsHamiltonJacobi (H : PhaseSpace ι) (S : ActionSpace ι) : Prop :=
  partialDerivation tIndex S + substitution S H = 0

/-- The values of the generators along a curve `q(t)` with fixed parameters. -/
def curveValue (Q : ι → TimeFunction) (α : ι → ℝ) : ι ⊕ ι ⊕ Unit → TimeFunction :=
  Sum.elim Q (Sum.elim (fun i => algebraMap ℝ TimeFunction (α i)) fun _ => TimeFunction.time)

/-- Evaluation of a function of `(q, α, t)` along a curve `q(t)` with fixed
parameters. -/
def along (Q : ι → TimeFunction) (α : ι → ℝ) : SmoothRingHom (ActionSpace ι) TimeFunction :=
  FreeSmoothRing.lift (curveValue Q α)

/-- The momenta `pᵢ = ∂S/∂qᵢ` along the curve. -/
def momentum (S : ActionSpace ι) (Q : ι → TimeFunction) (α : ι → ℝ) (i : ι) : TimeFunction :=
  along Q α (partialDerivation (qIndex i) S)

/-- An observable of the phase space along the curve `(q, ∂S/∂q)` is its
substitution evaluated along `q`. -/
theorem along_substitution (S : ActionSpace ι) (Q : ι → TimeFunction) (α : ι → ℝ)
    (f : PhaseSpace ι) :
    along Q α (substitution S f) = FreeSmoothRing.lift (Sum.elim Q (momentum S Q α)) f := by
  have h : (along Q α).comp (substitution S) =
      FreeSmoothRing.lift (Sum.elim Q (momentum S Q α)) :=
    FreeSmoothRing.hom_ext fun a => by
      rcases a with i | i
      · rw [SmoothRingHom.comp_apply, substitution, lift_generator, Sum.elim_inl, along,
          lift_generator, lift_generator, curveValue, Sum.elim_inl, Sum.elim_inl]
      · rw [SmoothRingHom.comp_apply, substitution, lift_generator, Sum.elim_inr,
          lift_generator, Sum.elim_inr, momentum]
  exact congrArg (fun φ : SmoothRingHom (PhaseSpace ι) TimeFunction => φ f) h

variable [Fintype ι]

/-- The time derivative of a function of `(q, α, t)` along a curve with fixed
parameters: `d/dt f = Σₖ (∂f/∂qₖ) q̇ₖ + ∂f/∂t`. -/
theorem timeDerivative_along (Q : ι → TimeFunction) (α : ι → ℝ) (f : ActionSpace ι) :
    timeDerivative (along Q α f) =
      ∑ k, along Q α (partialDerivation (qIndex k) f) * timeDerivative (Q k) +
        along Q α (partialDerivation tIndex f) := by
  rw [along, derivation_lift_mul, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [curveValue, Sum.elim_inl, Sum.elim_inr, SmoothDerivation.map_algebraMap, mul_zero,
    Finset.sum_const_zero, zero_add, Finset.univ_unique, Finset.sum_singleton,
    TimeFunction.timeDerivative_time, mul_one]

/-- The derivative of the substitution of an observable with respect to a
variable `c` that is not a co-ordinate: only the momenta `∂S/∂qₖ` depend on
`c`. -/
theorem partialDerivation_substitution_of_ne (S : ActionSpace ι) (f : PhaseSpace ι)
    {c : ι ⊕ ι ⊕ Unit} (hc : ∀ k, qIndex k ≠ c) :
    partialDerivation c (substitution S f) =
      ∑ k, substitution S (partialDerivation (Sum.inr k) f) *
        partialDerivation c (partialDerivation (qIndex k) S) := by
  rw [substitution, derivation_lift_mul, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [Finset.sum_eq_zero, zero_add]
  intro k _
  rw [partialDerivation_generator_of_ne (hc k), mul_zero]

/-- The derivative of the substitution of an observable with respect to a
co-ordinate. -/
theorem partialDerivation_substitution_q (S : ActionSpace ι) (f : PhaseSpace ι) (i : ι) :
    partialDerivation (qIndex i) (substitution S f) =
      substitution S (partialDerivation (Sum.inl i) f) +
        ∑ k, substitution S (partialDerivation (Sum.inr k) f) *
          partialDerivation (qIndex i) (partialDerivation (qIndex k) S) := by
  rw [substitution, derivation_lift_mul, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr]
  congr 1
  rw [Finset.sum_eq_single i]
  · rw [partialDerivation_generator_self, mul_one]
  · intro k _ hki
    rw [partialDerivation_generator_of_ne (c := qIndex i) (i := qIndex k)
      (fun h => hki (Sum.inl.inj h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The time derivative of `∂S/∂c` along a curve with fixed parameters. -/
theorem timeDerivative_along_partialDerivation (S : ActionSpace ι) (Q : ι → TimeFunction)
    (α : ι → ℝ) (c : ι ⊕ ι ⊕ Unit) :
    timeDerivative (along Q α (partialDerivation c S)) =
      ∑ k, along Q α (partialDerivation c (partialDerivation (qIndex k) S)) *
          timeDerivative (Q k) +
        along Q α (partialDerivation c (partialDerivation tIndex S)) := by
  rw [timeDerivative_along, partialDerivation_comm tIndex c S]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [partialDerivation_comm (qIndex k) c S]

/-- The Hamilton–Jacobi equation differentiated with respect to a variable
that is not a co-ordinate, along the curve. -/
theorem IsHamiltonJacobi.along_partialDerivation_of_ne {H : PhaseSpace ι} {S : ActionSpace ι}
    (hS : IsHamiltonJacobi H S) (Q : ι → TimeFunction) (α : ι → ℝ) {c : ι ⊕ ι ⊕ Unit}
    (hc : ∀ k, qIndex k ≠ c) :
    along Q α (partialDerivation c (partialDerivation tIndex S)) +
      ∑ k, along Q α (partialDerivation c (partialDerivation (qIndex k) S)) *
        FreeSmoothRing.lift (Sum.elim Q (momentum S Q α))
          (partialDerivation (Sum.inr k) H) = 0 := by
  have h := congrArg (fun f : ActionSpace ι => along Q α (partialDerivation c f)) hS
  simp only [map_add, map_zero, SmoothRingHom.map_add, SmoothRingHom.map_zero] at h
  rw [partialDerivation_substitution_of_ne S H hc, SmoothRingHom.map_sum] at h
  simp only [SmoothRingHom.map_mul, along_substitution] at h
  rw [← h]
  congr 1
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- The Hamilton–Jacobi equation differentiated with respect to a co-ordinate,
along the curve. -/
theorem IsHamiltonJacobi.along_partialDerivation_q {H : PhaseSpace ι} {S : ActionSpace ι}
    (hS : IsHamiltonJacobi H S) (Q : ι → TimeFunction) (α : ι → ℝ) (i : ι) :
    along Q α (partialDerivation (qIndex i) (partialDerivation tIndex S)) +
      (FreeSmoothRing.lift (Sum.elim Q (momentum S Q α)) (partialDerivation (Sum.inl i) H) +
        ∑ k, along Q α (partialDerivation (qIndex i) (partialDerivation (qIndex k) S)) *
          FreeSmoothRing.lift (Sum.elim Q (momentum S Q α))
            (partialDerivation (Sum.inr k) H)) = 0 := by
  have h := congrArg (fun f : ActionSpace ι => along Q α (partialDerivation (qIndex i) f)) hS
  simp only [map_add, map_zero, SmoothRingHom.map_add, SmoothRingHom.map_zero] at h
  rw [partialDerivation_substitution_q, SmoothRingHom.map_add, SmoothRingHom.map_sum] at h
  simp only [SmoothRingHom.map_mul, along_substitution] at h
  rw [← h]
  congr 2
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- Jacobi's theorem (Landau–Lifshitz §47). Let `S` satisfy the
Hamilton–Jacobi equation of `H`. Let `q(t)` be a curve along which every
`∂S/∂αᵢ` has zero time derivative, and let the matrix `∂²S/∂αᵢ∂qₖ` along the
curve be non-degenerate. Then `q(t)` with the momenta `pᵢ = ∂S/∂qᵢ` is a
trajectory of `H`. -/
theorem isTrajectory_of_isHamiltonJacobi {H : PhaseSpace ι} {S : ActionSpace ι}
    (hS : IsHamiltonJacobi H S) {Q : ι → TimeFunction} {α : ι → ℝ}
    (hβ : ∀ i, timeDerivative (along Q α (partialDerivation (αIndex i) S)) = 0)
    (hnd : ∀ w : ι → TimeFunction,
      (∀ i, ∑ k, along Q α (partialDerivation (αIndex i) (partialDerivation (qIndex k) S)) *
        w k = 0) → ∀ k, w k = 0) :
    IsTrajectory (canonical ι) H (Sum.elim Q (momentum S Q α)) := by
  -- The first set of Hamilton's equations, from the derivatives with respect to `α`.
  have hq := hnd (fun k => timeDerivative (Q k) -
      FreeSmoothRing.lift (Sum.elim Q (momentum S Q α)) (partialDerivation (Sum.inr k) H))
    fun i => by
      have h1 := hS.along_partialDerivation_of_ne Q α (c := αIndex i) (fun k => by simp)
      have h2 := hβ i
      rw [timeDerivative_along_partialDerivation] at h2
      have e1 := eq_neg_of_add_eq_zero_left h2
      have e2 := eq_neg_of_add_eq_zero_right h1
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [e1, e2, sub_self]
  have hq' := fun k => sub_eq_zero.mp (hq k)
  rw [isTrajectory_canonical_iff]
  refine ⟨fun i => hq' i, fun i => ?_⟩
  -- The second set, from the derivative with respect to `qᵢ`.
  have h1 := hS.along_partialDerivation_q Q α i
  have h2 := timeDerivative_along_partialDerivation S Q α (qIndex i)
  simp only [hq'] at h2
  rw [add_comm (FreeSmoothRing.lift _ _) _, ← add_assoc, add_comm (along _ _ _) _] at h1
  exact h2.trans (eq_neg_of_add_eq_zero_left h1)

/-! ### The free particle -/

/-- The complete integral `S = α q − α² t / 2m` of the free particle in one
dimension. -/
def freeAction (m : ℝ) : ActionSpace (Fin 1) :=
  generator (αIndex 0) * generator (qIndex 0) -
    algebraMap ℝ (ActionSpace (Fin 1)) (m⁻¹ / 2) *
      (generator (αIndex 0) * generator (αIndex 0) * generator tIndex)

theorem partialDerivation_q_freeAction (m : ℝ) :
    partialDerivation (qIndex 0) (freeAction m) = generator (αIndex (0 : Fin 1)) := by
  have h1 : partialDerivation (qIndex (0 : Fin 1)) (generator (αIndex (0 : Fin 1))) = 0 :=
    partialDerivation_generator_of_ne (by simp)
  have h2 : partialDerivation (qIndex (0 : Fin 1)) (generator (qIndex (0 : Fin 1))) = 1 :=
    partialDerivation_generator_self _
  have h3 : partialDerivation (qIndex (0 : Fin 1)) (generator (tIndex : Fin 1 ⊕ Fin 1 ⊕ Unit)) =
      0 := partialDerivation_generator_of_ne (by simp)
  rw [freeAction, map_sub, SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul,
    SmoothDerivation.map_mul, SmoothDerivation.map_mul, h1, h2, h3]
  simp

theorem partialDerivation_t_freeAction (m : ℝ) :
    partialDerivation tIndex (freeAction m) =
      -(algebraMap ℝ (ActionSpace (Fin 1)) (m⁻¹ / 2) *
        (generator (αIndex 0) * generator (αIndex 0))) := by
  have h1 : partialDerivation (tIndex : Fin 1 ⊕ Fin 1 ⊕ Unit) (generator (αIndex (0 : Fin 1))) =
      0 := partialDerivation_generator_of_ne (by simp)
  have h2 : partialDerivation (tIndex : Fin 1 ⊕ Fin 1 ⊕ Unit) (generator (qIndex (0 : Fin 1))) =
      0 := partialDerivation_generator_of_ne (by simp)
  have h3 : partialDerivation (tIndex : Fin 1 ⊕ Fin 1 ⊕ Unit)
      (generator (tIndex : Fin 1 ⊕ Fin 1 ⊕ Unit)) = 1 := partialDerivation_generator_self _
  rw [freeAction, map_sub, SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul,
    SmoothDerivation.map_mul, SmoothDerivation.map_mul, h1, h2, h3]
  simp

/-- `S = α q − α² t / 2m` satisfies the Hamilton–Jacobi equation of the free
particle, `∂S/∂t + (∂S/∂q)² / 2m = 0`. -/
theorem isHamiltonJacobi_freeAction (m : ℝ) :
    IsHamiltonJacobi (kineticEnergy fun _ : Fin 1 => m) (freeAction m) := by
  unfold IsHamiltonJacobi
  rw [partialDerivation_t_freeAction, kineticEnergy, Fin.sum_univ_one, SmoothRingHom.map_mul,
    SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap, substitution, PhaseSpace.p,
    lift_generator, Sum.elim_inr, partialDerivation_q_freeAction]
  exact neg_add_cancel _

theorem partialDerivation_α_freeAction (m : ℝ) :
    partialDerivation (αIndex 0) (freeAction m) =
      generator (qIndex 0) - algebraMap ℝ (ActionSpace (Fin 1)) m⁻¹ *
        (generator (αIndex 0) * generator tIndex) := by
  have h1 : partialDerivation (αIndex (0 : Fin 1)) (generator (αIndex (0 : Fin 1))) = 1 :=
    partialDerivation_generator_self _
  have h2 : partialDerivation (αIndex (0 : Fin 1)) (generator (qIndex (0 : Fin 1))) = 0 :=
    partialDerivation_generator_of_ne (by simp)
  have h3 : partialDerivation (αIndex (0 : Fin 1)) (generator (tIndex : Fin 1 ⊕ Fin 1 ⊕ Unit)) =
      0 := partialDerivation_generator_of_ne (by simp)
  have hm : algebraMap ℝ (ActionSpace (Fin 1)) (m⁻¹ / 2) * 2 =
      algebraMap ℝ (ActionSpace (Fin 1)) m⁻¹ := by
    rw [← map_ofNat (algebraMap ℝ (ActionSpace (Fin 1))) 2, ← map_mul]
    congr 1
    ring
  rw [freeAction, map_sub, SmoothDerivation.map_algebraMap_mul, SmoothDerivation.map_mul,
    SmoothDerivation.map_mul, SmoothDerivation.map_mul, h1, h2, h3]
  simp only [smul_eq_mul, mul_one, mul_zero, zero_add]
  linear_combination (-(generator (αIndex (0 : Fin 1)) * generator tIndex)) * hm

/-- Jacobi's theorem applied to the free particle: the uniform motion
`q = β + (α/m) t` with the momentum `∂S/∂q` is a trajectory of `p²/2m`. -/
theorem isTrajectory_freeAction (m α₀ β : ℝ) :
    IsTrajectory (canonical (Fin 1)) (kineticEnergy fun _ : Fin 1 => m)
      (Sum.elim
        (fun _ => algebraMap ℝ TimeFunction β +
          algebraMap ℝ TimeFunction (m⁻¹ * α₀) * TimeFunction.time)
        (momentum (freeAction m)
          (fun _ => algebraMap ℝ TimeFunction β +
            algebraMap ℝ TimeFunction (m⁻¹ * α₀) * TimeFunction.time) fun _ => α₀)) := by
  refine isTrajectory_of_isHamiltonJacobi (isHamiltonJacobi_freeAction m) (fun i => ?_)
    (fun w hw k => ?_)
  · rw [Subsingleton.elim i 0, partialDerivation_α_freeAction]
    have h : along (fun _ : Fin 1 => algebraMap ℝ TimeFunction β +
          algebraMap ℝ TimeFunction (m⁻¹ * α₀) * TimeFunction.time) (fun _ => α₀)
        (generator (qIndex 0) - algebraMap ℝ (ActionSpace (Fin 1)) m⁻¹ *
          (generator (αIndex 0) * generator tIndex)) = algebraMap ℝ TimeFunction β := by
      simp only [along, curveValue, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
        SmoothRingHom.map_algebraMap, lift_generator, Sum.elim_inl, Sum.elim_inr, map_mul]
      ring
    rw [h, SmoothDerivation.map_algebraMap]
  · have h := hw 0
    rw [Fin.sum_univ_one, partialDerivation_q_freeAction] at h
    have h1 : partialDerivation (αIndex (0 : Fin 1)) (generator (αIndex (0 : Fin 1))) = 1 :=
      partialDerivation_generator_self _
    rw [h1, SmoothRingHom.map_one, one_mul] at h
    rw [Subsingleton.elim k 0]
    exact h

end ProjectAInos.Mechanics.CompleteIntegral
