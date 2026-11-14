/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.AngularMomentum
public import ProjectAInos.Mechanics.Poisson.HeavyTop
public import ProjectAInos.Mechanics.TimeFunction

/-!
# Trajectories of Hamiltonian systems

A smooth curve in the space of generators of a free C-infinity ring is a
family `c` of smooth functions of time, and `FreeSmoothRing.lift c` evaluates
an observable along the curve. The curve is a trajectory of the Hamiltonian `H`
when every generator satisfies `d/dt x(c) = {x, H}(c)`. Then
`d/dt f(c) = {f, H}(c)` for every observable `f`, so an integral of the motion
takes the same value at all times along every trajectory.

For the canonical bracket the condition is Hamilton's equations along the
curve. The integrals of the models follow: the Hamiltonian itself, the Casimir
`|L|²` of the rigid body, the angular momentum in a central field, and the
Casimirs of the heavy top.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

variable {κ : Type*}

/-- `c` is a trajectory of the Hamiltonian `H`: each generator evolves by its
bracket with `H`, evaluated along the curve. -/
def IsTrajectory (π : PoissonStructure (FreeSmoothRing κ)) (H : FreeSmoothRing κ)
    (c : κ → TimeFunction) : Prop :=
  ∀ a, timeDerivative (c a) = FreeSmoothRing.lift c (π.bracket (generator a) H)

namespace IsTrajectory

variable {π : PoissonStructure (FreeSmoothRing κ)} {H : FreeSmoothRing κ} {c : κ → TimeFunction}

/-- Along a trajectory every observable evolves by its bracket with the
Hamiltonian: `d/dt f(c) = {f, H}(c)`. -/
theorem timeDerivative_lift (h : IsTrajectory π H c) (f : FreeSmoothRing κ) :
    timeDerivative (FreeSmoothRing.lift c f) = FreeSmoothRing.lift c (π.bracket f H) := by
  refine (FreeSmoothRing.map_derivation_eq (FreeSmoothRing.lift c) (π.hamiltonian H)
    timeDerivative (fun a => ?_) f).symm
  rw [AlmostPoissonStructure.hamiltonian_apply, lift_generator]
  exact (h a).symm

/-- An integral of the motion takes the same value at all times along a trajectory. -/
theorem lift_eq_of_isIntegral (h : IsTrajectory π H c) {f : FreeSmoothRing κ}
    (hf : π.IsIntegral H f) (s t : Fin 1 → ℝ) :
    FreeSmoothRing.lift c f s = FreeSmoothRing.lift c f t := by
  refine TimeFunction.eq_of_timeDerivative_eq_zero ?_ s t
  rw [h.timeDerivative_lift, hf, SmoothRingHom.map_zero]

/-- If the bracket of an observable with the Hamiltonian lies in an ideal that
vanishes along the trajectory, the observable takes the same value at all
times. -/
theorem lift_eq_of_bracket_mem (h : IsTrajectory π H c) {I : Ideal (FreeSmoothRing κ)}
    (hI : ∀ x ∈ I, FreeSmoothRing.lift c x = 0) {f : FreeSmoothRing κ}
    (hf : π.bracket f H ∈ I) (s t : Fin 1 → ℝ) :
    FreeSmoothRing.lift c f s = FreeSmoothRing.lift c f t := by
  refine TimeFunction.eq_of_timeDerivative_eq_zero ?_ s t
  rw [h.timeDerivative_lift, hI _ hf]

/-- A Poisson morphism of free rings carries trajectories back: if `c` is a
trajectory of `φ K`, the curve `a ↦ (φ xₐ)(c)` is a trajectory of `K`. For a
canonical transformation `φ` these are the equations of motion in the new
variables. -/
theorem of_isPoissonHom {κ' : Type*} {ρ : PoissonStructure (FreeSmoothRing κ')}
    {φ : SmoothRingHom (FreeSmoothRing κ') (FreeSmoothRing κ)}
    (hφ : IsPoissonHom ρ.toAlmostPoissonStructure π.toAlmostPoissonStructure φ)
    {K : FreeSmoothRing κ'} (h : IsTrajectory π (φ K) c) :
    IsTrajectory ρ K fun a => FreeSmoothRing.lift c (φ (generator a)) := by
  have hlift (g : FreeSmoothRing κ') :
      FreeSmoothRing.lift (fun a => FreeSmoothRing.lift c (φ (generator a))) g =
        FreeSmoothRing.lift c (φ g) :=
    congrArg (fun χ : SmoothRingHom (FreeSmoothRing κ') TimeFunction => χ g)
      (FreeSmoothRing.hom_ext
        (f := FreeSmoothRing.lift fun a => FreeSmoothRing.lift c (φ (generator a)))
        (g := (FreeSmoothRing.lift c).comp φ) fun a => by
          rw [lift_generator, SmoothRingHom.comp_apply])
  intro a
  rw [hlift, hφ]
  exact h.timeDerivative_lift _

/-- The Hamiltonian is constant along its trajectories. -/
theorem lift_hamiltonian_eq (h : IsTrajectory π H c) (s t : Fin 1 → ℝ) :
    FreeSmoothRing.lift c H s = FreeSmoothRing.lift c H t :=
  h.lift_eq_of_isIntegral (PoissonStructure.isIntegral_self H) s t

end IsTrajectory

section Canonical

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- For the canonical bracket a trajectory is a solution of Hamilton's
equations `q̇ᵢ = ∂H/∂pᵢ`, `ṗᵢ = −∂H/∂qᵢ` along the curve. -/
theorem isTrajectory_canonical_iff (H : PhaseSpace ι) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (PhaseSpace.canonical ι) H c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) =
        FreeSmoothRing.lift c (partialDerivation (Sum.inr i) H)) ∧
      ∀ i, timeDerivative (c (Sum.inr i)) =
        -FreeSmoothRing.lift c (partialDerivation (Sum.inl i) H) := by
  have hq (i : ι) : (PhaseSpace.canonical ι).bracket (generator (Sum.inl i)) H =
      partialDerivation (Sum.inr i) H := PhaseSpace.canonical_q_bracket i H
  have hp (i : ι) : (PhaseSpace.canonical ι).bracket (generator (Sum.inr i)) H =
      -partialDerivation (Sum.inl i) H := PhaseSpace.canonical_p_bracket i H
  unfold IsTrajectory
  rw [Sum.forall]
  simp only [hq, hp, SmoothRingHom.map_neg]

end Canonical

/-- Along every trajectory of the rigid body, for any Hamiltonian, `|L|²` is
constant. -/
theorem RigidBody.lift_casimir_eq {H : RigidBody.PhaseSpace} {c : Fin 3 → TimeFunction}
    (h : IsTrajectory RigidBody.poisson H c) (s t : Fin 1 → ℝ) :
    FreeSmoothRing.lift c RigidBody.casimir s = FreeSmoothRing.lift c RigidBody.casimir t :=
  h.lift_eq_of_isIntegral (RigidBody.isIntegral_casimir H) s t

/-- Along every trajectory of a central Hamiltonian, each component of the
angular momentum is constant (Landau–Lifshitz §§9, 14). -/
theorem AngularMomentum.lift_M_eq (f : SmoothOperation 3) {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory AngularMomentum.canonical (op f AngularMomentum.scalars) c) (a : Fin 3)
    (s t : Fin 1 → ℝ) :
    FreeSmoothRing.lift c (AngularMomentum.M a) s =
      FreeSmoothRing.lift c (AngularMomentum.M a) t :=
  h.lift_eq_of_isIntegral (AngularMomentum.isIntegral_M f a) s t

/-- Along every trajectory of the heavy top, for any Hamiltonian, `|Γ|²` is constant. -/
theorem HeavyTop.lift_Γ_sq_eq {H : HeavyTop.PhaseSpace} {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory HeavyTop.poisson H c) (s t : Fin 1 → ℝ) :
    FreeSmoothRing.lift c (HeavyTop.Γ ⬝ᵥ HeavyTop.Γ) s =
      FreeSmoothRing.lift c (HeavyTop.Γ ⬝ᵥ HeavyTop.Γ) t :=
  h.lift_eq_of_isIntegral (HeavyTop.isIntegral_Γ_sq H) s t

/-- Along every trajectory of the heavy top, for any Hamiltonian, `L · Γ` is constant. -/
theorem HeavyTop.lift_L_dot_Γ_eq {H : HeavyTop.PhaseSpace} {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory HeavyTop.poisson H c) (s t : Fin 1 → ℝ) :
    FreeSmoothRing.lift c (HeavyTop.L ⬝ᵥ HeavyTop.Γ) s =
      FreeSmoothRing.lift c (HeavyTop.L ⬝ᵥ HeavyTop.Γ) t :=
  h.lift_eq_of_isIntegral (HeavyTop.isIntegral_L_dot_Γ H) s t

end ProjectAInos.Mechanics
