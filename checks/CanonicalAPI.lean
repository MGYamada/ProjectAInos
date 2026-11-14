/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the canonical-formalism API: the chain rule for a
substitution, the Legendre transformation of a natural Lagrangian and of a
hyperregular Lagrangian, Jacobi's theorem on complete integrals, and
Liouville's theorem in infinitesimal form.
Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its
type. -/
noncomputable section
open ProjectAInos.SmoothAlgebra ProjectAInos.SmoothAlgebra.SmoothRing
open ProjectAInos.SmoothAlgebra.FreeSmoothRing ProjectAInos.SmoothAlgebra.PhaseSpace
open ProjectAInos.Mechanics

section ChainRule

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The chain rule for a substitution. -/
example {B : Type*} [CommRing B] [Algebra ℝ B] [SmoothRing B] (y : κ → B)
    (E : SmoothDerivation B B) (s : FreeSmoothRing κ) :
    E (FreeSmoothRing.lift y s) =
      ∑ a, FreeSmoothRing.lift y (partialDerivation a s) * E (y a) :=
  derivation_lift_mul y E s

end ChainRule

section Legendre

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example (m : ι → ℝ) (i : ι) :
    legendre m (PhaseSpace.q i) = (StandardJet.jetRing ι).q i 0 :=
  legendre_q m i

example (m : ι → ℝ) (i : ι) :
    legendre m (PhaseSpace.p i) =
      algebraMap ℝ (StandardJet ι) (m i) * (StandardJet.jetRing ι).q i 1 :=
  legendre_p m i

/-- The momentum of the phase space goes to `∂L/∂q̇`. -/
example (m : ι → ℝ) (u : FreeSmoothRing ι) (i : ι) :
    legendre m (PhaseSpace.p i) =
      (StandardJet.jetRing ι).momentum
        ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u)) i :=
  legendre_p_eq_momentum m u i

/-- The Hamiltonian goes to the energy of the Lagrangian. -/
example {m : ι → ℝ} (hm : ∀ i, m i ≠ 0) (u : FreeSmoothRing ι) :
    legendre m (kineticEnergy m + positionsToPhase u) =
      (StandardJet.jetRing ι).energy
        ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u)) :=
  legendre_hamiltonian hm u

/-- Newton's equations along a path. -/
example (m : ι → ℝ) (u : FreeSmoothRing ι) (γ : ι → TimeFunction) :
    StandardJet.IsSolution
        ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u)) γ ↔
      ∀ i, algebraMap ℝ TimeFunction (m i) * timeDerivative (timeDerivative (γ i)) =
        -FreeSmoothRing.lift γ (partialDerivation i u) :=
  isSolution_natural_iff m u γ

/-- The Legendre correspondence between trajectories and solutions. -/
example {m : ι → ℝ} (hm : ∀ i, m i ≠ 0) (u : FreeSmoothRing ι) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (kineticEnergy m + positionsToPhase u) c ↔
      StandardJet.IsSolution
          ((StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u))
          (fun i => c (Sum.inl i)) ∧
        ∀ i, c (Sum.inr i) =
          algebraMap ℝ TimeFunction (m i) * timeDerivative (c (Sum.inl i)) :=
  isTrajectory_natural_iff_isSolution hm u c

end Legendre

section Hyperregular

open VelocitySpace

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example (L : VelocitySpace ι) (i : ι) :
    momentum L i = partialDerivation (Sum.inr i) L := rfl

example (L : VelocitySpace ι) : energy L = ∑ i, v i * momentum L i - L := rfl

example (L : VelocitySpace ι) (i : ι) : legendre L (PhaseSpace.q i) = VelocitySpace.q i :=
  legendre_q L i

example (L : VelocitySpace ι) (i : ι) : legendre L (PhaseSpace.p i) = momentum L i :=
  legendre_p L i

example (L : VelocitySpace ι) (i j : ι) :
    VelocitySpace.hessian L i j = partialDerivation (Sum.inr j) (momentum L i) := rfl

example (L : VelocitySpace ι) (G : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι)) :
    IsHyperregular L G ↔
      G.comp (legendre L) = SmoothRingHom.id (PhaseSpace ι) ∧
        (legendre L).comp G = SmoothRingHom.id (VelocitySpace ι) :=
  ⟨fun h => ⟨h.left_inv, h.right_inv⟩, fun h => ⟨h.1, h.2⟩⟩

example (L : VelocitySpace ι) (G : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι)) :
    hamiltonian L G = G (energy L) := rfl

variable {L : VelocitySpace ι} {G : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι)}

/-- The matrix `∂²L/∂vᵢ∂vⱼ` of a hyperregular Lagrangian is invertible. -/
example (h : IsHyperregular L G) : inverseHessian L G * VelocitySpace.hessian L = 1 :=
  h.inverseHessian_mul_hessian

example (h : IsHyperregular L G) : VelocitySpace.hessian L * inverseHessian L G = 1 :=
  h.hessian_mul_inverseHessian

/-- The Legendre transformation takes the Hamiltonian to the energy. -/
example (h : IsHyperregular L G) : legendre L (hamiltonian L G) = energy L :=
  h.legendre_hamiltonian

/-- `FL(∂H/∂pᵢ) = vᵢ`. -/
example (h : IsHyperregular L G) (i : ι) :
    legendre L (partialDerivation (Sum.inr i) (hamiltonian L G)) = v i :=
  h.legendre_partialDerivation_inr_hamiltonian i

/-- `FL(∂H/∂qᵢ) = −∂L/∂qᵢ`. -/
example (h : IsHyperregular L G) (i : ι) :
    legendre L (partialDerivation (Sum.inl i) (hamiltonian L G)) =
      -partialDerivation (Sum.inl i) L :=
  h.legendre_partialDerivation_inl_hamiltonian i

example (γ : ι → TimeFunction) :
    velocityCurve γ = Sum.elim γ fun i => timeDerivative (γ i) := rfl

example (γ : ι → TimeFunction) (s : VelocitySpace ι) :
    StandardJet.prolongation γ (toJet s) = FreeSmoothRing.lift (velocityCurve γ) s :=
  prolongation_toJet γ s

/-- The Euler–Lagrange equations of `L(q, v)` along a path. -/
example (L : VelocitySpace ι) (γ : ι → TimeFunction) :
    StandardJet.IsSolution (toJet L) γ ↔
      ∀ i, timeDerivative (FreeSmoothRing.lift (velocityCurve γ) (momentum L i)) =
        FreeSmoothRing.lift (velocityCurve γ) (partialDerivation (Sum.inl i) L) :=
  isSolution_toJet_iff L γ

/-- The Legendre correspondence (Landau–Lifshitz §40, Theorem 51). -/
example (h : IsHyperregular L G) (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (canonical ι) (hamiltonian L G) c ↔
      StandardJet.IsSolution (toJet L) (fun i => c (Sum.inl i)) ∧
        ∀ i, c (Sum.inr i) =
          FreeSmoothRing.lift (velocityCurve fun i => c (Sum.inl i)) (momentum L i) :=
  h.isTrajectory_iff_isSolution c

example (L : VelocitySpace ι) (G : SmoothRingHom (VelocitySpace ι) (PhaseSpace ι))
    (f g : VelocitySpace ι) :
    lagrangeBracket L G f g = legendre L ((canonical ι).bracket (G f) (G g)) := rfl

example (h : IsHyperregular L G) (f g : PhaseSpace ι) :
    legendre L ((canonical ι).bracket f g) =
      lagrangeBracket L G (legendre L f) (legendre L g) :=
  h.legendre_bracket f g

/-- `{qᵢ, vⱼ}` is the inverse of the matrix `∂²L/∂vᵢ∂vⱼ`. -/
example (h : IsHyperregular L G) (i j : ι) :
    lagrangeBracket L G (VelocitySpace.q i) (v j) = inverseHessian L G j i :=
  h.lagrangeBracket_q_v i j

example (h : IsHyperregular L G) (i : ι) :
    lagrangeBracket L G (VelocitySpace.q i) (energy L) = v i :=
  h.lagrangeBracket_q_energy i

/-- A natural Lagrangian with non-zero masses is hyperregular, with the
Hamiltonian `Σ pᵢ² / 2mᵢ + U(q)`. -/
example {m : ι → ℝ} (hm : ∀ i, m i ≠ 0) (u : FreeSmoothRing ι) :
    IsHyperregular (natural m u) (naturalInverse m) :=
  isHyperregular_natural hm u

example {m : ι → ℝ} (hm : ∀ i, m i ≠ 0) (u : FreeSmoothRing ι) :
    hamiltonian (natural m u) (naturalInverse m) = kineticEnergy m + positionsToPhase u :=
  hamiltonian_natural hm u

example (m : ι → ℝ) (u : FreeSmoothRing ι) :
    toJet (natural m u) = (StandardJet.jetRing ι).naturalLagrangian m (positionsToJet u) :=
  toJet_natural m u

end Hyperregular

section CompleteIntegral

open CompleteIntegral

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example (H : PhaseSpace ι) (S : ActionSpace ι) :
    IsHamiltonJacobi H S ↔ partialDerivation tIndex S + substitution S H = 0 := Iff.rfl

example (S : ActionSpace ι) (Q : ι → TimeFunction) (α : ι → ℝ) (i : ι) :
    momentum S Q α i = along Q α (partialDerivation (qIndex i) S) := rfl

/-- Jacobi's theorem (Landau–Lifshitz §47). -/
example {H : PhaseSpace ι} {S : ActionSpace ι} (hS : IsHamiltonJacobi H S)
    {Q : ι → TimeFunction} {α : ι → ℝ}
    (hβ : ∀ i, timeDerivative (along Q α (partialDerivation (αIndex i) S)) = 0)
    (hnd : ∀ w : ι → TimeFunction,
      (∀ i, ∑ k, along Q α (partialDerivation (αIndex i) (partialDerivation (qIndex k) S)) *
        w k = 0) → ∀ k, w k = 0) :
    IsTrajectory (canonical ι) H (Sum.elim Q (momentum S Q α)) :=
  isTrajectory_of_isHamiltonJacobi hS hβ hnd

/-- The complete integral of the free particle. -/
example (m : ℝ) : IsHamiltonJacobi (kineticEnergy fun _ : Fin 1 => m) (freeAction m) :=
  isHamiltonJacobi_freeAction m

/-- Jacobi's theorem gives the uniform motion of the free particle. -/
example (m α₀ β : ℝ) :
    IsTrajectory (canonical (Fin 1)) (kineticEnergy fun _ : Fin 1 => m)
      (Sum.elim
        (fun _ => algebraMap ℝ TimeFunction β +
          algebraMap ℝ TimeFunction (m⁻¹ * α₀) * TimeFunction.time)
        (momentum (freeAction m)
          (fun _ => algebraMap ℝ TimeFunction β +
            algebraMap ℝ TimeFunction (m⁻¹ * α₀) * TimeFunction.time) fun _ => α₀)) :=
  isTrajectory_freeAction m α₀ β

end CompleteIntegral

section Liouville

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example (X : SmoothDerivation (PhaseSpace ι) (PhaseSpace ι)) :
    divergence X = ∑ a, partialDerivation a (X (generator a)) := rfl

/-- Liouville's theorem in infinitesimal form. -/
example (H : PhaseSpace ι) : divergence ((canonical ι).hamiltonian H) = 0 :=
  divergence_hamiltonian H

/-- With friction the phase volume of the oscillator contracts. -/
example (m a : ι → ℝ) (k : ℝ) :
    divergence (dissipativeField (Matrix.diagonal a) (Oscillator.hamiltonian m k)) =
      -algebraMap ℝ (PhaseSpace ι) (∑ i, a i * (m i)⁻¹) :=
  Oscillator.divergence_dissipativeField m a k

end Liouville
