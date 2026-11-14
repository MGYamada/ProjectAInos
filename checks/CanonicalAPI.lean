/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the canonical-formalism API: the chain rule for a
substitution, the Legendre transformation of a natural Lagrangian and of a
hyperregular Lagrangian, canonical transformations from a generating function,
Jacobi's theorem on complete integrals, separation of the variables, and
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

section GeneratingFunction

open GeneratingFunction Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example (x : PositionPair ι) (k : ι) : gradOld x k = partialDerivation (Sum.inl k) x := rfl

example (x : PositionPair ι) (l : ι) : gradNew x l = partialDerivation (Sum.inr l) x := rfl

/-- `qᵢ ↦ qᵢ`, `pᵢ ↦ ∂F/∂qᵢ`. -/
example (F : PositionPair ι) (i : ι) : oldMap F (PhaseSpace.q i) = oldPosition i :=
  oldMap_q F i

example (F : PositionPair ι) (i : ι) : oldMap F (PhaseSpace.p i) = gradOld F i :=
  oldMap_p F i

/-- `Qᵢ ↦ Qᵢ`, `Pᵢ ↦ −∂F/∂Qᵢ`. -/
example (F : PositionPair ι) (i : ι) : newMap F (PhaseSpace.q i) = newPosition i :=
  newMap_q F i

example (F : PositionPair ι) (i : ι) : newMap F (PhaseSpace.p i) = -gradNew F i :=
  newMap_p F i

example (F : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)) :
    IsFree F G ↔
      G.comp (oldMap F) = SmoothRingHom.id (PhaseSpace ι) ∧
        (oldMap F).comp G = SmoothRingHom.id (PositionPair ι) :=
  ⟨fun h => ⟨h.left_inv, h.right_inv⟩, fun h => ⟨h.1, h.2⟩⟩

example (F : PositionPair ι) (G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)) :
    transformation F G = G.comp (newMap F) := rfl

example (F : PositionPair ι) (k l : ι) :
    mixedHessian F k l = partialDerivation (Sum.inr l) (partialDerivation (Sum.inl k) F) := rfl

variable {F : PositionPair ι} {G : SmoothRingHom (PositionPair ι) (PhaseSpace ι)}

/-- The mixed matrix `∂²F/∂qₖ∂Qₗ` of a free generating function is invertible. -/
example (h : IsFree F G) : inverseMixed F G * mixedHessian F = 1 :=
  h.inverseMixed_mul_mixedHessian

example (h : IsFree F G) : mixedHessian F * inverseMixed F G = 1 :=
  h.mixedHessian_mul_inverseMixed

/-- The canonical bracket in the co-ordinates `(q, Q)`. -/
example (h : IsFree F G) (x y : PositionPair ι) :
    oldMap F ((canonical ι).bracket (G x) (G y)) =
      gradOld x ⬝ᵥ (gradNew y ᵥ* inverseMixed F G) -
        (gradNew x ᵥ* inverseMixed F G) ⬝ᵥ gradOld y :=
  h.oldMap_bracket x y

example (h : IsFree F G) (i j : ι) :
    (canonical ι).bracket (G (newPosition i)) (G (gradNew F j)) = if i = j then -1 else 0 :=
  h.bracket_newPosition_gradNew i j

/-- The transformation generated by a free generating function is canonical
(Landau–Lifshitz §45). -/
example (h : IsFree F G) :
    IsPoissonHom (canonical ι).toAlmostPoissonStructure (canonical ι).toAlmostPoissonStructure
      (transformation F G) :=
  h.isPoissonHom_transformation

example (h : IsFree F G) {G' : SmoothRingHom (PositionPair ι) (PhaseSpace ι)}
    (hr : (newMap F).comp G' = SmoothRingHom.id (PositionPair ι)) :
    (transformation F G).comp (G'.comp (oldMap F)) = SmoothRingHom.id (PhaseSpace ι) :=
  h.transformation_comp_inverse hr

example (h : IsFree F G) {G' : SmoothRingHom (PositionPair ι) (PhaseSpace ι)}
    (hl : G'.comp (newMap F) = SmoothRingHom.id (PhaseSpace ι)) :
    (G'.comp (oldMap F)).comp (transformation F G) = SmoothRingHom.id (PhaseSpace ι) :=
  h.inverse_comp_transformation hl

example : (exchange : PositionPair ι) = ∑ k, oldPosition k * newPosition k := rfl

/-- `Σ qᵢ Qᵢ` generates `Qᵢ = pᵢ`, `Pᵢ = −qᵢ`. -/
example : IsFree (exchange (ι := ι)) (SmoothRingHom.id (PhaseSpace ι)) := isFree_exchange

example (i : ι) :
    transformation (exchange (ι := ι)) (SmoothRingHom.id (PhaseSpace ι)) (PhaseSpace.q i) =
      PhaseSpace.p i :=
  transformation_exchange_q i

example (i : ι) :
    transformation (exchange (ι := ι)) (SmoothRingHom.id (PhaseSpace ι)) (PhaseSpace.p i) =
      -PhaseSpace.q i :=
  transformation_exchange_p i

end GeneratingFunction

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

section Separation

open CompleteIntegral Matrix

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example (S : ActionSpace ι) (i : ι) :
    substitution S (PhaseSpace.p i) = partialDerivation (qIndex i) S :=
  substitution_p S i

example (S : ActionSpace ι) (u : FreeSmoothRing ι) :
    substitution S (positionsToPhase (ι := ι) u) = positionsToAction ι u :=
  substitution_positionsToPhase S u

example (m : ℝ) (Ψ g u : ι → FreeSmoothRing ι) :
    stackelHamiltonian m Ψ g u =
      ∑ i, positionsToPhase (ι := ι) (Ψ i) *
        (algebraMap ℝ (PhaseSpace ι) (1 / (2 * m)) *
          (positionsToPhase (ι := ι) (g i) * (PhaseSpace.p i * PhaseSpace.p i)) +
            positionsToPhase (ι := ι) (u i)) :=
  rfl

/-- Stäckel's theorem in the direction of verification. -/
example {m : ℝ} {Ψ g u : ι → FreeSmoothRing ι} {Φ : Matrix ι ι (FreeSmoothRing ι)} {j₀ : ι}
    (hΨ : ∀ j, ∑ i, Ψ i * Φ i j = if j = j₀ then 1 else 0) {S : ActionSpace ι}
    (hS : ∀ i, algebraMap ℝ (ActionSpace ι) (1 / (2 * m)) *
        (positionsToAction ι (g i) *
          (partialDerivation (qIndex i) S * partialDerivation (qIndex i) S)) +
        positionsToAction ι (u i) = ∑ j, positionsToAction ι (Φ i j) * parameter j)
    (ht : partialDerivation tIndex S = -parameter j₀) :
    IsHamiltonJacobi (stackelHamiltonian m Ψ g u) S :=
  isHamiltonJacobi_stackel hΨ hS ht

example (m : ℝ) (ρ σ a b c : FreeSmoothRing (Fin 3)) :
    nestedHamiltonian m ρ σ a b c =
      stackelHamiltonian m ![1, ρ, ρ * σ] ![1, 1, 1] ![a, b, c] :=
  rfl

example (m : ℝ) (S : ActionSpace (Fin 3)) (i : Fin 3) :
    kinetic m S i =
      algebraMap ℝ (ActionSpace (Fin 3)) (1 / (2 * m)) *
        (partialDerivation (qIndex i) S * partialDerivation (qIndex i) S) :=
  rfl

/-- Separation of the variables in the form of spherical co-ordinates. -/
example {m : ℝ} {ρ σ a b c : FreeSmoothRing (Fin 3)} {S : ActionSpace (Fin 3)}
    (h0 : kinetic m S 0 + positionsToAction (Fin 3) a =
      parameter (0 : Fin 3) - positionsToAction (Fin 3) ρ * parameter (1 : Fin 3))
    (h1 : kinetic m S 1 + positionsToAction (Fin 3) b =
      parameter (1 : Fin 3) - positionsToAction (Fin 3) σ * parameter (2 : Fin 3))
    (h2 : kinetic m S 2 + positionsToAction (Fin 3) c = parameter (2 : Fin 3))
    (ht : partialDerivation tIndex S = -parameter (0 : Fin 3)) :
    IsHamiltonJacobi (nestedHamiltonian m ρ σ a b c) S :=
  isHamiltonJacobi_nested_of_separated h0 h1 h2 ht

example (m : ℝ) (lam g₀ g₁ κ₀ κ₁ u₀ u₁ u₂ : FreeSmoothRing (Fin 3)) :
    liouvilleHamiltonian m lam g₀ g₁ κ₀ κ₁ u₀ u₁ u₂ =
      stackelHamiltonian m ![lam, lam, lam * (κ₀ + κ₁)] ![g₀, g₁, 1] ![u₀, u₁, u₂] :=
  rfl

/-- Separation of the variables in the form of parabolic and elliptic
co-ordinates. -/
example {m : ℝ} {lam w₀ w₁ g₀ g₁ κ₀ κ₁ u₀ u₁ u₂ : FreeSmoothRing (Fin 3)}
    (h : lam * (w₀ + w₁) = 1) {S : ActionSpace (Fin 3)}
    (h0 : positionsToAction (Fin 3) g₀ * kinetic m S 0 + positionsToAction (Fin 3) u₀ =
      positionsToAction (Fin 3) w₀ * parameter (0 : Fin 3) + parameter (1 : Fin 3) -
        positionsToAction (Fin 3) κ₀ * parameter (2 : Fin 3))
    (h1 : positionsToAction (Fin 3) g₁ * kinetic m S 1 + positionsToAction (Fin 3) u₁ =
      positionsToAction (Fin 3) w₁ * parameter (0 : Fin 3) - parameter (1 : Fin 3) -
        positionsToAction (Fin 3) κ₁ * parameter (2 : Fin 3))
    (h2 : kinetic m S 2 + positionsToAction (Fin 3) u₂ = parameter (2 : Fin 3))
    (ht : partialDerivation tIndex S = -parameter (0 : Fin 3)) :
    IsHamiltonJacobi (liouvilleHamiltonian m lam g₀ g₁ κ₀ κ₁ u₀ u₁ u₂) S :=
  isHamiltonJacobi_liouville_of_separated h h0 h1 h2 ht

end Separation

section ActionFunction

open CompleteIntegral

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- `dS/dt = Σ pᵢ q̇ᵢ − H` along a curve (Landau–Lifshitz §43). -/
example {H : PhaseSpace ι} {S : ActionSpace ι} (h : IsHamiltonJacobi H S)
    (Q : ι → TimeFunction) (α : ι → ℝ) :
    timeDerivative (along Q α S) =
      ∑ k, momentum S Q α k * timeDerivative (Q k) -
        FreeSmoothRing.lift (Sum.elim Q (momentum S Q α)) H :=
  h.timeDerivative_along Q α

end ActionFunction

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
