/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the quotient and reduction API: smooth parametric
integrals, Hadamard's lemma, the quotient of a C-infinity ring by an ideal, the
quotient of a Poisson C-infinity ring by a Poisson ideal, coisotropic
reduction, reduction with respect to cyclic co-ordinates, the reduced mass as
a reduction, and the Routhian.
Default elaborator options are intentional: these checks must not rely on the
implementation's transparency settings. Every statement is pinned with its
type. -/
noncomputable section
open ProjectAInos.SmoothAlgebra ProjectAInos.SmoothAlgebra.SmoothRing
open ProjectAInos.SmoothAlgebra.SmoothOperation ProjectAInos.SmoothAlgebra.FreeSmoothRing
open ProjectAInos.Mechanics
open scoped ContDiff

section Interface

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  {G : Type u} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Interface (I): differentiation under the integral sign. -/
example {f : E × ℝ → G} (hf : ContDiff ℝ 1 f) (a b : ℝ) (x₀ : E) :
    HasFDerivAt (fun x => ∫ t in a..b, f (x, t)) (∫ t in a..b, fderivLeft f (x₀, t)) x₀ :=
  hasFDerivAt_parametric_intervalIntegral hf a b x₀

/-- Interface (I): a parametric integral of a smooth function is smooth. -/
example {f : E × ℝ → G} (hf : ContDiff ℝ ∞ f) (a b : ℝ) :
    ContDiff ℝ ∞ fun x => ∫ t in a..b, f (x, t) :=
  contDiff_infty_parametric_intervalIntegral hf a b

/-- Interface (I): smoothness in the parameter and the limits together. -/
example {f : E × ℝ → G} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p : E × ℝ × ℝ => ∫ t in p.2.1..p.2.2, f (p.1, t) :=
  contDiff_infty_parametric_intervalIntegral_limits hf

variable {n : ℕ}

example (i : Fin n) (f : SmoothOperation n) (z : Fin (n + n) → ℝ) :
    hadamard i f z = ∫ t in (0 : ℝ)..1, partialDeriv i f (segment n (z, t)) :=
  hadamard_apply i f z

/-- Interface (H): Hadamard's lemma. -/
example (f : SmoothOperation n) (x y : Fin n → ℝ) :
    f x - f y = ∑ i, (x i - y i) * hadamard i f (Fin.append x y) :=
  apply_sub_apply_eq_sum_hadamard f x y

/-- Hadamard's lemma in a C-infinity ring. -/
example {A : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A] (f : SmoothOperation n)
    (a b : Fin n → A) :
    op f a - op f b = ∑ i, (a i - b i) * op (hadamard i f) (Fin.append a b) :=
  op_sub_op f a b

end Interface

section IdealQuotient

variable {A B : Type*} [CommRing A] [Algebra ℝ A] [SmoothRing A]
  [CommRing B] [Algebra ℝ B] [SmoothRing B]

/-- The quotient by an ideal: two elements have the same class exactly when
their difference is in the ideal. -/
example {I : Ideal A} {a b : A} :
    (SmoothRingCon.ofIdeal I).projection a = (SmoothRingCon.ofIdeal I).projection b ↔
      a - b ∈ I :=
  SmoothRingCon.ofIdeal_projection_eq_iff

example {I : Ideal A} {a : A} : (SmoothRingCon.ofIdeal I).projection a = 0 ↔ a ∈ I :=
  SmoothRingCon.ofIdeal_projection_eq_zero_iff

/-- The morphisms out of the quotient are the morphisms that vanish on the ideal. -/
example (I : Ideal A) :
    SmoothRingHom (SmoothRingCon.ofIdeal I).Quotient B ≃
      {f : SmoothRingHom A B // ∀ a ∈ I, f a = 0} :=
  SmoothRingCon.ofIdealHomEquiv I

/-- A ring presented by equations is the quotient by the ideal of the equations. -/
example {ι K : Type*} (e : K → FreeSmoothRing ι) {a : FreeSmoothRing ι} :
    (SmoothRingCon.generate (equationRel e)).projection a = 0 ↔
      a ∈ Ideal.span (Set.range e) :=
  presented_projection_eq_zero_iff e

example {ι : Type*} {I : Ideal A} {φ ψ : SmoothRingHom (FreeSmoothRing ι) A}
    (h : ∀ i, φ (generator i) - ψ (generator i) ∈ I) (f : FreeSmoothRing ι) :
    φ f - ψ f ∈ I :=
  hom_sub_hom_mem h f

end IdealQuotient

section PoissonReduction

variable {P Q : Type*} [CommRing P] [Algebra ℝ P] [SmoothRing P]
  [CommRing Q] [Algebra ℝ Q] [SmoothRing Q] (π : PoissonStructure P) {ρ : PoissonStructure Q}

/-- The quotient by a Poisson ideal is a Poisson C-infinity ring. -/
example (I : Ideal P) (hI : π.IsPoissonIdeal I) (f g : P) :
    (π.quotient I hI).bracket ((SmoothRingCon.ofIdeal I).projection f)
        ((SmoothRingCon.ofIdeal I).projection g) =
      (SmoothRingCon.ofIdeal I).projection (π.bracket f g) :=
  π.quotient_bracket I hI f g

/-- Coisotropic reduction: the bracket of the reduced ring `N(I)/I`. -/
example (I : Ideal P) (f g : π.normalizer I) :
    (π.reduction I).bracket (π.reductionMap I f) (π.reductionMap I g) =
      π.reductionMap I ((π.restrictNormalizer I).bracket f g) :=
  π.reduction_bracket I f g

example {I : Ideal P} {f g : π.normalizer I} :
    π.reductionMap I f = π.reductionMap I g ↔ f.val - g.val ∈ I :=
  π.reductionMap_eq_iff

example {s : Set P} (h : ∀ a ∈ s, ∀ b ∈ s, π.bracket a b ∈ Ideal.span s) :
    π.IsCoisotropic (Ideal.span s) :=
  PoissonStructure.isCoisotropic_span h

/-- A model of the reduced ring. -/
example {I : Ideal P} {σ : SmoothRingHom Q P} (hσ : ∀ g, σ g ∈ π.normalizer I)
    {r : SmoothRingHom P Q} (hrσ : ∀ g, r (σ g) = g) (hr : ∀ j ∈ I, r j = 0)
    (h : ∀ f ∈ π.normalizer I, f - σ (r f) ∈ I) :
    Function.Bijective (PoissonStructure.toReduction σ hσ) :=
  PoissonStructure.toReduction_bijective hσ hrσ hr h

example {I : Ideal P} {σ : SmoothRingHom Q P} (hσ : ∀ g, σ g ∈ π.normalizer I)
    (hP : IsPoissonHom ρ.toAlmostPoissonStructure π.toAlmostPoissonStructure σ) :
    IsPoissonHom ρ.toAlmostPoissonStructure (π.reduction I).toAlmostPoissonStructure
      (PoissonStructure.toReduction σ hσ) :=
  PoissonStructure.isPoissonHom_toReduction hσ hP

end PoissonReduction

section CyclicReduction

open CyclicReduction

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

example (c : κ → ℝ) :
    momentumIdeal ι c = Ideal.span (Set.range fun k =>
      PhaseSpace.p (Sum.inr k) - algebraMap ℝ (PhaseSpace (ι ⊕ κ)) (c k)) := rfl

example (c : κ → ℝ) :
    (PhaseSpace.canonical (ι ⊕ κ)).IsCoisotropic (momentumIdeal ι c) :=
  isCoisotropic_momentumIdeal c

example {c : κ → ℝ} {f : PhaseSpace (ι ⊕ κ)} :
    f ∈ (PhaseSpace.canonical (ι ⊕ κ)).normalizer (momentumIdeal ι c) ↔
      ∀ k, partialDerivation (Sum.inl (Sum.inr k)) f ∈ momentumIdeal ι c :=
  mem_normalizer_iff

/-- Reduction with respect to cyclic co-ordinates: the reduced ring is the
phase space of the remaining co-ordinates. -/
example (c : κ → ℝ) : Function.Bijective (reductionHom ι c) := reductionHom_bijective c

example (c : κ → ℝ) :
    IsPoissonHom (PhaseSpace.canonical ι).toAlmostPoissonStructure
      ((PhaseSpace.canonical (ι ⊕ κ)).reduction (momentumIdeal ι c)).toAlmostPoissonStructure
      (reductionHom ι c) :=
  isPoissonHom_reductionHom c

example {c : κ → ℝ} {f : PhaseSpace (ι ⊕ κ)}
    (hf : f ∈ (PhaseSpace.canonical (ι ⊕ κ)).normalizer (momentumIdeal ι c)) :
    reductionHom ι c (restriction ι c f) =
      (PhaseSpace.canonical (ι ⊕ κ)).reductionMap (momentumIdeal ι c) ⟨f, hf⟩ :=
  reductionHom_restriction hf

/-- The trajectories of a Hamiltonian with cyclic co-ordinates. -/
example {H : PhaseSpace (ι ⊕ κ)} (hH : ∀ k, partialDerivation (Sum.inl (Sum.inr k)) H = 0)
    {x : (ι ⊕ κ) ⊕ (ι ⊕ κ) → TimeFunction}
    (hx : IsTrajectory (PhaseSpace.canonical (ι ⊕ κ)) H x) {c : κ → ℝ}
    (hc : ∀ k, x (Sum.inr (Sum.inr k)) = algebraMap ℝ TimeFunction (c k)) :
    IsTrajectory (PhaseSpace.canonical ι) (restriction ι c H)
      fun a => x (Sum.map Sum.inl Sum.inl a) :=
  isTrajectory_restriction hH hx hc

/-- A substitution fixes an element that does not depend on the co-ordinates it
changes. -/
example {s : FreeSmoothRing ι} {y : ι → FreeSmoothRing ι}
    (h : ∀ a, y a ≠ generator a → partialDerivation a s = 0) : FreeSmoothRing.lift y s = s :=
  lift_eq_self_of_partialDerivation_eq_zero h

end CyclicReduction

section ReducedMass

open TwoBody Matrix

variable {m₁ m₂ : ℝ}

example : totalMomentumIdeal = Ideal.span (Set.range totalMomentum) := rfl

example (μ : ℝ) (U : FreeSmoothRing (Fin 3)) :
    relativeHamiltonian μ U =
      algebraMap ℝ (PhaseSpace (Fin 3)) (μ⁻¹ / 2) * (PhaseSpace.p ⬝ᵥ PhaseSpace.p) +
        FreeSmoothRing.lift PhaseSpace.q U := rfl

/-- The change of variables to the centre of mass is an isomorphism of Poisson
C-infinity rings. -/
example (hM : m₁ + m₂ ≠ 0) :
    IsPoissonHom (PhaseSpace.canonical (Fin 3 ⊕ Fin 3)).toAlmostPoissonStructure
      TwoBody.canonical.toAlmostPoissonStructure (centreCoordinates m₁ m₂) :=
  isPoissonHom_centreCoordinates hM

example (hM : m₁ + m₂ ≠ 0) (f : Space) :
    centreCoordinates m₁ m₂ (particleCoordinates m₁ m₂ f) = f :=
  centreCoordinates_particleCoordinates hM f

example (hM : m₁ + m₂ ≠ 0) (g : CentreSpace) :
    particleCoordinates m₁ m₂ (centreCoordinates m₁ m₂ g) = g :=
  particleCoordinates_centreCoordinates hM g

/-- The reduced ring of two particles at total momentum zero is the phase space
of one particle. -/
example (hM : m₁ + m₂ ≠ 0) : Function.Bijective (reducedMassHom hM) :=
  reducedMassHom_bijective hM

example (hM : m₁ + m₂ ≠ 0) :
    IsPoissonHom (PhaseSpace.canonical (Fin 3)).toAlmostPoissonStructure
      (TwoBody.canonical.reduction totalMomentumIdeal).toAlmostPoissonStructure
      (reducedMassHom hM) :=
  isPoissonHom_reducedMassHom hM

/-- The class of the Hamiltonian is the Hamiltonian of one particle with the
reduced mass. -/
example (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0) (U : FreeSmoothRing (Fin 3)) :
    reducedMassHom hM (relativeHamiltonian (reducedMass m₁ m₂) U) =
      TwoBody.canonical.reductionMap totalMomentumIdeal
        ⟨TwoBody.hamiltonian m₁ m₂ U, hamiltonian_mem_normalizer h₁ h₂ hM U⟩ :=
  reducedMassHom_relativeHamiltonian h₁ h₂ hM U

/-- The relative motion of two bodies. -/
example (h₁ : m₁ ≠ 0) (h₂ : m₂ ≠ 0) (hM : m₁ + m₂ ≠ 0) {U : FreeSmoothRing (Fin 3)}
    {x : (Fin 2 × Fin 3) ⊕ (Fin 2 × Fin 3) → TimeFunction}
    (hx : IsTrajectory TwoBody.canonical (TwoBody.hamiltonian m₁ m₂ U) x)
    (hP : ∀ i, FreeSmoothRing.lift x (totalMomentum i) = 0) :
    IsTrajectory (PhaseSpace.canonical (Fin 3)) (relativeHamiltonian (reducedMass m₁ m₂) U)
      (Sum.elim (fun i => FreeSmoothRing.lift x (relative i))
        fun i => FreeSmoothRing.lift x (relativeMomentum m₁ m₂ i)) :=
  isTrajectory_relative h₁ h₂ hM hx hP

end ReducedMass

section Routhian

open Routhian VelocitySpace

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype ι] [Fintype κ]
  {L : VelocitySpace (ι ⊕ κ)} {G : SmoothRingHom (VelocitySpace (ι ⊕ κ)) (RouthSpace ι κ)}

example (L : VelocitySpace (ι ⊕ κ)) (G : SmoothRingHom (VelocitySpace (ι ⊕ κ)) (RouthSpace ι κ)) :
    routhian L G = G (∑ k : κ, v (Sum.inr k) * momentum L (Sum.inr k) - L) := rfl

example (h : IsPartiallyHyperregular L G) (k : κ) :
    partialLegendre L (partialDerivation (Sum.inr (Sum.inr k)) (routhian L G)) =
      v (Sum.inr k) :=
  h.partialLegendre_partialDerivation_p_routhian k

example (h : IsPartiallyHyperregular L G) (b : ι ⊕ κ) :
    partialLegendre L (partialDerivation (Sum.inl b) (routhian L G)) =
      -partialDerivation (Sum.inl b) L :=
  h.partialLegendre_partialDerivation_q_routhian b

example (h : IsPartiallyHyperregular L G) (j : ι) :
    partialLegendre L (partialDerivation (Sum.inr (Sum.inl j)) (routhian L G)) =
      -partialDerivation (Sum.inr (Sum.inl j)) L :=
  h.partialLegendre_partialDerivation_v_routhian j

/-- The Euler–Lagrange equations of `L` are the equations of the Routhian. -/
example (h : IsPartiallyHyperregular L G) (γ : ι ⊕ κ → TimeFunction) :
    IsRouthTrajectory (routhian L G) (routhCurve L γ) ↔ StandardJet.IsSolution (toJet L) γ :=
  h.isRouthTrajectory_routhCurve_iff γ

example (h : IsPartiallyHyperregular L G) {c : (ι ⊕ κ) ⊕ (ι ⊕ κ) → TimeFunction}
    (hc : IsRouthTrajectory (routhian L G) c) : c = routhCurve L fun a => c (Sum.inl a) :=
  h.eq_routhCurve hc

/-- Cyclic co-ordinates: the remaining co-ordinates satisfy the Euler–Lagrange
equations of the Routhian at the values of the momenta. -/
example {R : RouthSpace ι κ} {x : (ι ⊕ κ) ⊕ (ι ⊕ κ) → TimeFunction}
    (hx : IsRouthTrajectory R x) (hR : ∀ k, partialDerivation (Sum.inl (Sum.inr k)) R = 0)
    {c : κ → ℝ} (hc : ∀ k, x (Sum.inr (Sum.inr k)) = algebraMap ℝ TimeFunction (c k)) :
    StandardJet.IsSolution (toJet (reducedRouthian R c)) fun i => x (Sum.inl (Sum.inl i)) :=
  hx.isSolution_reducedRouthian hR hc

/-- A natural Lagrangian is hyperregular in the velocities with non-zero masses. -/
example {m : ι ⊕ κ → ℝ} (hm : ∀ k : κ, m (Sum.inr k) ≠ 0) (u : FreeSmoothRing (ι ⊕ κ)) :
    IsPartiallyHyperregular (natural m u) (Routhian.naturalInverse m) :=
  isPartiallyHyperregular_natural hm u

end Routhian
