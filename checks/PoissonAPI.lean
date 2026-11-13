/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
import ProjectAInos

/-! Public consumers of the Poisson C-infinity ring API. Default elaborator
options are intentional: these checks must not rely on the implementation's
transparency settings. Every statement is pinned with its type. -/
noncomputable section
open ProjectAInos.SmoothAlgebra ProjectAInos.SmoothAlgebra.SmoothRing ProjectAInos.Mechanics
open Matrix

section Abstract

variable {P : Type*} [CommRing P] [Algebra ℝ P] [SmoothRing P]

/-! The only axioms of the bracket are antisymmetry, the chain rule in the first
argument and the Jacobi identity. Additivity and the Leibniz rule are theorems. -/

example (π : AlmostPoissonStructure P) (f g h : P) :
    π.bracket (f * g) h = f * π.bracket g h + g * π.bracket f h :=
  π.bracket_mul_left f g h

example (π : AlmostPoissonStructure P) (f g h : P) :
    π.bracket f (g * h) = g * π.bracket f h + h * π.bracket f g :=
  π.bracket_mul_right f g h

example (π : AlmostPoissonStructure P) (f g h : P) :
    π.bracket (f + g) h = π.bracket f h + π.bracket g h :=
  π.bracket_add_left f g h

example (π : AlmostPoissonStructure P) (r : ℝ) (h : P) :
    π.bracket (algebraMap ℝ P r) h = 0 :=
  π.bracket_algebraMap_left r h

example (π : AlmostPoissonStructure P) (h f : P) : π.hamiltonian h f = π.bracket f h := rfl

example (π : AlmostPoissonStructure P) {n : ℕ} (f : SmoothOperation n) (c : Fin n → P)
    (g h : P) :
    π.jacobiator (op f c) g h = ∑ i, op (SmoothOperation.partialDeriv i f) c *
      π.jacobiator (c i) g h :=
  π.jacobiator_op f c g h

example (π : PoissonStructure P) (f g h : P) :
    π.bracket (π.bracket f g) h =
      π.bracket (π.bracket f h) g + π.bracket f (π.bracket g h) :=
  π.bracket_bracket f g h

example (π : PoissonStructure P) (f g : P) :
    π.hamiltonian (π.bracket f g) = -⁅π.hamiltonian f, π.hamiltonian g⁆ :=
  π.hamiltonian_bracket f g

/-- Poisson's theorem. -/
example (π : PoissonStructure P) {H f g : P} (hf : π.bracket f H = 0)
    (hg : π.bracket g H = 0) : π.bracket (π.bracket f g) H = 0 :=
  PoissonStructure.IsIntegral.bracket (π := π) hf hg

example (π : PoissonStructure P) {H : P} {n : ℕ} (f : SmoothOperation n) {c : Fin n → P}
    (hc : ∀ i, π.bracket (c i) H = 0) : π.bracket (op f c) H = 0 :=
  PoissonStructure.IsIntegral.op (π := π) f hc

example (π : PoissonStructure P) (H f : P) : f ∈ π.integrals H ↔ π.bracket f H = 0 := Iff.rfl

example (π : PoissonStructure P) (H μ : P) :
    π.bracket μ H = 0 ↔ π.bracket H μ = 0 :=
  PoissonStructure.isIntegral_iff_hamiltonian_eq_zero (π := π) H μ

/-- Coisotropic reduction: the bracket descends to the normalizer modulo the ideal. -/
example (π : PoissonStructure P) {I : Ideal P} {f f' g g' : P} (hf' : f' ∈ π.normalizer I)
    (hg : g ∈ π.normalizer I) (hff' : f - f' ∈ I) (hgg' : g - g' ∈ I) :
    π.bracket f g - π.bracket f' g' ∈ I :=
  PoissonStructure.bracket_sub_bracket_mem hf' hg hff' hgg'

example (π : PoissonStructure P) {I : Ideal P} {f g : P} (hf : f ∈ π.normalizer I)
    (hg : g ∈ π.normalizer I) : π.bracket f g ∈ π.normalizer I :=
  PoissonStructure.bracket_mem_normalizer hf hg

/-- Hamilton–Jacobi. -/
example (π : PoissonStructure P) {I : Ideal P}
    (hI : ∀ f ∈ I, ∀ g ∈ I, π.bracket f g ∈ I) {H : P} {E : ℝ}
    (hH : H - algebraMap ℝ P E ∈ I) {f : P} (hf : f ∈ I) : π.bracket f H ∈ I :=
  PoissonStructure.hamiltonJacobi (π := π) hI hH hf

/-- Maupertuis–Jacobi. -/
example (π : PoissonStructure P) {H H' u : P} {E E' : ℝ}
    (h : H' - algebraMap ℝ P E' = u * (H - algebraMap ℝ P E)) (g : P) :
    π.bracket g H' - u * π.bracket g H ∈ Ideal.span {H - algebraMap ℝ P E} :=
  PoissonStructure.maupertuis h g

end Abstract

section Free

variable {κ : Type*}

/-- The Jacobi identity on a free ring is a condition on generators. -/
example (π : AlmostPoissonStructure (FreeSmoothRing κ))
    (h : ∀ a b c, π.jacobiator (FreeSmoothRing.generator a) (FreeSmoothRing.generator b)
      (FreeSmoothRing.generator c) = 0) (f g k : FreeSmoothRing κ) :
    π.bracket (π.bracket f g) k + π.bracket (π.bracket g k) f +
      π.bracket (π.bracket k f) g = 0 :=
  FreeSmoothRing.jacobiator_eq_zero π h f g k

example [Fintype κ] [DecidableEq κ] (w : κ → κ → FreeSmoothRing κ)
    (hw : ∀ a b, w a b = -w b a) (a b : κ) :
    (FreeSmoothRing.almostPoisson w hw).bracket (FreeSmoothRing.generator a)
      (FreeSmoothRing.generator b) = w a b :=
  FreeSmoothRing.almostPoisson_bracket_generator w hw a b

end Free

section Canonical

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example (i j : ι) :
    (PhaseSpace.canonical ι).bracket (PhaseSpace.q i) (PhaseSpace.p j) =
      if i = j then 1 else 0 :=
  PhaseSpace.canonical_q_p i j

example (i j : ι) : (PhaseSpace.canonical ι).bracket (PhaseSpace.q i) (PhaseSpace.q j) = 0 :=
  PhaseSpace.canonical_q_q i j

example (i j : ι) : (PhaseSpace.canonical ι).bracket (PhaseSpace.p i) (PhaseSpace.p j) = 0 :=
  PhaseSpace.canonical_p_p i j

example (f g : PhaseSpace ι) :
    (PhaseSpace.canonical ι).bracket f g =
      ∑ i, (FreeSmoothRing.partialDerivation (Sum.inl i) f *
          FreeSmoothRing.partialDerivation (Sum.inr i) g -
        FreeSmoothRing.partialDerivation (Sum.inr i) f *
          FreeSmoothRing.partialDerivation (Sum.inl i) g) :=
  PhaseSpace.canonical_bracket f g

/-- Hamilton's equations. -/
example (i : ι) (H : PhaseSpace ι) :
    (PhaseSpace.canonical ι).bracket (PhaseSpace.q i) H =
      FreeSmoothRing.partialDerivation (Sum.inr i) H :=
  PhaseSpace.canonical_q_bracket i H

example (i : ι) (H : PhaseSpace ι) :
    (PhaseSpace.canonical ι).bracket (PhaseSpace.p i) H =
      -FreeSmoothRing.partialDerivation (Sum.inl i) H :=
  PhaseSpace.canonical_p_bracket i H

/-- The Jacobi identity of the canonical bracket. -/
example (f g h : PhaseSpace ι) :
    (PhaseSpace.canonical ι).bracket ((PhaseSpace.canonical ι).bracket f g) h +
      (PhaseSpace.canonical ι).bracket ((PhaseSpace.canonical ι).bracket g h) f +
      (PhaseSpace.canonical ι).bracket ((PhaseSpace.canonical ι).bracket h f) g = 0 :=
  (PhaseSpace.canonical ι).jacobi f g h

end Canonical

section RigidBody

example : RigidBody.poisson.bracket (RigidBody.L 0) (RigidBody.L 1) = -RigidBody.L 2 :=
  RigidBody.poisson_L_zero_L_one

example : RigidBody.poisson.bracket (RigidBody.L 1) (RigidBody.L 2) = -RigidBody.L 0 :=
  RigidBody.poisson_L_one_L_two

example : RigidBody.poisson.bracket (RigidBody.L 2) (RigidBody.L 0) = -RigidBody.L 1 :=
  RigidBody.poisson_L_two_L_zero

/-- The bracket of the rigid body is not the zero bracket. -/
example : RigidBody.poisson.bracket (RigidBody.L 0) (RigidBody.L 1) ≠ 0 :=
  RigidBody.poisson_L_zero_L_one_ne_zero

example (f g : RigidBody.PhaseSpace) :
    RigidBody.poisson.bracket f g =
      -(RigidBody.L ⬝ᵥ (RigidBody.gradient f ⨯₃ RigidBody.gradient g)) :=
  RigidBody.poisson_bracket f g

/-- Euler's equations. -/
example (I : Fin 3 → ℝ) (a : Fin 3) :
    RigidBody.poisson.bracket (RigidBody.L a) (RigidBody.kineticEnergy I) =
      (RigidBody.L ⨯₃ RigidBody.angularVelocity I) a :=
  RigidBody.euler_equations I a

example (I : Fin 3 → ℝ) :
    RigidBody.poisson.bracket (RigidBody.L 0) (RigidBody.kineticEnergy I) =
      algebraMap ℝ RigidBody.PhaseSpace ((I 2)⁻¹ - (I 1)⁻¹) *
        (RigidBody.L 1 * RigidBody.L 2) :=
  RigidBody.euler_equation_zero I

example (I : Fin 3 → ℝ) :
    RigidBody.kineticEnergy I =
      ∑ i, algebraMap ℝ RigidBody.PhaseSpace ((I i)⁻¹ / 2) * (RigidBody.L i * RigidBody.L i) :=
  rfl

example : RigidBody.casimir = ∑ i, RigidBody.L i * RigidBody.L i := rfl

/-- `|L|²` is a Casimir. -/
example (g : RigidBody.PhaseSpace) : RigidBody.poisson.bracket RigidBody.casimir g = 0 :=
  RigidBody.poisson_casimir_left g

end RigidBody

section Morphisms

variable {Q : Type*} [CommRing Q] [Algebra ℝ Q] [SmoothRing Q] {κ : Type*}

/-- A morphism out of a free ring is Poisson if it preserves generator brackets. -/
example {π : AlmostPoissonStructure (FreeSmoothRing κ)} {ρ : AlmostPoissonStructure Q}
    {φ : SmoothRingHom (FreeSmoothRing κ) Q}
    (h : ∀ a b, φ (π.bracket (FreeSmoothRing.generator a) (FreeSmoothRing.generator b)) =
      ρ.bracket (φ (FreeSmoothRing.generator a)) (φ (FreeSmoothRing.generator b)))
    (f g : FreeSmoothRing κ) : φ (π.bracket f g) = ρ.bracket (φ f) (φ g) :=
  FreeSmoothRing.isPoissonHom_of_generators h f g

end Morphisms

section AngularMomentum

open AngularMomentum

example : M = q ⨯₃ p := rfl

example : canonical.bracket (M 0) (M 1) = M 2 := canonical_M_zero_M_one

example : canonical.bracket (M 1) (M 2) = M 0 := canonical_M_one_M_two

example : canonical.bracket (M 2) (M 0) = M 1 := canonical_M_two_M_zero

example : canonical.bracket (M 0) (q 1) = q 2 := canonical_M_q 0 1

example : canonical.bracket (M 0) (p 1) = p 2 := canonical_M_p 0 1

example (a : Fin 3) : canonical.bracket (M a) (q ⬝ᵥ q) = 0 := canonical_M_q_sq a

/-- Conservation of angular momentum for every central Hamiltonian. -/
example (f : SmoothOperation 3) (a : Fin 3) :
    canonical.bracket (M a) (op f ![q ⬝ᵥ q, p ⬝ᵥ p, q ⬝ᵥ p]) = 0 :=
  isIntegral_M f a

/-- The momentum map of the rotations is a Poisson morphism from the rigid-body ring. -/
example (f g : RigidBody.PhaseSpace) :
    momentumMap (RigidBody.poisson.bracket f g) =
      canonical.bracket (momentumMap f) (momentumMap g) :=
  isPoissonHom_momentumMap f g

example (a : Fin 3) : momentumMap (RigidBody.L a) = -M a := momentumMap_L a

end AngularMomentum

section HeavyTop

open HeavyTop

example : HeavyTop.poisson.bracket (HeavyTop.L 0) (HeavyTop.L 1) = -HeavyTop.L 2 := by
  rw [HeavyTop.poisson_L_L]
  rfl

example : HeavyTop.poisson.bracket (HeavyTop.L 0) (Γ 1) = -Γ 2 := by
  rw [poisson_L_Γ]
  rfl

example (a b : Fin 3) : HeavyTop.poisson.bracket (Γ a) (Γ b) = 0 := poisson_Γ_Γ a b

/-- The equations of motion of the heavy top. -/
example (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) (a : Fin 3) :
    HeavyTop.poisson.bracket (HeavyTop.L a) (HeavyTop.hamiltonian I k χ) =
      (HeavyTop.L ⨯₃ HeavyTop.angularVelocity I) a + (Γ ⨯₃ weight k χ) a :=
  poisson_L_hamiltonian I k χ a

example (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) (a : Fin 3) :
    HeavyTop.poisson.bracket (Γ a) (HeavyTop.hamiltonian I k χ) =
      (Γ ⨯₃ HeavyTop.angularVelocity I) a :=
  poisson_Γ_hamiltonian I k χ a

example (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) :
    HeavyTop.hamiltonian I k χ =
      ∑ i, algebraMap ℝ HeavyTop.PhaseSpace ((I i)⁻¹ / 2) * (HeavyTop.L i * HeavyTop.L i) +
        ∑ i, algebraMap ℝ HeavyTop.PhaseSpace (k * χ i) * Γ i :=
  rfl

/-- The Casimirs of the heavy top. -/
example (g : HeavyTop.PhaseSpace) : HeavyTop.poisson.bracket (Γ ⬝ᵥ Γ) g = 0 :=
  poisson_Γ_sq_left g

example (g : HeavyTop.PhaseSpace) : HeavyTop.poisson.bracket (HeavyTop.L ⬝ᵥ Γ) g = 0 :=
  poisson_L_dot_Γ_left g

end HeavyTop

section Galilei

open AngularMomentum Galilei

example (m t : ℝ) (a : Fin 3) :
    K m t a = algebraMap ℝ Space m * q a - algebraMap ℝ Space t * p a := rfl

/-- The mass is the central term of the Galilei algebra. -/
example (m t : ℝ) (a b : Fin 3) :
    canonical.bracket (K m t a) (p b) = if a = b then algebraMap ℝ Space m else 0 :=
  canonical_K_p m t a b

example (m t : ℝ) (a b : Fin 3) : canonical.bracket (K m t a) (K m t b) = 0 :=
  canonical_K_K m t a b

example (m t : ℝ) : canonical.bracket (M 0) (K m t 1) = K m t 2 := canonical_M_K m t 0 1

example (m : ℝ) (a : Fin 3) : canonical.bracket (M a) (freeHamiltonian m) = 0 :=
  canonical_M_freeHamiltonian m a

example (m : ℝ) (a : Fin 3) : canonical.bracket (p a) (freeHamiltonian m) = 0 :=
  canonical_p_freeHamiltonian m a

/-- `{K, H₀} = p` cancels the explicit time dependence `K_t − K_s = −(t − s) p`. -/
example {m : ℝ} (hm : m ≠ 0) (t : ℝ) (a : Fin 3) :
    canonical.bracket (K m t a) (freeHamiltonian m) = p a :=
  canonical_K_freeHamiltonian hm t a

example (m t s : ℝ) (a : Fin 3) :
    K m t a - K m s a = -(algebraMap ℝ Space (t - s) * p a) :=
  K_sub_K m t s a

end Galilei

section Virial

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

example (H : PhaseSpace ι) :
    (PhaseSpace.canonical ι).bracket (∑ i, PhaseSpace.q i * PhaseSpace.p i) H =
      ∑ i, PhaseSpace.p i * FreeSmoothRing.partialDerivation (Sum.inr i) H -
        ∑ i, PhaseSpace.q i * FreeSmoothRing.partialDerivation (Sum.inl i) H :=
  PhaseSpace.canonical_dilation_bracket H

/-- The virial identity `{Σ qᵢ pᵢ, T + U} = 2T − kU`. -/
example (m : ι → ℝ) {U : PhaseSpace ι} {k : ℝ}
    (hU : ∑ i, PhaseSpace.q i * FreeSmoothRing.partialDerivation (Sum.inl i) U =
      algebraMap ℝ (PhaseSpace ι) k * U)
    (hUp : ∀ i, FreeSmoothRing.partialDerivation (Sum.inr i) U = 0) :
    (PhaseSpace.canonical ι).bracket PhaseSpace.dilation (PhaseSpace.kineticEnergy m + U) =
      2 * PhaseSpace.kineticEnergy m - algebraMap ℝ (PhaseSpace ι) k * U :=
  PhaseSpace.virial m hU hUp

/-- The hypotheses are satisfiable: the isotropic oscillator has degree two. -/
example (m : ι → ℝ) (k : ℝ) :
    (PhaseSpace.canonical ι).bracket PhaseSpace.dilation
        (PhaseSpace.kineticEnergy m + PhaseSpace.oscillatorPotential k) =
      2 * PhaseSpace.kineticEnergy m -
        algebraMap ℝ (PhaseSpace ι) 2 * PhaseSpace.oscillatorPotential k :=
  PhaseSpace.virial_oscillator m k

end Virial

section Trajectories

variable {κ : Type*}

/-- A morphism out of a free ring intertwines two vector fields if it does so
on generators. -/
example {B : Type*} [CommRing B] [Algebra ℝ B] [SmoothRing B]
    (φ : SmoothRingHom (FreeSmoothRing κ) B)
    (D : SmoothDerivation (FreeSmoothRing κ) (FreeSmoothRing κ)) (E : SmoothDerivation B B)
    (h : ∀ i, φ (D (FreeSmoothRing.generator i)) = E (φ (FreeSmoothRing.generator i)))
    (s : FreeSmoothRing κ) : φ (D s) = E (φ s) :=
  FreeSmoothRing.map_derivation_eq φ D E h s

example (π : PoissonStructure (FreeSmoothRing κ)) (H : FreeSmoothRing κ)
    (c : κ → TimeFunction) :
    IsTrajectory π H c ↔ ∀ a, timeDerivative (c a) =
      FreeSmoothRing.lift c (π.bracket (FreeSmoothRing.generator a) H) :=
  Iff.rfl

/-- Along a trajectory, `d/dt f(c) = {f, H}(c)` for every observable. -/
example {π : PoissonStructure (FreeSmoothRing κ)} {H : FreeSmoothRing κ}
    {c : κ → TimeFunction} (h : IsTrajectory π H c) (f : FreeSmoothRing κ) :
    timeDerivative (FreeSmoothRing.lift c f) = FreeSmoothRing.lift c (π.bracket f H) :=
  h.timeDerivative_lift f

/-- Integrals of the motion are constant along trajectories. -/
example {π : PoissonStructure (FreeSmoothRing κ)} {H f : FreeSmoothRing κ}
    {c : κ → TimeFunction} (h : IsTrajectory π H c) (hf : π.bracket f H = 0)
    (s t : Fin 1 → ℝ) : FreeSmoothRing.lift c f s = FreeSmoothRing.lift c f t :=
  h.lift_eq_of_isIntegral hf s t

example {π : PoissonStructure (FreeSmoothRing κ)} {H : FreeSmoothRing κ}
    {c : κ → TimeFunction} (h : IsTrajectory π H c) (s t : Fin 1 → ℝ) :
    FreeSmoothRing.lift c H s = FreeSmoothRing.lift c H t :=
  h.lift_hamiltonian_eq s t

/-- Trajectories of the canonical bracket are solutions of Hamilton's equations. -/
example {ι : Type*} [DecidableEq ι] [Fintype ι] (H : PhaseSpace ι)
    (c : ι ⊕ ι → TimeFunction) :
    IsTrajectory (PhaseSpace.canonical ι) H c ↔
      (∀ i, timeDerivative (c (Sum.inl i)) =
        FreeSmoothRing.lift c (FreeSmoothRing.partialDerivation (Sum.inr i) H)) ∧
      ∀ i, timeDerivative (c (Sum.inr i)) =
        -FreeSmoothRing.lift c (FreeSmoothRing.partialDerivation (Sum.inl i) H) :=
  isTrajectory_canonical_iff H c

/-- Angular momentum is constant along trajectories in a central field. -/
example (f : SmoothOperation 3) {c : Fin 3 ⊕ Fin 3 → TimeFunction}
    (h : IsTrajectory AngularMomentum.canonical (op f AngularMomentum.scalars) c) (a : Fin 3)
    (s t : Fin 1 → ℝ) :
    FreeSmoothRing.lift c (AngularMomentum.M a) s =
      FreeSmoothRing.lift c (AngularMomentum.M a) t :=
  AngularMomentum.lift_M_eq f h a s t

example {H : RigidBody.PhaseSpace} {c : Fin 3 → TimeFunction}
    (h : IsTrajectory RigidBody.poisson H c) (s t : Fin 1 → ℝ) :
    FreeSmoothRing.lift c RigidBody.casimir s = FreeSmoothRing.lift c RigidBody.casimir t :=
  RigidBody.lift_casimir_eq h s t

end Trajectories

section RotatingFrame

open AngularMomentum RotatingFrame

example (m : ℝ) (U : Space) (Ω : Fin 3 → ℝ) :
    hamiltonian m U Ω = Galilei.freeHamiltonian m + U - angularVelocity Ω ⬝ᵥ M := rfl

example (m : ℝ) (Ω : Fin 3 → ℝ) (a : Fin 3) :
    velocity m Ω a = algebraMap ℝ Space m⁻¹ * p a - (angularVelocity Ω ⨯₃ q) a := rfl

example (Ω : Fin 3 → ℝ) (a : Fin 3) : angularVelocity Ω a = algebraMap ℝ Space (Ω a) := rfl

/-- `q̇ = p / m − Ω × q`. -/
example (m : ℝ) {U : Space}
    (hU : ∀ a, FreeSmoothRing.partialDerivation (Sum.inr a) U = 0) (Ω : Fin 3 → ℝ)
    (a : Fin 3) :
    canonical.bracket (q a) (hamiltonian m U Ω) =
      algebraMap ℝ Space m⁻¹ * p a - (angularVelocity Ω ⨯₃ q) a :=
  canonical_q_hamiltonian m hU Ω a

/-- `ṗ = −∇U − Ω × p`. -/
example (m : ℝ) (U : Space) (Ω : Fin 3 → ℝ) (a : Fin 3) :
    canonical.bracket (p a) (hamiltonian m U Ω) =
      -FreeSmoothRing.partialDerivation (Sum.inl a) U - (angularVelocity Ω ⨯₃ p) a :=
  canonical_p_hamiltonian m U Ω a

/-- The Coriolis and centrifugal accelerations, with their signs. -/
example (m : ℝ) {U : Space}
    (hU : ∀ a, FreeSmoothRing.partialDerivation (Sum.inr a) U = 0) (Ω : Fin 3 → ℝ)
    (a : Fin 3) :
    canonical.bracket (velocity m Ω a) (hamiltonian m U Ω) =
      -(algebraMap ℝ Space m⁻¹ * FreeSmoothRing.partialDerivation (Sum.inl a) U) -
        2 * (angularVelocity Ω ⨯₃ velocity m Ω) a -
        (angularVelocity Ω ⨯₃ (angularVelocity Ω ⨯₃ q)) a :=
  canonical_velocity_hamiltonian m hU Ω a

/-- The energy contains the centrifugal potential. -/
example {m : ℝ} (hm : m ≠ 0) (U : Space) (Ω : Fin 3 → ℝ) :
    hamiltonian m U Ω =
      algebraMap ℝ Space (m / 2) * (velocity m Ω ⬝ᵥ velocity m Ω) -
        algebraMap ℝ Space (m / 2) *
          ((angularVelocity Ω ⨯₃ q) ⬝ᵥ (angularVelocity Ω ⨯₃ q)) + U :=
  hamiltonian_eq_velocity hm U Ω

end RotatingFrame

section Kepler

variable {P : Type*} [CommRing P] [Algebra ℝ P] [SmoothRing P]
  {π : PoissonStructure P} {q p : Fin 3 → P} {ρ : P}

/-- A Kepler frame assumes only brackets; the relation `ρ² |q|² = 1` is not a
hypothesis. -/
example : Kepler.IsFrame π q p ρ ↔
    (∀ i j, π.bracket (q i) (q j) = 0) ∧ (∀ i j, π.bracket (p i) (p j) = 0) ∧
      (∀ i j, π.bracket (q i) (p j) = if i = j then 1 else 0) ∧
      (∀ j, π.bracket ρ (q j) = 0) ∧ ∀ j, π.bracket ρ (p j) = -(ρ * ρ * ρ * q j) :=
  ⟨fun h => ⟨h.q_q, h.p_p, h.q_p, h.ρ_q, h.ρ_p⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

example (m α : ℝ) (a : Fin 3) :
    Kepler.rungeLenz m α q p ρ a =
      (p ⨯₃ (q ⨯₃ p)) a - algebraMap ℝ P m * algebraMap ℝ P α * (ρ * q a) := rfl

example (m α : ℝ) :
    Kepler.hamiltonian m α p ρ = algebraMap ℝ P (m⁻¹ / 2) * (p ⬝ᵥ p) - algebraMap ℝ P α * ρ :=
  rfl

example : Kepler.constraint q ρ = ρ * ρ * (q ⬝ᵥ q) - 1 := rfl

/-- E5a: the Runge–Lenz vector is conserved up to the constraint. -/
example (h : Kepler.IsFrame π q p ρ) {m : ℝ} (hm : m ≠ 0) (α : ℝ) (a : Fin 3) :
    π.bracket (Kepler.rungeLenz m α q p ρ a) (Kepler.hamiltonian m α p ρ) =
      algebraMap ℝ P α * ρ * p a * Kepler.constraint q ρ :=
  h.rungeLenz_hamiltonian hm α a

/-- E5b. -/
example (h : Kepler.IsFrame π q p ρ) (m α : ℝ) (a b : Fin 3) :
    π.bracket (Kepler.angularMomentum q p a) (Kepler.rungeLenz m α q p ρ b) =
      epsilon (Kepler.rungeLenz m α q p ρ) a b :=
  h.angularMomentum_rungeLenz m α a b

/-- E5c. -/
example (h : Kepler.IsFrame π q p ρ) {m : ℝ} (hm : m ≠ 0) (α : ℝ) (a b : Fin 3) :
    π.bracket (Kepler.rungeLenz m α q p ρ a) (Kepler.rungeLenz m α q p ρ b) =
      -(2 * algebraMap ℝ P m * Kepler.hamiltonian m α p ρ +
          algebraMap ℝ P m * algebraMap ℝ P α * ρ * Kepler.constraint q ρ) *
        epsilon (Kepler.angularMomentum q p) a b :=
  h.rungeLenz_rungeLenz hm α a b

/-- E5d. -/
example (m α : ℝ) : Kepler.rungeLenz m α q p ρ ⬝ᵥ Kepler.angularMomentum q p = 0 :=
  Kepler.rungeLenz_dotProduct_angularMomentum m α q p ρ

/-- E5e. -/
example {m : ℝ} (hm : m ≠ 0) (α : ℝ) :
    Kepler.rungeLenz m α q p ρ ⬝ᵥ Kepler.rungeLenz m α q p ρ =
      algebraMap ℝ P m * algebraMap ℝ P m * (algebraMap ℝ P α * algebraMap ℝ P α) +
        2 * algebraMap ℝ P m * Kepler.hamiltonian m α p ρ *
          (Kepler.angularMomentum q p ⬝ᵥ Kepler.angularMomentum q p) +
        algebraMap ℝ P m * algebraMap ℝ P m * (algebraMap ℝ P α * algebraMap ℝ P α) *
          Kepler.constraint q ρ :=
  Kepler.rungeLenz_dotProduct_self hm α q p ρ

/-- E5f: the orbit identity. -/
example (m α : ℝ) :
    Kepler.rungeLenz m α q p ρ ⬝ᵥ q =
      Kepler.angularMomentum q p ⬝ᵥ Kepler.angularMomentum q p -
        algebraMap ℝ P m * algebraMap ℝ P α * Kepler.distance q ρ :=
  Kepler.rungeLenz_dotProduct_q m α q p ρ

example (h : Kepler.IsFrame π q p ρ) (m α : ℝ) (a : Fin 3) :
    π.bracket (Kepler.angularMomentum q p a) (Kepler.hamiltonian m α p ρ) = 0 :=
  h.angularMomentum_hamiltonian m α a

/-- Kepler frames exist: the free ring on `q`, `p` and `ρ`. -/
example : Kepler.IsFrame KeplerModel.poisson KeplerModel.q KeplerModel.p KeplerModel.ρ :=
  KeplerModel.isFrame

example : KeplerModel.poisson.IsPoissonIdeal KeplerModel.constraintIdeal :=
  KeplerModel.isPoissonIdeal_constraintIdeal

/-- A Kepler motion is Newton's equations for the inverse-square force. -/
example (m α : ℝ) (Q Pm : Fin 3 → TimeFunction) (R : TimeFunction) :
    KeplerModel.IsKeplerMotion m α Q Pm R ↔
      R * R * (Q ⬝ᵥ Q) = 1 ∧
        (∀ i, timeDerivative (Q i) = algebraMap ℝ TimeFunction m⁻¹ * Pm i) ∧
        ∀ i, timeDerivative (Pm i) = -(algebraMap ℝ TimeFunction α * (R * R * R * Q i)) :=
  ⟨fun h => ⟨h.constraint, h.velocity, h.force⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

/-- The Runge–Lenz vector is constant along Kepler motions. -/
example {m α : ℝ} {Q Pm : Fin 3 → TimeFunction} {R : TimeFunction}
    (h : KeplerModel.IsKeplerMotion m α Q Pm R) (hm : m ≠ 0) (a : Fin 3) (s t : Fin 1 → ℝ) :
    Kepler.rungeLenz m α Q Pm R a s = Kepler.rungeLenz m α Q Pm R a t :=
  h.rungeLenz_eq hm a s t

example {m α : ℝ} {Q Pm : Fin 3 → TimeFunction} {R : TimeFunction}
    (h : KeplerModel.IsKeplerMotion m α Q Pm R) (a : Fin 3) (s t : Fin 1 → ℝ) :
    Kepler.angularMomentum Q Pm a s = Kepler.angularMomentum Q Pm a t :=
  h.angularMomentum_eq a s t

example {m α : ℝ} {Q Pm : Fin 3 → TimeFunction} {R : TimeFunction}
    (h : KeplerModel.IsKeplerMotion m α Q Pm R) :
    R * Kepler.distance Q R = 1 ∧ Kepler.distance Q R * Kepler.distance Q R = Q ⬝ᵥ Q :=
  ⟨h.R_mul_distance, h.distance_mul_distance⟩

/-- Kepler motions exist: the uniform circular motion. -/
example :
    KeplerModel.IsKeplerMotion 1 1 ![TimeFunction.cos, TimeFunction.sin, 0]
      ![-TimeFunction.sin, TimeFunction.cos, 0] 1 :=
  KeplerModel.isKeplerMotion_circular

end Kepler
