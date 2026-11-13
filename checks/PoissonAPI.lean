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
