/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.Electrodynamics.Hamiltonian
public import ProjectAinos.Mechanics.Poisson.RotatingFrame
public import ProjectAinos.SmoothGeometry.ODE.Averaging
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Larmor's theorem

A charge `e` of mass `m` in a uniform constant magnetic field `B` has, in the symmetric gauge
`a = ½ B × x` (`symmetricGauge`, whose field is `B` by `magneticTensor_symmetricGauge`), the
nonrelativistic Hamiltonian `Σᵢ πᵢ² / 2m + U` with `π = p − e a` (`hamiltonian`). Expanding the
square (Landau–Lifshitz, *The Classical Theory of Fields*, §45; units with `c = 1`),

`H = |p|² / 2m + U − Ω_L · M + (e² / 8m) |B × q|²`, `Ω_L = e B / 2m`,

so that `H` is the Hamiltonian of the frame rotating with the Larmor frequency `Ω_L`
(`RotatingFrame.hamiltonian`, §39) plus a term of the second order in the field
(`hamiltonian_eq_rotating`). The identity is exact and holds for every potential `U`.

* `systemHamiltonian_eq_rotating`: the same identity for particles `ι` of the masses `mₐ` and
  the charges `eₐ` with one ratio `eₐ / mₐ = γ` (Landau–Lifshitz's hypothesis), with the rotating
  Hamiltonian `rotatingHamiltonian` of the total angular momentum `totalAngularMomentum`, the
  common Larmor frequency `Ω_L = γ B / 2` (`ratioLarmorFrequency`) and the term
  `Σₐ (eₐ² / 8mₐ) |B × qₐ|²`. `systemHamiltonian_eq_rotating_const` is the case of one charge
  and one mass.
* `larmorField` and `rotatingField` are the equations of motion of the two Hamiltonians as
  vector fields on the phase space `ι × Fin 3 ⊕ ι × Fin 3 → ℝ`, for an arbitrary force `f` in
  place of `−∇U`; for one ratio `eₐ / mₐ` they differ by the field `diamagneticField` of the term
  of the second order (`larmorField_eq`). For a smooth potential of the positions they are the
  Hamiltonian fields (`hamiltonianField_systemHamiltonian`,
  `hamiltonianField_rotatingHamiltonian`).
* `norm_sub_le_larmor`: the effect of the neglected term. Let `z` solve the equations in the
  field and `Z` those in the rotating frame on `[0, L]` from the same point, both in a set where
  the rotating field is Lipschitz with the constant `K` and every particle is within the
  Euclidean distance `R` of the origin, and let `c ≥ |eₐ² / 4mₐ|` for every particle. Then in the
  sup norm of the phase space `‖z(t) − Z(t)‖ ≤ c |B|² R t e^{K t}`. The force is arbitrary, so
  that a Coulomb potential is admitted on a set that avoids the collisions.
  `norm_sub_le_larmor_const` is the bound `(e² |B|² R / 4m) t e^{K t}` for one charge and one
  mass, and `norm_sub_le_larmor_of_hamiltonianField` the statement for a smooth potential.
* `norm_exampleOrbit_sub_le`: an instance of the hypotheses of the bound, for the isotropic
  oscillator `U = 9 |q|² / 2` with `m = 1`, `e = 2`, `B = (0, 0, 4)`, where both motions are
  explicit (`exampleOrbit`) and differ.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.Electrodynamics.Larmor

open Set
open scoped NNReal Interval
open SmoothAlgebra SmoothRing FreeSmoothRing Matrix Mechanics

/-! ### The symmetric gauge -/

/-- The symmetric gauge `a = ½ B × x` of a uniform magnetic field `B`. -/
def symmetricGauge (B : Fin 3 → ℝ) : Fin 3 → FreeSmoothRing (Fin 3) :=
  fun i => algebraMap ℝ (FreeSmoothRing (Fin 3)) (1 / 2) *
    ((fun k => algebraMap ℝ (FreeSmoothRing (Fin 3)) (B k)) ⨯₃
      (generator : Fin 3 → FreeSmoothRing (Fin 3))) i

/-- The field of the symmetric gauge is the uniform field `B`: `Fᵢⱼ = Σₖ εᵢⱼₖ Bₖ`, so that
`Σⱼ Fᵢⱼ vⱼ = (v × B)ᵢ` (`epsilon`, `sum_epsilon_mul`). -/
theorem magneticTensor_symmetricGauge (B : Fin 3 → ℝ) (i j : Fin 3) :
    ChargedParticle.magneticTensor (symmetricGauge B) i j =
      epsilon (fun k => algebraMap ℝ (FreeSmoothRing (Fin 3)) (B k)) i j := by
  fin_cases i <;> fin_cases j <;>
    simp [ChargedParticle.magneticTensor, symmetricGauge, cross_apply, epsilon,
      SmoothDerivation.map_algebraMap_mul, partialDerivation_generator] <;>
    refine FreeSmoothRing.ext_lift fun x => ?_ <;>
    simp only [SmoothRingHom.map_mul, SmoothRingHom.map_sub, SmoothRingHom.map_neg,
      SmoothRingHom.map_algebraMap, Algebra.algebraMap_self, RingHom.id_apply] <;>
    ring

/-- In the phase space, the symmetric gauge is `½ B × q`. -/
theorem ofPosition_symmetricGauge (B : Fin 3 → ℝ) (i : Fin 3) :
    PhaseSpace.ofPosition (Fin 3) (symmetricGauge B i) =
      algebraMap ℝ AngularMomentum.Space (1 / 2) *
        (RotatingFrame.angularVelocity B ⨯₃ AngularMomentum.q) i := by
  fin_cases i <;>
    simp [symmetricGauge, cross_apply, RotatingFrame.angularVelocity, AngularMomentum.q,
      SmoothRingHom.map_sub]

/-! ### One charge -/

/-- The Larmor frequency `Ω_L = e B / 2m`. -/
def larmorFrequency (e m : ℝ) (B : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => e / (2 * m) * B i

/-- The nonrelativistic Hamiltonian `Σᵢ πᵢ² / 2m + U` of a charge `e` of mass `m` in the uniform
magnetic field `B`, with the kinetic momentum `π = p − e a` of the symmetric gauge. -/
def hamiltonian (m e : ℝ) (U : AngularMomentum.Space) (B : Fin 3 → ℝ) : AngularMomentum.Space :=
  algebraMap ℝ AngularMomentum.Space (m⁻¹ / 2) *
    ∑ i, ChargedParticle.kineticMomentum e (symmetricGauge B) i ^ 2 + U

/-- Larmor's theorem, exactly: the Hamiltonian of a charge in a uniform magnetic field is the
Hamiltonian in the frame rotating with the Larmor frequency `Ω_L = e B / 2m`, plus the term
`(e² / 8m) |B × q|²` of the second order in the field. -/
theorem hamiltonian_eq_rotating (m e : ℝ) (U : AngularMomentum.Space) (B : Fin 3 → ℝ) :
    hamiltonian m e U B = RotatingFrame.hamiltonian m U (larmorFrequency e m B) +
      algebraMap ℝ AngularMomentum.Space (e ^ 2 / (8 * m)) *
        ∑ i, (RotatingFrame.angularVelocity B ⨯₃ AngularMomentum.q) i ^ 2 := by
  refine FreeSmoothRing.ext_lift fun x => ?_
  simp only [hamiltonian, ChargedParticle.kineticMomentum, ofPosition_symmetricGauge,
    RotatingFrame.hamiltonian, Galilei.freeHamiltonian, AngularMomentum.M, dotProduct,
    Fin.sum_univ_three, cross_apply, RotatingFrame.angularVelocity, larmorFrequency, sq,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, AngularMomentum.q, AngularMomentum.p, PhaseSpace.q, PhaseSpace.p,
    SmoothRingHom.map_add, SmoothRingHom.map_mul, SmoothRingHom.map_sub,
    SmoothRingHom.map_algebraMap, lift_generator, Algebra.algebraMap_self, RingHom.id_apply]
  ring

/-- Hamilton's equation of the position of a charge in the uniform field:
`q̇ = (p − (e / 2) B × q) / m`. -/
theorem hamiltonianField_hamiltonian_inl (m e : ℝ) (B : Fin 3 → ℝ) (y : Fin 3 ⊕ Fin 3 → ℝ)
    (j : Fin 3) :
    hamiltonianField (hamiltonian m e 0 B) y (Sum.inl j) =
      m⁻¹ * (y (Sum.inr j) - e / 2 * (B ⨯₃ fun i => y (Sum.inl i)) j) := by
  rw [hamiltonianField_inl, ← lift_real]
  fin_cases j <;>
    simp [hamiltonian, ChargedParticle.kineticMomentum, ofPosition_symmetricGauge,
      Fin.sum_univ_three, cross_apply, sq, RotatingFrame.angularVelocity, AngularMomentum.q,
      PhaseSpace.q, PhaseSpace.p, SmoothDerivation.map_mul, partialDerivation_generator,
      SmoothRingHom.map_sub] <;>
    ring

/-- Hamilton's equation of the momentum of a charge in the uniform field:
`ṗ = (e / 2m) π × B` with `π = p − (e / 2) B × q`. -/
theorem hamiltonianField_hamiltonian_inr (m e : ℝ) (B : Fin 3 → ℝ) (y : Fin 3 ⊕ Fin 3 → ℝ)
    (j : Fin 3) :
    hamiltonianField (hamiltonian m e 0 B) y (Sum.inr j) =
      e / (2 * m) *
        ((fun i => y (Sum.inr i) - e / 2 * (B ⨯₃ fun i => y (Sum.inl i)) i) ⨯₃ B) j := by
  rw [hamiltonianField_inr, ← lift_real]
  fin_cases j <;>
    simp [hamiltonian, ChargedParticle.kineticMomentum, ofPosition_symmetricGauge,
      Fin.sum_univ_three, cross_apply, sq, RotatingFrame.angularVelocity, AngularMomentum.q,
      PhaseSpace.q, PhaseSpace.p, SmoothDerivation.map_mul, partialDerivation_generator,
      SmoothRingHom.map_sub, SmoothRingHom.map_neg] <;>
    ring

/-- Hamilton's equation of the position in the frame rotating with `Ω`, without a potential:
`q̇ = p / m − Ω × q`. -/
theorem hamiltonianField_rotatingFrame_inl (m : ℝ) (Ω : Fin 3 → ℝ) (y : Fin 3 ⊕ Fin 3 → ℝ)
    (j : Fin 3) :
    hamiltonianField (RotatingFrame.hamiltonian m 0 Ω) y (Sum.inl j) =
      m⁻¹ * y (Sum.inr j) - (Ω ⨯₃ fun i => y (Sum.inl i)) j := by
  rw [hamiltonianField_inl, ← lift_real]
  fin_cases j <;>
    simp [RotatingFrame.hamiltonian, Galilei.freeHamiltonian, AngularMomentum.M, dotProduct,
      Fin.sum_univ_three, cross_apply, RotatingFrame.angularVelocity, AngularMomentum.q,
      AngularMomentum.p, PhaseSpace.q, PhaseSpace.p, SmoothDerivation.map_mul,
      partialDerivation_generator, SmoothRingHom.map_sub, SmoothRingHom.map_neg] <;>
    ring

/-- Hamilton's equation of the momentum in the frame rotating with `Ω`, without a potential:
`ṗ = −Ω × p`. -/
theorem hamiltonianField_rotatingFrame_inr (m : ℝ) (Ω : Fin 3 → ℝ) (y : Fin 3 ⊕ Fin 3 → ℝ)
    (j : Fin 3) :
    hamiltonianField (RotatingFrame.hamiltonian m 0 Ω) y (Sum.inr j) =
      -(Ω ⨯₃ fun i => y (Sum.inr i)) j := by
  rw [hamiltonianField_inr, ← lift_real]
  fin_cases j <;>
    simp [RotatingFrame.hamiltonian, Galilei.freeHamiltonian, AngularMomentum.M, dotProduct,
      Fin.sum_univ_three, cross_apply, RotatingFrame.angularVelocity, AngularMomentum.q,
      AngularMomentum.p, PhaseSpace.q, PhaseSpace.p, SmoothDerivation.map_mul,
      partialDerivation_generator, SmoothRingHom.map_neg] <;>
    ring

/-! ### Several charges with one ratio of the charge to the mass -/

/-- The Larmor frequency `Ω_L = γ B / 2` of the ratio `γ = e / m` of the charge to the mass. -/
def ratioLarmorFrequency (γ : ℝ) (B : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => γ / 2 * B i

/-- The Larmor frequency of one charge depends on the ratio `e / m` only. -/
theorem larmorFrequency_eq_ratio (e m : ℝ) (B : Fin 3 → ℝ) :
    larmorFrequency e m B = ratioLarmorFrequency (e / m) B := by
  funext i
  simp only [larmorFrequency, ratioLarmorFrequency]
  ring

section System

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The position vector `qₐ` of the particle `a`. -/
def particleQ (a : ι) : Fin 3 → PhaseSpace (ι × Fin 3) := fun i => PhaseSpace.q (a, i)

/-- The canonical momentum vector `pₐ` of the particle `a`. -/
def particleP (a : ι) : Fin 3 → PhaseSpace (ι × Fin 3) := fun i => PhaseSpace.p (a, i)

variable (ι) in
/-- A constant vector on the phase space of the particles. The index type is explicit, since no
argument determines it. -/
def constVector (Ω : Fin 3 → ℝ) : Fin 3 → PhaseSpace (ι × Fin 3) :=
  fun i => algebraMap ℝ (PhaseSpace (ι × Fin 3)) (Ω i)

variable (ι) in
/-- The total angular momentum `M = Σₐ qₐ × pₐ`. The index type is explicit, since no argument
determines it. -/
def totalAngularMomentum : Fin 3 → PhaseSpace (ι × Fin 3) := ∑ a, particleQ a ⨯₃ particleP a

/-- The Hamiltonian `Σₐ |pₐ|² / 2mₐ + U − Ω · M` of particles of the masses `mₐ` in a frame
rotating with the constant angular velocity `Ω`, with the total angular momentum `M`. For one
particle it is `RotatingFrame.hamiltonian`. -/
def rotatingHamiltonian (m : ι → ℝ) (U : PhaseSpace (ι × Fin 3)) (Ω : Fin 3 → ℝ) :
    PhaseSpace (ι × Fin 3) :=
  ∑ a, algebraMap ℝ (PhaseSpace (ι × Fin 3)) ((m a)⁻¹ / 2) * ∑ i, particleP a i ^ 2 + U -
    constVector ι Ω ⬝ᵥ totalAngularMomentum ι

/-- The symmetric gauge at the position of the particle `a`. -/
def particleGauge (B : Fin 3 → ℝ) (a : ι) : Fin 3 → PhaseSpace (ι × Fin 3) :=
  fun i => FreeSmoothRing.lift (particleQ a) (symmetricGauge B i)

omit [Fintype ι] [DecidableEq ι] in
/-- The symmetric gauge at the position of the particle `a` is `½ B × qₐ`. -/
theorem particleGauge_eq (B : Fin 3 → ℝ) (a : ι) (i : Fin 3) :
    particleGauge B a i =
      algebraMap ℝ (PhaseSpace (ι × Fin 3)) (1 / 2) * (constVector ι B ⨯₃ particleQ a) i := by
  fin_cases i <;>
    simp [particleGauge, symmetricGauge, cross_apply, constVector, SmoothRingHom.map_sub]

/-- The kinetic momentum `πₐ = pₐ − e a(qₐ)` of the particle `a` of the charge `e`, in the
symmetric gauge. -/
def particleKineticMomentum (e : ℝ) (B : Fin 3 → ℝ) (a : ι) : Fin 3 → PhaseSpace (ι × Fin 3) :=
  fun i => particleP a i - algebraMap ℝ (PhaseSpace (ι × Fin 3)) e * particleGauge B a i

/-- The nonrelativistic Hamiltonian `Σₐ |πₐ|² / 2mₐ + U` of particles of the masses `mₐ` and the
charges `eₐ` in the uniform magnetic field `B`, with `πₐ = pₐ − (eₐ / 2) B × qₐ`. -/
def systemHamiltonian (m e : ι → ℝ) (U : PhaseSpace (ι × Fin 3)) (B : Fin 3 → ℝ) :
    PhaseSpace (ι × Fin 3) :=
  ∑ a, algebraMap ℝ (PhaseSpace (ι × Fin 3)) ((m a)⁻¹ / 2) *
    ∑ i, particleKineticMomentum (e a) B a i ^ 2 + U

omit [DecidableEq ι] in
/-- Larmor's theorem for a system of charges with one ratio `eₐ / mₐ = γ`, exactly: the
Hamiltonian in the uniform field `B` is the Hamiltonian in the frame rotating with the Larmor
frequency `Ω_L = γ B / 2`, plus the term `Σₐ (eₐ² / 8mₐ) |B × qₐ|²` of the second order in the
field. -/
theorem systemHamiltonian_eq_rotating {m e : ι → ℝ} {γ : ℝ} (he : ∀ a, e a / m a = γ)
    (U : PhaseSpace (ι × Fin 3)) (B : Fin 3 → ℝ) :
    systemHamiltonian m e U B = rotatingHamiltonian m U (ratioLarmorFrequency γ B) +
      ∑ a, algebraMap ℝ (PhaseSpace (ι × Fin 3)) (e a ^ 2 / (8 * m a)) *
        ∑ i, (constVector ι B ⨯₃ particleQ a) i ^ 2 := by
  have key : ∀ a : ι,
      algebraMap ℝ (PhaseSpace (ι × Fin 3)) ((m a)⁻¹ / 2) *
          ∑ i, particleKineticMomentum (e a) B a i ^ 2 =
        algebraMap ℝ (PhaseSpace (ι × Fin 3)) ((m a)⁻¹ / 2) * ∑ i, particleP a i ^ 2 -
          constVector ι (ratioLarmorFrequency γ B) ⬝ᵥ (particleQ a ⨯₃ particleP a) +
          algebraMap ℝ (PhaseSpace (ι × Fin 3)) (e a ^ 2 / (8 * m a)) *
            ∑ i, (constVector ι B ⨯₃ particleQ a) i ^ 2 := by
    intro a
    refine FreeSmoothRing.ext_lift fun x => ?_
    simp only [particleKineticMomentum, particleGauge_eq, dotProduct, Fin.sum_univ_three,
      cross_apply, constVector, ratioLarmorFrequency, sq, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, particleQ,
      particleP, PhaseSpace.q, PhaseSpace.p, SmoothRingHom.map_add, SmoothRingHom.map_mul,
      SmoothRingHom.map_sub, SmoothRingHom.map_algebraMap, lift_generator,
      Algebra.algebraMap_self, RingHom.id_apply]
    rw [← he a]
    ring
  rw [systemHamiltonian, rotatingHamiltonian, totalAngularMomentum, dotProduct_sum,
    Finset.sum_congr rfl fun a _ => key a, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

omit [DecidableEq ι] in
/-- For particles of one charge `e` and one mass `m`, `systemHamiltonian_eq_rotating` with the
Larmor frequency `Ω_L = e B / 2m`. -/
theorem systemHamiltonian_eq_rotating_const (m e : ℝ) (U : PhaseSpace (ι × Fin 3))
    (B : Fin 3 → ℝ) :
    systemHamiltonian (fun _ => m) (fun _ => e) U B =
      rotatingHamiltonian (fun _ => m) U (larmorFrequency e m B) +
        ∑ a, algebraMap ℝ (PhaseSpace (ι × Fin 3)) (e ^ 2 / (8 * m)) *
          ∑ i, (constVector ι B ⨯₃ particleQ a) i ^ 2 := by
  rw [larmorFrequency_eq_ratio]
  exact systemHamiltonian_eq_rotating (fun _ => rfl) U B

/-! ### The equations of motion as real fields -/

/-- The position of the particle `a` at a point of the phase space. -/
def realQ (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (a : ι) : Fin 3 → ℝ := fun i => z (Sum.inl (a, i))

/-- The momentum of the particle `a` at a point of the phase space. -/
def realP (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (a : ι) : Fin 3 → ℝ := fun i => z (Sum.inr (a, i))

/-- The positions of the particles at a point of the phase space. -/
def realPositions (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) : ι × Fin 3 → ℝ := fun k => z (Sum.inl k)

/-- The field of the rotating Hamiltonian `Σₐ |pₐ|² / 2mₐ + U − Ω · M`, with the force
`f = −∇U` as a function of the positions: `q̇ₐ = pₐ / mₐ − Ω × qₐ`, `ṗₐ = fₐ − Ω × pₐ`. The
force is arbitrary, so that `U` need only be defined where the motion takes place. -/
def rotatingField (m : ι → ℝ) (Ω : Fin 3 → ℝ) (f : (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ)
    (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) : ι × Fin 3 ⊕ ι × Fin 3 → ℝ
  | Sum.inl k => (m k.1)⁻¹ * z (Sum.inr k) - (Ω ⨯₃ realQ z k.1) k.2
  | Sum.inr k => f (realPositions z) k - (Ω ⨯₃ realP z k.1) k.2

/-- The kinetic momentum `πₐ = pₐ − (e / 2) B × qₐ` of a charge `e` at a point of the phase
space. -/
def realKineticMomentum (e : ℝ) (B : Fin 3 → ℝ) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (a : ι) :
    Fin 3 → ℝ :=
  fun i => z (Sum.inr (a, i)) - e / 2 * (B ⨯₃ realQ z a) i

/-- The field of the Hamiltonian `Σₐ |πₐ|² / 2mₐ + U` in the uniform field `B`, with the force
`f = −∇U`: `q̇ₐ = πₐ / mₐ`, `ṗₐ = fₐ + (eₐ / 2mₐ) πₐ × B`. -/
def larmorField (m e : ι → ℝ) (B : Fin 3 → ℝ) (f : (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ)
    (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) : ι × Fin 3 ⊕ ι × Fin 3 → ℝ
  | Sum.inl k => (m k.1)⁻¹ * realKineticMomentum (e k.1) B z k.1 k.2
  | Sum.inr k => f (realPositions z) k +
      e k.1 / (2 * m k.1) * (realKineticMomentum (e k.1) B z k.1 ⨯₃ B) k.2

/-- The field of the term `Σₐ (eₐ² / 8mₐ) |B × qₐ|²`: the force
`−(eₐ² / 4mₐ) (|B|² qₐ − (B · qₐ) B)` on the particle `a`. -/
def diamagneticField (m e : ι → ℝ) (B : Fin 3 → ℝ) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) :
    ι × Fin 3 ⊕ ι × Fin 3 → ℝ
  | Sum.inl _ => 0
  | Sum.inr k => -(e k.1 ^ 2 / (4 * m k.1)) *
      ((∑ j, B j ^ 2) * realQ z k.1 k.2 - (B ⬝ᵥ realQ z k.1) * B k.2)

omit [Fintype ι] [DecidableEq ι] in
/-- For one ratio `eₐ / mₐ = γ`, the field in the magnetic field is the field in the frame
rotating with the Larmor frequency `γ B / 2` plus the field of the term of the second order. -/
theorem larmorField_eq {m e : ι → ℝ} {γ : ℝ} (he : ∀ a, e a / m a = γ) (B : Fin 3 → ℝ)
    (f : (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) :
    larmorField m e B f z =
      rotatingField m (ratioLarmorFrequency γ B) f z + diamagneticField m e B z := by
  funext c
  rcases c with ⟨a, i⟩ | ⟨a, i⟩ <;> fin_cases i <;>
    simp [larmorField, rotatingField, diamagneticField, realKineticMomentum, realQ, realP,
      ratioLarmorFrequency, cross_apply, dotProduct, Fin.sum_univ_three] <;>
    rw [← he a] <;>
    ring

/-- `|(|B|² q − (B · q) B)ᵢ| ≤ |B|² R` when `|q| ≤ R`: the vector is `−B × (B × q)`. -/
theorem abs_diamagnetic_le {B q : Fin 3 → ℝ} {R : ℝ} (hR0 : 0 ≤ R)
    (hq : ∑ j, q j ^ 2 ≤ R ^ 2) (i : Fin 3) :
    |(∑ j, B j ^ 2) * q i - (B ⬝ᵥ q) * B i| ≤ (∑ j, B j ^ 2) * R := by
  set v : Fin 3 → ℝ := fun j => (∑ j, B j ^ 2) * q j - (B ⬝ᵥ q) * B j with hv
  have hB : 0 ≤ ∑ j, B j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (B j)
  have hsum : ∑ j, v j ^ 2 =
      (∑ j, B j ^ 2) ^ 2 * ∑ j, q j ^ 2 - (∑ j, B j ^ 2) * (B ⬝ᵥ q) ^ 2 := by
    simp only [hv, Fin.sum_univ_three, dotProduct]
    ring
  have hle : v i ^ 2 ≤ ∑ j, v j ^ 2 :=
    Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg (v j))
      (Finset.mem_univ i)
  have h1 : (∑ j, B j ^ 2) * (B ⬝ᵥ q) ^ 2 ≥ 0 := mul_nonneg hB (sq_nonneg _)
  have h2 : (∑ j, B j ^ 2) ^ 2 * ∑ j, q j ^ 2 ≤ (∑ j, B j ^ 2) ^ 2 * R ^ 2 :=
    mul_le_mul_of_nonneg_left hq (sq_nonneg _)
  refine abs_le_of_sq_le_sq ?_ (mul_nonneg hB hR0)
  change v i ^ 2 ≤ _
  nlinarith

omit [DecidableEq ι] in
/-- The force of the term of the second order is at most `c |B|² R` in the sup norm where every
particle is within the distance `R` of the origin, for a constant `c ≥ |eₐ² / 4mₐ|`. -/
theorem norm_diamagneticField_le {m e : ι → ℝ} (B : Fin 3 → ℝ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ a, |e a ^ 2 / (4 * m a)| ≤ c) {R : ℝ} (hR0 : 0 ≤ R)
    {z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ} (hz : ∀ a, ∑ i, z (Sum.inl (a, i)) ^ 2 ≤ R ^ 2) :
    ‖diamagneticField m e B z‖ ≤ c * (∑ i, B i ^ 2) * R := by
  have hB : 0 ≤ ∑ j, B j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (B j)
  have hC : 0 ≤ c * (∑ i, B i ^ 2) * R := by positivity
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun k => ?_
  rcases k with k | k
  · simpa [diamagneticField] using hC
  · rw [Real.norm_eq_abs, diamagneticField, abs_mul, abs_neg]
    calc |e k.1 ^ 2 / (4 * m k.1)| *
          |(∑ j, B j ^ 2) * realQ z k.1 k.2 - (B ⬝ᵥ realQ z k.1) * B k.2|
        ≤ c * ((∑ j, B j ^ 2) * R) :=
          mul_le_mul (hc k.1) (abs_diamagnetic_le hR0 (hz k.1) k.2) (abs_nonneg _) hc0
      _ = c * (∑ i, B i ^ 2) * R := by ring

omit [Fintype ι] [DecidableEq ι] in
/-- The field of the term of the second order is linear, hence continuous. -/
theorem continuous_diamagneticField (m e : ι → ℝ) (B : Fin 3 → ℝ) :
    Continuous (diamagneticField m e B) := by
  refine continuous_pi fun c => ?_
  rcases c with k | k
  · exact continuous_const
  · simp only [diamagneticField, realQ, dotProduct]
    fun_prop

omit [DecidableEq ι] in
/-- Larmor's theorem with an error bound. Let the particles have the masses `mₐ` and the
charges `eₐ` with one ratio `eₐ / mₐ = γ`, and let `c ≥ |eₐ² / 4mₐ|` for every particle. Let `z`
solve the equations of motion in the uniform field `B`, and `Z` those in the frame rotating with
the Larmor frequency `γ B / 2` without the field, on `[0, L]`, from the same point. Let both stay
in a set `s` on which the rotating field is Lipschitz with the constant `K`, and on which every
particle is within the Euclidean distance `R` of the origin. Then, in the sup norm of the phase
space, `‖z(t) − Z(t)‖ ≤ c |B|² R t e^{K t}`. The force `f` is arbitrary, so that a Coulomb
potential is admitted on a set that avoids the collisions. -/
theorem norm_sub_le_larmor {m e : ι → ℝ} {γ : ℝ} (he : ∀ a, e a / m a = γ) (B : Fin 3 → ℝ)
    {c : ℝ} (hc0 : 0 ≤ c) (hc : ∀ a, |e a ^ 2 / (4 * m a)| ≤ c)
    {f : (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ} {K : ℝ≥0} {s : Set (ι × Fin 3 ⊕ ι × Fin 3 → ℝ)}
    (hF : LipschitzOnWith K (rotatingField m (ratioLarmorFrequency γ B) f) s) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ x ∈ s, ∀ a, ∑ i, x (Sum.inl (a, i)) ^ 2 ≤ R ^ 2)
    {z Z : ℝ → ι × Fin 3 ⊕ ι × Fin 3 → ℝ} {L : ℝ}
    (hz : ∀ t ∈ Icc 0 L, HasDerivAt z (larmorField m e B f (z t)) t)
    (hZ : ∀ t ∈ Icc 0 L, HasDerivAt Z (rotatingField m (ratioLarmorFrequency γ B) f (Z t)) t)
    (hzs : ∀ t ∈ Icc 0 L, z t ∈ s) (hZs : ∀ t ∈ Icc 0 L, Z t ∈ s) (h0 : z 0 = Z 0) :
    ∀ t ∈ Icc 0 L, ‖z t - Z t‖ ≤ c * (∑ i, B i ^ 2) * R * t * Real.exp (K * t) := by
  intro t ht
  set C := c * (∑ i, B i ^ 2) * R
  have hB : 0 ≤ ∑ j, B j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (B j)
  have hC : 0 ≤ C := by positivity
  have hsub : Icc 0 t ⊆ Icc 0 L := Icc_subset_Icc_right ht.2
  have hr : ContinuousOn (fun u => diamagneticField m e B (z u)) (Icc 0 t) :=
    (continuous_diamagneticField m e B).comp_continuousOn
      fun u hu => (hz u (hsub hu)).continuousAt.continuousWithinAt
  have hδ : ∀ u ∈ Icc 0 t, ‖∫ v in 0..u, diamagneticField m e B (z v)‖ ≤ C * t := by
    intro u hu
    have hbound : ∀ v ∈ Ι 0 u, ‖diamagneticField m e B (z v)‖ ≤ C := by
      intro v hv
      rw [uIoc_of_le hu.1] at hv
      exact norm_diamagneticField_le B hc0 hc hR0
        (hR _ (hzs v (hsub ⟨hv.1.le, hv.2.trans hu.2⟩)))
    refine (intervalIntegral.norm_integral_le_of_norm_le_const hbound).trans ?_
    rw [sub_zero, abs_of_nonneg hu.1]
    exact mul_le_mul_of_nonneg_left hu.2 hC
  exact SmoothGeometry.Averaging.norm_sub_le_of_norm_integral_le' hF hr
    (fun u hu => by rw [← larmorField_eq he]; exact hz u (hsub hu))
    (fun u hu => hZ u (hsub hu)) (fun u hu => hzs u (hsub hu)) (fun u hu => hZs u (hsub hu))
    hδ h0 t ⟨ht.1, le_rfl⟩

omit [DecidableEq ι] in
/-- Larmor's theorem with an error bound for particles of one charge `e` and one mass `m > 0`:
`‖z(t) − Z(t)‖ ≤ (e² |B|² R / 4m) t e^{K t}`, with the Larmor frequency `Ω_L = e B / 2m`. -/
theorem norm_sub_le_larmor_const {m : ℝ} (hm : 0 < m) (e : ℝ) (B : Fin 3 → ℝ)
    {f : (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ} {K : ℝ≥0} {s : Set (ι × Fin 3 ⊕ ι × Fin 3 → ℝ)}
    (hF : LipschitzOnWith K (rotatingField (fun _ => m) (larmorFrequency e m B) f) s) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ x ∈ s, ∀ a, ∑ i, x (Sum.inl (a, i)) ^ 2 ≤ R ^ 2)
    {z Z : ℝ → ι × Fin 3 ⊕ ι × Fin 3 → ℝ} {L : ℝ}
    (hz : ∀ t ∈ Icc 0 L, HasDerivAt z (larmorField (fun _ => m) (fun _ => e) B f (z t)) t)
    (hZ : ∀ t ∈ Icc 0 L,
      HasDerivAt Z (rotatingField (fun _ => m) (larmorFrequency e m B) f (Z t)) t)
    (hzs : ∀ t ∈ Icc 0 L, z t ∈ s) (hZs : ∀ t ∈ Icc 0 L, Z t ∈ s) (h0 : z 0 = Z 0) :
    ∀ t ∈ Icc 0 L,
      ‖z t - Z t‖ ≤ e ^ 2 * (∑ i, B i ^ 2) * R / (4 * m) * t * Real.exp (K * t) := by
  intro t ht
  have hc : 0 ≤ e ^ 2 / (4 * m) := by positivity
  rw [larmorFrequency_eq_ratio] at hF hZ
  have h := norm_sub_le_larmor (m := fun _ => m) (e := fun _ => e) (fun _ => rfl) B hc
    (fun _ => (abs_of_nonneg hc).le) hF hR0 hR hz hZ hzs hZs h0 t ht
  calc ‖z t - Z t‖ ≤ e ^ 2 / (4 * m) * (∑ i, B i ^ 2) * R * t * Real.exp (K * t) := h
    _ = e ^ 2 * (∑ i, B i ^ 2) * R / (4 * m) * t * Real.exp (K * t) := by ring

/-! ### Hamilton's equations of the systems -/

/-- The generators of the particle `a`: `qᵢ ↦ q₍ₐ,ᵢ₎`, `pᵢ ↦ p₍ₐ,ᵢ₎`. -/
def particleGenerator (a : ι) : Fin 3 ⊕ Fin 3 → PhaseSpace (ι × Fin 3)
  | Sum.inl i => PhaseSpace.q (a, i)
  | Sum.inr i => PhaseSpace.p (a, i)

/-- A function on the phase space of one particle as the same function of the particle `a`. -/
def particleMap (a : ι) : SmoothRingHom AngularMomentum.Space (PhaseSpace (ι × Fin 3)) :=
  FreeSmoothRing.lift (particleGenerator a)

/-- The point of the phase space of one particle that the particle `a` occupies. -/
def particlePoint (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (a : ι) : Fin 3 ⊕ Fin 3 → ℝ
  | Sum.inl i => z (Sum.inl (a, i))
  | Sum.inr i => z (Sum.inr (a, i))

omit [Fintype ι] [DecidableEq ι] in
/-- The value of a function of the particle `a` is the value at the point of the particle. -/
theorem val_particleMap (a : ι) (s : AngularMomentum.Space) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) :
    (particleMap a s).val z = s.val (particlePoint z a) := by
  have h : (fun k => FreeSmoothRing.lift z (particleGenerator a k)) = particlePoint z a := by
    funext k
    rcases k with i | i <;> simp [particleGenerator, particlePoint, PhaseSpace.q, PhaseSpace.p]
  rw [← lift_real, particleMap, map_lift, h, lift_real]

omit [Fintype ι] in
/-- A function of the particle `a` depends on the momenta of no other particle. -/
theorem partialDerivation_inr_particleMap (a b : ι) (j : Fin 3) (s : AngularMomentum.Space) :
    partialDerivation (Sum.inr (b, j)) (particleMap a s) =
      if a = b then particleMap a (partialDerivation (Sum.inr j) s) else 0 := by
  rw [particleMap, derivation_lift_mul, Fintype.sum_sum_type]
  split_ifs with hab
  · subst hab
    rw [Finset.sum_eq_zero, zero_add, Finset.sum_eq_single j]
    · simp [particleGenerator, PhaseSpace.p]
    · intro i _ hij
      simp [particleGenerator, PhaseSpace.p, partialDerivation_generator, hij]
    · simp
    · intro i _
      simp [particleGenerator, PhaseSpace.q, partialDerivation_generator]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro i _
      simp [particleGenerator, PhaseSpace.p, partialDerivation_generator, hab]
    · intro i _
      simp [particleGenerator, PhaseSpace.q, partialDerivation_generator]

omit [Fintype ι] in
/-- A function of the particle `a` depends on the positions of no other particle. -/
theorem partialDerivation_inl_particleMap (a b : ι) (j : Fin 3) (s : AngularMomentum.Space) :
    partialDerivation (Sum.inl (b, j)) (particleMap a s) =
      if a = b then particleMap a (partialDerivation (Sum.inl j) s) else 0 := by
  rw [particleMap, derivation_lift_mul, Fintype.sum_sum_type]
  split_ifs with hab
  · subst hab
    rw [Finset.sum_eq_zero (s := Finset.univ) (f := fun i : Fin 3 => _ * partialDerivation _
      (particleGenerator a (Sum.inr i))), add_zero, Finset.sum_eq_single j]
    · simp [particleGenerator, PhaseSpace.q]
    · intro i _ hij
      simp [particleGenerator, PhaseSpace.q, partialDerivation_generator, hij]
    · simp
    · intro i _
      simp [particleGenerator, PhaseSpace.p, partialDerivation_generator]
  · rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
    · intro i _
      simp [particleGenerator, PhaseSpace.p, partialDerivation_generator]
    · intro i _
      simp [particleGenerator, PhaseSpace.q, partialDerivation_generator, hab]

omit [DecidableEq ι] in
/-- The rotating Hamiltonian of the system is the sum of the rotating Hamiltonians of the
particles, plus the potential. -/
theorem rotatingHamiltonian_eq_sum (m : ι → ℝ) (U : PhaseSpace (ι × Fin 3)) (Ω : Fin 3 → ℝ) :
    rotatingHamiltonian m U Ω =
      ∑ a, particleMap a (RotatingFrame.hamiltonian (m a) 0 Ω) + U := by
  have h : ∀ a : ι, particleMap a (RotatingFrame.hamiltonian (m a) 0 Ω) =
      algebraMap ℝ (PhaseSpace (ι × Fin 3)) ((m a)⁻¹ / 2) * ∑ i, particleP a i ^ 2 -
        constVector ι Ω ⬝ᵥ (particleQ a ⨯₃ particleP a) := by
    intro a
    simp only [RotatingFrame.hamiltonian, Galilei.freeHamiltonian, AngularMomentum.M, dotProduct,
      Fin.sum_univ_three, cross_apply, RotatingFrame.angularVelocity, constVector, particleQ,
      particleP, AngularMomentum.q, AngularMomentum.p, PhaseSpace.q, PhaseSpace.p, particleMap,
      particleGenerator, SmoothRingHom.map_add, SmoothRingHom.map_sub, SmoothRingHom.map_mul,
      SmoothRingHom.map_algebraMap, SmoothRingHom.map_zero, lift_generator, sq,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    ring
  rw [rotatingHamiltonian, totalAngularMomentum, dotProduct_sum,
    Finset.sum_congr rfl fun a _ => h a, Finset.sum_sub_distrib]
  ring

omit [DecidableEq ι] in
/-- The Hamiltonian of the system in the field is the sum of the Hamiltonians of the particles,
plus the potential. -/
theorem systemHamiltonian_eq_sum (m e : ι → ℝ) (U : PhaseSpace (ι × Fin 3)) (B : Fin 3 → ℝ) :
    systemHamiltonian m e U B = ∑ a, particleMap a (hamiltonian (m a) (e a) 0 B) + U := by
  have h : ∀ a : ι, particleMap a (hamiltonian (m a) (e a) 0 B) =
      algebraMap ℝ (PhaseSpace (ι × Fin 3)) ((m a)⁻¹ / 2) *
        ∑ i, particleKineticMomentum (e a) B a i ^ 2 := by
    intro a
    simp only [hamiltonian, ChargedParticle.kineticMomentum, ofPosition_symmetricGauge,
      particleKineticMomentum, particleGauge_eq, Fin.sum_univ_three, cross_apply,
      RotatingFrame.angularVelocity, constVector, particleQ, particleP, AngularMomentum.q,
      PhaseSpace.q, PhaseSpace.p, particleMap, particleGenerator, SmoothRingHom.map_add,
      SmoothRingHom.map_sub, SmoothRingHom.map_mul, SmoothRingHom.map_algebraMap,
      lift_generator, sq, add_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  rw [systemHamiltonian, Finset.sum_congr rfl fun a _ => (h a).symm]

omit [Fintype ι] [DecidableEq ι] in
/-- The value of a function of the positions is its value at the positions. -/
theorem val_ofPosition (V : FreeSmoothRing (ι × Fin 3)) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) :
    (PhaseSpace.ofPosition (ι × Fin 3) V).val z = V.val (realPositions z) := by
  rw [← lift_real, PhaseSpace.lift_ofPosition, lift_real]
  rfl

/-- Hamilton's equation of a position: functions `hₐ` of the particles and a function of the
positions move the particle `b` with the field of its own Hamiltonian `h_b`. -/
theorem hamiltonianField_sum_particleMap_inl (h : ι → AngularMomentum.Space)
    (V : FreeSmoothRing (ι × Fin 3)) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (b : ι) (j : Fin 3) :
    hamiltonianField (∑ a, particleMap a (h a) + PhaseSpace.ofPosition (ι × Fin 3) V) z
        (Sum.inl (b, j)) =
      hamiltonianField (h b) (particlePoint z b) (Sum.inl j) := by
  rw [hamiltonianField_inl, hamiltonianField_inl, map_add, map_sum,
    PhaseSpace.partialDerivation_inr_ofPosition, add_zero]
  simp only [partialDerivation_inr_particleMap, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  exact val_particleMap b _ z

/-- Hamilton's equation of a momentum: the potential adds the force `−∂V/∂q₍b,j₎`. -/
theorem hamiltonianField_sum_particleMap_inr (h : ι → AngularMomentum.Space)
    (V : FreeSmoothRing (ι × Fin 3)) (z : ι × Fin 3 ⊕ ι × Fin 3 → ℝ) (b : ι) (j : Fin 3) :
    hamiltonianField (∑ a, particleMap a (h a) + PhaseSpace.ofPosition (ι × Fin 3) V) z
        (Sum.inr (b, j)) =
      hamiltonianField (h b) (particlePoint z b) (Sum.inr j) -
        (partialDerivation (b, j) V).val (realPositions z) := by
  have hadd (x y : PhaseSpace (ι × Fin 3)) : (x + y).val z = x.val z + y.val z := by
    rw [← lift_real, SmoothRingHom.map_add, lift_real, lift_real]
  rw [hamiltonianField_inr, hamiltonianField_inr, map_add, map_sum,
    PhaseSpace.partialDerivation_inl_ofPosition]
  simp only [partialDerivation_inl_particleMap, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hadd, val_particleMap, val_ofPosition]
  ring

/-- The field of the rotating Hamiltonian with a potential `V` of the positions is
`rotatingField` with the force `−∇V`. -/
theorem hamiltonianField_rotatingHamiltonian (m : ι → ℝ) (V : FreeSmoothRing (ι × Fin 3))
    (Ω : Fin 3 → ℝ) :
    hamiltonianField (rotatingHamiltonian m (PhaseSpace.ofPosition (ι × Fin 3) V) Ω) =
      rotatingField m Ω (fun x k => -(partialDerivation k V).val x) := by
  funext z c
  rw [rotatingHamiltonian_eq_sum]
  rcases c with ⟨b, j⟩ | ⟨b, j⟩
  · rw [hamiltonianField_sum_particleMap_inl (fun a => RotatingFrame.hamiltonian (m a) 0 Ω),
      hamiltonianField_rotatingFrame_inl]
    rfl
  · have hp : (fun i => particlePoint z b (Sum.inr i)) = realP z b := rfl
    rw [hamiltonianField_sum_particleMap_inr (fun a => RotatingFrame.hamiltonian (m a) 0 Ω),
      hamiltonianField_rotatingFrame_inr, hp]
    simp only [rotatingField]
    ring

/-- The field of the Hamiltonian of the system in the field `B` with a potential `V` of the
positions is `larmorField` with the force `−∇V`. -/
theorem hamiltonianField_systemHamiltonian (m e : ι → ℝ) (V : FreeSmoothRing (ι × Fin 3))
    (B : Fin 3 → ℝ) :
    hamiltonianField (systemHamiltonian m e (PhaseSpace.ofPosition (ι × Fin 3) V) B) =
      larmorField m e B (fun x k => -(partialDerivation k V).val x) := by
  funext z c
  rw [systemHamiltonian_eq_sum]
  rcases c with ⟨b, j⟩ | ⟨b, j⟩
  · rw [hamiltonianField_sum_particleMap_inl (fun a => hamiltonian (m a) (e a) 0 B),
      hamiltonianField_hamiltonian_inl]
    rfl
  · have hπ : (fun i => particlePoint z b (Sum.inr i) -
        e b / 2 * (B ⨯₃ fun i => particlePoint z b (Sum.inl i)) i) =
        realKineticMomentum (e b) B z b := rfl
    rw [hamiltonianField_sum_particleMap_inr (fun a => hamiltonian (m a) (e a) 0 B),
      hamiltonianField_hamiltonian_inr, hπ]
    simp only [larmorField]
    ring

/-- Larmor's theorem with an error bound for a potential `V` that is a smooth function of the
positions everywhere: `norm_sub_le_larmor` for trajectories of `systemHamiltonian` and of
`rotatingHamiltonian`. -/
theorem norm_sub_le_larmor_of_hamiltonianField {m e : ι → ℝ} {γ : ℝ}
    (he : ∀ a, e a / m a = γ) (B : Fin 3 → ℝ) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ a, |e a ^ 2 / (4 * m a)| ≤ c) (V : FreeSmoothRing (ι × Fin 3)) {K : ℝ≥0}
    {s : Set (ι × Fin 3 ⊕ ι × Fin 3 → ℝ)}
    (hF : LipschitzOnWith K (hamiltonianField (rotatingHamiltonian m
      (PhaseSpace.ofPosition (ι × Fin 3) V) (ratioLarmorFrequency γ B))) s)
    {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ x ∈ s, ∀ a, ∑ i, x (Sum.inl (a, i)) ^ 2 ≤ R ^ 2)
    {z Z : ℝ → ι × Fin 3 ⊕ ι × Fin 3 → ℝ} {L : ℝ}
    (hz : ∀ t ∈ Icc 0 L, HasDerivAt z (hamiltonianField
      (systemHamiltonian m e (PhaseSpace.ofPosition (ι × Fin 3) V) B) (z t)) t)
    (hZ : ∀ t ∈ Icc 0 L, HasDerivAt Z (hamiltonianField (rotatingHamiltonian m
      (PhaseSpace.ofPosition (ι × Fin 3) V) (ratioLarmorFrequency γ B)) (Z t)) t)
    (hzs : ∀ t ∈ Icc 0 L, z t ∈ s) (hZs : ∀ t ∈ Icc 0 L, Z t ∈ s) (h0 : z 0 = Z 0) :
    ∀ t ∈ Icc 0 L, ‖z t - Z t‖ ≤ c * (∑ i, B i ^ 2) * R * t * Real.exp (K * t) := by
  rw [hamiltonianField_rotatingHamiltonian] at hF hZ
  rw [hamiltonianField_systemHamiltonian] at hz
  exact norm_sub_le_larmor he B hc0 hc hF hR0 hR hz hZ hzs hZs h0

end System

/-! ### An instance: the isotropic oscillator -/

/-- The force `−k x` of the isotropic oscillator potential `U = k |x|² / 2`. The index type is
explicit, since no argument determines it. -/
def oscillatorForce (ι : Type*) (k : ℝ) : (ι × Fin 3 → ℝ) → ι × Fin 3 → ℝ :=
  fun x j => -(k * x j)

/-- The planar orbit `q = cos (wt) (cos 4t, −sin 4t, 0)`, `p = −w sin (wt) (cos 4t, −sin 4t, 0)`
of one particle: an oscillation of the frequency `w` in a frame turning with the angular velocity
`−4` about the third axis. -/
def exampleOrbit (w t : ℝ) : Unit × Fin 3 ⊕ Unit × Fin 3 → ℝ
  | Sum.inl k => ![Real.cos (w * t) * Real.cos (4 * t), -(Real.cos (w * t) * Real.sin (4 * t)),
      0] k.2
  | Sum.inr k => ![-(w * Real.sin (w * t) * Real.cos (4 * t)),
      w * Real.sin (w * t) * Real.sin (4 * t), 0] k.2

/-- The velocity of `exampleOrbit w` in the phase space. -/
def exampleVelocity (w t : ℝ) : Unit × Fin 3 ⊕ Unit × Fin 3 → ℝ
  | Sum.inl k => ![-(w * Real.sin (w * t) * Real.cos (4 * t)) -
        4 * (Real.cos (w * t) * Real.sin (4 * t)),
      w * Real.sin (w * t) * Real.sin (4 * t) - 4 * (Real.cos (w * t) * Real.cos (4 * t)), 0] k.2
  | Sum.inr k => ![-(w ^ 2 * Real.cos (w * t) * Real.cos (4 * t)) +
        4 * w * Real.sin (w * t) * Real.sin (4 * t),
      w ^ 2 * Real.cos (w * t) * Real.sin (4 * t) + 4 * w * Real.sin (w * t) * Real.cos (4 * t),
      0] k.2

/-- The velocity of `exampleOrbit w` is `exampleVelocity w`. -/
theorem hasDerivAt_exampleOrbit (w t : ℝ) :
    HasDerivAt (exampleOrbit w) (exampleVelocity w t) t := by
  have hc (a : ℝ) : HasDerivAt (fun t => Real.cos (a * t)) (-(Real.sin (a * t) * a)) t := by
    have h := ((hasDerivAt_id t).const_mul a).cos
    simp only [id, mul_one] at h
    exact h.congr_deriv (by ring)
  have hs (a : ℝ) : HasDerivAt (fun t => Real.sin (a * t)) (Real.cos (a * t) * a) t := by
    have h := ((hasDerivAt_id t).const_mul a).sin
    simp only [id, mul_one] at h
    exact h
  rw [hasDerivAt_pi]
  rintro (⟨⟨⟩, i⟩ | ⟨⟨⟩, i⟩) <;> fin_cases i <;>
    simp only [exampleOrbit, exampleVelocity, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
  · exact ((hc w).mul (hc 4)).congr_deriv (by ring)
  · exact ((hc w).mul (hs 4)).neg.congr_deriv (by ring)
  · exact hasDerivAt_const t 0
  · exact (((hs w).const_mul w).mul (hc 4)).neg.congr_deriv (by ring)
  · exact (((hs w).const_mul w).mul (hs 4)).congr_deriv (by ring)
  · exact hasDerivAt_const t 0

/-- With `m = 1`, `e = 2` and `B = (0, 0, 4)`, the Larmor frequency is `Ω_L = (0, 0, 4)`; for
`U = 9 |x|² / 2`, `exampleOrbit 3` solves the equations of motion in the rotating frame. -/
theorem hasDerivAt_exampleOrbit_rotating (t : ℝ) :
    HasDerivAt (exampleOrbit 3)
      (rotatingField (fun _ => 1) (ratioLarmorFrequency 2 ![0, 0, 4]) (oscillatorForce Unit 9)
        (exampleOrbit 3 t)) t := by
  convert hasDerivAt_exampleOrbit 3 t using 1
  funext c
  rcases c with ⟨⟨⟩, i⟩ | ⟨⟨⟩, i⟩ <;> fin_cases i <;>
    simp [rotatingField, exampleOrbit, exampleVelocity, oscillatorForce, realQ, realP,
      realPositions, ratioLarmorFrequency, cross_apply] <;>
    ring

/-- For the same data, `exampleOrbit 5` solves the equations of motion in the field `B`: the
term of the second order adds `m Ω_L² = 16` to the spring constant across the field. -/
theorem hasDerivAt_exampleOrbit_larmor (t : ℝ) :
    HasDerivAt (exampleOrbit 5)
      (larmorField (fun _ => 1) (fun _ => 2) ![0, 0, 4] (oscillatorForce Unit 9)
        (exampleOrbit 5 t)) t := by
  convert hasDerivAt_exampleOrbit 5 t using 1
  funext c
  rcases c with ⟨⟨⟩, i⟩ | ⟨⟨⟩, i⟩ <;> fin_cases i <;>
    simp [larmorField, exampleOrbit, exampleVelocity, oscillatorForce, realQ, realPositions,
      realKineticMomentum, cross_apply] <;>
    ring

/-- The rotating field of the example is Lipschitz with the constant `13` in the sup norm. -/
theorem lipschitzWith_rotatingField_example :
    LipschitzWith 13
      (rotatingField (fun _ => 1) (ratioLarmorFrequency 2 ![0, 0, 4])
        (oscillatorForce Unit 9)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have hn : 0 ≤ ‖x - y‖ := norm_nonneg _
  have hcomp (c : Unit × Fin 3 ⊕ Unit × Fin 3) : -‖x - y‖ ≤ x c - y c ∧ x c - y c ≤ ‖x - y‖ := by
    have h := norm_le_pi_norm (x - y) c
    rw [Pi.sub_apply, Real.norm_eq_abs] at h
    exact abs_le.mp h
  have h1 := hcomp (Sum.inl ((), 0))
  have h2 := hcomp (Sum.inl ((), 1))
  have h3 := hcomp (Sum.inl ((), 2))
  have h4 := hcomp (Sum.inr ((), 0))
  have h5 := hcomp (Sum.inr ((), 1))
  have h6 := hcomp (Sum.inr ((), 2))
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun c => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  rcases c with ⟨⟨⟩, i⟩ | ⟨⟨⟩, i⟩ <;> fin_cases i <;>
    simp [rotatingField, oscillatorForce, realQ, realP, realPositions, ratioLarmorFrequency,
      cross_apply] <;>
    constructor <;> linarith

/-- In the example the orbits in the field and in the rotating frame differ by at most
`16 t e^{13 t}`: the bound of `norm_sub_le_larmor` with `e² |B|² R / 4m = 16`, `R = 1` and
`K = 13`. The two orbits are different: their frequencies are `5` and `3`. -/
theorem norm_exampleOrbit_sub_le {t : ℝ} (ht : 0 ≤ t) :
    ‖exampleOrbit 5 t - exampleOrbit 3 t‖ ≤ 16 * t * Real.exp (13 * t) := by
  let s : Set (Unit × Fin 3 ⊕ Unit × Fin 3 → ℝ) :=
    {x | ∀ a, ∑ i, x (Sum.inl (a, i)) ^ 2 ≤ 1 ^ 2}
  have hs (w u : ℝ) : exampleOrbit w u ∈ s := by
    intro a
    have h := Real.cos_sq_add_sin_sq (4 * u)
    have hw := Real.cos_sq_le_one (w * u)
    simp only [Fin.sum_univ_three, exampleOrbit, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    nlinarith [sq_nonneg (Real.cos (w * u)), sq_nonneg (Real.sin (4 * u))]
  have h0 : exampleOrbit 5 0 = exampleOrbit 3 0 := by
    funext c
    rcases c with ⟨⟨⟩, i⟩ | ⟨⟨⟩, i⟩ <;> fin_cases i <;> simp [exampleOrbit]
  have h := norm_sub_le_larmor (ι := Unit) (m := fun _ => 1) (e := fun _ => 2) (γ := 2)
    (fun _ => by norm_num) ![0, 0, 4] (c := 1) zero_le_one (fun _ => by norm_num)
    (f := oscillatorForce Unit 9) (s := s) lipschitzWith_rotatingField_example.lipschitzOnWith
    zero_le_one (fun x hx => hx) (L := t) (fun u _ => hasDerivAt_exampleOrbit_larmor u)
    (fun u _ => hasDerivAt_exampleOrbit_rotating u) (fun u _ => hs 5 u) (fun u _ => hs 3 u)
    h0 t ⟨ht, le_rfl⟩
  convert h using 2
  · norm_num [Fin.sum_univ_three]
  · norm_num

end ProjectAinos.Electrodynamics.Larmor
