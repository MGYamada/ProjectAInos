/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothAlgebra.Poisson.Free
public import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The free rigid body as a Lie–Poisson system

The phase space of the free rigid body is the free C-infinity ring on the three
components `L₀, L₁, L₂` of the angular momentum in the body frame, with
`{Lᵢ, Lⱼ} = −εᵢⱼₖ Lₖ` (Landau–Lifshitz §§34, 36). The Jacobi identity is checked
on generators. For the Hamiltonian `H = Σᵢ Lᵢ² / 2Iᵢ` the equations of motion
`{Lᵢ, H}` are Euler's equations, and `|L|²` is a Casimir: its bracket with every
element vanishes, so it is an integral of every Hamiltonian.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.RigidBody

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

/-- The phase space of the free rigid body: smooth functions of the angular
momentum in the body frame. -/
abbrev PhaseSpace := FreeSmoothRing (Fin 3)

/-- The `i`-th component of the angular momentum in the body frame. -/
def L (i : Fin 3) : PhaseSpace := generator i

/-- The brackets of the generators, `{Lᵢ, Lⱼ} = −εᵢⱼₖ Lₖ`. -/
def structureMatrix : Fin 3 → Fin 3 → PhaseSpace :=
  ![![0, -L 2, L 1], ![L 2, 0, -L 0], ![-L 1, L 0, 0]]

theorem structureMatrix_skew (a b : Fin 3) : structureMatrix a b = -structureMatrix b a := by
  fin_cases a <;> fin_cases b <;> simp [structureMatrix]

/-- The almost-Poisson structure of the rigid body, before the Jacobi identity. -/
def almostPoisson : AlmostPoissonStructure PhaseSpace :=
  FreeSmoothRing.almostPoisson structureMatrix structureMatrix_skew

theorem almostPoisson_L_L (a b : Fin 3) :
    almostPoisson.bracket (L a) (L b) = structureMatrix a b :=
  almostPoisson_bracket_generator structureMatrix structureMatrix_skew a b

/-- The Lie–Poisson structure of the rigid body. -/
def poisson : PoissonStructure PhaseSpace :=
  poissonOfCoordinates structureMatrix structureMatrix_skew fun a b c => by
    change almostPoisson.bracket (structureMatrix a b) (L c) +
      almostPoisson.bracket (structureMatrix b c) (L a) +
      almostPoisson.bracket (structureMatrix c a) (L b) = 0
    fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp [structureMatrix, AlmostPoissonStructure.bracket_neg_left, almostPoisson_L_L]

theorem poisson_bracket_eq_sum (f g : PhaseSpace) :
    poisson.bracket f g =
      ∑ a, ∑ b, partialDerivation a f * partialDerivation b g * structureMatrix a b := rfl

theorem poisson_L_L (a b : Fin 3) : poisson.bracket (L a) (L b) = structureMatrix a b :=
  almostPoisson_L_L a b

/-- `{L₀, L₁} = −L₂`. -/
theorem poisson_L_zero_L_one : poisson.bracket (L 0) (L 1) = -L 2 := poisson_L_L 0 1

/-- `{L₁, L₂} = −L₀`. -/
theorem poisson_L_one_L_two : poisson.bracket (L 1) (L 2) = -L 0 := poisson_L_L 1 2

/-- `{L₂, L₀} = −L₁`. -/
theorem poisson_L_two_L_zero : poisson.bracket (L 2) (L 0) = -L 1 := poisson_L_L 2 0

/-- The generators are not zero, as evaluation at the point `(1, 1, 1)` shows. -/
theorem L_ne_zero (i : Fin 3) : L i ≠ 0 := by
  intro h
  have h1 : FreeSmoothRing.lift (fun _ : Fin 3 => (1 : ℝ)) (L i) = 1 := lift_generator _ i
  rw [h, SmoothRingHom.map_zero] at h1
  exact zero_ne_one h1

/-- The bracket is not zero. -/
theorem poisson_L_zero_L_one_ne_zero : poisson.bracket (L 0) (L 1) ≠ 0 := by
  rw [poisson_L_zero_L_one]
  exact neg_ne_zero.mpr (L_ne_zero 2)

/-- The gradient of an observable, `(∂f/∂L₀, ∂f/∂L₁, ∂f/∂L₂)`. -/
def gradient (f : PhaseSpace) : Fin 3 → PhaseSpace := fun a => partialDerivation a f

/-- The bracket in vector form: `{f, g} = −L · (∇f × ∇g)`. -/
theorem poisson_bracket (f g : PhaseSpace) :
    poisson.bracket f g = -(L ⬝ᵥ (gradient f ⨯₃ gradient g)) := by
  rw [poisson_bracket_eq_sum]
  simp only [Fin.sum_univ_three, structureMatrix, cross_apply, dotProduct, gradient,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val']
  ring

/-- The equation of motion of the angular momentum for any Hamiltonian:
`{Lₐ, H} = (L × ∇H)ₐ`. -/
theorem poisson_L_bracket (a : Fin 3) (H : PhaseSpace) :
    poisson.bracket (L a) H = (L ⨯₃ gradient H) a := by
  rw [poisson_bracket_eq_sum]
  simp only [Fin.sum_univ_three, structureMatrix, cross_apply, gradient,
    L, partialDerivation_generator]
  fin_cases a <;> simp <;> ring

theorem partialDerivation_L (c i : Fin 3) :
    partialDerivation c (L i) = if i = c then 1 else 0 :=
  partialDerivation_generator c i

theorem partialDerivation_L_sq (c i : Fin 3) :
    partialDerivation c (L i * L i) = if i = c then 2 * L i else 0 := by
  rw [SmoothDerivation.map_mul, partialDerivation_L]
  split_ifs
  · rw [smul_eq_mul, mul_one, two_mul]
  · rw [smul_zero, add_zero]

/-- The kinetic energy `Σᵢ Lᵢ² / 2Iᵢ` of a body with principal moments of inertia `Iᵢ`. -/
def kineticEnergy (I : Fin 3 → ℝ) : PhaseSpace :=
  ∑ i, algebraMap ℝ PhaseSpace ((I i)⁻¹ / 2) * (L i * L i)

/-- The angular velocity `Ωᵢ = Lᵢ / Iᵢ` in the body frame. -/
def angularVelocity (I : Fin 3 → ℝ) : Fin 3 → PhaseSpace :=
  fun i => algebraMap ℝ PhaseSpace (I i)⁻¹ * L i

/-- The angular velocity is the gradient of the kinetic energy. -/
theorem gradient_kineticEnergy (I : Fin 3 → ℝ) :
    gradient (kineticEnergy I) = angularVelocity I := by
  funext b
  have h2 : (2 : PhaseSpace) = algebraMap ℝ PhaseSpace 2 := (map_ofNat _ 2).symm
  have hb : (I b)⁻¹ / 2 * 2 = (I b)⁻¹ := by ring
  rw [gradient, kineticEnergy, map_sum, Finset.sum_eq_single b]
  · rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, partialDerivation_L_sq]
    simp only [↓reduceIte, smul_eq_mul, mul_zero, add_zero, angularVelocity]
    rw [h2, ← mul_assoc, ← map_mul, hb]
  · intro i _ hib
    rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, partialDerivation_L_sq]
    simp [hib]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- Euler's equations in vector form, `{Lₐ, H} = (L × Ω)ₐ` (Landau–Lifshitz §36). -/
theorem euler_equations (I : Fin 3 → ℝ) (a : Fin 3) :
    poisson.bracket (L a) (kineticEnergy I) = (L ⨯₃ angularVelocity I) a := by
  rw [poisson_L_bracket, gradient_kineticEnergy]

/-- Euler's equation for `L₀`: `{L₀, H} = (1/I₂ − 1/I₁) L₁ L₂`. -/
theorem euler_equation_zero (I : Fin 3 → ℝ) :
    poisson.bracket (L 0) (kineticEnergy I) =
      algebraMap ℝ PhaseSpace ((I 2)⁻¹ - (I 1)⁻¹) * (L 1 * L 2) := by
  rw [euler_equations, cross_apply]
  simp only [angularVelocity, Matrix.cons_val_zero, map_sub]
  ring

/-- Euler's equation for `L₁`: `{L₁, H} = (1/I₀ − 1/I₂) L₂ L₀`. -/
theorem euler_equation_one (I : Fin 3 → ℝ) :
    poisson.bracket (L 1) (kineticEnergy I) =
      algebraMap ℝ PhaseSpace ((I 0)⁻¹ - (I 2)⁻¹) * (L 2 * L 0) := by
  rw [euler_equations, cross_apply]
  simp only [angularVelocity, Matrix.cons_val_one, Matrix.cons_val_zero, map_sub]
  ring

/-- Euler's equation for `L₂`: `{L₂, H} = (1/I₁ − 1/I₀) L₀ L₁`. -/
theorem euler_equation_two (I : Fin 3 → ℝ) :
    poisson.bracket (L 2) (kineticEnergy I) =
      algebraMap ℝ PhaseSpace ((I 1)⁻¹ - (I 0)⁻¹) * (L 0 * L 1) := by
  rw [euler_equations, cross_apply]
  simp only [angularVelocity, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, map_sub]
  ring

/-- The kinetic energy is an integral of the motion. -/
theorem isIntegral_kineticEnergy (I : Fin 3 → ℝ) :
    poisson.IsIntegral (kineticEnergy I) (kineticEnergy I) :=
  poisson.isIntegral_self _

/-- The squared angular momentum `|L|²`. -/
def casimir : PhaseSpace := ∑ i, L i * L i

theorem gradient_casimir : gradient casimir = fun i => 2 * L i := by
  funext b
  simp only [gradient, casimir, map_sum, partialDerivation_L_sq, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

/-- `|L|²` is a Casimir: its bracket with every element vanishes. -/
theorem poisson_casimir_left (g : PhaseSpace) : poisson.bracket casimir g = 0 := by
  rw [poisson_bracket, gradient_casimir]
  simp only [Fin.sum_univ_three, cross_apply, dotProduct, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  ring

theorem poisson_casimir_right (f : PhaseSpace) : poisson.bracket f casimir = 0 := by
  rw [poisson.antisymm, poisson_casimir_left, neg_zero]

/-- `|L|²` is an integral of the motion for every Hamiltonian. -/
theorem isIntegral_casimir (H : PhaseSpace) : poisson.IsIntegral H casimir :=
  poisson_casimir_left H

end ProjectAInos.Mechanics.RigidBody
