/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Mechanics.Poisson.Epsilon
public import ProjectAInos.SmoothAlgebra.Poisson.Free
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# The heavy top as a Lie–Poisson system

A rigid body with a fixed point in a uniform field is described in the body
frame by its angular momentum `L` and the vertical unit vector `Γ`
(Landau–Lifshitz §§34–36). The phase space is the free C-infinity ring on the
six components, with

`{Lᵢ, Lⱼ} = −εᵢⱼₖ Lₖ`, `{Lᵢ, Γⱼ} = −εᵢⱼₖ Γₖ`, `{Γᵢ, Γⱼ} = 0`.

The Jacobi identity is checked on generators. For every Hamiltonian the
equations of motion are `{L, H} = L × ∇_L H + Γ × ∇_Γ H` and
`{Γ, H} = Γ × ∇_L H`. For `H = Σᵢ Lᵢ² / 2Iᵢ + k Γ · χ` they are
`L × Ω + k Γ × χ` and `Γ × Ω`. The elements `|Γ|²` and `L · Γ` are Casimirs.
-/

@[expose] public section

noncomputable section

namespace ProjectAInos.Mechanics.HeavyTop

open SmoothAlgebra SmoothRing FreeSmoothRing Matrix

/-- The phase space of the heavy top: smooth functions of the angular momentum
and of the vertical unit vector, both in the body frame. -/
abbrev PhaseSpace := FreeSmoothRing (Fin 3 ⊕ Fin 3)

/-- The angular momentum in the body frame. -/
def L (a : Fin 3) : PhaseSpace := generator (Sum.inl a)

/-- The vertical unit vector in the body frame. -/
def Γ (a : Fin 3) : PhaseSpace := generator (Sum.inr a)

/-- The brackets of the generators. -/
def structureMatrix : Fin 3 ⊕ Fin 3 → Fin 3 ⊕ Fin 3 → PhaseSpace
  | Sum.inl a, Sum.inl b => -epsilon L a b
  | Sum.inl a, Sum.inr b => -epsilon Γ a b
  | Sum.inr a, Sum.inl b => -epsilon Γ a b
  | Sum.inr _, Sum.inr _ => 0

theorem structureMatrix_skew (a b : Fin 3 ⊕ Fin 3) :
    structureMatrix a b = -structureMatrix b a := by
  rcases a with a | a <;> rcases b with b | b
  · exact congrArg Neg.neg (epsilon_skew L a b)
  · exact congrArg Neg.neg (epsilon_skew Γ a b)
  · exact congrArg Neg.neg (epsilon_skew Γ a b)
  · exact neg_zero.symm

/-- The almost-Poisson structure of the heavy top, before the Jacobi identity. -/
def almostPoisson : AlmostPoissonStructure PhaseSpace :=
  FreeSmoothRing.almostPoisson structureMatrix structureMatrix_skew

theorem almostPoisson_generator (a b : Fin 3 ⊕ Fin 3) :
    almostPoisson.bracket (generator a) (generator b) = structureMatrix a b :=
  almostPoisson_bracket_generator structureMatrix structureMatrix_skew a b

theorem almostPoisson_L (a : Fin 3) (b : Fin 3 ⊕ Fin 3) :
    almostPoisson.bracket (L a) (generator b) = structureMatrix (Sum.inl a) b :=
  almostPoisson_generator _ b

theorem almostPoisson_Γ (a : Fin 3) (b : Fin 3 ⊕ Fin 3) :
    almostPoisson.bracket (Γ a) (generator b) = structureMatrix (Sum.inr a) b :=
  almostPoisson_generator _ b

/-- The Lie–Poisson structure of the heavy top. -/
def poisson : PoissonStructure PhaseSpace :=
  poissonOfCoordinates structureMatrix structureMatrix_skew fun a b c => by
    change almostPoisson.bracket (structureMatrix a b) (generator c) +
      almostPoisson.bracket (structureMatrix b c) (generator a) +
      almostPoisson.bracket (structureMatrix c a) (generator b) = 0
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      fin_cases a <;> fin_cases b <;> fin_cases c <;>
      simp [structureMatrix, epsilon, AlmostPoissonStructure.bracket_neg_left, almostPoisson_L,
        almostPoisson_Γ]

theorem poisson_bracket_eq_sum (f g : PhaseSpace) :
    poisson.bracket f g =
      ∑ a, ∑ b, partialDerivation a f * partialDerivation b g * structureMatrix a b := rfl

theorem poisson_generator (a b : Fin 3 ⊕ Fin 3) :
    poisson.bracket (generator a) (generator b) = structureMatrix a b :=
  almostPoisson_generator a b

/-- `{Lₐ, L_b} = −εₐ_bc L_c`. -/
theorem poisson_L_L (a b : Fin 3) : poisson.bracket (L a) (L b) = -epsilon L a b :=
  poisson_generator _ _

/-- `{Lₐ, Γ_b} = −εₐ_bc Γ_c`. -/
theorem poisson_L_Γ (a b : Fin 3) : poisson.bracket (L a) (Γ b) = -epsilon Γ a b :=
  poisson_generator _ _

/-- `{Γₐ, Γ_b} = 0`. -/
theorem poisson_Γ_Γ (a b : Fin 3) : poisson.bracket (Γ a) (Γ b) = 0 :=
  poisson_generator _ _

/-- The gradient with respect to the angular momentum. -/
def gradL (f : PhaseSpace) : Fin 3 → PhaseSpace := fun a => partialDerivation (Sum.inl a) f

/-- The gradient with respect to the vertical vector. -/
def gradΓ (f : PhaseSpace) : Fin 3 → PhaseSpace := fun a => partialDerivation (Sum.inr a) f

/-- The equation of motion of the angular momentum for any Hamiltonian:
`{Lₐ, H} = (L × ∇_L H + Γ × ∇_Γ H)ₐ`. -/
theorem poisson_L_bracket (a : Fin 3) (H : PhaseSpace) :
    poisson.bracket (L a) H = (L ⨯₃ gradL H) a + (Γ ⨯₃ gradΓ H) a := by
  change (FreeSmoothRing.almostPoisson structureMatrix structureMatrix_skew).bracket
    (generator (Sum.inl a)) H = _
  rw [almostPoisson_bracket_generator_left, Fintype.sum_sum_type, Fin.sum_univ_three,
    Fin.sum_univ_three, cross_apply, cross_apply]
  fin_cases a <;> simp [structureMatrix, epsilon, gradL, gradΓ] <;> ring

/-- The equation of motion of the vertical vector for any Hamiltonian:
`{Γₐ, H} = (Γ × ∇_L H)ₐ`. -/
theorem poisson_Γ_bracket (a : Fin 3) (H : PhaseSpace) :
    poisson.bracket (Γ a) H = (Γ ⨯₃ gradL H) a := by
  change (FreeSmoothRing.almostPoisson structureMatrix structureMatrix_skew).bracket
    (generator (Sum.inr a)) H = _
  rw [almostPoisson_bracket_generator_left, Fintype.sum_sum_type, Fin.sum_univ_three,
    Fin.sum_univ_three, cross_apply]
  fin_cases a <;> simp [structureMatrix, epsilon, gradL] <;> ring

/-- The bracket in vector form:
`{f, g} = −L · (∇_L f × ∇_L g) − Γ · (∇_L f × ∇_Γ g + ∇_Γ f × ∇_L g)`. -/
theorem poisson_bracket (f g : PhaseSpace) :
    poisson.bracket f g =
      -(L ⬝ᵥ (gradL f ⨯₃ gradL g)) -
        Γ ⬝ᵥ (gradL f ⨯₃ gradΓ g + gradΓ f ⨯₃ gradL g) := by
  rw [poisson_bracket_eq_sum]
  simp only [Fintype.sum_sum_type, Fin.sum_univ_three, structureMatrix, epsilon, cross_apply,
    dotProduct, gradL, gradΓ, Pi.add_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val']
  ring

theorem partialDerivation_inl_L (c i : Fin 3) :
    partialDerivation (Sum.inl c) (L i) = if i = c then 1 else 0 := by
  rw [L, partialDerivation_generator]
  simp

theorem partialDerivation_inr_Γ (c i : Fin 3) :
    partialDerivation (Sum.inr c) (Γ i) = if i = c then 1 else 0 := by
  rw [Γ, partialDerivation_generator]
  simp

theorem partialDerivation_inl_Γ (c i : Fin 3) : partialDerivation (Sum.inl c) (Γ i) = 0 :=
  partialDerivation_generator_of_ne (by simp)

theorem partialDerivation_inr_L (c i : Fin 3) : partialDerivation (Sum.inr c) (L i) = 0 :=
  partialDerivation_generator_of_ne (by simp)

/-- The Hamiltonian `Σᵢ Lᵢ² / 2Iᵢ + k Γ · χ` of a top with principal moments of
inertia `Iᵢ`, weight `k` and centre of mass `χ` in the body frame. -/
def hamiltonian (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) : PhaseSpace :=
  ∑ i, algebraMap ℝ PhaseSpace ((I i)⁻¹ / 2) * (L i * L i) +
    ∑ i, algebraMap ℝ PhaseSpace (k * χ i) * Γ i

/-- The angular velocity `Ωᵢ = Lᵢ / Iᵢ` in the body frame. -/
def angularVelocity (I : Fin 3 → ℝ) : Fin 3 → PhaseSpace :=
  fun i => algebraMap ℝ PhaseSpace (I i)⁻¹ * L i

/-- The constant vector `k χ`. -/
def weight (k : ℝ) (χ : Fin 3 → ℝ) : Fin 3 → PhaseSpace :=
  fun i => algebraMap ℝ PhaseSpace (k * χ i)

theorem gradL_hamiltonian (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) :
    gradL (hamiltonian I k χ) = angularVelocity I := by
  funext b
  have h2 : (2 : PhaseSpace) = algebraMap ℝ PhaseSpace 2 := (map_ofNat _ 2).symm
  have hb : (I b)⁻¹ / 2 * 2 = (I b)⁻¹ := by ring
  have hsq (i : Fin 3) : partialDerivation (Sum.inl b) (L i * L i) =
      if i = b then 2 * L i else 0 := by
    rw [SmoothDerivation.map_mul, partialDerivation_inl_L]
    split_ifs
    · rw [smul_eq_mul, mul_one, two_mul]
    · rw [smul_zero, add_zero]
  have hkin : partialDerivation (Sum.inl b)
      (∑ i, algebraMap ℝ PhaseSpace ((I i)⁻¹ / 2) * (L i * L i)) =
        algebraMap ℝ PhaseSpace (I b)⁻¹ * L b := by
    rw [map_sum, Finset.sum_eq_single b]
    · rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, hsq]
      simp only [↓reduceIte, smul_eq_mul, mul_zero, add_zero]
      rw [h2, ← mul_assoc, ← map_mul, hb]
    · intro i _ hib
      rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, hsq]
      simp [hib]
    · intro h
      exact absurd (Finset.mem_univ b) h
  have hpot : partialDerivation (Sum.inl b)
      (∑ i, algebraMap ℝ PhaseSpace (k * χ i) * Γ i) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, partialDerivation_inl_Γ]
    simp
  simp only [gradL, hamiltonian, map_add, hkin, hpot, add_zero, angularVelocity]

theorem gradΓ_hamiltonian (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) :
    gradΓ (hamiltonian I k χ) = weight k χ := by
  funext b
  have hkin : partialDerivation (Sum.inr b)
      (∑ i, algebraMap ℝ PhaseSpace ((I i)⁻¹ / 2) * (L i * L i)) = 0 := by
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, SmoothDerivation.map_mul,
      partialDerivation_inr_L]
    simp
  have hpot : partialDerivation (Sum.inr b)
      (∑ i, algebraMap ℝ PhaseSpace (k * χ i) * Γ i) = algebraMap ℝ PhaseSpace (k * χ b) := by
    rw [map_sum, Finset.sum_eq_single b]
    · rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, partialDerivation_inr_Γ]
      simp
    · intro i _ hib
      rw [SmoothDerivation.map_mul, SmoothDerivation.map_algebraMap, partialDerivation_inr_Γ]
      simp [hib]
    · intro h
      exact absurd (Finset.mem_univ b) h
  simp only [gradΓ, hamiltonian, map_add, hkin, hpot, zero_add, weight]

/-- The equation of motion of the angular momentum of the heavy top:
`{L, H} = L × Ω + Γ × k χ`. -/
theorem poisson_L_hamiltonian (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) (a : Fin 3) :
    poisson.bracket (L a) (hamiltonian I k χ) =
      (L ⨯₃ angularVelocity I) a + (Γ ⨯₃ weight k χ) a := by
  rw [poisson_L_bracket, gradL_hamiltonian, gradΓ_hamiltonian]

/-- The equation of motion of the vertical vector of the heavy top:
`{Γ, H} = Γ × Ω`. -/
theorem poisson_Γ_hamiltonian (I : Fin 3 → ℝ) (k : ℝ) (χ : Fin 3 → ℝ) (a : Fin 3) :
    poisson.bracket (Γ a) (hamiltonian I k χ) = (Γ ⨯₃ angularVelocity I) a := by
  rw [poisson_Γ_bracket, gradL_hamiltonian]

/-- `|Γ|²` is a Casimir. -/
theorem poisson_Γ_sq_left (g : PhaseSpace) : poisson.bracket (Γ ⬝ᵥ Γ) g = 0 := by
  simp only [dotProduct, Fin.sum_univ_three, AlmostPoissonStructure.bracket_add_left,
    AlmostPoissonStructure.bracket_mul_left, poisson_Γ_bracket, cross_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- `L · Γ` is a Casimir. -/
theorem poisson_L_dot_Γ_left (g : PhaseSpace) : poisson.bracket (L ⬝ᵥ Γ) g = 0 := by
  simp only [dotProduct, Fin.sum_univ_three, AlmostPoissonStructure.bracket_add_left,
    AlmostPoissonStructure.bracket_mul_left, poisson_Γ_bracket, poisson_L_bracket, cross_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- `|Γ|²` is an integral of the motion for every Hamiltonian. -/
theorem isIntegral_Γ_sq (H : PhaseSpace) : poisson.IsIntegral H (Γ ⬝ᵥ Γ) :=
  poisson_Γ_sq_left H

/-- `L · Γ` is an integral of the motion for every Hamiltonian. -/
theorem isIntegral_L_dot_Γ (H : PhaseSpace) : poisson.IsIntegral H (L ⬝ᵥ Γ) :=
  poisson_L_dot_Γ_left H

end ProjectAInos.Mechanics.HeavyTop
