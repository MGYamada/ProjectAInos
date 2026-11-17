/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.Poisson.Canonical
public import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Ring

/-!
# Momentum functions of translations and of linear maps

On the canonical phase space with coordinates `q` and momenta `p`, a vector `a` gives the
function `translationMomentum a = Σ aᵢ pᵢ` and a matrix `A` gives
`linearMomentum A = Σ A μ ν q μ p ν`. Their brackets with the generators are

* `{Σ aᵢ pᵢ, q ρ} = −a ρ`, `{Σ aᵢ pᵢ, p σ} = 0`,
* `{ℓ_A, q ρ} = −Σ A μ ρ q μ`, `{ℓ_A, p σ} = Σ A σ ν p ν`,

and among themselves they close:

* `canonical_translationMomentum_translationMomentum`: `{P_a, P_b} = 0`,
* `canonical_linearMomentum_translationMomentum`: `{ℓ_A, P_a} = P_{a ᵥ* A}`,
* `canonical_linearMomentum_linearMomentum`: `{ℓ_A, ℓ_B} = ℓ_{B A − A B}`.

So `A ↦ ℓ_A` carries the commutator of matrices to the bracket, with the opposite sign. The
brackets of the charges of a group of affine maps follow from these three identities by matrix
algebra.
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SmoothAlgebra.PhaseSpace

open SmoothRing FreeSmoothRing

variable {ι : Type*} [Fintype ι]

/-- `Σ aᵢ pᵢ`, the momentum function of the translation along `a`. -/
def translationMomentum (a : ι → ℝ) : PhaseSpace ι := ∑ i, a i • p i

/-- `Σ A μ ν q μ p ν`, the momentum function of the linear map with the matrix `A`. -/
def linearMomentum (A : Matrix ι ι ℝ) : PhaseSpace ι := ∑ μ, ∑ ν, A μ ν • (q μ * p ν)

theorem translationMomentum_add (a b : ι → ℝ) :
    translationMomentum (a + b) = translationMomentum a + translationMomentum b := by
  simp only [translationMomentum, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem translationMomentum_smul (r : ℝ) (a : ι → ℝ) :
    translationMomentum (r • a) = r • translationMomentum a := by
  simp only [translationMomentum, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem translationMomentum_sub (a b : ι → ℝ) :
    translationMomentum (a - b) = translationMomentum a - translationMomentum b := by
  simp only [translationMomentum, Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem linearMomentum_add (A B : Matrix ι ι ℝ) :
    linearMomentum (A + B) = linearMomentum A + linearMomentum B := by
  simp only [linearMomentum, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem linearMomentum_smul (r : ℝ) (A : Matrix ι ι ℝ) :
    linearMomentum (r • A) = r • linearMomentum A := by
  simp only [linearMomentum, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem linearMomentum_sub (A B : Matrix ι ι ℝ) :
    linearMomentum (A - B) = linearMomentum A - linearMomentum B := by
  simp only [linearMomentum, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

variable [DecidableEq ι]

/-- `{Σ aᵢ pᵢ, q ρ} = −a ρ`. -/
theorem canonical_translationMomentum_q (a : ι → ℝ) (ρ : ι) :
    (canonical ι).bracket (translationMomentum a) (q ρ) = -algebraMap ℝ (PhaseSpace ι) (a ρ) := by
  rw [translationMomentum, AlmostPoissonStructure.bracket_sum_left, Finset.sum_eq_single ρ]
  · rw [AlmostPoissonStructure.bracket_smul_left, canonical_p_q, Algebra.algebraMap_eq_smul_one]
    simp only [↓reduceIte, smul_neg]
  · intro i _ hi
    rw [AlmostPoissonStructure.bracket_smul_left, canonical_p_q]
    simp only [hi, ↓reduceIte, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ ρ) h

/-- `{Σ aᵢ pᵢ, p σ} = 0`. -/
theorem canonical_translationMomentum_p (a : ι → ℝ) (σ : ι) :
    (canonical ι).bracket (translationMomentum a) (p σ) = 0 := by
  rw [translationMomentum, AlmostPoissonStructure.bracket_sum_left]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [AlmostPoissonStructure.bracket_smul_left, canonical_p_p, smul_zero]

/-- Translations commute: `{P_a, P_b} = 0`. -/
theorem canonical_translationMomentum_translationMomentum (a b : ι → ℝ) :
    (canonical ι).bracket (translationMomentum a) (translationMomentum b) = 0 := by
  have h : translationMomentum b = ∑ i, b i • (p i : PhaseSpace ι) := rfl
  rw [h, AlmostPoissonStructure.bracket_sum_right]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [AlmostPoissonStructure.bracket_smul_right, canonical_translationMomentum_p, smul_zero]

/-- `{ℓ_A, q ρ} = −Σ A μ ρ q μ`. -/
theorem canonical_linearMomentum_q (A : Matrix ι ι ℝ) (ρ : ι) :
    (canonical ι).bracket (linearMomentum A) (q ρ) = -∑ μ, A μ ρ • q μ := by
  rw [linearMomentum, AlmostPoissonStructure.bracket_sum_left, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [AlmostPoissonStructure.bracket_sum_left, Finset.sum_eq_single ρ]
  · rw [AlmostPoissonStructure.bracket_smul_left, AlmostPoissonStructure.bracket_mul_left,
      canonical_p_q, canonical_q_q]
    simp only [↓reduceIte, mul_zero, add_zero]
    rw [← smul_neg]
    congr 1
    ring
  · intro ν _ hν
    rw [AlmostPoissonStructure.bracket_smul_left, AlmostPoissonStructure.bracket_mul_left,
      canonical_p_q, canonical_q_q]
    simp only [hν, ↓reduceIte, mul_zero, add_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ ρ) h

/-- `{ℓ_A, p σ} = Σ A σ ν p ν`. -/
theorem canonical_linearMomentum_p (A : Matrix ι ι ℝ) (σ : ι) :
    (canonical ι).bracket (linearMomentum A) (p σ) = ∑ ν, A σ ν • p ν := by
  rw [linearMomentum, AlmostPoissonStructure.bracket_sum_left, Finset.sum_eq_single σ]
  · rw [AlmostPoissonStructure.bracket_sum_left]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [AlmostPoissonStructure.bracket_smul_left, AlmostPoissonStructure.bracket_mul_left,
      canonical_p_p, canonical_q_p]
    simp only [↓reduceIte, mul_zero, zero_add, mul_one]
  · intro μ _ hμ
    rw [AlmostPoissonStructure.bracket_sum_left]
    refine Finset.sum_eq_zero fun ν _ => ?_
    rw [AlmostPoissonStructure.bracket_smul_left, AlmostPoissonStructure.bracket_mul_left,
      canonical_p_p, canonical_q_p]
    simp only [hμ, ↓reduceIte, mul_zero, add_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ σ) h

/-- A linear map acts on the translations: `{ℓ_A, P_a} = P_{a ᵥ* A}`. -/
theorem canonical_linearMomentum_translationMomentum (A : Matrix ι ι ℝ) (a : ι → ℝ) :
    (canonical ι).bracket (linearMomentum A) (translationMomentum a) =
      translationMomentum (Matrix.vecMul a A) := by
  have h : translationMomentum a = ∑ i, a i • (p i : PhaseSpace ι) := rfl
  rw [h, AlmostPoissonStructure.bracket_sum_right]
  simp only [AlmostPoissonStructure.bracket_smul_right, canonical_linearMomentum_p,
    translationMomentum, Matrix.vecMul, dotProduct, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

/-- The bracket of two linear momentum functions is the linear momentum function of the
commutator: `{ℓ_A, ℓ_B} = ℓ_{B A − A B}`. -/
theorem canonical_linearMomentum_linearMomentum (A B : Matrix ι ι ℝ) :
    (canonical ι).bracket (linearMomentum A) (linearMomentum B) =
      linearMomentum (B * A - A * B) := by
  have h : linearMomentum B = ∑ ρ, ∑ σ, B ρ σ • ((q ρ : PhaseSpace ι) * p σ) := rfl
  have hBA : linearMomentum (B * A) =
      ∑ ρ, ∑ σ, B ρ σ • ((q ρ : PhaseSpace ι) * ∑ ν, A σ ν • p ν) := by
    simp only [linearMomentum, Matrix.mul_apply, Finset.sum_smul, Finset.mul_sum,
      Finset.smul_sum, mul_smul_comm, smul_smul]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    exact Finset.sum_comm
  have hAB : linearMomentum (A * B) =
      ∑ ρ, ∑ σ, B ρ σ • ((p σ : PhaseSpace ι) * ∑ μ, A μ ρ • q μ) := by
    simp only [linearMomentum, Matrix.mul_apply, Finset.sum_smul, Finset.mul_sum,
      Finset.smul_sum, mul_smul_comm, smul_smul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [mul_comm (p σ) (q μ), mul_comm (B ρ σ) (A μ ρ)]
  rw [h, AlmostPoissonStructure.bracket_sum_right, linearMomentum_sub, hBA, hAB,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  rw [AlmostPoissonStructure.bracket_sum_right, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [AlmostPoissonStructure.bracket_smul_right, AlmostPoissonStructure.bracket_mul_right,
    canonical_linearMomentum_p, canonical_linearMomentum_q, ← smul_sub]
  congr 1
  ring

end ProjectAinos.SmoothAlgebra.PhaseSpace
