/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.Poisson.Canonical
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Ring

/-!
# Orbital charges of a constant metric

A matrix `η` lowers the index of the coordinates of the canonical phase space:
`loweredCoordinate η μ = Σ η μ α q α`. The orbital charges are

`orbitalCharge η μ ν = x_μ p_ν − x_ν p_μ`.

Their brackets with the momenta and among themselves are those of the Lie algebra of the affine
isometries of `η`:

* `canonical_orbitalCharge_p`: `{J_μν, p_ρ} = η_μρ p_ν − η_νρ p_μ`,
* `canonical_orbitalCharge_orbitalCharge`: for a symmetric `η`,
  `{J_μν, J_ρσ} = η_μρ J_νσ − η_νρ J_μσ + η_νσ J_μρ − η_μσ J_νρ`.

No inverse of `η` is used for these identities, and `η` may be degenerate. If `G` is the inverse
of a symmetric `η`, the quadratic function `momentumQuadratic G = Σ G σ τ p σ p τ` of the momenta
has `{x_μ, G(p, p)} = 2 p_μ`, and the momenta and the orbital charges have zero bracket with it
(`canonical_p_momentumQuadratic`, `canonical_orbitalCharge_momentumQuadratic`).
-/

@[expose] public section

noncomputable section

namespace ProjectAinos.SmoothAlgebra.PhaseSpace

open SmoothRing FreeSmoothRing

variable {ι : Type*} [Fintype ι]

/-- The coordinate with its index lowered by `η`: `x_μ = Σ η μ α q α`. -/
def loweredCoordinate (η : Matrix ι ι ℝ) (μ : ι) : PhaseSpace ι := ∑ α, η μ α • q α

/-- The orbital charge `J_μν = x_μ p_ν − x_ν p_μ`. -/
def orbitalCharge (η : Matrix ι ι ℝ) (μ ν : ι) : PhaseSpace ι :=
  loweredCoordinate η μ * p ν - loweredCoordinate η ν * p μ

/-- The quadratic function `Σ G σ τ p σ p τ` of the momenta. -/
def momentumQuadratic (G : Matrix ι ι ℝ) : PhaseSpace ι := ∑ σ, ∑ τ, G σ τ • (p σ * p τ)

theorem orbitalCharge_antisymm (η : Matrix ι ι ℝ) (μ ν : ι) :
    orbitalCharge η μ ν = -orbitalCharge η ν μ := by
  unfold orbitalCharge
  ring

theorem orbitalCharge_self (η : Matrix ι ι ℝ) (μ : ι) : orbitalCharge η μ μ = 0 :=
  sub_self _

variable [DecidableEq ι]

/-- For a diagonal matrix the lowered coordinate is `s_μ q_μ`. -/
theorem loweredCoordinate_diagonal (s : ι → ℝ) (μ : ι) :
    loweredCoordinate (Matrix.diagonal s) μ = s μ • q μ := by
  rw [loweredCoordinate, Finset.sum_eq_single μ]
  · rw [Matrix.diagonal_apply_eq]
  · intro α _ hα
    rw [Matrix.diagonal_apply_ne _ hα.symm, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ μ) h

/-- For a diagonal matrix the quadratic function is `Σ s_σ p_σ²`. -/
theorem momentumQuadratic_diagonal (s : ι → ℝ) :
    momentumQuadratic (Matrix.diagonal s) = ∑ σ, s σ • (p σ * p σ : PhaseSpace ι) := by
  rw [momentumQuadratic]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_eq_single σ]
  · rw [Matrix.diagonal_apply_eq]
  · intro τ _ hτ
    rw [Matrix.diagonal_apply_ne _ hτ.symm, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ σ) h

/-- `{x_μ, p_ν} = η_μν`. -/
theorem canonical_loweredCoordinate_p (η : Matrix ι ι ℝ) (μ ν : ι) :
    (canonical ι).bracket (loweredCoordinate η μ) (p ν) =
      algebraMap ℝ (PhaseSpace ι) (η μ ν) := by
  rw [loweredCoordinate, AlmostPoissonStructure.bracket_sum_left, Finset.sum_eq_single ν]
  · rw [AlmostPoissonStructure.bracket_smul_left, canonical_q_p, Algebra.algebraMap_eq_smul_one]
    simp only [↓reduceIte]
  · intro α _ hα
    rw [AlmostPoissonStructure.bracket_smul_left, canonical_q_p]
    simp only [hα, ↓reduceIte, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ ν) h

/-- `{p_ν, x_μ} = −η_μν`. -/
theorem canonical_p_loweredCoordinate (η : Matrix ι ι ℝ) (ν μ : ι) :
    (canonical ι).bracket (p ν) (loweredCoordinate η μ) =
      -algebraMap ℝ (PhaseSpace ι) (η μ ν) := by
  rw [(canonical ι).antisymm, canonical_loweredCoordinate_p]

theorem canonical_loweredCoordinate_q (η : Matrix ι ι ℝ) (μ ρ : ι) :
    (canonical ι).bracket (loweredCoordinate η μ) (q ρ) = 0 := by
  rw [loweredCoordinate, AlmostPoissonStructure.bracket_sum_left]
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [AlmostPoissonStructure.bracket_smul_left, canonical_q_q, smul_zero]

/-- `{x_μ, x_ν} = 0`. -/
theorem canonical_loweredCoordinate_loweredCoordinate (η : Matrix ι ι ℝ) (μ ν : ι) :
    (canonical ι).bracket (loweredCoordinate η μ) (loweredCoordinate η ν) = 0 := by
  have h : loweredCoordinate η ν = ∑ α, η ν α • (q α : PhaseSpace ι) := rfl
  rw [h, AlmostPoissonStructure.bracket_sum_right]
  refine Finset.sum_eq_zero fun α _ => ?_
  rw [AlmostPoissonStructure.bracket_smul_right, canonical_loweredCoordinate_q, smul_zero]

/-- The momenta transform as a covector: `{J_μν, p_ρ} = η_μρ p_ν − η_νρ p_μ`. -/
theorem canonical_orbitalCharge_p (η : Matrix ι ι ℝ) (μ ν ρ : ι) :
    (canonical ι).bracket (orbitalCharge η μ ν) (p ρ) =
      algebraMap ℝ (PhaseSpace ι) (η μ ρ) * p ν - algebraMap ℝ (PhaseSpace ι) (η ν ρ) * p μ := by
  rw [orbitalCharge, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_mul_left,
    canonical_p_p, canonical_p_p, canonical_loweredCoordinate_p, canonical_loweredCoordinate_p]
  ring

/-- `{J_μν, x_ρ} = η_ρμ x_ν − η_ρν x_μ`. -/
theorem canonical_orbitalCharge_loweredCoordinate (η : Matrix ι ι ℝ) (μ ν ρ : ι) :
    (canonical ι).bracket (orbitalCharge η μ ν) (loweredCoordinate η ρ) =
      algebraMap ℝ (PhaseSpace ι) (η ρ μ) * loweredCoordinate η ν -
        algebraMap ℝ (PhaseSpace ι) (η ρ ν) * loweredCoordinate η μ := by
  rw [orbitalCharge, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_mul_left,
    canonical_p_loweredCoordinate, canonical_p_loweredCoordinate,
    canonical_loweredCoordinate_loweredCoordinate, canonical_loweredCoordinate_loweredCoordinate]
  ring

/-- The brackets of the orbital charges of a symmetric `η`:
`{J_μν, J_ρσ} = η_μρ J_νσ − η_νρ J_μσ + η_νσ J_μρ − η_μσ J_νρ`. -/
theorem canonical_orbitalCharge_orbitalCharge {η : Matrix ι ι ℝ} (hη : η.IsSymm)
    (μ ν ρ σ : ι) :
    (canonical ι).bracket (orbitalCharge η μ ν) (orbitalCharge η ρ σ) =
      algebraMap ℝ (PhaseSpace ι) (η μ ρ) * orbitalCharge η ν σ -
        algebraMap ℝ (PhaseSpace ι) (η ν ρ) * orbitalCharge η μ σ +
        algebraMap ℝ (PhaseSpace ι) (η ν σ) * orbitalCharge η μ ρ -
        algebraMap ℝ (PhaseSpace ι) (η μ σ) * orbitalCharge η ν ρ := by
  have h : orbitalCharge η ρ σ = loweredCoordinate η ρ * p σ - loweredCoordinate η σ * p ρ := rfl
  rw [h, AlmostPoissonStructure.bracket_sub_right, AlmostPoissonStructure.bracket_mul_right,
    AlmostPoissonStructure.bracket_mul_right, canonical_orbitalCharge_p,
    canonical_orbitalCharge_p, canonical_orbitalCharge_loweredCoordinate,
    canonical_orbitalCharge_loweredCoordinate, hη.apply μ ρ, hη.apply ν ρ, hη.apply μ σ,
    hη.apply ν σ]
  unfold orbitalCharge
  ring

/-- `{p_ν, G(p, p)} = 0`. -/
theorem canonical_p_momentumQuadratic (G : Matrix ι ι ℝ) (ν : ι) :
    (canonical ι).bracket (p ν) (momentumQuadratic G) = 0 := by
  rw [momentumQuadratic, AlmostPoissonStructure.bracket_sum_right]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [AlmostPoissonStructure.bracket_sum_right]
  refine Finset.sum_eq_zero fun τ _ => ?_
  rw [AlmostPoissonStructure.bracket_smul_right, AlmostPoissonStructure.bracket_mul_right,
    canonical_p_p, canonical_p_p, mul_zero, mul_zero, add_zero, smul_zero]

/-- If `G` is the inverse of the symmetric `η`, then `{x_μ, G(p, p)} = 2 p_μ`. -/
theorem canonical_loweredCoordinate_momentumQuadratic {η G : Matrix ι ι ℝ} (hη : η.IsSymm)
    (hG : η * G = 1) (μ : ι) :
    (canonical ι).bracket (loweredCoordinate η μ) (momentumQuadratic G) = 2 * p μ := by
  have hG' : G * η = 1 := mul_eq_one_comm.mp hG
  have h1 (σ : ι) : ∑ τ, G σ τ * η μ τ = if σ = μ then 1 else 0 := by
    have h := congrFun (congrFun hG' σ) μ
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun τ _ => by rw [hη.apply μ τ]
  have h2 (τ : ι) : ∑ σ, G σ τ * η μ σ = if μ = τ then 1 else 0 := by
    have h := congrFun (congrFun hG μ) τ
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun σ _ => mul_comm _ _
  have step (σ τ : ι) : (canonical ι).bracket (loweredCoordinate η μ) (G σ τ • (p σ * p τ)) =
      (G σ τ * η μ τ) • p σ + (G σ τ * η μ σ) • p τ := by
    rw [AlmostPoissonStructure.bracket_smul_right, AlmostPoissonStructure.bracket_mul_right,
      canonical_loweredCoordinate_p, canonical_loweredCoordinate_p, smul_add, mul_smul, mul_smul,
      Algebra.smul_def (η μ τ), Algebra.smul_def (η μ σ), mul_comm (p σ), mul_comm (p τ)]
  rw [momentumQuadratic, AlmostPoissonStructure.bracket_sum_right]
  simp only [AlmostPoissonStructure.bracket_sum_right, step, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun σ τ => (G σ τ * η μ σ) • (p τ : PhaseSpace ι))]
  simp only [← Finset.sum_smul, h1, h2, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  ring

/-- The orbital charges are symmetries of the quadratic function of the momenta. -/
theorem canonical_orbitalCharge_momentumQuadratic {η G : Matrix ι ι ℝ} (hη : η.IsSymm)
    (hG : η * G = 1) (μ ν : ι) :
    (canonical ι).bracket (orbitalCharge η μ ν) (momentumQuadratic G) = 0 := by
  rw [orbitalCharge, AlmostPoissonStructure.bracket_sub_left,
    AlmostPoissonStructure.bracket_mul_left, AlmostPoissonStructure.bracket_mul_left,
    canonical_p_momentumQuadratic, canonical_p_momentumQuadratic,
    canonical_loweredCoordinate_momentumQuadratic hη hG,
    canonical_loweredCoordinate_momentumQuadratic hη hG]
  ring

end ProjectAinos.SmoothAlgebra.PhaseSpace
