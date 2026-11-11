/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.Isometry
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! # Coordinate matrices and determinants of Lorentz transformations -/
@[expose] public section
noncomputable section
namespace ProjectAInos.SmoothGeometry.Minkowski
variable {d : ℕ}

def metricMatrix (σ : LorentzConvention) (d : ℕ) : Matrix (Fin (d+1)) (Fin (d+1)) ℝ :=
  Matrix.diagonal (lorentzSign σ)

theorem metricMatrix_eq (σ : LorentzConvention) :
    LinearMap.BilinForm.toMatrix' (minkowskiForm σ d).toLinearMap₁₂ = metricMatrix σ d := by
  ext i j
  by_cases h : i = j
  · subst j; simp [LinearMap.BilinForm.toMatrix'_apply, minkowskiForm_apply, Pi.single_apply, mul_ite, metricMatrix]
  · simp [h, Ne.symm h, LinearMap.BilinForm.toMatrix'_apply, minkowskiForm_apply,
    Pi.single_apply, mul_ite, metricMatrix]

theorem metricMatrix_det_ne_zero (σ : LorentzConvention) :
    (metricMatrix σ d).det ≠ 0 := by
  rw [metricMatrix, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  have h := lorentzSign_sq σ i
  intro hz; simp [hz] at h

namespace LorentzGroup

def matrix (L : LorentzGroup d) := L.val.toLinearMap.toMatrix'

theorem matrix_preserves_metric (L : LorentzGroup d) (σ : LorentzConvention) :
    (matrix L).transpose * metricMatrix σ d * matrix L = metricMatrix σ d := by
  unfold matrix
  rw [← metricMatrix_eq, ← LinearMap.BilinForm.toMatrix'_comp]
  apply congrArg LinearMap.BilinForm.toMatrix'
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  exact preserves_metric L σ v w

theorem matrix_det_sq (L : LorentzGroup d) : (matrix L).det ^ 2 = 1 := by
  have h := congrArg Matrix.det (matrix_preserves_metric L .timeNegative)
  simp only [Matrix.det_mul, Matrix.det_transpose] at h
  have hn := metricMatrix_det_ne_zero (d := d) .timeNegative
  apply (mul_right_cancel₀ hn)
  nlinarith [h]

theorem matrix_det_eq_one_or_neg_one (L : LorentzGroup d) :
    (matrix L).det = 1 ∨ (matrix L).det = -1 := by
  have h := matrix_det_sq L
  have hh : ((matrix L).det - 1) * ((matrix L).det + 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp hh with h | h
  · left; linarith
  · right; linarith

end LorentzGroup
end ProjectAInos.SmoothGeometry.Minkowski
