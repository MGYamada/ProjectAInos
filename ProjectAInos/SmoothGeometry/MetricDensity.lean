/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Tactic

/-! # Metric volume density without an orientation

The Gram determinant defines an absolute density on ordered vector families.
Its change-of-family law uses the absolute determinant, also for singular
changes. No orientation, positive-definite metric or norm is involved.
-/

@[expose] public section
noncomputable section
open Module
open scoped BigOperators

namespace ProjectAInos.SmoothGeometry.MetricDensity

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-- Gram matrix of an ordered family, in row/column vector order. -/
def gram (B : LinearMap.BilinForm ℝ V) (v : Fin n → V) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => B (v i) (v j)

/-- The orientation-free volume of an ordered vector family. -/
def value (B : LinearMap.BilinForm ℝ V) (v : Fin n → V) : ℝ :=
  Real.sqrt |(gram B v).det|

theorem value_nonneg (B : LinearMap.BilinForm ℝ V) (v : Fin n → V) : 0 ≤ value B v :=
  Real.sqrt_nonneg _

theorem value_sq (B : LinearMap.BilinForm ℝ V) (v : Fin n → V) :
    value B v ^ 2 = |(gram B v).det| := Real.sq_sqrt (abs_nonneg _)

/-- An arbitrary change of the vector family gives matrix congruence. -/
theorem gram_change (B : LinearMap.BilinForm ℝ V) (v : Fin n → V)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    gram B (fun i => ∑ j, A j i • v j) = A.transpose * gram B v * A := by
  ext i j
  simp only [gram, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Absolute determinant scaling, valid even when the change is singular. -/
theorem value_change (B : LinearMap.BilinForm ℝ V) (v : Fin n → V)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    value B (fun i => ∑ j, A j i • v j) = |A.det| * value B v := by
  unfold value
  rw [gram_change, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  have h : |A.det * (gram B v).det * A.det| = A.det ^ 2 * |(gram B v).det| := by
    rw [abs_mul, abs_mul, ← sq_abs A.det]
    ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- Reversing the metric sign does not change volume density. -/
theorem value_neg (B : LinearMap.BilinForm ℝ V) (v : Fin n → V) :
    value (-B) v = value B v := by
  have h : gram (-B) v = -(gram B v) := rfl
  simp only [value, h, Matrix.det_neg, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul]

theorem gram_basis (B : LinearMap.BilinForm ℝ V) (b : Basis (Fin n) ℝ V) :
    gram B b = LinearMap.BilinForm.toMatrix b B := by
  ext i j
  simp [gram, LinearMap.BilinForm.toMatrix_apply]

/-- Nondegeneracy of the metric makes every basis have positive volume. -/
theorem value_basis_pos (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (b : Basis (Fin n) ℝ V) : 0 < value B b := by
  apply Real.sqrt_pos.mpr
  apply abs_pos.mpr
  rw [gram_basis]
  exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB

/-- Express the density in any basis; the result is independent of that basis. -/
theorem value_eq_basis (B : LinearMap.BilinForm ℝ V) (b : Basis (Fin n) ℝ V)
    (v : Fin n → V) :
    value B v = |Matrix.det (fun i j => b.repr (v j) i)| * value B b := by
  have hv : v = fun j => ∑ i, b.repr (v j) i • b i := by
    funext j
    exact (b.sum_repr (v j)).symm
  conv_lhs => rw [hv]
  exact value_change B b _

/-- Smoothness of the determinant follows from its finite polynomial expansion. -/
theorem contDiff_matrix_det {r : WithTop ℕ∞} :
    ContDiff ℝ r (fun A : Fin n → Fin n → ℝ => Matrix.det (Matrix.of A)) := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  fun_prop

end ProjectAInos.SmoothGeometry.MetricDensity
