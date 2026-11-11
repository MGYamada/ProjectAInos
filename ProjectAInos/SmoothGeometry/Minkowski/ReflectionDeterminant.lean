/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ProjectAInos.SmoothGeometry.Minkowski.Reflection
public import ProjectAInos.SmoothGeometry.Minkowski.Matrix
public import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Determinants of Lorentz reflections -/
@[expose] public section
noncomputable section
namespace ProjectAInos.SmoothGeometry.Minkowski
variable {d : ℕ}

theorem reflectionLinear_det (u : MinkowskiModel d) (hu : intervalQuadratic u ≠ 0) :
    (reflectionLinear u).det = -1 := by
  rw [← LinearMap.det_toMatrix']
  have hm : LinearMap.toMatrix' (reflectionLinear u) =
      1 + Matrix.replicateCol Unit (fun i => -(2 / intervalQuadratic u) * u i) *
        Matrix.replicateRow Unit (fun i => lorentzSign .timePositive i * u i) := by
    ext i j
    simp [LinearMap.toMatrix'_apply, reflectionLinear_apply, Matrix.mul_apply,
      pair, minkowskiForm_apply, Pi.single_apply, mul_ite, Matrix.one_apply]
    ring
  rw [hm, Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Unit)
    (fun i => -(2 / intervalQuadratic u) * u i) (fun i => lorentzSign .timePositive i * u i)]
  simp only [dotProduct]
  have hsum : (∑ i : Fin (d+1), lorentzSign .timePositive i * u i * (-(2 / intervalQuadratic u) * u i)) =
      -(2 / intervalQuadratic u) * intervalQuadratic u := by
    rw [intervalQuadratic_apply, pair, minkowskiForm_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  field_simp
  ring

end ProjectAInos.SmoothGeometry.Minkowski
