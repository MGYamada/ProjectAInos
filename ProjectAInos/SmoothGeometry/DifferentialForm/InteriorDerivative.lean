/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Interior
public import ProjectAInos.SmoothGeometry.DifferentialForm.Coordinates
public import Mathlib.LinearAlgebra.Determinant

/-! # Exterior derivative of contraction with coordinate volume

This coordinate-model calculation identifies the trace of the actual
derivative. Native geometric versions use the proved chart laws.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module

namespace ProjectAInos.SmoothGeometry.DifferentialForm

/-- A top-degree continuous form is determined by its value on a basis. -/
theorem topForm_ext_basis {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    {n : ℕ} (b : Basis (Fin n) ℝ V) {α β : V [⋀^Fin n]→L[ℝ] ℝ}
    (h : α b = β b) : α = β := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  rw [α.toAlternatingMap.eq_smul_basis_det b, β.toAlternatingMap.eq_smul_basis_det b]
  exact congrArg (fun r : ℝ => r • b.det) h

/-- In four coordinates, `d(ι_V vol) = (∂ᵢVⁱ) vol`. -/
theorem extDeriv_interior_volume_four {V : (Fin 4 → ℝ) → (Fin 4 → ℝ)} {x : Fin 4 → ℝ}
    (hV : DifferentiableAt ℝ V x) :
    extDeriv (fun y => interior (V y) (coordinateForm id)) x =
      (∑ i : Fin 4, fderiv ℝ V x (Pi.single i 1) i) • coordinateForm id := by
  let L := (coordinateForm (n := 4) id).curryLeft
  have hfun : (fun y => interior (V y) (coordinateForm (n := 4) id)) = L ∘ V := rfl
  have hd := L.hasFDerivAt.comp x hV.hasFDerivAt
  apply topForm_ext_basis (Pi.basisFun ℝ (Fin 4))
  rw [hfun]
  simp only [extDeriv, hd.fderiv, ContinuousAlternatingMap.alternatizeUncurryFin_apply]
  norm_num [L, ContinuousAlternatingMap.curryLeft_apply_apply, coordinateForm_apply,
    Matrix.det_succ_row_zero, Matrix.submatrix_apply, Fin.sum_univ_succ,
    Fin.removeNth, Fin.succAbove, Pi.single_apply]

end ProjectAInos.SmoothGeometry.DifferentialForm
