/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.HodgeFour
public import ProjectAInos.SmoothGeometry.DifferentialForm.Interior
import all Mathlib.LinearAlgebra.ExteriorPower.BilinForm

/-! # Four-dimensional Hodge and vector-current signs -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower

namespace ProjectAInos.SmoothGeometry.Minkowski
open DifferentialForm

theorem wedgePairing_one_three (a : Fin 1 → Dual ℝ (MinkowskiModel 3))
    (b : Fin 3 → Dual ℝ (MinkowskiModel 3)) :
    wedgePairing (volume .standard 3)
      (by norm_num [MinkowskiModel] : 1 + 3 = Module.finrank ℝ (Dual ℝ (MinkowskiModel 3)))
      (ιMulti ℝ 1 a) (ιMulti ℝ 3 b) =
      coordinateVolume 4 (exteriorPower.wedge ℝ (Dual ℝ (MinkowskiModel 3)) 1 3
        (ιMulti ℝ 1 a) (ιMulti ℝ 3 b)) := by
  change ((by norm_num [MinkowskiModel] : 1 + 3 = Module.finrank ℝ (Dual ℝ (MinkowskiModel 3))).symm ▸
    (basisVolumeDegree (Pi.basisFun ℝ (Fin 4)).dualBasis _
      (Module.finrank_eq_card_basis (Pi.basisFun ℝ (Fin 4)).dualBasis)).toLinearMap)
    (exteriorPower.wedge ℝ (Dual ℝ (MinkowskiModel 3)) 1 3 (ιMulti ℝ 1 a) (ιMulti ℝ 3 b)) = _
  rw [basisVolumeDegree_cast]
  rfl
  all_goals norm_num [MinkowskiModel]

/-- All four one-form signs, for either Lorentz convention and standard orientation. -/
theorem hodge_coordinate_one (σ : LorentzConvention) (i : Fin 4) :
    hodgeFiber σ .standard (by decide : 1 + 3 = 3 + 1) (coordinateForm ![i]) =
      (lorentzSign σ i * (-1 : ℝ) ^ (i : ℕ)) •
        (coordinateForm i.succAbove : MinkowskiModel 3 [⋀^Fin 3]→L[ℝ] ℝ) := by
  apply toExterior.injective
  rw [toExterior_hodgeFiber, map_smul]
  simp only [coordinateForm, ofCovectors, LinearEquiv.apply_symm_apply]
  symm
  apply hodge_unique
  intro α
  suffices H : (wedgePairing (volume .standard 3) (by norm_num [MinkowskiModel])).flip
      ((lorentzSign σ i * (-1 : ℝ) ^ (i : ℕ)) •
        ιMulti ℝ 3 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (i.succAbove j))) =
      (coMetric σ 3).exteriorPower 1
        (ιMulti ℝ 1 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![i] j))) from
    congrArg (fun f => f α) H
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change wedgePairing (volume .standard 3) (by norm_num [MinkowskiModel])
    (ιMulti ℝ 1 a) ((lorentzSign σ i * (-1 : ℝ) ^ (i : ℕ)) • ιMulti ℝ 3 _) = _
  rw [map_smul, wedgePairing_one_three]
  have hw : exteriorPower.wedge ℝ (Dual ℝ (MinkowskiModel 3)) 1 3 (ιMulti ℝ 1 a)
      (ιMulti ℝ 3 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (i.succAbove j))) =
      ιMulti ℝ 4 (Fin.append a (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (i.succAbove j))) := by
    apply Subtype.ext
    simp only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, ιMulti_apply_coe]
    exact ExteriorAlgebra.ιMulti_mul_ιMulti _ _
  rw [hw, coordinateVolume_ιMulti]
  change (lorentzSign σ i * (-1 : ℝ) ^ (i : ℕ)) *
    (Matrix.of fun r j => Fin.append a
      (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (i.succAbove j)) r (Pi.single j 1)).det =
    (coMetric σ 3).exteriorPower 1
      (ιMulti ℝ 1 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![i] j))) (ιMulti ℝ 1 a)
  rw [LinearMap.BilinForm.bilinForm_ιMulti_ιMulti, Matrix.det_succ_row_zero]
  cases σ <;> fin_cases i <;>
    norm_num [-Basis.coe_dualBasis, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Matrix.submatrix_apply, coMetric_basis, Basis.coord_apply, lorentzSign,
      Fin.append, Fin.addCases, Pi.single_apply]
  all_goals norm_num [Basis.dualBasis_apply, Basis.coord_apply, Pi.single_apply, Fin.succAbove]

/-- Cofactor expansion of coordinate volume with a vector inserted first. -/
theorem interior_coordinate_volume {n : ℕ} (v : Fin (n + 1) → ℝ) :
    interior v (coordinateForm id) =
      ∑ i : Fin (n + 1), ((-1 : ℝ) ^ (i : ℕ) * v i) • coordinateForm i.succAbove := by
  ext w
  rw [interior_apply, coordinateForm_apply, Matrix.det_succ_row_zero]
  change (∑ i : Fin (n + 1), (-1 : ℝ) ^ (i : ℕ) * v i *
    Matrix.det (Matrix.of fun r j => w r (i.succAbove j))) = _
  simp only [ContinuousAlternatingMap.sum_apply, ContinuousAlternatingMap.smul_apply,
    smul_eq_mul, coordinateForm_apply]

/-- The Hodge of a metric-dual vector is contraction of the standard volume. -/
theorem hodge_flat_one (σ : LorentzConvention) (v : MinkowskiModel 3) :
    hodgeFiber σ .standard (by decide : 1 + 3 = 3 + 1) (oneFormEquiv (flat σ v)) =
      interior v (coordinateForm id) := by
  have hv : oneFormEquiv (flat σ v) =
      ∑ i : Fin 4, (lorentzSign σ i * v i) • coordinateForm ![i] := by
    ext w
    simp [oneFormEquiv_apply, flat_apply, minkowskiForm_apply,
      coordinateForm_apply, mul_assoc]
  rw [hv, map_sum, interior_coordinate_volume]
  simp_rw [map_smul, hodge_coordinate_one, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  cases σ <;> fin_cases i <;> simp [lorentzSign, mul_comm]

end ProjectAInos.SmoothGeometry.Minkowski
