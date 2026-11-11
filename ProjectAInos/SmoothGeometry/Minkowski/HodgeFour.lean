/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ProjectAInos.SmoothGeometry.Minkowski.HodgeNaturality
import all Mathlib.LinearAlgebra.ExteriorPower.BilinForm

/-! # Four-dimensional basis signs and observer decomposition -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower
namespace ProjectAInos.SmoothGeometry.Minkowski
open DifferentialForm

theorem coordinateVolume_ιMulti (n : ℕ) (a : Fin n → Dual ℝ (Fin n → ℝ)) :
    coordinateVolume n (ιMulti ℝ n a) = (Matrix.of fun i j => a i (Pi.single j 1)).det := by
  simp only [coordinateVolume, basisVolumeDegree, LinearEquiv.trans_apply, LinearEquiv.funUnique_apply,
    Basis.equivFun_apply]
  change ((Pi.basisFun ℝ (Fin n)).dualBasis.exteriorPower n).repr (ιMulti ℝ n a)
    (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin n) n) = _
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  have h : (Set.powersetCard.ofFinEmbEquiv.symm (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin n) n) : Fin n → Fin n) = id :=
    (Set.powersetCard.ofFinEmbEquiv.symm _).strictMono.eq_id
  change (Matrix.of fun i j => ((Pi.basisFun ℝ (Fin n)).dualBasis).coord
    (Set.powersetCard.ofFinEmbEquiv.symm (⟨Finset.univ, by simp⟩ : Set.powersetCard (Fin n) n) j) (a i)).det = _
  rw [h]
  simp [Basis.coord_apply]
theorem wedgePairing_four (a b : Fin 2 → Dual ℝ (MinkowskiModel 3)) :
    wedgePairing (volume .standard 3) (by norm_num [MinkowskiModel] : 2+2=Module.finrank ℝ (Dual ℝ (MinkowskiModel 3)))
      (ιMulti ℝ 2 a) (ιMulti ℝ 2 b) =
      coordinateVolume 4 (exteriorPower.wedge ℝ (Dual ℝ (MinkowskiModel 3)) 2 2 (ιMulti ℝ 2 a) (ιMulti ℝ 2 b)) := by
  change ((by norm_num [MinkowskiModel] : 2+2=Module.finrank ℝ (Dual ℝ (MinkowskiModel 3))).symm ▸
    (basisVolumeDegree (Pi.basisFun ℝ (Fin 4)).dualBasis _ (Module.finrank_eq_card_basis (Pi.basisFun ℝ (Fin 4)).dualBasis)).toLinearMap)
    (exteriorPower.wedge ℝ (Dual ℝ (MinkowskiModel 3)) 2 2 (ιMulti ℝ 2 a) (ιMulti ℝ 2 b)) = _
  rw [basisVolumeDegree_cast]
  rfl
  all_goals norm_num [MinkowskiModel]

/-- The sign of `star (dt ∧ dx)` with the standard spacetime orientation. -/
theorem hodge_dt_dx (σ : LorentzConvention) :
    hodgeFiber σ .standard (by decide : 2+2=3+1) (coordinateForm ![0,1]) =
      -(coordinateForm ![2,3] : MinkowskiModel 3 [⋀^Fin 2]→L[ℝ] ℝ) := by
  apply toExterior.injective
  rw [toExterior_hodgeFiber, map_neg]
  simp only [coordinateForm, ofCovectors, LinearEquiv.apply_symm_apply]
  symm
  apply hodge_unique
  intro α
  suffices H : (wedgePairing (volume .standard 3) (by norm_num [MinkowskiModel])).flip
      (-ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![2,3] j))) =
      (coMetric σ 3).exteriorPower 2 (ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![0,1] j))) from
    congrArg (fun f => f α) H
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change wedgePairing (volume .standard 3) (by norm_num [MinkowskiModel]) (ιMulti ℝ 2 a) (-ιMulti ℝ 2 _) = _
  rw [map_neg, wedgePairing_four]
  have hw : exteriorPower.wedge ℝ (Dual ℝ (MinkowskiModel 3)) 2 2 (ιMulti ℝ 2 a)
      (ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![2,3] j))) =
      ιMulti ℝ 4 (Fin.append a (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![2,3] j))) := by
    apply Subtype.ext
    simp only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, ιMulti_apply_coe]
    exact ExteriorAlgebra.ιMulti_mul_ιMulti _ _
  rw [hw, coordinateVolume_ιMulti]
  change -(Matrix.of fun i j => Fin.append a (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![2,3] j)) i (Pi.single j 1)).det =
    (coMetric σ 3).exteriorPower 2 (ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![0,1] j))) (ιMulti ℝ 2 a)
  rw [LinearMap.BilinForm.bilinForm_ιMulti_ιMulti]
  rw [Matrix.det_succ_row_zero]
  cases σ <;> norm_num [-Basis.coe_dualBasis, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, coMetric_basis, Basis.coord_apply, lorentzSign, Fin.append, Fin.addCases,
    Pi.single_apply]
  all_goals norm_num [Basis.dualBasis_apply, Basis.coord_apply, Pi.single_apply, Fin.succAbove]
  all_goals ring

/-- The sign of `star (dt ∧ dz)` with the standard spacetime orientation. -/
theorem hodge_dt_dz (σ : LorentzConvention) :
    hodgeFiber σ .standard (by decide : 2+2=3+1) (coordinateForm ![0,3]) =
      -(coordinateForm ![1,2] : MinkowskiModel 3 [⋀^Fin 2]→L[ℝ] ℝ) := by
  apply toExterior.injective
  rw [toExterior_hodgeFiber, map_neg]
  simp only [coordinateForm, ofCovectors, LinearEquiv.apply_symm_apply]
  symm
  apply hodge_unique
  intro α
  suffices H : (wedgePairing (volume .standard 3) (by norm_num [MinkowskiModel])).flip
      (-ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![1,2] j))) =
      (coMetric σ 3).exteriorPower 2 (ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![0,3] j))) from
    congrArg (fun f => f α) H
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change wedgePairing (volume .standard 3) (by norm_num [MinkowskiModel]) (ιMulti ℝ 2 a) (-ιMulti ℝ 2 _) = _
  rw [map_neg, wedgePairing_four]
  have hw : exteriorPower.wedge ℝ (Dual ℝ (MinkowskiModel 3)) 2 2 (ιMulti ℝ 2 a)
      (ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![1,2] j))) =
      ιMulti ℝ 4 (Fin.append a (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![1,2] j))) := by
    apply Subtype.ext
    simp only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, ιMulti_apply_coe]
    exact ExteriorAlgebra.ιMulti_mul_ιMulti _ _
  rw [hw, coordinateVolume_ιMulti]
  change -(Matrix.of fun i j => Fin.append a (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![1,2] j)) i (Pi.single j 1)).det =
    (coMetric σ 3).exteriorPower 2 (ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![0,3] j))) (ιMulti ℝ 2 a)
  rw [LinearMap.BilinForm.bilinForm_ιMulti_ιMulti]
  rw [Matrix.det_succ_row_zero]
  cases σ <;> norm_num [-Basis.coe_dualBasis, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, coMetric_basis, Basis.coord_apply, lorentzSign, Fin.append, Fin.addCases,
    Pi.single_apply]
  all_goals norm_num [Basis.dualBasis_apply, Basis.coord_apply, Pi.single_apply, Fin.succAbove]
  all_goals ring

/-- The sign of `star (dt ∧ dy)` with the standard spacetime orientation. -/
theorem hodge_dt_dy (σ : LorentzConvention) :
    hodgeFiber σ .standard (by decide : 2+2=3+1) (coordinateForm ![0,2]) =
      (coordinateForm ![1,3] : MinkowskiModel 3 [⋀^Fin 2]→L[ℝ] ℝ) := by
  apply toExterior.injective
  rw [toExterior_hodgeFiber]
  simp only [coordinateForm, ofCovectors, LinearEquiv.apply_symm_apply]
  symm
  apply hodge_unique
  intro α
  suffices H : (wedgePairing (volume .standard 3) (by norm_num [MinkowskiModel])).flip
      (ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![1,3] j))) =
      (coMetric σ 3).exteriorPower 2 (ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![0,2] j))) from
    congrArg (fun f => f α) H
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change wedgePairing (volume .standard 3) (by norm_num [MinkowskiModel]) (ιMulti ℝ 2 a) (ιMulti ℝ 2 _) = _
  rw [wedgePairing_four]
  have hw : exteriorPower.wedge ℝ (Dual ℝ (MinkowskiModel 3)) 2 2 (ιMulti ℝ 2 a)
      (ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![1,3] j))) =
      ιMulti ℝ 4 (Fin.append a (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![1,3] j))) := by
    apply Subtype.ext
    simp only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul, ιMulti_apply_coe]
    exact ExteriorAlgebra.ιMulti_mul_ιMulti _ _
  rw [hw, coordinateVolume_ιMulti]
  change (Matrix.of fun i j => Fin.append a (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![1,3] j)) i (Pi.single j 1)).det =
    (coMetric σ 3).exteriorPower 2 (ιMulti ℝ 2 (fun j => (Pi.basisFun ℝ (Fin 4)).dualBasis (![0,2] j))) (ιMulti ℝ 2 a)
  rw [LinearMap.BilinForm.bilinForm_ιMulti_ιMulti]
  rw [Matrix.det_succ_row_zero]
  cases σ <;> norm_num [-Basis.coe_dualBasis, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
    Matrix.submatrix_apply, coMetric_basis, Basis.coord_apply, lorentzSign, Fin.append, Fin.addCases,
    Pi.single_apply]
  all_goals norm_num [Basis.dualBasis_apply, Basis.coord_apply, Pi.single_apply, Fin.succAbove]

theorem hodge_dy_dz (σ : LorentzConvention) :
    hodgeFiber σ .standard (by decide : 2+2=3+1) (coordinateForm ![2,3]) =
      (coordinateForm ![0,1] : MinkowskiModel 3 [⋀^Fin 2]→L[ℝ] ℝ) := by
  have h := congrArg (hodgeFiber σ .standard (by decide : 2+2=3+1)) (hodge_dt_dx σ)
  rw [hodgeFiber_two_square, map_neg] at h
  exact neg_injective h.symm

theorem hodge_dx_dz (σ : LorentzConvention) :
    hodgeFiber σ .standard (by decide : 2+2=3+1) (coordinateForm ![1,3]) =
      -(coordinateForm ![0,2] : MinkowskiModel 3 [⋀^Fin 2]→L[ℝ] ℝ) := by
  have h := congrArg (hodgeFiber σ .standard (by decide : 2+2=3+1)) (hodge_dt_dy σ)
  rw [hodgeFiber_two_square] at h
  exact h.symm

theorem hodge_dx_dy (σ : LorentzConvention) :
    hodgeFiber σ .standard (by decide : 2+2=3+1) (coordinateForm ![1,2]) =
      (coordinateForm ![0,3] : MinkowskiModel 3 [⋀^Fin 2]→L[ℝ] ℝ) := by
  have h := congrArg (hodgeFiber σ .standard (by decide : 2+2=3+1)) (hodge_dt_dz σ)
  rw [hodgeFiber_two_square, map_neg] at h
  exact neg_injective h.symm

end ProjectAInos.SmoothGeometry.Minkowski
