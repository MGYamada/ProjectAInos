/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Minkowski.Dual
public import ProjectAInos.SmoothGeometry.DifferentialForm.HodgeBasis

/-! # Oriented Minkowski Hodge duality on continuous differential forms -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower
namespace ProjectAInos.SmoothGeometry.Minkowski
open DifferentialForm

/-- Spacetime orientation is independent of metric and time orientation. -/
inductive SpacetimeOrientation
  | standard
  | reversed
  deriving DecidableEq

def algebraicFlat (σ : LorentzConvention) (d : ℕ) :
    MinkowskiModel d ≃ₗ[ℝ] Dual ℝ (MinkowskiModel d) :=
  (flat σ).toLinearEquiv.trans LinearMap.toContinuousLinearMap.symm

def coMetricEquiv (σ : LorentzConvention) (d : ℕ) :
    Dual ℝ (MinkowskiModel d) ≃ₗ[ℝ] Dual ℝ (Dual ℝ (MinkowskiModel d)) :=
  (algebraicFlat σ d).symm.trans (Module.evalEquiv ℝ (MinkowskiModel d))

def coMetric (σ : LorentzConvention) (d : ℕ) : LinearMap.BilinForm ℝ (Dual ℝ (MinkowskiModel d)) :=
  (coMetricEquiv σ d).toLinearMap

theorem coMetric_bijective (σ : LorentzConvention) (d : ℕ) : Function.Bijective (coMetric σ d) :=
  (coMetricEquiv σ d).bijective

theorem coMetric_symmetric (σ : LorentzConvention) (d : ℕ) : (coMetric σ d).IsSymm := by
  constructor
  intro α β
  obtain ⟨v, rfl⟩ := (algebraicFlat σ d).surjective α
  obtain ⟨w, rfl⟩ := (algebraicFlat σ d).surjective β
  change (algebraicFlat σ d w) ((algebraicFlat σ d).symm (algebraicFlat σ d v)) =
    (algebraicFlat σ d v) ((algebraicFlat σ d).symm (algebraicFlat σ d w))
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact minkowskiForm_symmetric σ w v

/-- Normalize the volume by the ordered coordinate covector basis. -/
def coordinateVolume (n : ℕ) : ExteriorCovector n n ≃ₗ[ℝ] ℝ :=
  basisVolumeDegree (Pi.basisFun ℝ (Fin n)).dualBasis n (by simp)

def volume (o : SpacetimeOrientation) (d : ℕ) :
    ⋀[ℝ]^(Module.finrank ℝ (Dual ℝ (MinkowskiModel d))) (Dual ℝ (MinkowskiModel d)) ≃ₗ[ℝ] ℝ :=
  match o with
  | .standard => basisVolume (Pi.basisFun ℝ (Fin (d+1))).dualBasis
  | .reversed => (basisVolume (Pi.basisFun ℝ (Fin (d+1))).dualBasis).trans (LinearEquiv.neg ℝ)

def hodgeFiber (σ : LorentzConvention) (o : SpacetimeOrientation) {d k l : ℕ}
    (hkl : k+l = d+1) :
    (MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) ≃L[ℝ] (MinkowskiModel d [⋀^Fin l]→L[ℝ] ℝ) :=
  (toExterior.trans ((DifferentialForm.hodge (coMetric σ d) (coMetric_bijective σ d)
    (volume o d) (by simpa [MinkowskiModel] using hkl)).trans toExterior.symm)).toContinuousLinearEquiv

@[simp] theorem toExterior_hodgeFiber (σ : LorentzConvention) (o : SpacetimeOrientation)
    {d k l : ℕ} (hkl : k+l=d+1) (α : MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) :
    toExterior (hodgeFiber σ o hkl α) =
      DifferentialForm.hodge (coMetric σ d) (coMetric_bijective σ d) (volume o d)
        (by simpa [MinkowskiModel] using hkl) (toExterior α) :=
  toExterior.apply_symm_apply _

/-- The defining Hodge equation on continuous alternating forms, evaluated by
oriented volume. The right side is the exterior power of the inverse metric. -/
theorem hodgeFiber_pairing (σ : LorentzConvention) (o : SpacetimeOrientation)
    {d k l : ℕ} (hkl : k+l=d+1) (α β : MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) :
    wedgePairing (volume o d) (by simpa [MinkowskiModel] using hkl)
      (toExterior α) (toExterior (hodgeFiber σ o hkl β)) =
      (coMetric σ d).exteriorPower k (toExterior α) (toExterior β) := by
  rw [toExterior_hodgeFiber]
  exact hodge_pairing_symmetric _ _ _ (coMetric_symmetric σ d) _ _ _

def hodgeForm (σ : LorentzConvention) (o : SpacetimeOrientation) {d k l : ℕ}
    (hkl : k+l = d+1) (ω : Form (MinkowskiModel d) k) : Form (MinkowskiModel d) l :=
  fun x => hodgeFiber σ o hkl (ω x)

theorem hodgeForm_contDiff (σ : LorentzConvention) (o : SpacetimeOrientation) {d k l : ℕ}
    (hkl : k+l = d+1) (ω : Form (MinkowskiModel d) k) {r : WithTop ℕ∞}
    (hω : ContDiff ℝ r ω) : ContDiff ℝ r (hodgeForm σ o hkl ω) :=
  (hodgeFiber σ o hkl).contDiff.comp hω

theorem coMetric_basis (σ : LorentzConvention) (d : ℕ) (i : Fin (d+1)) :
    coMetric σ d ((Pi.basisFun ℝ (Fin (d+1))).dualBasis i) =
      lorentzSign σ i • ((Pi.basisFun ℝ (Fin (d+1))).dualBasis).coord i := by
  have hv : algebraicFlat σ d (lorentzSign σ i • Pi.single i 1) =
      (Pi.basisFun ℝ (Fin (d+1))).dualBasis i := by
    apply LinearMap.ext
    intro w
    change minkowskiForm σ d (lorentzSign σ i • Pi.single i 1) w = _
    simp [minkowskiForm_apply, Pi.single_apply, mul_ite,
      ← mul_assoc]
  apply LinearMap.ext
  intro α
  rw [← hv]
  change α ((algebraicFlat σ d).symm (algebraicFlat σ d (lorentzSign σ i • Pi.single i 1))) = _
  rw [LinearEquiv.symm_apply_apply, map_smul]
  simp [Basis.coord_apply]

theorem coMetric_opposite (σ : LorentzConvention) (d : ℕ) : coMetric σ.opposite d = -coMetric σ d := by
  apply (Pi.basisFun ℝ (Fin (d+1))).dualBasis.ext
  intro i
  simp only [LinearMap.neg_apply, coMetric_basis, lorentzSign_opposite]
  exact _root_.neg_smul (lorentzSign σ i) ((Pi.basisFun ℝ (Fin (d+1))).dualBasis.coord i)

theorem lorentzSign_product (σ : LorentzConvention) (d : ℕ) :
    (∏ i : Fin (d+1), lorentzSign σ i) = (-1 : ℝ)^(σ.negativeIndex d) := by
  cases σ <;> simp [Fin.prod_univ_succ, lorentzSign, LorentzConvention.negativeIndex]

theorem hodgeFiber_reverse {d k l : ℕ} (σ : LorentzConvention) (hkl : k+l = d+1)
    (α : MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) :
    hodgeFiber σ .reversed hkl α = -hodgeFiber σ .standard hkl α := by
  change toExterior.symm (DifferentialForm.hodge _ _ _ _ (toExterior α)) = _
  rw [show volume .reversed d = (volume .standard d).trans (LinearEquiv.neg ℝ) from rfl,
    hodge_reverse_volume, map_neg]
  rfl

theorem hodgeFiber_opposite {d k l : ℕ} (σ : LorentzConvention) (o : SpacetimeOrientation)
    (hkl : k+l = d+1) (α : MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) :
    hodgeFiber σ.opposite o hkl α = (-1 : ℝ)^k • hodgeFiber σ o hkl α := by
  have hc : coMetric σ.opposite d = (-1 : ℝ) • coMetric σ d := by
    exact (coMetric_opposite σ d).trans (_root_.neg_one_smul ℝ (coMetric σ d)).symm
  unfold hodgeFiber
  simp only [LinearEquiv.coe_toContinuousLinearEquiv', LinearEquiv.trans_apply]
  rw [hodge_smul_metric_of_eq (coMetric σ d) (coMetric_bijective σ d) (volume o d)
    (coMetric σ.opposite d) (coMetric_bijective σ.opposite d) (-1) hc, map_smul]

theorem hodgeFiber_square {d k l : ℕ} (σ : LorentzConvention) (o : SpacetimeOrientation)
    (hkl : k+l = d+1) (hlk : l+k = d+1) (α : MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) :
    hodgeFiber σ o hlk (hodgeFiber σ o hkl α) = (-1 : ℝ)^(k*l+σ.negativeIndex d) • α := by
  have H (β : MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) :
      hodgeFiber σ .standard hlk (hodgeFiber σ .standard hkl β) =
        (-1 : ℝ)^(k*l+σ.negativeIndex d) • β := by
    change toExterior.symm (DifferentialForm.hodge _ _ _ _
      (toExterior (toExterior.symm (DifferentialForm.hodge _ _ _ _ (toExterior β))))) = _
    rw [LinearEquiv.apply_symm_apply]
    rw [hodge_square_orthogonal (Pi.basisFun ℝ (Fin (d+1))).dualBasis
      (coMetric σ d) (lorentzSign σ) (coMetricEquiv σ d).bijective (coMetric_basis σ d)
      (volume .standard d) (basisVolume_top _)]
    rw [lorentzSign_product, ← pow_add, map_smul, LinearEquiv.symm_apply_apply]
  cases o with
  | standard => exact H α
  | reversed => rw [hodgeFiber_reverse, hodgeFiber_reverse, map_neg, neg_neg, H]

theorem hodgeFiber_two_square (σ : LorentzConvention) (o : SpacetimeOrientation)
    (α : MinkowskiModel 3 [⋀^Fin 2]→L[ℝ] ℝ) :
    hodgeFiber σ o (by decide : 2+2=3+1) (hodgeFiber σ o (by decide) α) = -α := by
  rw [hodgeFiber_square]
  cases σ <;> norm_num [LorentzConvention.negativeIndex]
    <;> exact _root_.neg_one_smul ℝ α

theorem hodgeFiber_two_opposite (σ : LorentzConvention) (o : SpacetimeOrientation)
    (α : MinkowskiModel 3 [⋀^Fin 2]→L[ℝ] ℝ) :
    hodgeFiber σ.opposite o (by decide : 2+2=3+1) α = hodgeFiber σ o (by decide) α := by
  rw [hodgeFiber_opposite]
  norm_num

end ProjectAInos.SmoothGeometry.Minkowski
