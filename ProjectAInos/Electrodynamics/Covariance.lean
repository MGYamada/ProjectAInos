module
public import ProjectAInos.Electrodynamics.Invariants
import all Mathlib.LinearAlgebra.ExteriorPower.BilinForm

/-! # Lorentz covariance and orientation of the electromagnetic invariants -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
open Module exteriorPower
namespace ProjectAInos.Electrodynamics
open SmoothGeometry SmoothGeometry.Minkowski SmoothGeometry.DifferentialForm SpecialRelativity

def exteriorPairing (F G : TwoForm) : ℝ :=
  (coMetric .timeNegative 3).exteriorPower 2 (toExterior F) (toExterior G)

theorem exteriorPairing_coordinates (F G : TwoForm) :
    exteriorPairing F G = (1 / 2 : ℝ) * tensorContraction F G := by
  rw [tensorContraction_coordinates]
  unfold exteriorPairing
  conv_lhs => rw [twoForm_expansion F, twoForm_expansion G]
  simp [-Basis.coe_dualBasis, twoFormExpansion, coordinateForm, ofCovectors,
    LinearMap.BilinForm.bilinForm_ιMulti_ιMulti, Matrix.det_fin_two,
    coMetric_basis, Basis.coord_apply, lorentzSign]
  ring

def lorentzPullback (L : LorentzGroup 3) (F : TwoForm) : TwoForm :=
  F.compContinuousLinearMap (LorentzGroup.toContinuousLinearEquiv L).toContinuousLinearMap

theorem exteriorPairing_lorentz (L : LorentzGroup 3) (F G : TwoForm) :
    exteriorPairing (lorentzPullback L F) (lorentzPullback L G) = exteriorPairing F G := by
  unfold exteriorPairing lorentzPullback
  rw [toExterior_comp, toExterior_comp]
  exact exteriorPower_isometry (coMetric .timeNegative 3) L.val.dualMap.toLinearMap
    (coMetric_pullback .timeNegative L) _ _

theorem scalarInvariant_lorentz (L : LorentzGroup 3) (F : TwoForm) :
    scalarInvariant (lorentzPullback L F) = scalarInvariant F := by
  change (1 / 2 : ℝ) * tensorContraction _ _ = (1 / 2 : ℝ) * tensorContraction _ _
  rw [← exteriorPairing_coordinates, ← exteriorPairing_coordinates, exteriorPairing_lorentz]

theorem star_properLorentz (L : properLorentzGroup 3) (F : TwoForm) :
    star (lorentzPullback L.val F) = lorentzPullback L.val (star F) :=
  hodgeFiber_pullback .timeNegative .standard (by decide) L F

theorem pseudoscalarInvariant_properLorentz (L : properLorentzGroup 3) (F : TwoForm) :
    pseudoscalarInvariant (lorentzPullback L.val F) = pseudoscalarInvariant F := by
  have he (G : TwoForm) : pseudoscalarInvariant G = (1 / 2 : ℝ) * exteriorPairing G (star G) := by
    rw [exteriorPairing_coordinates]
    unfold pseudoscalarInvariant
    ring
  rw [he, he, star_properLorentz, exteriorPairing_lorentz]

theorem pseudoscalarInvariant_wedge (F : TwoForm) :
    pseudoscalarInvariant F = -(1 / 2 : ℝ) *
      wedgePairing (volume .standard 3) (by norm_num [MinkowskiModel]) (toExterior F) (toExterior F) := by
  have h := hodgeFiber_pairing .timeNegative .standard (by decide : 2 + 2 = 3 + 1) F (star F)
  have hs : hodgeFiber .timeNegative .standard (by decide : 2 + 2 = 3 + 1) (star F) = -F :=
    hodgeFiber_two_square .timeNegative .standard F
  rw [hs, map_neg, map_neg] at h
  change -wedgePairing (volume .standard 3) _ (toExterior F) (toExterior F) = exteriorPairing F (star F) at h
  rw [exteriorPairing_coordinates] at h
  unfold pseudoscalarInvariant
  linarith

/-- Every Lorentz map preserves the scalar; the pseudoscalar picks up det L.
In particular an orientation-reversing map changes its sign. -/
theorem pseudoscalarInvariant_lorentz (L : LorentzGroup 3) (F : TwoForm) :
    pseudoscalarInvariant (lorentzPullback L F) =
      L.val.toLinearMap.det * pseudoscalarInvariant F := by
  rw [pseudoscalarInvariant_wedge, pseudoscalarInvariant_wedge]
  simp only [lorentzPullback, toExterior_comp]
  rw [wedgePairing_map]
  change -(1 / 2 : ℝ) * (L.val.toLinearMap.dualMap.det * _) = _
  rw [LinearMap.det_dualMap]
  ring

theorem pseudoscalarInvariant_orientationReversing (L : LorentzGroup 3)
    (hL : L.val.toLinearMap.det = -1) (F : TwoForm) :
    pseudoscalarInvariant (lorentzPullback L F) = -pseudoscalarInvariant F := by
  rw [pseudoscalarInvariant_lorentz, hL, neg_one_mul]

end ProjectAInos.Electrodynamics
