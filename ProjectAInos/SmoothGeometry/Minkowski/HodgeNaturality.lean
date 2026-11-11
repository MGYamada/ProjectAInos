/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ProjectAInos.SmoothGeometry.Minkowski.Hodge
public import ProjectAInos.SmoothGeometry.Minkowski.Isometry
public import ProjectAInos.SmoothGeometry.DifferentialForm.Naturality

/-! # Hodge duality commutes with proper Lorentz pullbacks -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower
namespace ProjectAInos.SmoothGeometry.Minkowski
open DifferentialForm
variable {d k l : ℕ}

theorem algebraicFlat_pullback (σ : LorentzConvention) (L : LorentzGroup d) (v : MinkowskiModel d) :
    L.val.dualMap (algebraicFlat σ d v) = algebraicFlat σ d (L.val.symm v) := by
  apply LinearMap.ext
  intro w
  change minkowskiForm σ d v (L.val w) = minkowskiForm σ d (L.val.symm v) w
  simpa using LorentzGroup.preserves_metric L σ (L.val.symm v) w

theorem coMetric_flat (σ : LorentzConvention) (v w : MinkowskiModel d) :
    coMetric σ d (algebraicFlat σ d v) (algebraicFlat σ d w) = minkowskiForm σ d v w := by
  change (algebraicFlat σ d w) ((algebraicFlat σ d).symm (algebraicFlat σ d v)) = _
  rw [LinearEquiv.symm_apply_apply]
  exact minkowskiForm_symmetric σ w v

theorem coMetric_pullback (σ : LorentzConvention) (L : LorentzGroup d)
    (α β : Dual ℝ (MinkowskiModel d)) :
    coMetric σ d (L.val.dualMap α) (L.val.dualMap β) = coMetric σ d α β := by
  obtain ⟨v, rfl⟩ := (algebraicFlat σ d).surjective α
  obtain ⟨w, rfl⟩ := (algebraicFlat σ d).surjective β
  rw [algebraicFlat_pullback, algebraicFlat_pullback, coMetric_flat, coMetric_flat]
  exact LorentzGroup.preserves_metric L⁻¹ σ v w

theorem hodgeFiber_pullback (σ : LorentzConvention) (o : SpacetimeOrientation)
    (hkl : k+l=d+1) (L : properLorentzGroup d)
    (ω : MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) :
    hodgeFiber σ o hkl (ω.compContinuousLinearMap (LorentzGroup.toContinuousLinearEquiv L.val).toContinuousLinearMap) =
      (hodgeFiber σ o hkl ω).compContinuousLinearMap (LorentzGroup.toContinuousLinearEquiv L.val).toContinuousLinearMap := by
  have hd : L.val.val.toLinearMap.det = 1 := by
    have h := L.property
    change L.val.val.det = 1 at h
    simpa only [LinearEquiv.coe_det, Units.val_one] using congrArg Units.val h
  have hdual : L.val.val.dualMap.toLinearMap.det = 1 := by
    change L.val.val.toLinearMap.dualMap.det = 1
    rw [LinearMap.det_dualMap, hd]
  change toExterior.symm (hodge _ _ _ _ (toExterior (ω.compContinuousLinearMap _))) = _
  rw [toExterior_comp]
  change toExterior.symm (hodge _ _ _ _ (exteriorPower.map k L.val.val.dualMap.toLinearMap (toExterior ω))) = _
  rw [hodge_isometry (coMetric σ d) (coMetric_bijective σ d) (volume o d) _
    L.val.val.dualMap (coMetric_pullback σ L.val) hdual]
  exact fromExterior_map_dual (LorentzGroup.toContinuousLinearEquiv L.val).toContinuousLinearMap _

/-- The pointwise Hodge operation commutes with pullback of form fields. -/
theorem hodgeForm_pullback (σ : LorentzConvention) (o : SpacetimeOrientation)
    (hkl : k+l=d+1) (L : properLorentzGroup d) (ω : Form (MinkowskiModel d) k) :
    hodgeForm σ o hkl (pullback L.val.val ω) = pullback L.val.val (hodgeForm σ o hkl ω) := by
  funext x
  change hodgeFiber σ o hkl ((ω (L.val.val x)).compContinuousLinearMap
      (fderiv ℝ L.val.val x)) =
    (hodgeFiber σ o hkl (ω (L.val.val x))).compContinuousLinearMap (fderiv ℝ L.val.val x)
  have hd : fderiv ℝ L.val.val x =
      (LorentzGroup.toContinuousLinearEquiv L.val).toContinuousLinearMap :=
    (LorentzGroup.toContinuousLinearEquiv L.val).toContinuousLinearMap.fderiv
  rw [hd]
  exact hodgeFiber_pullback σ o hkl L _

end ProjectAInos.SmoothGeometry.Minkowski
