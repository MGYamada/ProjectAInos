/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.HodgeFiber
public import ProjectAInos.SmoothGeometry.Lorentzian.VolumeExamples
public import ProjectAInos.SmoothGeometry.Minkowski.HodgeFour

/-! # Exact comparison of native Lorentz and flat Minkowski Hodge -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module exteriorPower
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry
open DifferentialForm

namespace Minkowski

/-- The standard top-covector functional evaluates the form on the ordered coordinate basis. -/
theorem coordinateVolume_eq_pairing (n : ℕ) :
    (coordinateVolume n).toLinearMap =
      (pairingDual ℝ (Fin n → ℝ) n).flip (ιMulti ℝ n (Pi.basisFun ℝ (Fin n))) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro a
  change coordinateVolume n (ιMulti ℝ n a) =
    pairingDual ℝ (Fin n → ℝ) n (ιMulti ℝ n a) (ιMulti ℝ n (Pi.basisFun ℝ (Fin n)))
  rw [coordinateVolume_ιMulti, pairingDual_ιMulti_ιMulti, ← Matrix.det_transpose]
  congr 1
  ext i j
  simp [Pi.basisFun_apply]

theorem coordinateVolume_toExterior (n : ℕ) (α : (Fin n → ℝ) [⋀^Fin n]→L[ℝ] ℝ) :
    coordinateVolume n (toExterior α) = α (Pi.basisFun ℝ (Fin n)) := by
  change (coordinateVolume n).toLinearMap (toExterior α) = _
  rw [coordinateVolume_eq_pairing]
  exact pairing_toExterior α _

theorem coordinateVolume_coordinateForm (n : ℕ) : coordinateVolume n (toExterior (coordinateForm id)) = 1 := by
  rw [coordinateVolume_toExterior, coordinateForm_apply]
  have h : (Matrix.of fun i j : Fin n => (Pi.basisFun ℝ (Fin n)) i (id j)) =
      (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    simp [Pi.basisFun_apply, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [h, Matrix.det_one]

/-- The top-degree transport in the flat volume agrees with the fixed coordinate degree. -/
theorem volume_standard_cast (d : ℕ)
    (h : d + 1 = Module.finrank ℝ (Dual ℝ (MinkowskiModel d)))
    (α : ExteriorCovector (d + 1) (d + 1)) :
    volume .standard d (h ▸ α) = coordinateVolume (d + 1) α := by
  let b := (Pi.basisFun ℝ (Fin (d + 1))).dualBasis
  have hh := basisVolumeDegree_cast b h (Module.finrank_eq_card_basis b) α
  have cast_apply {i j : ℕ} (hij : i = j)
      (f : ⋀[ℝ]^j (Dual ℝ (MinkowskiModel d)) →ₗ[ℝ] ℝ)
      (z : ⋀[ℝ]^i (Dual ℝ (MinkowskiModel d))) :
      (hij.symm ▸ f) z = f (hij ▸ z) := by subst j; rfl
  rw [cast_apply h] at hh
  exact hh

end Minkowski

namespace LorentzMetric

theorem minkowskiMetric_algebraicFlat (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d) :
    (minkowskiMetric σ d).algebraicFlat x = Minkowski.algebraicFlat σ d := by
  ext v w
  rfl

theorem minkowskiMetric_coMetric (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d) :
    (minkowskiMetric σ d).coMetric x = Minkowski.coMetric σ d := by
  unfold coMetric coMetricEquiv
  rw [minkowskiMetric_algebraicFlat]
  rfl

theorem minkowski_hodgeVolume_normalized (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d) :
    Minkowski.volume .standard d (finiteToExterior
      ((minkowskiMetric σ d).hodgeTopVolume (OrientedAtlas.standard (d + 1)) x)) = 1 := by
  unfold hodgeTopVolume
  rw [LorentzianVolumeExamples.minkowski_volume, finiteToExterior_degreeCast,
    Minkowski.volume_standard_cast, finiteToExterior_model, Minkowski.coordinateVolume_coordinateForm]

theorem minkowski_finiteVolumeFunctional (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d) :
    finiteVolumeFunctional ((minkowskiMetric σ d).hodgeTopVolume (OrientedAtlas.standard (d + 1)) x)
      ((minkowskiMetric σ d).hodgeTopVolume_ne_zero (OrientedAtlas.standard (d + 1)) x) =
        Minkowski.volume .standard d := by
  apply LinearEquiv.toLinearMap_injective
  symm
  apply exteriorVolume_unique
  exact minkowski_hodgeVolume_normalized σ d x

/-- The native construction agrees exactly with the established flat Hodge API. -/
theorem minkowskiMetric_hodgeFiber (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d)
    {k l : ℕ} (hkl : k + l = d + 1) (α : MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) :
    (minkowskiMetric σ d).hodgeFiber (OrientedAtlas.standard (d + 1)) x hkl α =
      Minkowski.hodgeFiber σ .standard hkl α := by
  apply toExterior.injective
  rw [Minkowski.toExterior_hodgeFiber]
  change finiteToExterior (finiteHodge ((minkowskiMetric σ d).coMetric x)
    ((minkowskiMetric σ d).coMetric_bijective x)
    ((minkowskiMetric σ d).hodgeTopVolume (OrientedAtlas.standard (d + 1)) x) _ _ α) = _
  rw [finiteToExterior_hodge]
  have h := hodge_congr_data ((minkowskiMetric σ d).coMetric x) (Minkowski.coMetric σ d)
    ((minkowskiMetric σ d).coMetric_bijective x) (Minkowski.coMetric_bijective σ d)
    (minkowskiMetric_coMetric σ d x) _ _ (minkowski_finiteVolumeFunctional σ d x)
    (hkl.trans (cotangent_topDegree x))
  exact congrArg (fun f : ExteriorCovector (d + 1) k ≃ₗ[ℝ] ExteriorCovector (d + 1) l =>
    f (toExterior α)) h

end LorentzMetric

end ProjectAInos.SmoothGeometry
