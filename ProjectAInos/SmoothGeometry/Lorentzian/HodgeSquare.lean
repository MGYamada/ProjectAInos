/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.HodgeSmooth

/-! # Lorentz Hodge square without a global frame

A pointwise signature witness is sufficient. Its oriented volume is a
sign, and this sign cancels in the square. No flatness is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open DifferentialForm

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

/-- The orientation sign of a pointwise Lorentz frame. -/
def frameVolume (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (x : M)
    (L : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d) : ℝ :=
  g.volumeForm o x (fun i => L.symm (Pi.single i 1))

theorem frameVolume_sq (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (x : M)
    (L : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d)
    (hL : ∀ v w, g.form x v w = minkowskiForm σ d (L v) (L w)) :
    g.frameVolume o x L ^ 2 = 1 := by
  have h := g.abs_volumeForm o x (fun i => L.symm (Pi.single i 1))
  change |g.frameVolume o x L| = _ at h
  have hG : MetricDensity.gram (g.form x).toLinearMap₁₂ (fun i => L.symm (Pi.single i 1)) =
      Minkowski.metricMatrix σ d := by
    rw [← Minkowski.metricMatrix_eq]
    ext i j
    change g.form x (L.symm (Pi.single i 1)) (L.symm (Pi.single j 1)) = _
    rw [hL, L.apply_symm_apply, L.apply_symm_apply]
    rfl
  change |g.frameVolume o x L| = Real.sqrt |(MetricDensity.gram _ _).det| at h
  rw [hG, LorentzianVolumeExamples.minkowski_abs_det, Real.sqrt_one] at h
  calc
    _ = |g.frameVolume o x L| ^ 2 := (sq_abs _).symm
    _ = 1 := by rw [h]; norm_num

/-- The signed volume in a pointwise frame is exactly a multiple of coordinate volume. -/
theorem frameVolume_form (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (x : M)
    (L : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d) :
    g.frameVolume o x L • (coordinateForm (n := d + 1) id).compContinuousLinearMap
      L.toContinuousLinearMap = g.volumeForm o x := by
  apply nativeTopForm_ext_basis ((Pi.basisFun ℝ (Fin (d + 1))).map L.symm.toLinearEquiv)
  change g.frameVolume o x L * coordinateForm id
    (fun i => L (((Pi.basisFun ℝ (Fin (d + 1))).map L.symm.toLinearEquiv) i)) = _
  have hb : (fun i => L (((Pi.basisFun ℝ (Fin (d + 1))).map L.symm.toLinearEquiv) i)) =
      Pi.basisFun ℝ (Fin (d + 1)) := by funext i; simp
  rw [hb]
  have hc : coordinateForm (n := d + 1) id (Pi.basisFun ℝ (Fin (d + 1))) = 1 := by
    rw [← Minkowski.coordinateVolume_toExterior, Minkowski.coordinateVolume_coordinateForm]
  rw [hc, mul_one]
  unfold frameVolume
  apply congrArg (g.volumeForm o x)
  funext i
  simp only [Basis.map_apply, Pi.basisFun_apply]
  rfl

/-- Intrinsic Hodge in any pointwise Lorentz frame, including its orientation sign. -/
theorem hodgeFiber_frame (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (x : M)
    (L : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d)
    (hL : ∀ v w, g.form x v w = minkowskiForm σ d (L v) (L w))
    {k l : ℕ} (hkl : k + l = d + 1) (β : MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) :
    g.hodgeFiber o x hkl (β.compContinuousLinearMap L.toContinuousLinearMap) =
      g.frameVolume o x L • (Minkowski.hodgeFiber σ .standard hkl β).compContinuousLinearMap
        L.toContinuousLinearMap := by
  let h := minkowskiMetric σ d
  let o₀ := OrientedAtlas.standard (d + 1)
  have hv : g.frameVolume o x L • (h.volumeForm o₀ 0).compContinuousLinearMap
      L.toContinuousLinearMap = g.volumeForm o x := by
    rw [LorentzianVolumeExamples.minkowski_volume]
    exact g.frameVolume_form o x L
  have hm : ∀ α β : Dual ℝ (MinkowskiModel d),
      h.coMetric 0 ((ContinuousLinearMap.id ℝ (MinkowskiModel d)).toLinearMap.dualMap α) β =
        g.coMetric x (L.toLinearMap.dualMap α) (L.toLinearMap.dualMap β) := by
    intro α β
    exact (g.coMetric_naturality h x 0 L hL α β).symm
  have hh := finiteHodgeOfDegree_formula (g.coMetric x) (g.coMetric_bijective x)
    (h.coMetric 0) (h.coMetric_bijective 0) (g.volumeForm o x) (g.volumeForm_ne_zero o x)
    (cotangent_topDegree x) (h.volumeForm o₀ 0) (h.volumeForm_ne_zero o₀ 0)
    (cotangent_topDegree (M := MinkowskiModel d) 0) L (ContinuousLinearMap.id ℝ (MinkowskiModel d))
    (g.frameVolume o x L) hm hv hkl β
  change g.hodgeFiber o x hkl _ = _ • (h.hodgeFiber o₀ 0 hkl _).compContinuousLinearMap _ at hh
  rw [minkowskiMetric_hodgeFiber] at hh
  have hβ : β.compContinuousLinearMap (ContinuousLinearMap.id ℝ (MinkowskiModel d)) = β := by
    ext v
    rfl
  rw [hβ] at hh
  exact hh

/-- The general Lorentz square identity holds at every point, without flatness or a global frame. -/
theorem hodgeFiber_square (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (x : M)
    {k l : ℕ} (hkl : k + l = d + 1) (hlk : l + k = d + 1)
    (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x [⋀^Fin k]→L[ℝ] ℝ) :
    g.hodgeFiber o x hlk (g.hodgeFiber o x hkl α) =
      (-1 : ℝ) ^ (k * l + σ.negativeIndex d) • α := by
  obtain ⟨L, hL⟩ := g.signature x
  let β := α.compContinuousLinearMap L.symm.toContinuousLinearMap
  have hβ : β.compContinuousLinearMap L.toContinuousLinearMap = α := by
    ext v
    change α (fun i => L.symm (L (v i))) = α v
    simp
  rw [← hβ, g.hodgeFiber_frame o x L hL hkl, map_smul, g.hodgeFiber_frame o x L hL hlk,
    Minkowski.hodgeFiber_square, smul_smul]
  have hr : g.frameVolume o x L * g.frameVolume o x L = 1 := by
    simpa only [pow_two] using g.frameVolume_sq o x L hL
  rw [hr, one_smul]
  rfl

/-- The square formula is an equality of smooth native sections. -/
theorem smoothHodge_square (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    {k l : ℕ} (hkl : k + l = d + 1) (hlk : l + k = d + 1)
    (α : SmoothForm 𝓘(ℝ, MinkowskiModel d) M k) :
    g.smoothHodge o hlk (g.smoothHodge o hkl α) =
      (-1 : ℝ) ^ (k * l + σ.negativeIndex d) • α := by
  ext x : 1
  exact g.hodgeFiber_square o x hkl hlk (α x)

end ProjectAInos.SmoothGeometry.LorentzMetric
