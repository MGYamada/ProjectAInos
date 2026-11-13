/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurveMetric

/-! # Smooth inverse metric in actual local charts -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

/-- The coordinate metric is the conjugate of native metric duality. -/
def chartFlat (g : LorentzMetric σ d M) {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source) :
    MinkowskiModel d ≃L[ℝ] (MinkowskiModel d →L[ℝ] ℝ) :=
  ((chartTangentEquiv he hx).symm.trans (g.flat x)).trans
    ((chartTangentEquiv he hx).arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))

theorem chartFlat_apply (g : LorentzMetric σ d M) {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source)
    (v w : MinkowskiModel d) : g.chartFlat he hx v w = g.chartMetric e x v w := by
  change g.form x ((chartTangentEquiv he hx).symm v) ((chartTangentEquiv he hx).symm w) = _
  simp only [chartTangentEquiv_symm, chartMetric_apply]

theorem chartFlat_toContinuousLinearMap (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source) :
    (g.chartFlat he hx).toContinuousLinearMap = g.chartMetric e x := by
  ext v w
  exact g.chartFlat_apply he hx v w

theorem chartMetric_isInvertible (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source) :
    (g.chartMetric e x).IsInvertible := ⟨g.chartFlat he hx, g.chartFlat_toContinuousLinearMap he hx⟩

/-- Coordinate inverse metric, with its geometric interpretation valid on the chart source. -/
def chartSharp (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M (MinkowskiModel d)) (x : M) :
    (MinkowskiModel d →L[ℝ] ℝ) →L[ℝ] MinkowskiModel d := (g.chartMetric e x).inverse

theorem chartSharp_apply (g : LorentzMetric σ d M) {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source)
    (α : MinkowskiModel d →L[ℝ] ℝ) :
    g.chartSharp e x α = chartTangentEquiv he hx
      (g.sharp x (α.comp (chartTangentEquiv he hx).toContinuousLinearMap)) := by
  apply (g.chartMetric_isInvertible he hx).injective
  rw [chartSharp, IsInvertible.self_apply_inverse (g.chartMetric_isInvertible he hx)]
  ext v
  rw [← g.chartFlat_apply he hx]
  change α v = g.form x
    ((chartTangentEquiv he hx).symm (chartTangentEquiv he hx
      (g.sharp x (α.comp (chartTangentEquiv he hx).toContinuousLinearMap))))
    ((chartTangentEquiv he hx).symm v)
  rw [ContinuousLinearEquiv.symm_apply_apply, g.form_sharp_left]
  simp [chartTangentMap_field he hx]

/-- Inverse metric coefficients are smooth locally, with norms only on coordinate models. -/
theorem chartSharp_contMDiffAt (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, (MinkowskiModel d →L[ℝ] ℝ) →L[ℝ] MinkowskiModel d)
      ∞ (g.chartSharp e) x :=
  (g.chartMetric_isInvertible he hx).contDiffAt_map_inverse.contMDiffAt.comp x
    (g.chartMetric_contMDiffAt he hx)

end ProjectAInos.SmoothGeometry.LorentzMetric
