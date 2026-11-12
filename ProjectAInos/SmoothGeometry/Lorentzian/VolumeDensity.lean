/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.MetricDensity
public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurveMetric

/-! # Smooth Lorentz volume density on actual tangent spaces

Density is defined intrinsically by a Gram determinant. Smooth chart
coefficients and their absolute-Jacobian overlap law are consequences.
No orientation or global frame is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Module Bundle
open scoped Manifold ContDiff Topology BigOperators

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

/-- The Lorentz metric is nondegenerate as an algebraic bilinear form on each native fibre. -/
theorem algebraicForm_nondegenerate (g : LorentzMetric σ d M) (x : M) :
    (g.form x).toLinearMap₁₂.Nondegenerate := by
  constructor
  · exact g.nondegenerate x
  · intro v hv
    apply g.nondegenerate x v
    intro w
    rw [g.symmetric]
    exact hv w

/-- Orientation-free volume density evaluated on an ordered family of native tangent vectors. -/
def volumeDensity (g : LorentzMetric σ d M) (x : M)
    (v : Fin (d + 1) → TangentSpace 𝓘(ℝ, MinkowskiModel d) x) : ℝ :=
  MetricDensity.value (g.form x).toLinearMap₁₂ v

theorem volumeDensity_nonneg (g : LorentzMetric σ d M) (x : M)
    (v : Fin (d + 1) → TangentSpace 𝓘(ℝ, MinkowskiModel d) x) : 0 ≤ g.volumeDensity x v :=
  MetricDensity.value_nonneg _ _

theorem volumeDensity_change (g : LorentzMetric σ d M) (x : M)
    (v : Fin (d + 1) → TangentSpace 𝓘(ℝ, MinkowskiModel d) x)
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ) :
    g.volumeDensity x (fun i => ∑ j, A j i • v j) = |A.det| * g.volumeDensity x v :=
  MetricDensity.value_change _ _ _

theorem volumeDensity_basis_pos (g : LorentzMetric σ d M) (x : M)
    (b : Basis (Fin (d + 1)) ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x)) :
    0 < g.volumeDensity x b := MetricDensity.value_basis_pos _ (g.algebraicForm_nondegenerate x) b

/-- A pointwise metric-preserving tangent map preserves the intrinsic volume density. -/
theorem volumeDensity_naturality (g : LorentzMetric σ d M)
    {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
    [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N] (h : LorentzMetric σ d N) (x : M) (y : N)
    (L : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →ₗ[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    (hL : ∀ u w, h.form y (L u) (L w) = g.form x u w)
    (v : Fin (d + 1) → TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    h.volumeDensity y (L ∘ v) = g.volumeDensity x v := by
  unfold volumeDensity MetricDensity.value
  congr 3
  ext i j
  exact hL _ _

@[simp] theorem opposite_volumeDensity (g : LorentzMetric σ d M) (x : M)
    (v : Fin (d + 1) → TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.opposite.volumeDensity x v = g.volumeDensity x v := by
  have h : (g.opposite.form x).toLinearMap₁₂ = -(g.form x).toLinearMap₁₂ := by ext u w; rfl
  unfold volumeDensity
  rw [h, MetricDensity.value_neg]

/-- The coordinate basis is an actual basis of the native tangent fibre on the chart source. -/
def chartBasis {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source) :
    Basis (Fin (d + 1)) ℝ (TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :=
  (Pi.basisFun ℝ (Fin (d + 1))).map (chartTangentEquiv he hx).symm.toLinearEquiv

omit [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M] in
@[simp] theorem chartBasis_apply {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source)
    (i : Fin (d + 1)) : chartBasis he hx i = chartField e (Pi.single i 1) x := by
  simp [chartBasis, chartTangentEquiv_symm, Pi.basisFun_apply]

omit [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M] in
@[simp] theorem chartBasis_repr {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) (i : Fin (d + 1)) :
    (chartBasis he hx).repr v i = chartTangentMap e x v i := by
  simp [chartBasis, chartTangentEquiv_apply]

/-- The usual positive chart coefficient `sqrt(abs(det g_ij))`. -/
def chartDensity (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M (MinkowskiModel d))
    (x : M) : ℝ := Real.sqrt |Matrix.det (g.chartComponent e x)|

theorem chartDensity_eq_native (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M (MinkowskiModel d)) (x : M) :
    g.chartDensity e x = g.volumeDensity x (fun i => chartField e (Pi.single i 1) x) := rfl

@[simp] theorem opposite_chartDensity (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M (MinkowskiModel d)) (x : M) :
    g.opposite.chartDensity e x = g.chartDensity e x := by
  rw [g.opposite.chartDensity_eq_native, g.chartDensity_eq_native, g.opposite_volumeDensity]

theorem chartDensity_eq_basis (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source) :
    g.chartDensity e x = g.volumeDensity x (chartBasis he hx) := by
  rw [chartDensity_eq_native]
  congr 1
  funext i
  exact (chartBasis_apply he hx i).symm

theorem chartDensity_pos (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source) :
    0 < g.chartDensity e x := by
  rw [g.chartDensity_eq_basis he hx]
  exact g.volumeDensity_basis_pos x _

theorem chartComponent_det_ne_zero (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source) :
    Matrix.det (g.chartComponent e x) ≠ 0 := by
  have h := Real.sqrt_pos.mp (g.chartDensity_pos he hx)
  exact abs_pos.mp h

/-- The intrinsic density has the expected absolute determinant coordinate expression. -/
theorem volumeDensity_eq_chart (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source)
    (v : Fin (d + 1) → TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.volumeDensity x v = |Matrix.det (fun i j => chartTangentMap e x (v j) i)| * g.chartDensity e x := by
  have h := MetricDensity.value_eq_basis (g.form x).toLinearMap₁₂ (chartBasis he hx) v
  rw [g.chartDensity_eq_basis he hx]
  simpa only [volumeDensity, chartBasis_repr] using h

/-- Density coefficients transform by the absolute Jacobian of the actual chart transition. -/
theorem chartDensity_transition (g : LorentzMetric σ d M)
    {e e' : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    g.chartDensity e x =
      |Matrix.det (fun i j => fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single j 1) i)| *
        g.chartDensity e' x := by
  rw [g.chartDensity_eq_native e x, g.volumeDensity_eq_chart he' hx']
  simp only [chartTangentMap_transition he he' hx hx', chartTangentMap_field he hx]

/-- Chart density is smooth locally on the source, because its determinant never vanishes there. -/
theorem chartDensity_contMDiffAt (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ) ∞ (g.chartDensity e) x := by
  have hmat : ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      𝓘(ℝ, Fin (d + 1) → Fin (d + 1) → ℝ) ∞ (g.chartComponent e) x := by
    apply contMDiffAt_pi_module_iff.mpr
    intro i
    apply contMDiffAt_pi_module_iff.mpr
    intro j
    exact g.contMDiffAt_pairing (chartField_contMDiffAt he hx (Pi.single i 1))
      (chartField_contMDiffAt he hx (Pi.single j 1))
  have hdet := MetricDensity.contDiff_matrix_det.contMDiff.contMDiffAt.comp x hmat
  have hn := g.chartComponent_det_ne_zero he hx
  have hs : ContDiffAt ℝ ∞ (fun r : ℝ => Real.sqrt |r|) (Matrix.det (g.chartComponent e x)) :=
    (contDiffAt_abs hn).sqrt (abs_ne_zero.mpr hn)
  have hcomp := hs.contMDiffAt.comp x hdet
  simpa only [Function.comp_def, chartDensity] using! hcomp

/-- In the model's identity chart, coordinate fields are the original model vectors. -/
theorem chartField_refl (v x : MinkowskiModel d) :
    chartField (OpenPartialHomeomorph.refl (MinkowskiModel d)) v x = v := by
  simp [chartField, VectorField.mpullback_apply, modelField,
    NormedSpace.fromTangentSpace, tangentSpaceCastModel]
  rfl

theorem chartDensity_refl (g : LorentzMetric σ d (MinkowskiModel d)) (x : MinkowskiModel d) :
    g.chartDensity (OpenPartialHomeomorph.refl (MinkowskiModel d)) x =
      Real.sqrt |Matrix.det (fun i j => g.form x (Pi.single i 1) (Pi.single j 1))| := by
  unfold chartDensity
  congr 3
  ext i j
  change g.form x (chartField _ (Pi.single i 1) x) (chartField _ (Pi.single j 1) x) = _
  rw [chartField_refl, chartField_refl]

end ProjectAInos.SmoothGeometry.LorentzMetric
