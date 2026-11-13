/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.ChartDerivatives
public import ProjectAInos.SmoothGeometry.Manifold.QuadraticChart

/-! # Local inertial coordinates

A quadratic change of coordinates realizes a chosen Lorentz basis and
eliminates the Levi-Civita coefficients at one point. These are pointwise
normal coordinates; no local flatness or completeness is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The Christoffel coefficients bundled as a bilinear map on the coordinate
model. It depends on the chart and is not a tensor on the manifold. -/
def chartChristoffelBilinear (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M E)
    (x : M) : E →L[ℝ] E →L[ℝ] E :=
  ∑ i, ∑ j, (proj i : E →L[ℝ] ℝ).smulRight
    ((proj j : E →L[ℝ] ℝ).smulRight (fun k => g.chartChristoffel e x k i j))

theorem chartChristoffelBilinear_apply (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M E) (x : M) (v w : E) (k : Fin (d + 1)) :
    g.chartChristoffelBilinear e x v w k =
      ∑ i, ∑ j, g.chartChristoffel e x k i j * v i * w j := by
  simp only [chartChristoffelBilinear, sum_apply, Finset.sum_apply, smulRight_apply,
    proj_apply, smul_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem chartChristoffelBilinear_symmetric (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (v w : E) :
    g.chartChristoffelBilinear e x v w = g.chartChristoffelBilinear e x w v := by
  ext k
  simp only [chartChristoffelBilinear_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [g.chartChristoffel_symmetric he hx k j i]
  ring

/-- The bundled coefficients are extracted from the native connection acting
on constant coordinate fields. -/
theorem chartChristoffelBilinear_eq (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (v w : E) :
    g.chartChristoffelBilinear e x v w =
      chartTangentMap e x (g.leviCivita (chartField e w) x (chartField e v x)) := by
  ext k
  have h := g.leviCivita_chart_coordinates he hx (mdifferentiableAt_const (c := w)) v k
  simpa only [mvfderiv_const, zero_apply, Pi.zero_apply, zero_add,
    chartChristoffelBilinear_apply] using h.symm

/-- Any chosen tangent basis is realized by a chart whose connection
coefficients vanish at the base point. The Hessian correction has positive
sign in the source-to-target transition law. -/
theorem exists_chart_tangent_christoffel (g : LorentzMetric σ d M) (p : M)
    (S : TangentSpace I p ≃L[ℝ] E) :
    ∃ e : OpenPartialHomeomorph M E, e ∈ IsManifold.maximalAtlas I ∞ M ∧
      p ∈ e.source ∧ e p = 0 ∧
      (∀ v, chartTangentMap e p v = S v) ∧
      ∀ k i j, g.chartChristoffel e p k i j = 0 := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hp : p ∈ e.source := mem_chart_source E p
  let L : E ≃L[ℝ] E := (chartTangentEquiv he hp).symm.trans S
  let B : E →L[ℝ] E →L[ℝ] E :=
    (compL ℝ E E E (L : E →L[ℝ] E)).comp (g.chartChristoffelBilinear e p)
  have hB (u v : E) : B u v = B v u := by
    change L (g.chartChristoffelBilinear e p u v) = L (g.chartChristoffelBilinear e p v u)
    rw [g.chartChristoffelBilinear_symmetric he hp]
  obtain ⟨e', he', hp', h0, hD, hDD⟩ := QuadraticChart.exists_manifoldChart he hp L B hB
  refine ⟨e', he', hp', h0, ?_, ?_⟩
  · intro v
    rw [chartTangentMap_transition he he' hp hp', hD]
    change S ((chartTangentEquiv he hp).symm (chartTangentEquiv he hp v)) = S v
    rw [ContinuousLinearEquiv.symm_apply_apply]
  · intro k i j
    have h := g.leviCivita_chart_transition he he' hp hp'
      (L.symm (Pi.single i 1)) (L.symm (Pi.single j 1)) k
    rw [chartTangentMap_transition he he' hp hp', hD,
      ← g.chartChristoffelBilinear_eq he hp, hDD] at h
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h
    have hcancel : B (L.symm (Pi.single i 1)) (L.symm (Pi.single j 1)) =
        L (g.chartChristoffelBilinear e p (L.symm (Pi.single i 1))
          (L.symm (Pi.single j 1))) := rfl
    rw [hcancel] at h
    have hz := (add_eq_left.mp h.symm)
    simpa [Pi.single_apply] using hz

/-- At a point with zero Christoffel coefficients, all first coordinate
derivatives of the metric vanish by metric compatibility. -/
theorem chartComponent_fderiv_eq_zero (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {p : M} (hp : p ∈ e.source)
    (hΓ : ∀ k i j, g.chartChristoffel e p k i j = 0) (i j : Fin (d + 1)) :
    fderiv ℝ (fun y => g.chartComponent e (e.symm y) i j) (e p) = 0 := by
  have hcov (v w : E) : g.leviCivita (chartField e w) p (chartField e v p) = 0 := by
    apply (chartTangentEquiv he hp).injective
    rw [chartTangentEquiv_apply, ← g.chartChristoffelBilinear_eq he hp, map_zero]
    ext k
    simp only [chartChristoffelBilinear_apply, hΓ, zero_mul, Finset.sum_const_zero,
      Pi.zero_apply]
  have hi := chartField_mdifferentiableAt he hp (Pi.single i 1)
  have hj := chartField_mdifferentiableAt he hp (Pi.single j 1)
  have hd := g.mdifferentiableAt_pairing hi hj
  ext v
  change fderiv ℝ ((fun x => g.form x (chartField e (Pi.single i 1) x)
    (chartField e (Pi.single j 1) x)) ∘ e.symm) (e p) v = 0
  rw [← mvfderiv_chartField he hp hd]
  change mvfderiv I (fun x => g.form x (chartField e (Pi.single i 1) x)
    (chartField e (Pi.single j 1) x)) p (chartField e v p) = 0
  rw [g.leviCivita_metricCompatible _ hi hj, hcov, hcov]
  simp

/-- A centered, smooth Lorentz-normal chart at one point. The metric and its
first derivatives are normalized there; curvature may still be nonzero. -/
structure IsInertialChartAt (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M E) (p : M) : Prop where
  smooth : e ∈ IsManifold.maximalAtlas I ∞ M
  mem_source : p ∈ e.source
  centered : e p = 0
  metric : ∀ v w, g.form p (chartField e v p) (chartField e w p) = minkowskiForm σ d v w
  christoffel_zero : ∀ k i j, g.chartChristoffel e p k i j = 0
  metric_derivative_zero : ∀ i j,
    fderiv ℝ (fun y => g.chartComponent e (e.symm y) i j) (e p) = 0

/-- A chosen pointwise Lorentz basis extends to an actual local inertial
chart. No analytic manifold structure, global frame or completeness is needed. -/
theorem exists_inertialChart_for_equiv (g : LorentzMetric σ d M) (p : M)
    (S : TangentSpace I p ≃L[ℝ] E)
    (hS : ∀ v w, g.form p v w = minkowskiForm σ d (S v) (S w)) :
    ∃ e : OpenPartialHomeomorph M E, g.IsInertialChartAt e p ∧
      ∀ v, chartTangentMap e p v = S v := by
  obtain ⟨e, he, hp, h0, hT, hΓ⟩ := g.exists_chart_tangent_christoffel p S
  refine ⟨e, ⟨he, hp, h0, ?_, hΓ, g.chartComponent_fderiv_eq_zero he hp hΓ⟩, hT⟩
  intro v w
  rw [hS, ← hT, ← hT, chartTangentMap_field he hp, chartTangentMap_field he hp]

/-- Every smooth Lorentz metric, in either convention, admits local inertial
coordinates at each point. This is weaker than `IsLocallyMinkowski`. -/
theorem exists_inertialChart (g : LorentzMetric σ d M) (p : M) :
    ∃ e : OpenPartialHomeomorph M E, g.IsInertialChartAt e p := by
  obtain ⟨S, hS⟩ := g.signature p
  obtain ⟨e, he, _⟩ := g.exists_inertialChart_for_equiv p S hS
  exact ⟨e, he⟩

end ProjectAInos.SmoothGeometry.LorentzMetric
