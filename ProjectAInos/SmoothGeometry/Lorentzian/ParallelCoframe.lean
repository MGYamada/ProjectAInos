/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.LocalInertial
public import ProjectAInos.SmoothGeometry.Lorentzian.LocalFlatness
public import ProjectAInos.SmoothGeometry.Manifold.ClosedCoframe
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Integrating a parallel coordinate coframe

The parallel-covector equation uses Christoffel coefficients derived from
the native Levi-Civita connection. Torsion-freeness makes the coframe closed,
and Poincaré integration gives coordinates with zero coefficients throughout
their source. Existence of such a coframe from zero curvature is separate.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap Set Filter
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The coordinate equation for a parallel vector-valued coframe. The plus
sign is the covector connection convention `∂θ = θ Γ`. -/
def IsParallelChartCoframeOn (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M E) (U : Set E) (θ : E → E →L[ℝ] E) : Prop :=
  ∀ q ∈ U, ∀ u v, fderiv ℝ θ q u v = θ q (g.chartChristoffelBilinear e (e.symm q) u v)

/-- Torsion-freeness makes every parallel coordinate coframe closed. -/
theorem IsParallelChartCoframeOn.closed {g : LorentzMetric σ d M}
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {U : Set E} (hU : U ⊆ e.target) {θ : E → E →L[ℝ] E}
    (h : g.IsParallelChartCoframeOn e U θ) :
    ∀ q ∈ U, ∀ u v, fderiv ℝ θ q u v = fderiv ℝ θ q v u := by
  intro q hq u v
  rw [h q hq u v, h q hq v u,
    g.chartChristoffelBilinear_symmetric he (e.map_target (hU hq))]

/-- A smooth invertible parallel coframe integrates to an actual chart
whose native Levi-Civita coefficients vanish everywhere on its source. -/
theorem exists_chart_zeroChristoffel_of_parallelCoframe (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hUsub : U ⊆ e.target)
    {θ : E → E →L[ℝ] E} (hθ : ContDiffOn ℝ ∞ θ U)
    (hparallel : g.IsParallelChartCoframeOn e U θ)
    (hinv : ∀ q ∈ U, (θ q).IsInvertible) {p : M} (hp : p ∈ e.source) (hpU : e p ∈ U) :
    ∃ e' : OpenPartialHomeomorph M E, e' ∈ IsManifold.maximalAtlas I ∞ M ∧
      p ∈ e'.source ∧ e' p = 0 ∧ e'.source ⊆ e.source ∧
      (∀ x ∈ e'.source, e x ∈ U ∧ fderiv ℝ (e' ∘ e.symm) (e x) = θ (e x)) ∧
      ∀ x ∈ e'.source, ∀ k i j, g.chartChristoffel e' x k i j = 0 := by
  obtain ⟨e', he', hp', h0, hsource, hder⟩ := ClosedCoframe.exists_manifoldChart he hU hconv hθ
    (hparallel.closed he hUsub) hinv hp hpU
  have hD (x) (hx : x ∈ e'.source) : fderiv ℝ (e' ∘ e.symm) (e x) = θ (e x) :=
    (hder x hx).2.fderiv
  refine ⟨e', he', hp', h0, hsource, fun x hx => ⟨(hder x hx).1, hD x hx⟩, ?_⟩
  intro x hx k i j
  have hxold := hsource hx
  have hxU := (hder x hx).1
  have hin : e.symm ⁻¹' e'.source ∈ 𝓝 (e x) := by
    have hc := (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hxold)).continuousAt
    apply hc
    simpa only [e.left_inv hxold] using e'.open_source.mem_nhds hx
  have hEq (w : E) : (fun q => fderiv ℝ (e' ∘ e.symm) q w) =ᶠ[𝓝 (e x)]
      (fun q => θ q w) := by
    filter_upwards [e.open_target.mem_nhds (e.map_source hxold), hin] with q hq hq'
    have h := hD (e.symm q) hq'
    rw [e.right_inv hq] at h
    exact congrArg (fun A : E →L[ℝ] E => A w) h
  have hDD (u w : E) : fderiv ℝ (fun q => fderiv ℝ (e' ∘ e.symm) q w) (e x) u =
      θ (e x) (g.chartChristoffelBilinear e x u w) := by
    have hd := (hθ.contDiffAt (hU.mem_nhds hxU)).differentiableAt (by simp)
    have hdw := (ContinuousLinearMap.apply ℝ E w).hasFDerivAt.comp (e x) hd.hasFDerivAt
    rw [(hEq w).fderiv_eq]
    have h := congrArg (fun A : E →L[ℝ] E => A u) hdw.fderiv
    change fderiv ℝ (fun q => θ q w) (e x) u = fderiv ℝ θ (e x) u w at h
    rw [h, hparallel (e x) hxU, e.left_inv hxold]
  obtain ⟨L, hL⟩ := hinv (e x) hxU
  have h := g.leviCivita_chart_transition he he' hxold hx
    (L.symm (Pi.single i 1)) (L.symm (Pi.single j 1)) k
  rw [chartTangentMap_transition he he' hxold hx, hD x hx,
    ← g.chartChristoffelBilinear_eq he hxold, hDD, ← hL] at h
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply] at h
  have hz := add_eq_left.mp h.symm
  simpa [Pi.single_apply] using hz

/-- If connection coefficients vanish throughout a chart with connected
target, its metric components are constant throughout that chart. -/
theorem chartComponent_eq_of_zeroChristoffel (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hconnected : IsPreconnected e.target)
    (hΓ : ∀ x ∈ e.source, ∀ k i j, g.chartChristoffel e x k i j = 0)
    {x y : M} (hx : x ∈ e.source) (hy : y ∈ e.source) (i j : Fin (d + 1)) :
    g.chartComponent e x i j = g.chartComponent e y i j := by
  let f : E → ℝ := fun q => g.chartComponent e (e.symm q) i j
  have hd : DifferentiableOn ℝ f e.target := by
    intro q hq
    have hp := e.map_target hq
    have hf := g.mdifferentiableAt_pairing
      (chartField_mdifferentiableAt he hp (Pi.single i 1))
      (chartField_mdifferentiableAt he hp (Pi.single j 1))
    exact (hf.comp q ((contMDiffAt_symm_of_mem_maximalAtlas he hq).mdifferentiableAt
      (by simp))).differentiableAt.differentiableWithinAt
  have hz : e.target.EqOn (fderiv ℝ f) 0 := by
    intro q hq
    have h := g.chartComponent_fderiv_eq_zero he (e.map_target hq)
      (hΓ _ (e.map_target hq)) i j
    simpa only [f, e.right_inv hq, Pi.zero_apply] using h
  have h := e.open_target.is_const_of_fderiv_eq_zero hconnected hd hz
    (e.map_source hx) (e.map_source hy)
  simpa only [f, e.left_inv hx, e.left_inv hy] using h

/-- Constancy of metric components gives constancy of all coordinate-frame
pairings. Both vectors are arbitrary, not only basis elements. -/
theorem chartPairing_eq_of_zeroChristoffel (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hconnected : IsPreconnected e.target)
    (hΓ : ∀ x ∈ e.source, ∀ k i j, g.chartChristoffel e x k i j = 0)
    {x y : M} (hx : x ∈ e.source) (hy : y ∈ e.source) (v w : E) :
    g.form x (chartField e v x) (chartField e w x) =
      g.form y (chartField e v y) (chartField e w y) := by
  rw [chartField_eq_sum e x v, chartField_eq_sum e x w,
    chartField_eq_sum e y v, chartField_eq_sum e y w]
  simp only [map_sum, map_smul, sum_apply, smul_apply]
  change (∑ j, w j • ∑ i, v i • g.chartComponent e x i j) =
    ∑ j, w j • ∑ i, v i • g.chartComponent e y i j
  simp_rw [g.chartComponent_eq_of_zeroChristoffel he hconnected hΓ hx hy]

/-- A parallel coframe normalized at one point yields a Minkowski chart on
an open neighborhood. Metric normalization propagates from the single point
by metric compatibility; it is not assumed at every point of the domain. -/
theorem exists_minkowskiChart_of_parallelCoframe (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hUsub : U ⊆ e.target)
    {θ : E → E →L[ℝ] E} (hθ : ContDiffOn ℝ ∞ θ U)
    (hparallel : g.IsParallelChartCoframeOn e U θ)
    (hinv : ∀ q ∈ U, (θ q).IsInvertible) {p : M} (hp : p ∈ e.source) (hpU : e p ∈ U)
    (hnorm : ∀ v w, g.form p (chartField e v p) (chartField e w p) =
      minkowskiForm σ d (θ (e p) v) (θ (e p) w)) :
    ∃ c : OpenPartialHomeomorph M E, c ∈ IsManifold.maximalAtlas I ∞ M ∧
      p ∈ c.source ∧ ∀ x ∈ c.source, ∀ v w : TangentSpace I x,
        g.form x v w = minkowskiForm σ d (chartTangentMap c x v) (chartTangentMap c x w) := by
  obtain ⟨e', he', hp', _, _, hD, hΓ⟩ :=
    g.exists_chart_zeroChristoffel_of_parallelCoframe he hU hconv hUsub hθ hparallel hinv hp hpU
  have hT (v : TangentSpace I p) : chartTangentMap e' p v = θ (e p) (chartTangentMap e p v) := by
    rw [chartTangentMap_transition he he' hp hp', (hD p hp').2]
  have hmp (v w : TangentSpace I p) :
      g.form p v w = minkowskiForm σ d (chartTangentMap e' p v) (chartTangentMap e' p w) := by
    rw [hT, hT]
    simpa only [chartField_tangentMap he hp] using
      hnorm (chartTangentMap e p v) (chartTangentMap e p w)
  obtain ⟨c, hc, hpc, hsub, hfun, _, hconvex⟩ := Manifold.exists_chart_convexTarget he' hp'
  have hTc (x : M) : chartTangentMap c x = chartTangentMap e' x := by
    change mvfderiv I (⇑c) x = mvfderiv I (⇑e') x
    rw [hfun]
  have hΓc (x) (hx : x ∈ c.source) (k i j) : g.chartChristoffel c x k i j = 0 := by
    simpa only [chartChristoffel, hTc, chartField, hfun] using hΓ x (hsub hx) k i j
  have hmpc (v w : TangentSpace I p) :
      g.form p v w = minkowskiForm σ d (chartTangentMap c p v) (chartTangentMap c p w) := by
    simpa only [hTc] using hmp v w
  refine ⟨c, hc, hpc, ?_⟩
  intro x hx v w
  have h := g.chartPairing_eq_of_zeroChristoffel hc hconvex.isPreconnected hΓc hx hpc
    (chartTangentMap c x v) (chartTangentMap c x w)
  rw [chartField_tangentMap hc hx, chartField_tangentMap hc hx, hmpc,
    chartTangentMap_field hc hpc, chartTangentMap_field hc hpc] at h
  exact h

end ProjectAInos.SmoothGeometry.LorentzMetric
