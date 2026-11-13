/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.LocalFlatnessConverse
public import ProjectAInos.SmoothGeometry.Lorentzian.PiecewisePath

/-! # Local path independence in a flat neighborhood

In a chart with zero connection coefficients, constant components give
native parallel fields. Transport consequently depends only on the endpoint
chart identifications. Curvature zero near a point constructs such a chart;
path independence is not a premise of the local flatness proof.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open ContinuousLinearMap Set Filter
open scoped ContDiff Manifold Topology

namespace ProjectAInos.SmoothGeometry

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

namespace LorentzMetric

/-- A chart normalizing the metric throughout its source has zero
Christoffel coefficients throughout that source. -/
theorem chartChristoffel_eq_zero_of_minkowskiChart (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hm : ∀ x ∈ e.source, ∀ v w : TangentSpace I x,
      g.form x v w = minkowskiForm σ d (chartTangentMap e x v) (chartTangentMap e x w))
    {x : M} (hx : x ∈ e.source) (k i j : Fin (d + 1)) :
    g.chartChristoffel e x k i j = 0 := by
  have hd (a b : Fin (d + 1)) : mvfderiv I (fun y => g.chartComponent e y a b) x = 0 := by
    have hconst : (fun y => g.chartComponent e y a b) =ᶠ[𝓝 x]
        fun _ => minkowskiForm σ d (Pi.single a 1) (Pi.single b 1) := by
      filter_upwards [e.open_source.mem_nhds hx] with y hy
      simp only [chartComponent, hm y hy, chartTangentMap_field he hy]
    rw [mvfderiv_congr_of_eventuallyEq hconst, mvfderiv_const]
  rw [g.chartChristoffel_eq he hx]
  simp [hd]

end LorentzMetric

namespace RegularPath

open LorentzMetric

/-- Endpoint coordinates compute transport along every regular path lying
in a chart with zero connection coefficients. -/
theorem transport_eq_chart (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hΓ : ∀ z ∈ e.source, ∀ k i j, g.chartChristoffel e z k i j = 0)
    {x y : M} (p : RegularPath d M x y)
    (hstay : ∀ t ∈ Icc (0 : ℝ) 1, p.curve t ∈ e.source)
    (hx : x ∈ e.source) (hy : y ∈ e.source) :
    p.transport g = (chartTangentEquiv he hx).trans (chartTangentEquiv he hy).symm := by
  ext v
  let w := chartTangentMap e x v
  have hp : g.IsParallelOn (Icc (0 : ℝ) 1) (fun t => chartField e w (p.curve t)) := by
    apply g.isParallelOn_of_chartODE he
      (fun t ht => (p.regular t ht).mdifferentiableAt (by norm_num)) hstay
    intro t ht
    have hz : g.chartParallelOperator e p.curve t w = 0 := by
      ext k
      simp [g.chartParallelOperator_apply, hΓ _ (hstay t ht)]
    rw [hz]
    exact hasDerivAt_const t w
  have hc {a b : M} (h : a = b) : tangentCongr h (chartField e w a) = chartField e w b := by
    subst b
    rfl
  have ht := p.transport_apply_eq g hp
  rw [hc, hc, chartField_tangentMap he hx] at ht
  simpa only [ContinuousLinearEquiv.trans_apply, chartTangentEquiv_symm,
    chartTangentEquiv_apply, w] using ht

theorem transport_eq_of_same_endpoints_in_flatChart (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hΓ : ∀ z ∈ e.source, ∀ k i j, g.chartChristoffel e z k i j = 0)
    {x y : M} (p q : RegularPath d M x y)
    (hp : ∀ t ∈ Icc (0 : ℝ) 1, p.curve t ∈ e.source)
    (hq : ∀ t ∈ Icc (0 : ℝ) 1, q.curve t ∈ e.source) :
    p.transport g = q.transport g := by
  have hx : x ∈ e.source := p.source ▸ hp 0 (by norm_num)
  have hy : y ∈ e.source := p.target ▸ hp 1 (by norm_num)
  rw [p.transport_eq_chart g he hΓ hp hx hy, q.transport_eq_chart g he hΓ hq hx hy]

end RegularPath

namespace PiecewisePath

open LorentzMetric

/-- The same endpoint formula holds for finite concatenations, including
corners. The source condition concerns the actual continuous path. -/
theorem transport_eq_chart (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hΓ : ∀ z ∈ e.source, ∀ k i j, g.chartChristoffel e z k i j = 0)
    {x y : M} (p : PiecewisePath d M x y)
    (hstay : range p.toPath ⊆ e.source) (hx : x ∈ e.source) (hy : y ∈ e.source) :
    p.transport g = (chartTangentEquiv he hx).trans (chartTangentEquiv he hy).symm := by
  induction p with
  | refl x =>
    ext v
    simp [transport]
  | segment p =>
    exact p.transport_eq_chart g he hΓ (fun t ht => hstay ⟨⟨t, ht⟩, rfl⟩) hx hy
  | @trans x y z p q ihp ihq =>
    have hp : range p.toPath ⊆ e.source := by
      intro a ha
      apply hstay
      change a ∈ range (p.toPath.trans q.toPath)
      rw [Path.trans_range]
      exact Or.inl ha
    have hq : range q.toPath ⊆ e.source := by
      intro a ha
      apply hstay
      change a ∈ range (p.toPath.trans q.toPath)
      rw [Path.trans_range]
      exact Or.inr ha
    have hm : y ∈ e.source := hp p.toPath.target_mem_range
    rw [transport_trans, ihp hp hx hm, ihq hq hm hy]
    ext v
    simp [chartTangentMap_field he hm]

/-- In one flat chart, all finite piecewise regular paths with the same
endpoints have equal intrinsic transport, regardless of their decomposition. -/
theorem transport_eq_of_same_endpoints_in_flatChart (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hΓ : ∀ z ∈ e.source, ∀ k i j, g.chartChristoffel e z k i j = 0)
    {x y : M} (p q : PiecewisePath d M x y)
    (hp : range p.toPath ⊆ e.source) (hq : range q.toPath ⊆ e.source) :
    p.transport g = q.transport g := by
  have hx := hp p.toPath.source_mem_range
  have hy := hp p.toPath.target_mem_range
  rw [p.transport_eq_chart g he hΓ hp hx hy, q.transport_eq_chart g he hΓ hq hx hy]

end PiecewisePath

namespace LorentzMetric

/-- Curvature zero near a point constructs an open neighborhood with
path-independent transport for all finite piecewise regular paths contained
in it. This does not assert global path independence on the manifold. -/
theorem exists_pathIndependent_neighborhood (g : LorentzMetric σ d M) (p : M)
    (hR : ∀ᶠ x in 𝓝 p, g.curvature x = 0) :
    ∃ U : TopologicalSpace.Opens M, p ∈ U ∧ ∀ {x y : M} (a b : PiecewisePath d M x y),
      range a.toPath ⊆ U → range b.toPath ⊆ U → a.transport g = b.transport g := by
  obtain ⟨e, he, hp, hm⟩ := g.exists_minkowskiChart_of_curvature_eq_zero_near p hR
  refine ⟨⟨e.source, e.open_source⟩, hp, ?_⟩
  intro x y a b ha hb
  exact a.transport_eq_of_same_endpoints_in_flatChart g he
    (fun _ hx => g.chartChristoffel_eq_zero_of_minkowskiChart he hm hx) b ha hb

end LorentzMetric

end ProjectAInos.SmoothGeometry
