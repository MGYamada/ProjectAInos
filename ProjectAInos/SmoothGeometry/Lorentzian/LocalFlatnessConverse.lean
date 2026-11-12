/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.FlatConnection
public import ProjectAInos.SmoothGeometry.Lorentzian.ParallelCoframe

/-! # Zero curvature gives local Minkowski geometry

A pointwise inertial chart fixes the normalization at its center. A smooth
extension of its native connection coefficients and the flat radial-frame
construction supply an invertible parallel coframe on a small ball. The
coframe integration theorem then yields a Minkowski chart throughout an
open neighborhood. Only zero curvature near the point is required.
-/

@[expose] public section
noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open ContinuousLinearMap Set Filter Metric
open scoped ContDiff Manifold Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

open LinearODE

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- Native curvature vanishing near a point gives a genuine Minkowski chart
on a neighborhood of that point. No global frame, global chart, analytic
metric, Hausdorffness or geodesic completeness is assumed. -/
theorem exists_minkowskiChart_of_curvature_eq_zero_near (g : LorentzMetric σ d M)
    (p : M) (hR : ∀ᶠ x in 𝓝 p, g.curvature x = 0) :
    ∃ c : OpenPartialHomeomorph M E, c ∈ IsManifold.maximalAtlas I ∞ M ∧
      p ∈ c.source ∧ ∀ x ∈ c.source, ∀ v w : TangentSpace I x,
        g.form x v w = minkowskiForm σ d (chartTangentMap c x v) (chartTangentMap c x w) := by
  obtain ⟨e, he⟩ := g.exists_inertialChart p
  obtain ⟨Γ, hΓ, V, hV, hpV, hVtarget, hEq⟩ :=
    g.exists_smooth_chartChristoffel_extension he.smooth he.mem_source
  have h0V : (0 : E) ∈ V := he.centered ▸ hpV
  have hRcoord : ∀ᶠ q in 𝓝 (0 : E), g.curvature (e.symm q) = 0 := by
    have hc := (contMDiffAt_symm_of_mem_maximalAtlas he.smooth
      (e.map_source he.mem_source)).continuousAt
    have hn : ∀ᶠ x in 𝓝 (e.symm (e p)), g.curvature x = 0 := by
      simpa only [e.left_inv he.mem_source] using hR
    simpa only [he.centered] using hc.eventually hn
  have hVnear : ∀ᶠ q in 𝓝 (0 : E), q ∈ V := hV.mem_nhds h0V
  obtain ⟨a, ha, haV⟩ := Metric.mem_nhds_iff.mp (hVnear.and hRcoord)
  have hflat : IsFlatConnectionOn Γ (ball (0 : E) a) := by
    rw [isFlatConnectionOn_iff]
    intro q hq
    have hqV := (haV hq).1
    have hg : Γ =ᶠ[𝓝 q] fun z => g.chartChristoffelBilinear e (e.symm z) := by
      filter_upwards [hV.mem_nhds hqV] with z hz
      exact hEq hz
    rw [coefficientCurvature_congr hg]
    exact g.coefficientCurvature_eq_zero he.smooth (hVtarget hqV) (haV hq).2
  obtain ⟨r, hr, hrsub, hθ, hinv, hθ0, hparallel⟩ := exists_parallel_radialCoframe Γ hΓ
    (isOpen_ball.mem_nhds (mem_ball_self ha)) hflat
  have hrV : ball (0 : E) r ⊆ V := fun q hq => (haV (hrsub hq)).1
  apply g.exists_minkowskiChart_of_parallelCoframe he.smooth isOpen_ball (convex_ball 0 r)
    (hrV.trans hVtarget) hθ ?_ hinv he.mem_source ?_ ?_
  · intro q hq u v
    rw [hparallel q hq, hEq (hrV hq)]
  · rw [he.centered]
    exact mem_ball_self hr
  · intro v w
    rw [he.centered, hθ0]
    exact he.metric v w

/-- The converse to local Minkowski geometry implying zero native curvature. -/
theorem isLocallyMinkowski_of_curvature_eq_zero (g : LorentzMetric σ d M)
    (hR : ∀ p, g.curvature p = 0) : g.IsLocallyMinkowski := by
  apply g.isLocallyMinkowski_of_charts
  intro p
  exact g.exists_minkowskiChart_of_curvature_eq_zero_near p (Eventually.of_forall hR)

/-- A smooth Lorentz metric is locally Minkowski exactly when its native
curvature vanishes everywhere. This is a local conclusion, not an assertion
of a global inertial chart or geodesic completeness. -/
theorem isLocallyMinkowski_iff_curvature_eq_zero (g : LorentzMetric σ d M) :
    g.IsLocallyMinkowski ↔ ∀ p, g.curvature p = 0 :=
  ⟨fun h => h.curvature_eq_zero, g.isLocallyMinkowski_of_curvature_eq_zero⟩

end ProjectAInos.SmoothGeometry.LorentzMetric
