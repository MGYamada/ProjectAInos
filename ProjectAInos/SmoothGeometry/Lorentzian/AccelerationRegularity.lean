/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Geodesic
public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurveRegularity

/-! # Continuity of native covariant acceleration

C² regularity of a curve implies continuity of its acceleration as a map
into the actual tangent bundle. Only a local chart is used in the proof.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- A C² native curve has continuous covariant acceleration. -/
theorem covariantAcceleration_contMDiffAt (g : LorentzMetric σ d M)
    {γ : ℝ → M} {t : ℝ} (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    ContMDiffAt 𝓘(ℝ) ((I).prod I) 0
      (fun s => TotalSpace.mk' E (γ s) (g.covariantAlong (curveVelocity γ) s)) t := by
  let e := chartAt E (γ t)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ t)
  have hx : γ t ∈ e.source := mem_chart_source E (γ t)
  have hq : ContDiffAt ℝ 2 (e ∘ γ) t :=
    (((contMDiffAt_of_mem_maximalAtlas he hx).of_le (by simp)).comp t hγ).contDiffAt
  have hv : ContDiffAt ℝ 1 (deriv (e ∘ γ)) t := hq.derivWithin (by norm_num)
  have ha : ContDiffAt ℝ 0 (deriv (deriv (e ∘ γ))) t := hv.derivWithin (by norm_num)
  let C : ℝ → E := fun s k => deriv (deriv (e ∘ γ)) s k + ∑ i, ∑ j,
    g.chartChristoffel e (γ s) k i j * deriv (e ∘ γ) s i * deriv (e ∘ γ) s j
  have hC : ContDiffAt ℝ 0 C t := by
    apply contDiffAt_pi.mpr
    intro k
    exact ((contDiffAt_pi.mp ha) k).add
      (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
        (((((g.chartChristoffel_contMDiffAt he hx k i j).of_le (by simp)).comp t
          (hγ.of_le (by norm_num))).contDiffAt).mul
            ((contDiffAt_pi.mp (hv.of_le (by norm_num))) i)).mul
              ((contDiffAt_pi.mp (hv.of_le (by norm_num))) j))
  apply (chartAlong_contMDiffAt he hx (hγ.of_le (by norm_num)) hC).congr_of_eventuallyEq
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by norm_num)).mp hγ
  filter_upwards [hγ.continuousAt (e.open_source.mem_nhds hx), hn] with s hs hγs
  congr 1
  have hc : chartTangentMap e (γ s) (g.covariantAlong (curveVelocity γ) s) = C s := by
    ext k
    exact g.covariantAcceleration_coordinates he hs hγs k
  rw [← hc, chartField_tangentMap he hs]

/-- The geodesic equation extends to the closure wherever the curve is C².
Scalar metric tests avoid any global separation assumption on the manifold. -/
theorem IsGeodesicOn.closure {g : LorentzMetric σ d M} {γ : ℝ → M} {s : Set ℝ}
    (hg : g.IsGeodesicOn s γ)
    (hγ : ∀ t ∈ closure s, ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    g.IsGeodesicOn (closure s) γ := by
  intro t ht
  refine ⟨hγ t ht, ?_⟩
  let e := chartAt E (γ t)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ t)
  have hx : γ t ∈ e.source := mem_chart_source E (γ t)
  apply g.nondegenerate (γ t) _
  intro v
  let w := chartTangentMap e (γ t) v
  have hc := (g.contDiffAt_pairing_along ((hγ t ht).of_le (show (0 : ℕ∞ω) ≤ 2 by norm_num))
    (((chartField_contMDiffAt he hx w).of_le (by simp)).comp t
      ((hγ t ht).of_le (by norm_num)))
    (g.covariantAcceleration_contMDiffAt (hγ t ht))).continuousAt
  have hz := hc.continuousWithinAt.eq_const_of_mem_closure (c := 0) ht (fun r hr => by
    simp only [(hg r hr).2, map_zero])
  rw [g.symmetric]
  simpa only [w, chartField_tangentMap he hx] using hz

end ProjectAInos.SmoothGeometry.LorentzMetric
