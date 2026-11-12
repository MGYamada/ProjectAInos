/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.ChartDuality
public import ProjectAInos.SmoothGeometry.Lorentzian.HodgeFlat
public import ProjectAInos.SmoothGeometry.DifferentialForm.HodgeFormula

/-! # Local coordinate formula for native Lorentz Hodge -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Module Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open DifferentialForm

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

/-- `G⁻¹ η` on the coordinate model; this transfers the inverse metric in one slot. -/
def hodgeChartMap (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M (MinkowskiModel d))
    (x : M) : MinkowskiModel d →L[ℝ] MinkowskiModel d :=
  (g.chartSharp e x).comp (Minkowski.flat .timeNegative).toContinuousLinearMap

theorem hodgeChartMap_contMDiffAt (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d) ∞
      (g.hodgeChartMap e) x := (g.chartSharp_contMDiffAt he hx).clm_comp contMDiffAt_const

/-- The reference inverse metric after precomposition is the native inverse metric in coordinates. -/
theorem coMetric_hodgeChartMap (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M (MinkowskiModel d)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M) {x : M} (hx : x ∈ e.source)
    (α β : Dual ℝ (MinkowskiModel d)) :
    Minkowski.coMetric .timeNegative d ((g.hodgeChartMap e x).toLinearMap.dualMap α) β =
      g.coMetric x ((chartTangentEquiv he hx).toLinearMap.dualMap α)
        ((chartTangentEquiv he hx).toLinearMap.dualMap β) := by
  have hs : Minkowski.coMetric .timeNegative d ((g.hodgeChartMap e x).toLinearMap.dualMap α) β =
      Minkowski.coMetric .timeNegative d β ((g.hodgeChartMap e x).toLinearMap.dualMap α) :=
    (Minkowski.coMetric_symmetric .timeNegative d).eq _ _
  rw [hs]
  change α (g.chartSharp e x (Minkowski.flat .timeNegative
      ((Minkowski.flat .timeNegative).symm (LinearMap.toContinuousLinearMap β)))) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, g.chartSharp_apply he hx]
  change g.coMetric x ((chartTangentEquiv he hx).toLinearMap.dualMap β)
    ((chartTangentEquiv he hx).toLinearMap.dualMap α) = _
  exact (g.coMetric_symmetric x).eq ((chartTangentEquiv he hx).toLinearMap.dualMap β)
    ((chartTangentEquiv he hx).toLinearMap.dualMap α)

/-- Hodge of any lifted coordinate form, in a selected signed local chart. -/
theorem hodgeFiber_chartLift (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    (p : M) {x : M} (hx : x ∈ (o.chart p).source) {k l : ℕ} (hkl : k + l = d + 1)
    (β : Form (MinkowskiModel d) k) :
    g.hodgeFiber o x hkl (chartLift (o.chart p) β x) =
      (o.sign p * g.chartDensity (o.chart p) x) •
        (Minkowski.hodgeFiber .timeNegative .standard hkl
          ((β (o.chart p x)).compContinuousLinearMap (g.hodgeChartMap (o.chart p) x))).compContinuousLinearMap
            (chartTangentEquiv (o.mem_atlas p) hx).toContinuousLinearMap := by
  let h := minkowskiMetric .timeNegative d
  let o₀ := OrientedAtlas.standard (d + 1)
  have hv : (o.sign p * g.chartDensity (o.chart p) x) •
      (h.volumeForm o₀ 0).compContinuousLinearMap
        (chartTangentEquiv (o.mem_atlas p) hx).toContinuousLinearMap = g.volumeForm o x := by
    rw [LorentzianVolumeExamples.minkowski_volume, g.volumeForm_apply o hx]
    rfl
  have hm : ∀ α β : Dual ℝ (MinkowskiModel d),
      h.coMetric 0 ((g.hodgeChartMap (o.chart p) x).toLinearMap.dualMap α) β =
        g.coMetric x ((chartTangentEquiv (o.mem_atlas p) hx).toLinearMap.dualMap α)
          ((chartTangentEquiv (o.mem_atlas p) hx).toLinearMap.dualMap β) := by
    intro α β
    rw [minkowskiMetric_coMetric]
    exact g.coMetric_hodgeChartMap (o.mem_atlas p) hx α β
  have hh := finiteHodgeOfDegree_formula (g.coMetric x) (g.coMetric_bijective x)
    (h.coMetric 0) (h.coMetric_bijective 0) (g.volumeForm o x) (g.volumeForm_ne_zero o x)
    (cotangent_topDegree x) (h.volumeForm o₀ 0) (h.volumeForm_ne_zero o₀ 0)
    (cotangent_topDegree (M := MinkowskiModel d) 0)
    (chartTangentEquiv (o.mem_atlas p) hx) (g.hodgeChartMap (o.chart p) x)
    (o.sign p * g.chartDensity (o.chart p) x) hm hv hkl (β (o.chart p x))
  change g.hodgeFiber o x hkl _ = _ •
    (h.hodgeFiber o₀ 0 hkl _).compContinuousLinearMap _ at hh
  rw [minkowskiMetric_hodgeFiber] at hh
  exact hh

/-- The full local Hodge expression, using the actual inverse-chart coefficients. -/
def hodgeChart (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M) (p : M)
    {k l : ℕ} (hkl : k + l = d + 1) (β : Form (MinkowskiModel d) k) : Form (MinkowskiModel d) l :=
  fun y => (o.sign p * g.chartDensity (o.chart p) ((o.chart p).symm y)) •
    Minkowski.hodgeFiber .timeNegative .standard hkl
      ((β y).compContinuousLinearMap (g.hodgeChartMap (o.chart p) ((o.chart p).symm y)))

/-- On each local source, the coordinate formula recovers the intrinsic native operator. -/
theorem nativeHodge_eq_chartLift (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    (p : M) {k l : ℕ} (hkl : k + l = d + 1) (α : NativeForm 𝓘(ℝ, MinkowskiModel d) M k)
    {x : M} (hx : x ∈ (o.chart p).source) :
    g.nativeHodge o hkl α x =
      chartLift (o.chart p) (g.hodgeChart o p hkl (chartCoefficients (o.chart p) α)) x := by
  have h := g.hodgeFiber_chartLift o p hx hkl (chartCoefficients (o.chart p) α)
  rw [chartLift_chartCoefficients (o.mem_atlas p) α hx] at h
  rw [nativeHodge, h]
  unfold chartLift nativePullback hodgeChart
  rw [(o.chart p).left_inv hx]
  rfl

/-- Intrinsic Hodge has the stated coordinate formula on each oriented chart target. -/
theorem chartCoefficients_nativeHodge (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    (p : M) {k l : ℕ} (hkl : k + l = d + 1) (α : NativeForm 𝓘(ℝ, MinkowskiModel d) M k)
    {y : MinkowskiModel d} (hy : y ∈ (o.chart p).target) :
    chartCoefficients (o.chart p) (g.nativeHodge o hkl α) y =
      g.hodgeChart o p hkl (chartCoefficients (o.chart p) α) y := by
  calc
    _ = chartCoefficients (o.chart p)
        (chartLift (o.chart p) (g.hodgeChart o p hkl (chartCoefficients (o.chart p) α))) y := by
      unfold chartCoefficients nativePullback
      rw [g.nativeHodge_eq_chartLift o p hkl α ((o.chart p).map_target hy)]
      rfl
    _ = _ := chartCoefficients_chartLift (o.mem_atlas p) _ hy

/-- In the standard model chart the formula is the usual inverse-metric and density expression. -/
theorem hodgeFiber_standard (g : LorentzMetric σ d (MinkowskiModel d)) (x : MinkowskiModel d)
    {k l : ℕ} (hkl : k + l = d + 1) (α : MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) :
    g.hodgeFiber (OrientedAtlas.standard (d + 1)) x hkl α =
      g.chartDensity (OpenPartialHomeomorph.refl (MinkowskiModel d)) x •
        Minkowski.hodgeFiber .timeNegative .standard hkl
          (α.compContinuousLinearMap (g.hodgeChartMap (OpenPartialHomeomorph.refl (MinkowskiModel d)) x)) := by
  have h := g.nativeHodge_eq_chartLift (OrientedAtlas.standard (d + 1)) x hkl
    (fun _ => α) (x := x) (by trivial)
  change g.hodgeFiber (OrientedAtlas.standard (d + 1)) x hkl α =
    chartLift (OpenPartialHomeomorph.refl (MinkowskiModel d))
      (g.hodgeChart (OrientedAtlas.standard (d + 1)) x hkl
        (chartCoefficients (OpenPartialHomeomorph.refl (MinkowskiModel d)) (fun _ => α))) x at h
  rw [chartLift_refl, chartCoefficients_refl] at h
  simpa only [hodgeChart, OrientedAtlas.standard, OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply, id_eq, one_mul] using! h

end ProjectAInos.SmoothGeometry.LorentzMetric
