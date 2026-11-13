/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.HodgeCoordinates

/-! # Hodge as a smooth operation on native differential forms -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric
open DifferentialForm

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

/-- Local Hodge coefficients are smooth whenever the input coefficients are smooth there. -/
theorem hodgeChart_contDiffAt (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    (p : M) {k l : ℕ} (hkl : k + l = d + 1) {β : Form (MinkowskiModel d) k}
    {y : MinkowskiModel d} (hy : y ∈ (o.chart p).target) (hβ : ContDiffAt ℝ ∞ β y) :
    ContDiffAt ℝ ∞ (g.hodgeChart o p hkl β) y := by
  have hi := contMDiffAt_symm_of_mem_maximalAtlas (o.mem_atlas p) hy
  have hx := (o.chart p).map_target hy
  have hρ := (g.chartDensity_contMDiffAt (o.mem_atlas p) hx).comp y hi
  have hT := (g.hodgeChartMap_contMDiffAt (o.mem_atlas p) hx).comp y hi
  have hpre := hT.compContinuousLinearMapCLM.clm_apply hβ.contMDiffAt
  have hs := (Minkowski.hodgeFiber .timeNegative .standard hkl).toContinuousLinearMap.contMDiffAt.comp y hpre
  exact ((contMDiffAt_const.mul hρ).smul hs).contDiffAt

/-- Native Hodge preserves local smoothness on the actual alternating tangent bundle. -/
theorem contMDiffAt_nativeHodge (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    {k l : ℕ} (hkl : k + l = d + 1) {α : NativeForm 𝓘(ℝ, MinkowskiModel d) M k} {x : M}
    (hα : ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) y (α y)) x) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d [⋀^Fin l]→L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (MinkowskiModel d [⋀^Fin l]→L[ℝ] ℝ) y (g.nativeHodge o hkl α y)) x := by
  have hx := o.mem_source x
  have hy := (o.chart x).map_source hx
  have hα' : ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (MinkowskiModel d [⋀^Fin k]→L[ℝ] ℝ) y (α y))
      ((o.chart x).symm (o.chart x x)) := by simpa only [(o.chart x).left_inv hx] using hα
  have hc := chartCoefficients_contDiffAt (o.mem_atlas x) hy hα'
  have hh := chartLift_contMDiffAt (o.mem_atlas x) hx (g.hodgeChart_contDiffAt o x hkl hy hc)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(o.chart x).open_source.mem_nhds hx] with y hy
  exact congrArg (TotalSpace.mk' (MinkowskiModel d [⋀^Fin l]→L[ℝ] ℝ) y)
    (g.nativeHodge_eq_chartLift o x hkl α hy)

/-- Hodge is a linear map of smooth native sections, constructed from the pointwise operator. -/
def smoothHodge (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    {k l : ℕ} (hkl : k + l = d + 1) :
    SmoothForm 𝓘(ℝ, MinkowskiModel d) M k →ₗ[ℝ] SmoothForm 𝓘(ℝ, MinkowskiModel d) M l where
  toFun α := ⟨g.nativeHodge o hkl (fun x => α x), fun x => g.contMDiffAt_nativeHodge o hkl (α.contMDiff x)⟩
  map_add' α β := by ext x : 1; exact (g.hodgeFiber o x hkl).map_add (α x) (β x)
  map_smul' r α := by ext x : 1; exact (g.hodgeFiber o x hkl).map_smul r (α x)

@[simp] theorem smoothHodge_apply (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    {k l : ℕ} (hkl : k + l = d + 1) (α : SmoothForm 𝓘(ℝ, MinkowskiModel d) M k) (x : M) :
    g.smoothHodge o hkl α x = g.hodgeFiber o x hkl (α x) := rfl

theorem smoothHodge_reverse (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    {k l : ℕ} (hkl : k + l = d + 1) (α : SmoothForm 𝓘(ℝ, MinkowskiModel d) M k) :
    g.smoothHodge o.reverse hkl α = -g.smoothHodge o hkl α := by
  ext x : 1
  exact g.hodgeFiber_reverse o x hkl (α x)

theorem smoothHodge_opposite (g : LorentzMetric σ d M) (o : OrientedAtlas (d + 1) M)
    {k l : ℕ} (hkl : k + l = d + 1) (α : SmoothForm 𝓘(ℝ, MinkowskiModel d) M k) :
    g.opposite.smoothHodge o hkl α = (-1 : ℝ) ^ k • g.smoothHodge o hkl α := by
  ext x : 1
  exact g.hodgeFiber_opposite o x hkl (α x)

theorem smoothHodge_minkowski (σ : LorentzConvention) (d : ℕ) {k l : ℕ} (hkl : k + l = d + 1)
    (α : Form (MinkowskiModel d) k) (hα : ContDiff ℝ ∞ α) (x : MinkowskiModel d) :
    (minkowskiMetric σ d).smoothHodge (OrientedAtlas.standard (d + 1)) hkl (ofFlat α hα) x =
      Minkowski.hodgeFiber σ .standard hkl (α x) := minkowskiMetric_hodgeFiber σ d x hkl (α x)

end ProjectAInos.SmoothGeometry.LorentzMetric
