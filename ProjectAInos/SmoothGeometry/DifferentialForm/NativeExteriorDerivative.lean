/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeChart

/-! # Exterior differentiation on native smooth forms

The model derivative is lifted through an actual smooth chart. Its overlap
law proves independence of the chart before the global section is bundled.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

/-- Smooth model forms have smooth exterior derivative locally. -/
theorem contDiffAt_extDeriv {β : Form E k} {y : E} (hβ : ContDiffAt ℝ ∞ β y) :
    ContDiffAt ℝ ∞ (extDeriv β) y := by
  simpa only [Function.comp_def, ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply,
    extDeriv] using!
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ E ℝ).contDiff.contDiffAt.comp y
      (hβ.fderiv_right (m := ∞) (by simp))

/-- The exterior derivatives of chart coefficients satisfy the same pullback overlap law. -/
theorem chartExtDeriv_transition (α : SmoothForm 𝓘(ℝ, E) M k)
    {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E}
    (hy : y ∈ e'.target) (hye : e'.symm y ∈ e.source) :
    extDeriv (chartCoefficients e' (fun x => α x)) y =
      pullback (e ∘ e'.symm) (extDeriv (chartCoefficients e (fun x => α x))) y := by
  have hnear : ∀ᶠ z in 𝓝 y, e'.symm z ∈ e.source :=
    (contMDiffAt_symm_of_mem_maximalAtlas he' hy).continuousAt (e.open_source.mem_nhds hye)
  have heq : chartCoefficients e' (fun x => α x) =ᶠ[𝓝 y]
      pullback (e ∘ e'.symm) (chartCoefficients e (fun x => α x)) := by
    filter_upwards [e'.open_target.mem_nhds hy, hnear] with z hz hze
    exact chartCoefficients_transition he he' (fun x => α x) hz hze
  rw [heq.extDeriv_eq]
  exact extDeriv_pullback
    ((α.chartCoefficients_contDiffAt he (e.map_source hye)).differentiableAt (by simp))
    (formChartTransition_contDiffAt he he' hy hye) (by simp)

/-- Chartwise exterior derivatives lift to exactly the same native alternating covector. -/
theorem chartLift_extDeriv_independent (α : SmoothForm 𝓘(ℝ, E) M k)
    {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    chartLift e' (extDeriv (chartCoefficients e' (fun y => α y))) x =
      chartLift e (extDeriv (chartCoefficients e (fun y => α y))) x := by
  have hxe : e'.symm (e' x) ∈ e.source := by simpa only [e'.left_inv hx'] using hx
  calc
    _ = chartLift e' (pullback (e ∘ e'.symm)
        (extDeriv (chartCoefficients e (fun y => α y)))) x := by
      unfold chartLift nativePullback
      rw [chartExtDeriv_transition α he he' (e'.map_source hx') hxe]
    _ = _ := chartLift_transition he he' _ hx hx'

/-- Pointwise exterior derivative through a chart centered at each point. -/
def nativeExteriorDerivative (α : NativeForm 𝓘(ℝ, E) M k) : NativeForm 𝓘(ℝ, E) M (k + 1) :=
  fun x => chartLift (chartAt E x) (extDeriv (chartCoefficients (chartAt E x) α)) x

/-- The definition agrees with any smooth chart containing the point. -/
theorem nativeExteriorDerivative_eq_chart (α : SmoothForm 𝓘(ℝ, E) M k)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {x : M} (hx : x ∈ e.source) :
    nativeExteriorDerivative (fun y => α y) x =
      chartLift e (extDeriv (chartCoefficients e (fun y => α y))) x :=
  chartLift_extDeriv_independent α he (IsManifold.chart_mem_maximalAtlas x) hx
    (mem_chart_source E x)

/-- The chart-independent exterior derivative is a smooth native section. -/
theorem contMDiff_nativeExteriorDerivative (α : SmoothForm 𝓘(ℝ, E) M k) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin (k + 1)]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) x
        (nativeExteriorDerivative (fun y => α y) x)) := by
  intro x
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) x
  have hx := mem_chart_source E x
  have h := chartLift_contMDiffAt he hx
    (contDiffAt_extDeriv (α.chartCoefficients_contDiffAt he ((chartAt E x).map_source hx)))
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds hx] with y hy
  exact congrArg (TotalSpace.mk' (E [⋀^Fin (k + 1)]→L[ℝ] ℝ) y)
    (nativeExteriorDerivative_eq_chart α he hy)

/-- Exterior derivative as an operation on smooth native differential forms. -/
def smoothExteriorDerivative (α : SmoothForm 𝓘(ℝ, E) M k) : SmoothForm 𝓘(ℝ, E) M (k + 1) :=
  ⟨nativeExteriorDerivative (fun y => α y), contMDiff_nativeExteriorDerivative α⟩

/-- In every smooth chart the constructed operator has the standard exterior derivative. -/
theorem chartCoefficients_smoothExteriorDerivative (α : SmoothForm 𝓘(ℝ, E) M k)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {y : E} (hy : y ∈ e.target) :
    chartCoefficients e (fun x => smoothExteriorDerivative α x) y =
      extDeriv (chartCoefficients e (fun x => α x)) y := by
  have h := chartCoefficients_chartLift he (extDeriv (chartCoefficients e (fun x => α x))) hy
  ext v
  change nativeExteriorDerivative (fun x => α x) (e.symm y)
    (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y (v i)) = _
  rw [nativeExteriorDerivative_eq_chart α he (e.map_target hy)]
  exact congrArg (fun A => A v) h

/-- The constructed native exterior derivative squares to zero. -/
theorem smoothExteriorDerivative_squared (α : SmoothForm 𝓘(ℝ, E) M k) :
    smoothExteriorDerivative (smoothExteriorDerivative α) = 0 := by
  ext x v
  let e := chartAt E x
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) x
  have hx := mem_chart_source E x
  have hy : e x ∈ e.target := e.map_source hx
  have heq : chartCoefficients e (fun y => smoothExteriorDerivative α y) =ᶠ[𝓝 (e x)]
      extDeriv (chartCoefficients e (fun y => α y)) := by
    filter_upwards [e.open_target.mem_nhds hy] with y hy'
    exact chartCoefficients_smoothExteriorDerivative α he hy'
  change nativeExteriorDerivative (fun y => smoothExteriorDerivative α y) x v = 0
  rw [nativeExteriorDerivative_eq_chart (smoothExteriorDerivative α) he hx]
  change extDeriv (chartCoefficients e (fun y => smoothExteriorDerivative α y)) (e x)
    (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (v i)) = 0
  rw [heq.extDeriv_eq, extDeriv_extDeriv_apply (α.chartCoefficients_contDiffAt he hy) (by simp)]
  rfl

/-- Exterior differentiation is additive on smooth native forms. -/
theorem smoothExteriorDerivative_add (α β : SmoothForm 𝓘(ℝ, E) M k) :
    smoothExteriorDerivative (α + β) = smoothExteriorDerivative α + smoothExteriorDerivative β := by
  ext x v
  let e := chartAt E x
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) x
  have hy : e x ∈ e.target := e.map_source (mem_chart_source E x)
  change (extDeriv (chartCoefficients e ((fun y => α y) + (fun y => β y))) (e x))
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (v i)) =
    (extDeriv (chartCoefficients e (fun y => α y)) (e x))
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (v i)) +
    (extDeriv (chartCoefficients e (fun y => β y)) (e x))
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (v i))
  rw [chartCoefficients_add, extDeriv_add
    ((α.chartCoefficients_contDiffAt he hy).differentiableAt (by simp))
    ((β.chartCoefficients_contDiffAt he hy).differentiableAt (by simp))]
  rfl

/-- Exterior differentiation commutes with constant scalar multiplication. -/
theorem smoothExteriorDerivative_smul (r : ℝ) (α : SmoothForm 𝓘(ℝ, E) M k) :
    smoothExteriorDerivative (r • α) = r • smoothExteriorDerivative α := by
  ext x v
  let e := chartAt E x
  change (extDeriv (chartCoefficients e (r • (fun y => α y))) (e x))
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (v i)) =
    r • (extDeriv (chartCoefficients e (fun y => α y)) (e x))
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x (v i))
  rw [chartCoefficients_smul, extDeriv_smul]
  rfl

/-- Exterior derivative as a linear map of spaces of smooth sections. -/
def smoothExteriorDerivativeLinear :
    SmoothForm 𝓘(ℝ, E) M k →ₗ[ℝ] SmoothForm 𝓘(ℝ, E) M (k + 1) where
  toFun := smoothExteriorDerivative
  map_add' := smoothExteriorDerivative_add
  map_smul' := smoothExteriorDerivative_smul

/-- The value of the exterior derivative depends only on the native form germ. -/
theorem smoothExteriorDerivative_local {α β : SmoothForm 𝓘(ℝ, E) M k} {x : M}
    (h : ∀ᶠ y in 𝓝 x, α y = β y) :
    smoothExteriorDerivative α x = smoothExteriorDerivative β x := by
  let e := chartAt E x
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) x
  have hx := mem_chart_source E x
  have ht : Filter.Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
    have hc : ContinuousAt e.symm (e x) :=
      (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx)).continuousAt
    simpa only [ContinuousAt, e.left_inv hx] using hc
  have hc : chartCoefficients e (fun y => α y) =ᶠ[𝓝 (e x)]
      chartCoefficients e (fun y => β y) := by
    filter_upwards [ht.eventually h] with y hy
    ext v
    change α (e.symm y) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y (v i)) =
      β (e.symm y) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y (v i))
    rw [hy]
  change chartLift e (extDeriv (chartCoefficients e (fun y => α y))) x =
    chartLift e (extDeriv (chartCoefficients e (fun y => β y))) x
  unfold chartLift nativePullback
  rw [hc.extDeriv_eq]

/-- On the model manifold the native definition is exactly the existing model derivative. -/
theorem nativeExteriorDerivative_flat (α : Form E k) : nativeExteriorDerivative α = extDeriv α := by
  funext x
  unfold nativeExteriorDerivative
  rw [chartAt_self_eq, chartCoefficients_refl, chartLift_refl]

/-- Flat smooth forms retain their original exterior derivative under the native embedding. -/
theorem smoothExteriorDerivative_flat (α : Form E k) (hα : ContDiff ℝ ∞ α) :
    (fun x => smoothExteriorDerivative (ofFlat α hα) x) = exteriorDerivative α :=
  nativeExteriorDerivative_flat α

end ProjectAInos.SmoothGeometry.DifferentialForm
