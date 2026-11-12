/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeFlat
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! # Differential forms in actual smooth charts

All regularity and inverse statements are local to the chart domains.
The manifold is boundaryless; its model space need not be finite dimensional.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {k : ℕ}

/-- Model coefficients obtained by the actual derivative of the inverse chart. -/
def chartCoefficients (e : OpenPartialHomeomorph M E) (α : NativeForm 𝓘(ℝ, E) M k) :
    Form E k := nativePullback 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm α

/-- Lift a model form to native tangent fibres using the chart derivative. -/
def chartLift (e : OpenPartialHomeomorph M E) (β : Form E k) :
    NativeForm 𝓘(ℝ, E) M k := nativePullback 𝓘(ℝ, E) 𝓘(ℝ, E) e β

/-- Smoothness of chart coefficients only needs local smoothness of the native form. -/
theorem chartCoefficients_contDiffAt {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {α : NativeForm 𝓘(ℝ, E) M k} {y : E} (hy : y ∈ e.target)
    (hα : ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) x (α x)) (e.symm y)) :
    ContDiffAt ℝ ∞ (chartCoefficients e α) y :=
  (contMDiffAt_flat_iff _).mp (contMDiffAt_nativePullback 𝓘(ℝ, E) 𝓘(ℝ, E)
    (contMDiffAt_symm_of_mem_maximalAtlas he hy) hα)

/-- A smooth native form has smooth coefficients on the entire chart target. -/
theorem SmoothForm.chartCoefficients_contDiffAt (α : SmoothForm 𝓘(ℝ, E) M k)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {y : E} (hy : y ∈ e.target) : ContDiffAt ℝ ∞ (chartCoefficients e (fun x => α x)) y :=
  DifferentialForm.chartCoefficients_contDiffAt he hy (α.contMDiff (e.symm y))

/-- Smooth model coefficients lift smoothly at points of the chart source. -/
theorem chartLift_contMDiffAt {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {β : Form E k} {x : M}
    (hx : x ∈ e.source) (hβ : ContDiffAt ℝ ∞ β (e x)) :
    ContMDiffAt 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y (chartLift e β y)) x :=
  contMDiffAt_nativePullback 𝓘(ℝ, E) 𝓘(ℝ, E)
    (contMDiffAt_of_mem_maximalAtlas he hx) ((contMDiffAt_flat_iff β).mpr hβ)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Inverse chart derivatives recover the original native form on the source. -/
theorem chartLift_chartCoefficients {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (α : NativeForm 𝓘(ℝ, E) M k) {x : M} (hx : x ∈ e.source) :
    chartLift e (chartCoefficients e α) x = α x := by
  have hf := (contMDiffAt_of_mem_maximalAtlas he hx).mdifferentiableAt (by simp)
  have hg := (contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hx)).mdifferentiableAt (by simp)
  rw [chartLift, chartCoefficients, ← nativePullback_comp_at 𝓘(ℝ, E) 𝓘(ℝ, E) 𝓘(ℝ, E) hf hg]
  have h : (e.symm ∘ e) =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  rw [nativePullback_congr_map 𝓘(ℝ, E) 𝓘(ℝ, E) h α, nativePullback_id]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- The reverse recovery identity holds on the chart target. -/
theorem chartCoefficients_chartLift {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (β : Form E k) {y : E} (hy : y ∈ e.target) :
    chartCoefficients e (chartLift e β) y = β y := by
  have hf := (contMDiffAt_symm_of_mem_maximalAtlas he hy).mdifferentiableAt (by simp)
  have hg := (contMDiffAt_of_mem_maximalAtlas he (e.map_target hy)).mdifferentiableAt (by simp)
  rw [chartCoefficients, chartLift, ← nativePullback_comp_at 𝓘(ℝ, E) 𝓘(ℝ, E) 𝓘(ℝ, E) hf hg]
  have h : (e ∘ e.symm) =ᶠ[𝓝 y] id := by
    filter_upwards [e.open_target.mem_nhds hy] with z hz
    exact e.right_inv hz
  rw [nativePullback_congr_map 𝓘(ℝ, E) 𝓘(ℝ, E) h β, nativePullback_id]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Smoothness of the actual coordinate change on an overlap. -/
theorem formChartTransition_contDiffAt {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {y : E}
    (hy : y ∈ e'.target) (hye : e'.symm y ∈ e.source) :
    ContDiffAt ℝ ∞ (e ∘ e'.symm) y :=
  ((contMDiffAt_of_mem_maximalAtlas he hye).comp y
    (contMDiffAt_symm_of_mem_maximalAtlas he' hy)).contDiffAt

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Coefficients in two charts are related by the actual pullback of their transition map. -/
theorem chartCoefficients_transition {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (α : NativeForm 𝓘(ℝ, E) M k) {y : E}
    (hy : y ∈ e'.target) (hye : e'.symm y ∈ e.source) :
    chartCoefficients e' α y = pullback (e ∘ e'.symm) (chartCoefficients e α) y := by
  have hf := (contMDiffAt_symm_of_mem_maximalAtlas he' hy).mdifferentiableAt (by simp)
  have hg := (contMDiffAt_of_mem_maximalAtlas he hye).mdifferentiableAt (by simp)
  rw [← nativePullback_flat, nativePullback_comp_at 𝓘(ℝ, E) 𝓘(ℝ, E) 𝓘(ℝ, E) hf hg]
  ext v
  change α (e'.symm y) (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e'.symm y (v i)) =
    chartLift e (chartCoefficients e α) (e'.symm y)
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e'.symm y (v i))
  rw [chartLift_chartCoefficients he α hye]

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Lifting a form after coordinate change recovers the same native form. -/
theorem chartLift_transition {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (β : Form E k) {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    chartLift e' (pullback (e ∘ e'.symm) β) x = chartLift e β x := by
  have hf := (contMDiffAt_of_mem_maximalAtlas he' hx').mdifferentiableAt (by simp)
  have hxe : e'.symm (e' x) ∈ e.source := by simpa only [e'.left_inv hx'] using hx
  have hg := (formChartTransition_contDiffAt he he' (e'.map_source hx') hxe).contMDiffAt
    |>.mdifferentiableAt (by simp)
  rw [chartLift, chartLift, ← nativePullback_flat,
    ← nativePullback_comp_at 𝓘(ℝ, E) 𝓘(ℝ, E) 𝓘(ℝ, E) hf hg]
  apply nativePullback_congr_map
  filter_upwards [e'.open_source.mem_nhds hx'] with y hy
  exact congrArg e (e'.left_inv hy)

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
/-- Equality of chart coefficients at the image determines the native value. -/
theorem nativeForm_eq_of_chartCoefficients {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    {α β : NativeForm 𝓘(ℝ, E) M k} {x : M} (hx : x ∈ e.source)
    (h : chartCoefficients e α (e x) = chartCoefficients e β (e x)) : α x = β x := by
  calc
    α x = chartLift e (chartCoefficients e α) x := (chartLift_chartCoefficients he α hx).symm
    _ = chartLift e (chartCoefficients e β) x := by unfold chartLift nativePullback; rw [h]
    _ = β x := chartLift_chartCoefficients he β hx

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp] theorem chartCoefficients_add (e : OpenPartialHomeomorph M E)
    (α β : NativeForm 𝓘(ℝ, E) M k) :
    chartCoefficients e (α + β) = chartCoefficients e α + chartCoefficients e β := by
  funext y
  ext v
  rfl

omit [IsManifold 𝓘(ℝ, E) ∞ M] in
@[simp] theorem chartCoefficients_smul (e : OpenPartialHomeomorph M E)
    (r : ℝ) (α : NativeForm 𝓘(ℝ, E) M k) :
    chartCoefficients e (r • α) = r • chartCoefficients e α := by
  funext y
  ext v
  rfl

@[simp] theorem chartCoefficients_refl (α : Form E k) :
    chartCoefficients (OpenPartialHomeomorph.refl E) α = α :=
  nativePullback_id 𝓘(ℝ, E) α

@[simp] theorem chartLift_refl (β : Form E k) :
    chartLift (OpenPartialHomeomorph.refl E) β = β :=
  nativePullback_id 𝓘(ℝ, E) β

end ProjectAInos.SmoothGeometry.DifferentialForm
