/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Calculus
public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeNaturality

/-! # Exterior product on native finite-dimensional smooth forms

The coordinate product is lifted through actual charts. The pullback law proves
independence of the chart. No norm on native tangent fibres or global frame is used.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {n k l : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Fin n → ℝ) M]
  [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M]

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] in
/-- Wedges of chart coefficients satisfy the pullback overlap law. -/
theorem chartWedge_transition (α : NativeForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : NativeForm 𝓘(ℝ, Fin n → ℝ) M l)
    {e e' : OpenPartialHomeomorph M (Fin n → ℝ)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ M) {y : Fin n → ℝ}
    (hy : y ∈ e'.target) (hye : e'.symm y ∈ e.source) :
    wedge (chartCoefficients e' α) (chartCoefficients e' β) y =
      pullback (e ∘ e'.symm) (wedge (chartCoefficients e α) (chartCoefficients e β)) y := by
  rw [pullback_wedge]
  change wedgeFiber _ _ = wedgeFiber _ _
  rw [chartCoefficients_transition he he' α hy hye,
    chartCoefficients_transition he he' β hy hye]

omit [IsManifold 𝓘(ℝ, Fin n → ℝ) ∞ M] in
/-- The native product obtained in any two overlapping smooth charts is identical. -/
theorem chartLift_wedge_independent (α : NativeForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : NativeForm 𝓘(ℝ, Fin n → ℝ) M l)
    {e e' : OpenPartialHomeomorph M (Fin n → ℝ)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ M) {x : M}
    (hx : x ∈ e.source) (hx' : x ∈ e'.source) :
    chartLift e' (wedge (chartCoefficients e' α) (chartCoefficients e' β)) x =
      chartLift e (wedge (chartCoefficients e α) (chartCoefficients e β)) x := by
  have hxe : e'.symm (e' x) ∈ e.source := by simpa only [e'.left_inv hx'] using hx
  calc
    _ = chartLift e' (pullback (e ∘ e'.symm)
        (wedge (chartCoefficients e α) (chartCoefficients e β))) x := by
      unfold chartLift nativePullback
      rw [chartWedge_transition α β he he' (e'.map_source hx') hxe]
    _ = _ := chartLift_transition he he' _ hx hx'

/-- Pointwise exterior product, transported from a chart centered at each point. -/
def nativeWedge (α : NativeForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : NativeForm 𝓘(ℝ, Fin n → ℝ) M l) : NativeForm 𝓘(ℝ, Fin n → ℝ) M (k + l) :=
  fun x => chartLift (chartAt (Fin n → ℝ) x)
    (wedge (chartCoefficients (chartAt (Fin n → ℝ) x) α)
      (chartCoefficients (chartAt (Fin n → ℝ) x) β)) x

/-- Every smooth chart gives the same native exterior product. -/
theorem nativeWedge_eq_chart (α : NativeForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : NativeForm 𝓘(ℝ, Fin n → ℝ) M l)
    {e : OpenPartialHomeomorph M (Fin n → ℝ)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ M) {x : M} (hx : x ∈ e.source) :
    nativeWedge α β x = chartLift e (wedge (chartCoefficients e α) (chartCoefficients e β)) x :=
  chartLift_wedge_independent α β he (IsManifold.chart_mem_maximalAtlas x) hx
    (mem_chart_source (Fin n → ℝ) x)

/-- Coordinate coefficients of the native product are the existing normalized wedge. -/
theorem chartCoefficients_nativeWedge (α : NativeForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : NativeForm 𝓘(ℝ, Fin n → ℝ) M l)
    {e : OpenPartialHomeomorph M (Fin n → ℝ)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ M) {y : Fin n → ℝ}
    (hy : y ∈ e.target) :
    chartCoefficients e (nativeWedge α β) y =
      wedge (chartCoefficients e α) (chartCoefficients e β) y := by
  have h := chartCoefficients_chartLift he (wedge (chartCoefficients e α) (chartCoefficients e β)) hy
  ext v
  change nativeWedge α β (e.symm y)
    (fun i => mfderiv 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin n → ℝ) e.symm y (v i)) = _
  rw [nativeWedge_eq_chart α β he (e.map_target hy)]
  exact congrArg (fun A => A v) h

/-- Exterior product of smooth native forms is a smooth section. -/
theorem contMDiff_nativeWedge (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) :
    ContMDiff 𝓘(ℝ, Fin n → ℝ)
      (𝓘(ℝ, Fin n → ℝ).prod 𝓘(ℝ, (Fin n → ℝ) [⋀^Fin (k + l)]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' ((Fin n → ℝ) [⋀^Fin (k + l)]→L[ℝ] ℝ) x
        (nativeWedge (fun y => α y) (fun y => β y) x)) := by
  intro x
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x
  have hx := mem_chart_source (Fin n → ℝ) x
  have hy := (chartAt (Fin n → ℝ) x).map_source hx
  have h := chartLift_contMDiffAt he hx
    (wedge_contDiffAt (α.chartCoefficients_contDiffAt he hy) (β.chartCoefficients_contDiffAt he hy))
  apply h.congr_of_eventuallyEq
  filter_upwards [(chartAt (Fin n → ℝ) x).open_source.mem_nhds hx] with y hy
  exact congrArg (TotalSpace.mk' ((Fin n → ℝ) [⋀^Fin (k + l)]→L[ℝ] ℝ) y)
    (nativeWedge_eq_chart (fun z => α z) (fun z => β z) he hy)

/-- Exterior product on smooth sections of the native alternating tensor bundles. -/
def smoothWedge (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) : SmoothForm 𝓘(ℝ, Fin n → ℝ) M (k + l) :=
  ⟨nativeWedge (fun y => α y) (fun y => β y), contMDiff_nativeWedge α β⟩

theorem chartCoefficients_smoothWedge (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l)
    {e : OpenPartialHomeomorph M (Fin n → ℝ)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin n → ℝ) ∞ M) {y : Fin n → ℝ}
    (hy : y ∈ e.target) :
    chartCoefficients e (fun x => smoothWedge α β x) y =
      wedge (chartCoefficients e (fun x => α x)) (chartCoefficients e (fun x => β x)) y :=
  chartCoefficients_nativeWedge _ _ he hy

/-- Native wedge specializes exactly to the established flat normalization. -/
theorem nativeWedge_flat (α : Form (Fin n → ℝ) k) (β : Form (Fin n → ℝ) l) :
    nativeWedge α β = wedge α β := by
  funext x
  unfold nativeWedge
  rw [chartAt_self_eq, chartCoefficients_refl, chartCoefficients_refl, chartLift_refl]

theorem smoothWedge_flat (α : Form (Fin n → ℝ) k) (β : Form (Fin n → ℝ) l)
    (hα : ContDiff ℝ ∞ α) (hβ : ContDiff ℝ ∞ β) :
    (fun x => smoothWedge (ofFlat α hα) (ofFlat β hβ) x) = wedge α β :=
  nativeWedge_flat α β

theorem smoothWedge_add_left (α α' : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) :
    smoothWedge (α + α') β = smoothWedge α β + smoothWedge α' β := by
  ext x v
  change wedgeFiber
    (chartCoefficients (chartAt (Fin n → ℝ) x) ((fun y => α y) + (fun y => α' y)) _)
    _ _ = _
  rw [chartCoefficients_add]
  simp only [Pi.add_apply, map_add, LinearMap.add_apply, ContinuousAlternatingMap.add_apply]
  rfl

theorem smoothWedge_add_right (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β β' : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) :
    smoothWedge α (β + β') = smoothWedge α β + smoothWedge α β' := by
  ext x v
  change wedgeFiber _
    (chartCoefficients (chartAt (Fin n → ℝ) x) ((fun y => β y) + (fun y => β' y)) _) _ = _
  rw [chartCoefficients_add]
  simp only [Pi.add_apply, map_add, ContinuousAlternatingMap.add_apply]
  rfl

theorem smoothWedge_smul_left (r : ℝ) (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) :
    smoothWedge (r • α) β = r • smoothWedge α β := by
  ext x v
  change wedgeFiber
    (chartCoefficients (chartAt (Fin n → ℝ) x) (r • (fun y => α y)) _) _ _ = _
  rw [chartCoefficients_smul]
  simp only [Pi.smul_apply, map_smul, LinearMap.smul_apply, ContinuousAlternatingMap.smul_apply]
  rfl

theorem smoothWedge_smul_right (r : ℝ) (α : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k)
    (β : SmoothForm 𝓘(ℝ, Fin n → ℝ) M l) :
    smoothWedge α (r • β) = r • smoothWedge α β := by
  ext x v
  change wedgeFiber _
    (chartCoefficients (chartAt (Fin n → ℝ) x) (r • (fun y => β y)) _) _ = _
  rw [chartCoefficients_smul]
  simp only [Pi.smul_apply, map_smul, ContinuousAlternatingMap.smul_apply]
  rfl

/-- The native product as a bilinear map of spaces of smooth forms. -/
def smoothWedgeLinear : SmoothForm 𝓘(ℝ, Fin n → ℝ) M k →ₗ[ℝ]
    SmoothForm 𝓘(ℝ, Fin n → ℝ) M l →ₗ[ℝ] SmoothForm 𝓘(ℝ, Fin n → ℝ) M (k + l) where
  toFun α :=
    { toFun := smoothWedge α
      map_add' := smoothWedge_add_right α
      map_smul' := fun r β => smoothWedge_smul_right r α β }
  map_add' α α' := LinearMap.ext (smoothWedge_add_left α α')
  map_smul' r α := LinearMap.ext (smoothWedge_smul_left r α)

variable {m : ℕ} {N : Type*} [TopologicalSpace N] [ChartedSpace (Fin m → ℝ) N]
  [IsManifold 𝓘(ℝ, Fin m → ℝ) ∞ N]

/-- Pullback preserves exterior product for every smooth map, also across dimensions. -/
theorem smoothPullback_wedge (f : C^∞⟮𝓘(ℝ, Fin n → ℝ), M; 𝓘(ℝ, Fin m → ℝ), N⟯)
    (α : SmoothForm 𝓘(ℝ, Fin m → ℝ) N k) (β : SmoothForm 𝓘(ℝ, Fin m → ℝ) N l) :
    smoothPullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin m → ℝ) f (smoothWedge α β) =
      smoothWedge (smoothPullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin m → ℝ) f α)
        (smoothPullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin m → ℝ) f β) := by
  ext x : 1
  let e := chartAt (Fin n → ℝ) x
  let e' := chartAt (Fin m → ℝ) (f x)
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin n → ℝ)) (n := ∞) x
  have he' := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, Fin m → ℝ)) (n := ∞) (f x)
  have hx : x ∈ e.source := mem_chart_source (Fin n → ℝ) x
  have hfx : f x ∈ e'.source := mem_chart_source (Fin m → ℝ) (f x)
  have hy := e.map_source hx
  have hfy : f (e.symm (e x)) ∈ e'.source := by simpa only [e.left_inv hx] using hfx
  apply nativeForm_eq_of_chartCoefficients he hx
  rw [chartCoefficients_smoothWedge _ _ he hy]
  change chartCoefficients e
      (nativePullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin m → ℝ) f (fun y => smoothWedge α β y)) (e x) =
    wedgeFiber
      (chartCoefficients e (nativePullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin m → ℝ) f (fun y => α y)) (e x))
      (chartCoefficients e (nativePullback 𝓘(ℝ, Fin n → ℝ) 𝓘(ℝ, Fin m → ℝ) f (fun y => β y)) (e x))
  rw [chartCoefficients_nativePullback he he' _ hy (f.contMDiff _) hfy,
    chartCoefficients_nativePullback he he' _ hy (f.contMDiff _) hfy,
    chartCoefficients_nativePullback he he' _ hy (f.contMDiff _) hfy]
  calc
    _ = pullback (e' ∘ (f ∘ e.symm))
        (wedge (chartCoefficients e' (fun y => α y)) (chartCoefficients e' (fun y => β y))) (e x) := by
      unfold pullback
      dsimp only [Function.comp_apply]
      rw [chartCoefficients_smoothWedge α β he' (e'.map_source hfy)]
    _ = _ := congrFun (pullback_wedge _ _ _) (e x)

end ProjectAInos.SmoothGeometry.DifferentialForm
