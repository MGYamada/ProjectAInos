/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeExteriorDerivative

/-! # Naturality of the native exterior derivative

Coordinate changes and general smooth maps use actual tangent derivatives.
Source and target model spaces may have different dimensions.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {E M F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ, F) ∞ N] {k : ℕ}

omit [IsManifold 𝓘(ℝ, E) ∞ M] [IsManifold 𝓘(ℝ, F) ∞ N] in
/-- Chart coefficients of a general pullback use the local coordinate map and its derivative. -/
theorem chartCoefficients_nativePullback {e : OpenPartialHomeomorph M E}
    {e' : OpenPartialHomeomorph N F}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N)
    {f : M → N} (α : NativeForm 𝓘(ℝ, F) N k) {y : E} (hy : y ∈ e.target)
    (hf : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ f (e.symm y))
    (hfy : f (e.symm y) ∈ e'.source) :
    chartCoefficients e (nativePullback 𝓘(ℝ, E) 𝓘(ℝ, F) f α) y =
      pullback (e' ∘ (f ∘ e.symm)) (chartCoefficients e' α) y := by
  have hs := contMDiffAt_symm_of_mem_maximalAtlas he hy
  have ht := contMDiffAt_of_mem_maximalAtlas he' hfy
  rw [chartCoefficients, ← nativePullback_comp_at 𝓘(ℝ, E) 𝓘(ℝ, E) 𝓘(ℝ, F)
    (hs.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  rw [← nativePullback_flat, nativePullback_comp_at 𝓘(ℝ, E) 𝓘(ℝ, F) 𝓘(ℝ, F)
    ((hf.comp y hs).mdifferentiableAt (by simp)) (ht.mdifferentiableAt (by simp))]
  ext v
  change α (f (e.symm y))
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (f ∘ e.symm) y (v i)) =
    chartLift e' (chartCoefficients e' α) (f (e.symm y))
      (fun i => mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) (f ∘ e.symm) y (v i))
  rw [chartLift_chartCoefficients he' α hfy]

/-- Exterior differentiation commutes with the coordinate expression of native pullback. -/
theorem chartExtDeriv_nativePullback (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯)
    (α : SmoothForm 𝓘(ℝ, F) N k) {e : OpenPartialHomeomorph M E}
    {e' : OpenPartialHomeomorph N F}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, F) ∞ N) {y : E}
    (hy : y ∈ e.target) (hfy : f (e.symm y) ∈ e'.source) :
    extDeriv (chartCoefficients e (fun x => smoothPullback 𝓘(ℝ, E) 𝓘(ℝ, F) f α x)) y =
      pullback (e' ∘ (f ∘ e.symm)) (extDeriv (chartCoefficients e' (fun x => α x))) y := by
  have hs := contMDiffAt_symm_of_mem_maximalAtlas he hy
  have hi := (f.contMDiff (e.symm y)).comp y hs
  have hnear : ∀ᶠ z in 𝓝 y, f (e.symm z) ∈ e'.source :=
    hi.continuousAt (e'.open_source.mem_nhds hfy)
  have heq : chartCoefficients e (fun x => smoothPullback 𝓘(ℝ, E) 𝓘(ℝ, F) f α x) =ᶠ[𝓝 y]
      pullback (e' ∘ (f ∘ e.symm)) (chartCoefficients e' (fun x => α x)) := by
    filter_upwards [e.open_target.mem_nhds hy, hnear] with z hz hfz
    exact chartCoefficients_nativePullback he he' (fun x => α x) hz (f.contMDiff _) hfz
  rw [heq.extDeriv_eq]
  exact extDeriv_pullback
    ((α.chartCoefficients_contDiffAt he' (e'.map_source hfy)).differentiableAt (by simp))
    (((contMDiffAt_of_mem_maximalAtlas he' hfy).comp y hi).contDiffAt) (by simp)

/-- The native exterior derivative commutes with every smooth pullback. -/
theorem smoothExteriorDerivative_pullback (f : C^∞⟮𝓘(ℝ, E), M; 𝓘(ℝ, F), N⟯)
    (α : SmoothForm 𝓘(ℝ, F) N k) :
    smoothExteriorDerivative (smoothPullback 𝓘(ℝ, E) 𝓘(ℝ, F) f α) =
      smoothPullback 𝓘(ℝ, E) 𝓘(ℝ, F) f (smoothExteriorDerivative α) := by
  ext x : 1
  let e := chartAt E x
  let e' := chartAt F (f x)
  have he := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := ∞) x
  have he' := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, F)) (n := ∞) (f x)
  have hx : x ∈ e.source := mem_chart_source E x
  have hfx : f x ∈ e'.source := mem_chart_source F (f x)
  have hfy : f (e.symm (e x)) ∈ e'.source := by simpa only [e.left_inv hx] using hfx
  apply nativeForm_eq_of_chartCoefficients he hx
  rw [chartCoefficients_smoothExteriorDerivative _ he (e.map_source hx),
    chartExtDeriv_nativePullback f α he he' (e.map_source hx) hfy]
  change pullback (e' ∘ (f ∘ e.symm)) (extDeriv (chartCoefficients e' (fun y => α y))) (e x) =
    chartCoefficients e (nativePullback 𝓘(ℝ, E) 𝓘(ℝ, F) f
      (fun y => smoothExteriorDerivative α y)) (e x)
  rw [chartCoefficients_nativePullback he he' _ (e.map_source hx) (f.contMDiff _) hfy]
  unfold pullback
  dsimp only [Function.comp_apply]
  rw [chartCoefficients_smoothExteriorDerivative α he' (e'.map_source hfy)]

end ProjectAInos.SmoothGeometry.DifferentialForm
