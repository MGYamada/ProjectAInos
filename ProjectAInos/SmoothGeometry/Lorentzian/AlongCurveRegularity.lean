/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurveMetric

/-! # Reconstructing regular tangent fields along curves from coordinates -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- Regular coordinate components and a regular base curve reconstruct a
regular field in the actual tangent bundle. -/
theorem chartAlong_contMDiffAt {n : ℕ∞} {γ : ℝ → M} {C : ℝ → E} {t : ℝ}
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : γ t ∈ e.source) (hγ : ContMDiffAt 𝓘(ℝ) I n γ t)
    (hC : ContDiffAt ℝ n C t) :
    ContMDiffAt 𝓘(ℝ) ((I).prod I) n
      (fun s => TotalSpace.mk' E (γ s) (chartField e (C s) (γ s))) t := by
  let f := trivializationAt E TM (γ t)
  have hf : γ t ∈ f.baseSet := mem_baseSet_trivializationAt E TM (γ t)
  let G : M → E →L[ℝ] E := fun y => (f.continuousLinearMapAt ℝ y).comp (chartFieldMap e y)
  have hG : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ G (γ t) := by
    apply Tensor.contMDiffAt_clm_iff.mpr
    intro v
    have hv := chartField_contMDiffAt he hx v
    rw [contMDiffAt_section] at hv
    apply hv.congr_of_eventuallyEq
    filter_upwards [f.open_baseSet.mem_nhds hf] with y hy
    simp only [G, comp_apply, chartFieldMap_apply,
      Trivialization.continuousLinearMapAt_apply_of_mem ℝ f hy]
    rfl
  apply contMDiffAt_totalSpace.mpr
  refine ⟨hγ, ?_⟩
  apply (((hG.of_le (by simp)).comp t hγ).clm_apply hC.contMDiffAt).congr_of_eventuallyEq
  filter_upwards [hγ.continuousAt (f.open_baseSet.mem_nhds hf)] with s hs
  simp only [G, Function.comp_apply, comp_apply, chartFieldMap_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ f hs]
  rfl

/-- Differentiable coordinate components suffice for native
differentiability along a differentiable base curve. -/
theorem chartAlong_mdifferentiableAt {γ : ℝ → M} {C : ℝ → E} {t : ℝ}
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : γ t ∈ e.source) (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hC : DifferentiableAt ℝ C t) :
    MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (chartField e (C s) (γ s))) t := by
  let f := trivializationAt E TM (γ t)
  have hf : γ t ∈ f.baseSet := mem_baseSet_trivializationAt E TM (γ t)
  let G : M → E →L[ℝ] E := fun y => (f.continuousLinearMapAt ℝ y).comp (chartFieldMap e y)
  have hG : ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E) ∞ G (γ t) := by
    apply Tensor.contMDiffAt_clm_iff.mpr
    intro v
    have hv := chartField_contMDiffAt he hx v
    rw [contMDiffAt_section] at hv
    apply hv.congr_of_eventuallyEq
    filter_upwards [f.open_baseSet.mem_nhds hf] with y hy
    simp only [G, comp_apply, chartFieldMap_apply,
      Trivialization.continuousLinearMapAt_apply_of_mem ℝ f hy]
    rfl
  rw [mdifferentiableAt_totalSpace]
  refine ⟨hγ, ?_⟩
  apply (((hG.mdifferentiableAt (by simp)).comp t hγ).clm_apply
    hC.mdifferentiableAt).congr_of_eventuallyEq
  filter_upwards [hγ.continuousAt (f.open_baseSet.mem_nhds hf)] with s hs
  simp only [G, Function.comp_apply, comp_apply, chartFieldMap_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem ℝ f hs]
  rfl

/-- Native differentiability is equivalent to differentiability of vector
components in any smooth chart, with differentiability of the curve explicit. -/
theorem alongField_mdifferentiableAt_iff {γ : ℝ → M} {V : AlongField (d := d) γ} {t : ℝ}
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : γ t ∈ e.source) (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t ↔
        DifferentiableAt ℝ (alongComponents e V) t := by
  refine ⟨alongComponents_mdifferentiableAt he hx, fun hV => ?_⟩
  apply (chartAlong_mdifferentiableAt he hx hγ hV).congr_of_eventuallyEq
  filter_upwards [hγ.continuousAt (e.open_source.mem_nhds hx)] with s hs
  simp only [alongComponents, chartField_tangentMap he hs]

/-- Addition preserves native differentiability along the same curve. -/
theorem alongField_mdifferentiableAt_add {γ : ℝ → M} {V W : AlongField (d := d) γ} {t : ℝ}
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t)
    (hW : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (W s)) t) :
    MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) ((V + W) s)) t := by
  have hγ := ((mdifferentiableAt_totalSpace I _).mp hV).1
  let e := chartAt E (γ t)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ t)
  have hx : γ t ∈ e.source := mem_chart_source E (γ t)
  apply (alongField_mdifferentiableAt_iff he hx hγ).mpr
  have heq : alongComponents e (V + W) = alongComponents e V + alongComponents e W := by
    funext s
    exact map_add _ _ _
  rw [heq]
  exact (alongComponents_mdifferentiableAt he hx hV).add (alongComponents_mdifferentiableAt he hx hW)

/-- Scalar multiplication preserves native differentiability of along fields. -/
theorem alongField_mdifferentiableAt_smul {γ : ℝ → M} {V : AlongField (d := d) γ}
    {f : ℝ → ℝ} {t : ℝ} (hf : DifferentiableAt ℝ f t)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t) :
    MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (f s • V s)) t := by
  have hγ := ((mdifferentiableAt_totalSpace I _).mp hV).1
  let e := chartAt E (γ t)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ t)
  have hx : γ t ∈ e.source := mem_chart_source E (γ t)
  apply (alongField_mdifferentiableAt_iff he hx hγ).mpr
  have heq : alongComponents e (fun s => f s • V s) = fun s => f s • alongComponents e V s := by
    funext s
    exact map_smul _ _ _
  rw [heq]
  exact hf.smul (alongComponents_mdifferentiableAt he hx hV)

/-- The zero field is differentiable along a differentiable curve. -/
theorem alongField_zero_mdifferentiableAt {γ : ℝ → M} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (0 : TM (γ s))) t := by
  simpa only [chartField_zero] using chartAlong_mdifferentiableAt
    (IsManifold.chart_mem_maximalAtlas (γ t)) (mem_chart_source E (γ t)) hγ
    (differentiableAt_const (0 : E))

end ProjectAInos.SmoothGeometry.LorentzMetric
