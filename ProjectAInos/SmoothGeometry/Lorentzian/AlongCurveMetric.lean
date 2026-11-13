/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurve

/-! # Metric compatibility along curves -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- The linear coordinate-frame map into the native tangent fibre. -/
def chartFieldMap (e : OpenPartialHomeomorph M E) (x : M) : E →L[ℝ] TM x :=
  (mfderiv I I e x).inverse.comp (NormedSpace.fromTangentSpace (e x)).symm.toContinuousLinearMap

omit [IsManifold I ∞ M] in
@[simp] theorem chartFieldMap_apply (e : OpenPartialHomeomorph M E) (x : M) (v : E) :
    chartFieldMap e x v = chartField e v x := rfl

/-- The metric in a coordinate frame, as a bilinear form on the model only.
No norm is introduced on any tangent fibre. -/
def chartMetric (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M E) (x : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  (ContinuousLinearMap.precomp ℝ (chartFieldMap e x)).comp
    ((g.form x).comp (chartFieldMap e x))

@[simp] theorem chartMetric_apply (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M E) (x : M) (v w : E) :
    g.chartMetric e x v w = g.form x (chartField e v x) (chartField e w x) := rfl

/-- Smoothness can be tested on the two fixed model vectors. -/
theorem chartMetric_contMDiffAt (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) :
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ) ∞ (g.chartMetric e) x := by
  apply Tensor.contMDiffAt_clm_iff.mpr
  intro v
  apply Tensor.contMDiffAt_clm_iff.mpr
  intro w
  exact g.contMDiffAt_pairing (chartField_contMDiffAt he hx v) (chartField_contMDiffAt he hx w)

/-- Metric compatibility holds for arbitrary differentiable tangent fields
along a differentiable curve, without ambient extensions. -/
theorem hasDerivAt_pairing_along (g : LorentzMetric σ d M)
    {γ : ℝ → M} {V W : AlongField (d := d) γ} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t)
    (hW : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (W s)) t) :
    HasDerivAt (fun s => g.form (γ s) (V s) (W s))
      (g.form (γ t) (g.covariantAlong V t) (W t) +
        g.form (γ t) (V t) (g.covariantAlong W t)) t := by
  -- Fix the norm-induced instances only on the coordinate bilinear-form model.
  -- This keeps the nested CLM derivative API's instances aligned.
  let bNorm : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let bSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  let := bNorm.toAddCommGroup
  let := bSpace.toModule
  let := bNorm.toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let e := chartAt E (γ t)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ t)
  have hx : γ t ∈ e.source := mem_chart_source E (γ t)
  let C := alongComponents e V
  let D := alongComponents e W
  let B : ℝ → E →L[ℝ] E →L[ℝ] ℝ := g.chartMetric e ∘ γ
  have hC : DifferentiableAt ℝ C t := alongComponents_mdifferentiableAt he hx hV
  have hD : DifferentiableAt ℝ D t := alongComponents_mdifferentiableAt he hx hW
  have hB : DifferentiableAt ℝ B t :=
    (((g.chartMetric_contMDiffAt he hx).mdifferentiableAt (by simp)).comp t hγ).differentiableAt
  have hBder : HasDerivAt B (deriv B t) t :=
    DifferentiableAt.hasDerivAt (𝕜 := ℝ) (F := E →L[ℝ] E →L[ℝ] ℝ) (f := B) hB
  let ev : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.apply ℝ ℝ (D t)).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) (C t))
  have hconst : deriv (fun s => B s (C t) (D t)) t = deriv B t (C t) (D t) :=
    (ev.hasFDerivAt.comp_hasDerivAt t hBder).deriv
  have hpair := g.mdifferentiableAt_pairing (chartField_mdifferentiableAt he hx (C t))
    (chartField_mdifferentiableAt he hx (D t))
  have hd := deriv_comp_curve hpair hγ
  change deriv (fun s => B s (C t) (D t)) t = _ at hd
  rw [hconst, g.leviCivita_metricCompatible (curveVelocity γ t)
    (chartField_mdifferentiableAt he hx (C t)) (chartField_mdifferentiableAt he hx (D t))] at hd
  have hcval : chartField e (C t) (γ t) = V t := chartField_tangentMap he hx (V t)
  have hdval : chartField e (D t) (γ t) = W t := chartField_tangentMap he hx (W t)
  rw [hcval, hdval] at hd
  have heq : (fun s => g.form (γ s) (V s) (W s)) =ᶠ[𝓝 t] fun s => B s (C s) (D s) := by
    filter_upwards [hγ.continuousAt (e.open_source.mem_nhds hx)] with s hs
    simp only [B, Function.comp_apply, chartMetric_apply, C, D, alongComponents,
      chartField_tangentMap he hs]
  have hp := ((hBder.clm_apply hC.hasDerivAt).clm_apply hD.hasDerivAt).congr_of_eventuallyEq heq
  apply hp.congr_deriv
  simp only [add_apply, hd, B, Function.comp_apply, chartMetric_apply, hcval, hdval]
  symm
  change g.form (γ t)
    (chartField e (deriv C t) (γ t) + g.leviCivita (chartField e (C t)) (γ t) (curveVelocity γ t))
    (W t) + g.form (γ t) (V t)
    (chartField e (deriv D t) (γ t) + g.leviCivita (chartField e (D t)) (γ t) (curveVelocity γ t)) = _
  simp only [map_add, add_apply]
  ring

end ProjectAInos.SmoothGeometry.LorentzMetric
