/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurveRegularity
public import ProjectAInos.SmoothGeometry.Lorentzian.Geodesic
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Local parallel fields along prescribed curves

The linear coordinate ODE is extracted from the native Levi-Civita
connection. Local existence and uniqueness are derived analytically.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle ContinuousLinearMap Set Metric
open scoped Manifold ContDiff Topology NNReal

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The linear coordinate parallel-field equation `V' = A(t)V`.
Its coefficients are computed from the native connection and curve. -/
def chartParallelOperator (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M E)
    (γ : ℝ → M) (t : ℝ) : E →L[ℝ] E :=
  ContinuousLinearMap.pi fun k => ∑ i, ∑ j,
    (-(g.chartChristoffel e (γ t) k i j * deriv (e ∘ γ) t i)) • (proj j : E →L[ℝ] ℝ)

theorem chartParallelOperator_apply (g : LorentzMetric σ d M)
    (e : OpenPartialHomeomorph M E) (γ : ℝ → M) (t : ℝ) (v : E) (k : Fin (d + 1)) :
    g.chartParallelOperator e γ t v k =
      -(∑ i, ∑ j, g.chartChristoffel e (γ t) k i j * deriv (e ∘ γ) t i * v j) := by
  simp [chartParallelOperator, Finset.sum_neg_distrib, neg_mul]

/-- A `C²` curve gives `C¹` coefficients for the linear parallel equation. -/
theorem chartParallelOperator_contDiffAt (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {t : ℝ} (hx : γ t ∈ e.source)
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    ContDiffAt ℝ 1 (g.chartParallelOperator e γ) t := by
  have hq : ContDiffAt ℝ 2 (e ∘ γ) t :=
    (((contMDiffAt_of_mem_maximalAtlas he hx).of_le (by simp)).comp t hγ).contDiffAt
  have hq' := hq.derivWithin (m := 1) (by norm_num)
  apply ContMDiffAt.contDiffAt
  apply Tensor.contMDiffAt_clm_iff.mpr
  intro v
  apply ContDiffAt.contMDiffAt
  apply contDiffAt_pi.mpr
  intro k
  simp only [chartParallelOperator_apply]
  apply ContDiffAt.neg
  apply ContDiffAt.sum
  intro i _
  apply ContDiffAt.sum
  intro j _
  have hc := (((g.chartChristoffel_contMDiffAt he hx k i j).of_le (by simp)).comp t
    (hγ.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2))).contDiffAt
  exact (hc.mul ((proj i : E →L[ℝ] ℝ).contDiff.contDiffAt.comp t hq')).mul contDiffAt_const

/-- Native parallelism is precisely the linear coordinate ODE, with all
regularity and chart hypotheses explicit. -/
theorem covariantAlong_eq_zero_iff_hasDerivAt (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {V : AlongField (d := d) γ} {t : ℝ} (hx : γ t ∈ e.source)
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t) :
    g.covariantAlong V t = 0 ↔
      HasDerivAt (alongComponents e V)
        (g.chartParallelOperator e γ t (alongComponents e V t)) t := by
  have hC := alongComponents_mdifferentiableAt he hx hV
  have heq : g.covariantAlong V t = 0 ↔ deriv (alongComponents e V) t =
      g.chartParallelOperator e γ t (alongComponents e V t) := by
    constructor
    · intro hz
      ext k
      rw [chartParallelOperator_apply, eq_neg_iff_add_eq_zero,
        ← g.covariantAlong_coordinates he hx hγ hV k, hz, map_zero]
      rfl
    · intro hd
      apply (chartTangentEquiv he hx).injective
      ext k
      simp only [chartTangentEquiv_apply, map_zero, Pi.zero_apply,
        g.covariantAlong_coordinates he hx hγ hV k, hd, chartParallelOperator_apply,
        neg_add_cancel]
  rw [heq]
  exact ⟨fun h => hC.hasDerivAt.congr_deriv h, HasDerivAt.deriv⟩

/-- Coordinate ODE solutions give differentiable native parallel fields. -/
theorem isParallelOn_of_chartODE (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {C : ℝ → E} {s : Set ℝ}
    (hγ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ) I γ t)
    (hstay : ∀ t ∈ s, γ t ∈ e.source)
    (hC : ∀ t ∈ s, HasDerivAt C (g.chartParallelOperator e γ t (C t)) t) :
    g.IsParallelOn s (fun t => chartField e (C t) (γ t)) := by
  intro t ht
  have hV := chartAlong_mdifferentiableAt he (hstay t ht) (hγ t ht) (hC t ht).differentiableAt
  refine ⟨hV, (g.covariantAlong_eq_zero_iff_hasDerivAt he (hstay t ht) (hγ t ht) hV).mpr ?_⟩
  have heq : alongComponents e (fun t => chartField e (C t) (γ t)) =ᶠ[𝓝 t] C := by
    filter_upwards [(hγ t ht).continuousAt (e.open_source.mem_nhds (hstay t ht))] with r hr
    exact chartTangentMap_field he hr (C r)
  rw [heq.self_of_nhds]
  exact (hC t ht).congr_of_eventuallyEq heq

/-- Every tangent vector extends to a parallel field near a parameter of a
prescribed `C²` curve. Neither geodesicity nor nonzero speed is required. -/
theorem exists_parallel_local (g : LorentzMetric σ d M) {γ : ℝ → M} {t₀ : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t₀) (v : TangentSpace I (γ t₀)) :
    ∃ ε > (0 : ℝ), ∃ V : AlongField (d := d) γ, V t₀ = v ∧
      g.IsParallelOn (Ioo (t₀ - ε) (t₀ + ε)) V := by
  let e := chartAt E (γ t₀)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ t₀)
  have hx : γ t₀ ∈ e.source := mem_chart_source E (γ t₀)
  let A := g.chartParallelOperator e γ
  let w := chartTangentMap e (γ t₀) v
  let F : ℝ × E → ℝ × E := fun z => (1, A z.1 z.2)
  have hA : ContDiffAt ℝ 1 A t₀ := g.chartParallelOperator_contDiffAt he hx hγ
  have hF : ContDiffAt ℝ 1 F (t₀, w) :=
    contDiffAt_const.prodMk ((hA.comp (t₀, w) contDiffAt_fst).clm_apply contDiffAt_snd)
  obtain ⟨α, hinit, ε, hε, hode⟩ :=
    hF.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have htime : EqOn (fun t => (α t).1) id (Ioo (t₀ - ε) (t₀ + ε)) := by
    apply ODE_solution_unique_of_mem_Ioo (K := 0) (v := fun _ _ : ℝ => (1 : ℝ))
      (s := fun _ => Set.univ) (fun _ _ => (LipschitzWith.const 1).lipschitzOnWith) ht₀
    · intro t ht
      exact ⟨(ContinuousLinearMap.fst ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t (hode t ht), trivial⟩
    · intro t _
      exact ⟨hasDerivAt_id t, trivial⟩
    · exact congrArg Prod.fst hinit
  have hC (t : ℝ) (ht : t ∈ Ioo (t₀ - ε) (t₀ + ε)) :
      HasDerivAt (fun r => (α r).2) (A t (α t).2) t := by
    have h := (ContinuousLinearMap.snd ℝ ℝ E).hasFDerivAt.comp_hasDerivAt t (hode t ht)
    change HasDerivAt (fun r => (α r).2) (A (α t).1 (α t).2) t at h
    simpa only [htime ht, id_eq] using h
  have hγn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hγ.of_le (by norm_num))
  have hn : ∀ᶠ t in 𝓝 t₀, γ t ∈ e.source ∧ MDifferentiableAt 𝓘(ℝ) I γ t := by
    filter_upwards [hγ.continuousAt (e.open_source.mem_nhds hx), hγn] with t ht hgt
    exact ⟨ht, hgt.mdifferentiableAt (by norm_num)⟩
  obtain ⟨δ, hδ, hδset⟩ := Metric.eventually_nhds_iff_ball.mp hn
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  have hsub : Ioo (t₀ - η) (t₀ + η) ⊆ Ioo (t₀ - ε) (t₀ + ε) := by
    intro t ht
    have : η ≤ ε := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  have hgood (t : ℝ) (ht : t ∈ Ioo (t₀ - η) (t₀ + η)) :
      γ t ∈ e.source ∧ MDifferentiableAt 𝓘(ℝ) I γ t := by
    apply hδset
    rw [Real.ball_eq_Ioo]
    have : η ≤ δ := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨η, hη, fun t => chartField e (α t).2 (γ t), ?_, ?_⟩
  · change chartField e (α t₀).2 (γ t₀) = v
    rw [hinit]
    exact chartField_tangentMap he hx v
  · exact g.isParallelOn_of_chartODE he (fun t ht => (hgood t ht).2)
      (fun t ht => (hgood t ht).1) (fun t ht => hC t (hsub ht))

/-- Parallel fields with the same value agree near the initial parameter.
The local Lipschitz estimate is derived from the linear connection ODE. -/
theorem parallel_unique_local (g : LorentzMetric σ d M)
    {γ : ℝ → M} {V W : AlongField (d := d) γ} {t₀ : ℝ} {s u : Set ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t₀) (hs : s ∈ 𝓝 t₀) (hu : u ∈ 𝓝 t₀)
    (hV : g.IsParallelOn s V) (hW : g.IsParallelOn u W) (hinit : V t₀ = W t₀) :
    ∀ᶠ t in 𝓝 t₀, V t = W t := by
  let e := chartAt E (γ t₀)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ t₀)
  have hx : γ t₀ ∈ e.source := mem_chart_source E (γ t₀)
  let A := g.chartParallelOperator e γ
  have hA : ContinuousAt A t₀ := (g.chartParallelOperator_contDiffAt he hx hγ).continuousAt
  let K : ℝ≥0 := ‖A t₀‖₊ + 1
  have hb : ∀ᶠ t in 𝓝 t₀, ‖A t‖₊ ≤ K := by
    have hn : ∀ᶠ t in 𝓝 t₀, ‖A t‖ < ‖A t₀‖ + 1 :=
      hA.norm (isOpen_Iio.mem_nhds (lt_add_one _))
    filter_upwards [hn] with t ht
    exact_mod_cast ht.le
  have hγn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp
    (hγ.of_le (by norm_num))
  have hn := hγ.continuousAt (e.open_source.mem_nhds hx)
  have hCV : ∀ᶠ t in 𝓝 t₀, HasDerivAt (alongComponents e V) (A t (alongComponents e V t)) t := by
    filter_upwards [hs, hn, hγn] with t ht hxt hgt
    exact (g.covariantAlong_eq_zero_iff_hasDerivAt he hxt
      (hgt.mdifferentiableAt (by norm_num)) (hV t ht).1).mp (hV t ht).2
  have hCW : ∀ᶠ t in 𝓝 t₀, HasDerivAt (alongComponents e W) (A t (alongComponents e W t)) t := by
    filter_upwards [hu, hn, hγn] with t ht hxt hgt
    exact (g.covariantAlong_eq_zero_iff_hasDerivAt he hxt
      (hgt.mdifferentiableAt (by norm_num)) (hW t ht).1).mp (hW t ht).2
  have heq := ODE_solution_unique_of_eventually (v := fun t => A t) (s := fun _ => univ)
    (hb.mono fun t ht => ((A t).lipschitzWith.weaken ht).lipschitzOnWith)
    (hCV.mono fun _ ht => ⟨ht, trivial⟩) (hCW.mono fun _ ht => ⟨ht, trivial⟩)
    (congrArg (chartTangentMap e (γ t₀)) hinit)
  filter_upwards [heq, hn] with t ht hxt
  exact (chartTangentEquiv he hxt).injective ht

end ProjectAInos.SmoothGeometry.LorentzMetric
