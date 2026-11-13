/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.Geodesic
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod

/-! # Local coordinate initial-value problems for Lorentz geodesics

The phase vector field is extracted from the native connection in an
arbitrary smooth chart. Its local smoothness supplies the hypotheses of
Picard–Lindelöf; Lipschitz assumptions are proved rather than postulated.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField ContinuousLinearMap Set Metric
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

private theorem autonomous_solution_contDiffOn_two
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → F} {α : ℝ → F} {s : Set ℝ} (hs : IsOpen s)
    (hf : ∀ t ∈ s, ContDiffAt ℝ 1 f (α t))
    (hα : ∀ t ∈ s, HasDerivAt α (f (α t)) t) : ContDiffOn ℝ 2 α s := by
  have hd : DifferentiableOn ℝ α s := fun t ht => (hα t ht).differentiableAt.differentiableWithinAt
  have heq : EqOn (deriv α) (f ∘ α) s := fun t ht => (hα t ht).deriv
  have hc : ContinuousOn (f ∘ α) s := fun t ht =>
    (hf t ht).continuousAt.comp_continuousWithinAt (hd.continuousOn t ht)
  have h1 : ContDiffOn ℝ 1 α s := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
    exact ⟨hd, by simp, contDiffOn_zero.mpr (hc.congr heq)⟩
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hs]
  refine ⟨hd, by simp, ContDiffOn.congr ?_ heq⟩
  intro t ht
  exact (hf t ht).comp_contDiffWithinAt t (h1 t ht)

private theorem autonomous_solution_unique
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → F} {α β : ℝ → F} {t₀ : ℝ}
    (hf : ContDiffAt ℝ 1 f (α t₀))
    (hα : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (f (α t)) t)
    (hβ : ∀ᶠ t in 𝓝 t₀, HasDerivAt β (f (β t)) t)
    (heq : α t₀ = β t₀) : α =ᶠ[𝓝 t₀] β := by
  obtain ⟨K, u, hu, hlu⟩ := hf.exists_lipschitzOnWith
  have ha := hα.self_of_nhds.continuousAt hu
  have hb : ∀ᶠ t in 𝓝 t₀, β t ∈ u := hβ.self_of_nhds.continuousAt (heq ▸ hu)
  exact ODE_solution_unique_of_eventually (v := fun _ => f) (s := fun _ => u)
    (Filter.Eventually.of_forall fun _ => hlu) (hα.and ha) (hβ.and hb) heq

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- The coordinate geodesic phase field `(q,v) ↦ (v,−Γ(q)(v,v))`.
Only its values with `q ∈ e.target` are used. -/
def chartGeodesicField (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M E)
    (z : E × E) : E × E :=
  (z.2, fun k => -(∑ i, ∑ j, g.chartChristoffel e (e.symm z.1) k i j * z.2 i * z.2 j))

/-- Smoothness of the native connection implies smoothness of its phase
field on the chart's coordinate domain. -/
theorem chartGeodesicField_contDiffAt (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {z : E × E} (hz : z.1 ∈ e.target) : ContDiffAt ℝ ∞ (g.chartGeodesicField e) z := by
  have hc (k i j : Fin (d + 1)) :
      ContDiffAt ℝ ∞ (fun z : E × E => g.chartChristoffel e (e.symm z.1) k i j) z := by
    have h := (g.chartChristoffel_contMDiffAt he (e.map_target hz) k i j).comp z.1
      (contMDiffAt_symm_of_mem_maximalAtlas he hz)
    exact h.contDiffAt.comp z contDiffAt_fst
  apply ContDiffAt.prodMk contDiffAt_snd
  apply contDiffAt_pi.mpr
  intro k
  exact (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j _ =>
    ((hc k i j).mul (by fun_prop)).mul (by fun_prop)).neg

/-- Coordinate geodesic IVPs have a `C²` solution on a positive open
interval, staying in the chart domain. This is a proved existence theorem
for arbitrary initial position in the chart and arbitrary initial velocity. -/
theorem exists_chartGeodesic (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {q : E} (hq : q ∈ e.target) (v : E) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → E × E, α t₀ = (q, v) ∧
      ContDiffOn ℝ 2 α (Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε),
        (α t).1 ∈ e.target ∧ HasDerivAt α (g.chartGeodesicField e (α t)) t := by
  have hF := (g.chartGeodesicField_contDiffAt he (z := (q, v)) hq).of_le (by simp : (1 : ℕ∞ω) ≤ ∞)
  obtain ⟨α, hinit, ε, hε, hode⟩ :=
    hF.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have htarget : ∀ᶠ t in 𝓝 t₀, (α t).1 ∈ e.target := by
    apply (hode t₀ ht₀).continuousAt.fst
    exact e.open_target.mem_nhds (by simpa [hinit] using hq)
  obtain ⟨δ, hδ, hδset⟩ := Metric.mem_nhds_iff.mp htarget
  let η := min ε δ
  have hη : 0 < η := lt_min hε hδ
  have hsub : Ioo (t₀ - η) (t₀ + η) ⊆ Ioo (t₀ - ε) (t₀ + ε) := by
    intro t ht
    have : η ≤ ε := min_le_left _ _
    constructor <;> linarith [ht.1, ht.2]
  have hstay (t : ℝ) (ht : t ∈ Ioo (t₀ - η) (t₀ + η)) : (α t).1 ∈ e.target := by
    apply hδset
    rw [Real.ball_eq_Ioo]
    have : η ≤ δ := min_le_right _ _
    constructor <;> linarith [ht.1, ht.2]
  refine ⟨η, hη, α, hinit, ?_, fun t ht => ⟨hstay t ht, hode t (hsub ht)⟩⟩
  exact autonomous_solution_contDiffOn_two isOpen_Ioo
    (fun t ht => (g.chartGeodesicField_contDiffAt he (hstay t ht)).of_le (by simp))
    (fun t ht => hode t (hsub ht))

/-- Germ uniqueness for the chart phase equation. Local Lipschitzness
follows from the constructed smooth connection. -/
theorem chartGeodesic_unique (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {α β : ℝ → E × E} {t₀ : ℝ} (hx : (α t₀).1 ∈ e.target)
    (hα : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (g.chartGeodesicField e (α t)) t)
    (hβ : ∀ᶠ t in 𝓝 t₀, HasDerivAt β (g.chartGeodesicField e (β t)) t)
    (heq : α t₀ = β t₀) : α =ᶠ[𝓝 t₀] β :=
  autonomous_solution_unique ((g.chartGeodesicField_contDiffAt he hx).of_le (by simp)) hα hβ heq

/-- A regular solution of the coordinate phase equation lifts to an
intrinsic affine geodesic on the chart source. -/
theorem isGeodesicOn_of_chartPhase (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {α : ℝ → E × E} {s : Set ℝ} (hs : IsOpen s) (hα : ContDiffOn ℝ 2 α s)
    (hstay : ∀ t ∈ s, (α t).1 ∈ e.target)
    (hode : ∀ t ∈ s, HasDerivAt α (g.chartGeodesicField e (α t)) t) :
    g.IsGeodesicOn s (fun t => e.symm (α t).1) := by
  let γ : ℝ → M := fun t => e.symm (α t).1
  have hq (t : ℝ) (ht : t ∈ s) : HasDerivAt (fun r => (α r).1) (α t).2 t :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t (hode t ht)
  have hv (t : ℝ) (ht : t ∈ s) :
      HasDerivAt (fun r => (α r).2) (g.chartGeodesicField e (α t)).2 t :=
    (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t (hode t ht)
  intro t ht
  have hx : γ t ∈ e.source := e.map_target (hstay t ht)
  have hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t :=
    ((contMDiffAt_symm_of_mem_maximalAtlas he (hstay t ht)).of_le (by simp)).comp t
      ((hα t ht).contDiffAt (hs.mem_nhds ht)).fst.contMDiffAt
  refine ⟨hγ, (g.geodesic_equation_iff_coordinates he hx hγ).mpr ?_⟩
  have heq : e ∘ γ =ᶠ[𝓝 t] fun r => (α r).1 := by
    filter_upwards [hs.mem_nhds ht] with r hr
    exact e.right_inv (hstay r hr)
  have hvel : deriv (e ∘ γ) =ᶠ[𝓝 t] fun r => (α r).2 := by
    filter_upwards [heq.deriv, hs.mem_nhds ht] with r hr hrs
    exact hr.trans (hq r hrs).deriv
  intro k
  rw [hvel.deriv_eq, hvel.self_of_nhds, (hv t ht).deriv]
  exact neg_add_cancel _

/-- At a `C²` geodesic point, chart position and ordinary coordinate velocity
solve the first-order phase equation. -/
theorem hasDerivAt_chartPhase (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {t : ℝ} (hx : γ t ∈ e.source)
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (ha : g.covariantAlong (curveVelocity γ) t = 0) :
    HasDerivAt (fun r => (e (γ r), deriv (e ∘ γ) r))
      (g.chartGeodesicField e (e (γ t), deriv (e ∘ γ) t)) t := by
  have hq : ContDiffAt ℝ 2 (e ∘ γ) t :=
    (((contMDiffAt_of_mem_maximalAtlas he hx).of_le (by simp)).comp t hγ).contDiffAt
  have hv := (hq.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h := ((hq.differentiableAt (by norm_num)).hasDerivAt.prodMk hv.hasDerivAt)
  have heq : deriv (deriv (e ∘ γ)) t =
      (g.chartGeodesicField e (e (γ t), deriv (e ∘ γ) t)).2 := by
    ext k
    change _ = -(∑ i, ∑ j, g.chartChristoffel e (e.symm (e (γ t))) k i j * _ * _)
    rw [e.left_inv hx]
    exact eq_neg_iff_add_eq_zero.mpr ((g.geodesic_equation_iff_coordinates he hx hγ).mp ha k)
  exact h.congr_deriv (Prod.ext rfl heq)

/-- Every actual tangent initial condition has a local affine geodesic.
The equality transporting the initial velocity is explicit, so no global
trivialization of the tangent bundle is used. -/
theorem exists_geodesic (g : LorentzMetric σ d M) (p : M)
    (v : TangentSpace I p) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → M, ∃ hp : γ t₀ = p,
      (hp ▸ curveVelocity (d := d) γ t₀) = v ∧
        g.IsGeodesicOn (Ioo (t₀ - ε) (t₀ + ε)) γ := by
  let e := chartAt E p
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas p
  have hx : p ∈ e.source := mem_chart_source E p
  obtain ⟨ε, hε, α, hinit, hα, hode⟩ :=
    g.exists_chartGeodesic he (e.map_source hx) (chartTangentMap e p v) t₀
  let γ : ℝ → M := fun t => e.symm (α t).1
  have hp : γ t₀ = p := by
    dsimp [γ]
    rw [hinit]
    exact e.left_inv hx
  have hg : g.IsGeodesicOn (Ioo (t₀ - ε) (t₀ + ε)) γ :=
    g.isGeodesicOn_of_chartPhase he isOpen_Ioo hα (fun t ht => (hode t ht).1)
      (fun t ht => (hode t ht).2)
  have ht₀ : t₀ ∈ Ioo (t₀ - ε) (t₀ + ε) := ⟨by linarith, by linarith⟩
  have heq : e ∘ γ =ᶠ[𝓝 t₀] fun t => (α t).1 := by
    filter_upwards [isOpen_Ioo.mem_nhds ht₀] with t ht
    exact e.right_inv (hode t ht).1
  have hq : HasDerivAt (fun t => (α t).1) (α t₀).2 t₀ :=
    (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t₀ (hode t₀ ht₀).2
  have hvel : chartTangentMap e (γ t₀) (curveVelocity γ t₀) = chartTangentMap e p v := by
    rw [chartTangentMap_curveVelocity he (hp.symm ▸ hx)
      ((hg t₀ ht₀).1.mdifferentiableAt (by norm_num)), heq.deriv_eq, hq.deriv, hinit]
  refine ⟨ε, hε, γ, hp, ?_, hg⟩
  apply (chartTangentEquiv he hx).injective
  change chartTangentMap e p (hp ▸ curveVelocity γ t₀) = chartTangentMap e p v
  rw [chartTangentMap_cast]
  exact hvel

/-- Local uniqueness of intrinsic geodesics from identical position and
actual tangent velocity. Only neighborhoods of the initial parameter are
needed; no completeness or global chart is assumed. -/
theorem geodesic_unique (g : LorentzMetric σ d M) {γ β : ℝ → M} {t₀ : ℝ}
    {s u : Set ℝ} (hs : s ∈ 𝓝 t₀) (hu : u ∈ 𝓝 t₀)
    (hγ : g.IsGeodesicOn s γ) (hβ : g.IsGeodesicOn u β)
    (hp : γ t₀ = β t₀) (hv : (hp ▸ curveVelocity (d := d) γ t₀) = curveVelocity β t₀) :
    γ =ᶠ[𝓝 t₀] β := by
  let e := chartAt E (γ t₀)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ t₀)
  have hx : γ t₀ ∈ e.source := mem_chart_source E (γ t₀)
  have hy : β t₀ ∈ e.source := hp ▸ hx
  have hγ₀ := (hγ t₀ (mem_of_mem_nhds hs)).1.mdifferentiableAt (by norm_num)
  have hβ₀ := (hβ t₀ (mem_of_mem_nhds hu)).1.mdifferentiableAt (by norm_num)
  have hnγ := hγ₀.continuousAt (e.open_source.mem_nhds hx)
  have hnβ := hβ₀.continuousAt (e.open_source.mem_nhds hy)
  let α : ℝ → E × E := fun t => (e (γ t), deriv (e ∘ γ) t)
  let α' : ℝ → E × E := fun t => (e (β t), deriv (e ∘ β) t)
  have hα : ∀ᶠ t in 𝓝 t₀, HasDerivAt α (g.chartGeodesicField e (α t)) t := by
    filter_upwards [hs, hnγ] with t ht hxt
    exact g.hasDerivAt_chartPhase he hxt (hγ t ht).1 (hγ t ht).2
  have hα' : ∀ᶠ t in 𝓝 t₀, HasDerivAt α' (g.chartGeodesicField e (α' t)) t := by
    filter_upwards [hu, hnβ] with t ht hyt
    exact g.hasDerivAt_chartPhase he hyt (hβ t ht).1 (hβ t ht).2
  have hinit : α t₀ = α' t₀ := by
    apply Prod.ext (congrArg e hp)
    change deriv (e ∘ γ) t₀ = deriv (e ∘ β) t₀
    rw [← chartTangentMap_curveVelocity he hx hγ₀,
      ← chartTangentMap_curveVelocity he hy hβ₀, ← hv, chartTangentMap_cast]
  have hsol := g.chartGeodesic_unique he (e.map_source hx) hα hα' hinit
  filter_upwards [hsol, hnγ, hnβ] with t ht hx' hy'
  exact e.injOn hx' hy' (congrArg Prod.fst ht)

end ProjectAInos.SmoothGeometry.LorentzMetric
