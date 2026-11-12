/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.ChartConnection
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-! # Covariant differentiation along a curve

Fields along a curve take values in the actual tangent fibres. Their
derivative is constructed in charts and shown independent of the chart;
no immersion or ambient extension of the field is assumed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle VectorField ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

/-- The velocity is an actual tangent vector, with no choice of coordinates. -/
def curveVelocity (γ : ℝ → M) (t : ℝ) : TM (γ t) :=
  mfderiv 𝓘(ℝ) I γ t ((NormedSpace.fromTangentSpace t).symm 1)

/-- A vector field along a curve, including curves with zero velocity or
self-intersections. -/
abbrev AlongField (γ : ℝ → M) := ∀ t : ℝ, TM (γ t)

/-- Coordinate components of an along-curve tangent field. -/
def alongComponents (e : OpenPartialHomeomorph M E) {γ : ℝ → M}
    (V : AlongField (d := d) γ) (t : ℝ) : E := chartTangentMap e (γ t) (V t)

omit [IsManifold I ∞ M] in
/-- Changing the written base point by equality does not change tangent
coordinates. This handles initial data without trivializing the bundle. -/
theorem chartTangentMap_cast (e : OpenPartialHomeomorph M E) {x y : M}
    (h : x = y) (v : TM x) : chartTangentMap e y (h ▸ v) = chartTangentMap e x v := by
  subst y
  rfl

omit [IsManifold I ∞ M] in
@[simp] theorem chartField_add (e : OpenPartialHomeomorph M E) (u v : E) (x : M) :
    chartField e (u + v) x = chartField e u x + chartField e v x := by
  simp [chartField, mpullback_apply, modelField]

omit [IsManifold I ∞ M] in
@[simp] theorem chartField_smul (e : OpenPartialHomeomorph M E) (a : ℝ) (v : E) (x : M) :
    chartField e (a • v) x = a • chartField e v x := by
  simp [chartField, mpullback_apply, modelField]

omit [IsManifold I ∞ M] in
@[simp] theorem chartField_zero (e : OpenPartialHomeomorph M E) (x : M) :
    chartField e 0 x = 0 := by
  simp [chartField, mpullback_apply, modelField]

omit [IsManifold I ∞ M] in
/-- The manifold chain rule identifies velocity components with coordinate
derivatives along the parameter. -/
theorem chartTangentMap_curveVelocity {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) {γ : ℝ → M} {t : ℝ}
    (hx : γ t ∈ e.source) (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    chartTangentMap e (γ t) (curveVelocity γ t) = deriv (e ∘ γ) t := by
  have h := mfderiv_comp t ((contMDiffAt_of_mem_maximalAtlas he hx).mdifferentiableAt
    (by simp)) hγ
  have hv := congrArg (fun L => L ((NormedSpace.fromTangentSpace t).symm 1)) h
  rw [mfderiv_eq_fderiv] at hv
  change deriv (e ∘ γ) t = chartTangentMap e (γ t) (curveVelocity γ t) at hv
  exact hv.symm

omit [IsManifold I ∞ M] in
/-- Chain rule along a curve for any normed-vector-space-valued function. -/
theorem deriv_comp_curve {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : M → F} {γ : ℝ → M} {t : ℝ}
    (hf : MDifferentiableAt I 𝓘(ℝ, F) f (γ t)) (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    deriv (f ∘ γ) t = mvfderiv I f (γ t) (curveVelocity γ t) := by
  have h := congrArg (fun L => L ((NormedSpace.fromTangentSpace t).symm 1))
    (mvfderiv_comp t hf hγ)
  rw [mvfderiv_eq_fderiv] at h
  exact h

/-- Local differentiability of an ambient tangent field gives differentiable
components in every smooth chart containing the point. -/
theorem chartTangentMap_mdifferentiableAt {V : ∀ x, TM x}
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source)
    (hV : MDifferentiableAt I ((I).prod I) (T% V) x) :
    MDifferentiableAt I I (fun y => chartTangentMap e y (V y)) x := by
  have h := (((contMDiffAt_of_mem_maximalAtlas he hx).contMDiffAt_tangentMap
    (m := 1) (by simp)).mdifferentiableAt (by norm_num)).comp x hV
  rw [mdifferentiableAt_totalSpace] at h
  simpa [chartTangentMap, tangentMap, NormedSpace.fromTangentSpace,
    tangentSpaceCastModel, TangentBundle.trivializationAt_apply] using! h.2

/-- The same coordinate regularity for a field along a curve, without any
ambient extension of that field. -/
theorem alongComponents_mdifferentiableAt {γ : ℝ → M} {V : AlongField (d := d) γ}
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {t : ℝ} (hx : γ t ∈ e.source)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t) :
    DifferentiableAt ℝ (alongComponents e V) t := by
  have h := (((contMDiffAt_of_mem_maximalAtlas he hx).contMDiffAt_tangentMap
    (m := 1) (by simp)).mdifferentiableAt (by norm_num)).comp t hV
  rw [mdifferentiableAt_totalSpace] at h
  apply MDifferentiableAt.differentiableAt
  simpa [alongComponents, chartTangentMap, tangentMap, NormedSpace.fromTangentSpace,
    tangentSpaceCastModel, TangentBundle.trivializationAt_apply] using! h.2

/-- In any chart a connection splits into differentiation of components
and its action on the constant coordinate field with the same value. -/
theorem leviCivita_chart_decomposition (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) {V : ∀ y, TM y}
    (hV : MDifferentiableAt I ((I).prod I) (T% V) x) (v : TM x) :
    g.leviCivita V x v =
      chartField e (mvfderiv I (fun y => chartTangentMap e y (V y)) x v) x +
      g.leviCivita (chartField e (chartTangentMap e x (V x))) x v := by
  let C : M → E := fun y => chartTangentMap e y (V y)
  have hC := chartTangentMap_mdifferentiableAt he hx hV
  have heq : ∀ᶠ y in 𝓝 x, (fun y => chartField e (C y) y) y = V y := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact chartField_tangentMap he hy (V y)
  have hW : MDifferentiableAt I ((I).prod I) (T% (fun y => chartField e (C y) y)) x := by
    apply hV.congr_of_eventuallyEq
    filter_upwards [heq] with y hy
    exact congrArg (fun v => TotalSpace.mk' E y v) hy
  have hcov := g.leviCivita.isCovariantDerivativeOnUniv.congr_of_eventuallyEq
    hW hV Filter.univ_mem heq
  apply (chartTangentEquiv he hx).injective
  ext k
  have h₁ := g.leviCivita_chart_coordinates he hx hC (chartTangentMap e x v) k
  have h₂ := g.leviCivita_chart_coordinates he hx (V := fun _ => C x)
    mdifferentiableAt_const (chartTangentMap e x v) k
  rw [hcov, chartField_tangentMap he hx] at h₁
  simp only [chartField_tangentMap he hx, mvfderiv, mfderiv_const, comp_zero,
    zero_apply, Pi.zero_apply, zero_add] at h₂
  simp only [chartTangentEquiv_apply, map_add, Pi.add_apply, chartTangentMap_field he hx]
  rw [h₁, h₂]

/-- Chart construction of the covariant derivative along a curve. The second
term uses the native connection on the constant coordinate field with value
`V t`; no extension of the entire along-curve field is chosen. -/
def chartCovariantAlong (g : LorentzMetric σ d M) (e : OpenPartialHomeomorph M E)
    {γ : ℝ → M} (V : AlongField (d := d) γ) (t : ℝ) : TM (γ t) :=
  chartField e (deriv (alongComponents e V) t) (γ t) +
    g.leviCivita (chartField e (alongComponents e V t)) (γ t) (curveVelocity γ t)

/-- The chart construction is independent of the chart on every overlap.
Only differentiability of the curve and the source-chart components is
required; neither nonzero velocity nor an ambient field extension is used. -/
theorem chartCovariantAlong_eq (g : LorentzMetric σ d M)
    {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {V : AlongField (d := d) γ} {t : ℝ}
    (hx : γ t ∈ e.source) (hx' : γ t ∈ e'.source)
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hC : DifferentiableAt ℝ (alongComponents e V) t) :
    g.chartCovariantAlong e V t = g.chartCovariantAlong e' V t := by
  let C := alongComponents e V
  let τ : E → E := e' ∘ e.symm
  let J : ℝ → E →L[ℝ] E := fun s => fderiv ℝ τ (e (γ s))
  let w := C t
  let W := chartField e w
  let B : M → E := fun y => chartTangentMap e' y (W y)
  have hcoord : DifferentiableAt ℝ (e ∘ γ) t :=
    (((contMDiffAt_of_mem_maximalAtlas he hx).mdifferentiableAt (by simp)).comp t hγ).differentiableAt
  have hJ : DifferentiableAt ℝ J t :=
    (((chartTransition_contDiffAt he he' hx hx').fderiv_right (m := 1)
      (by simp)).differentiableAt one_ne_zero).comp t hcoord
  have hn : ∀ᶠ s in 𝓝 t, γ s ∈ e.source ∧ γ s ∈ e'.source :=
    hγ.continuousAt (Filter.inter_mem (e.open_source.mem_nhds hx) (e'.open_source.mem_nhds hx'))
  have heq : alongComponents e' V =ᶠ[𝓝 t] fun s => J s (C s) := by
    filter_upwards [hn] with s hs
    exact chartTangentMap_transition he he' hs.1 hs.2 (V s)
  have hd := heq.deriv_eq
  rw [deriv_clm_apply hJ hC] at hd
  have hW := chartField_mdifferentiableAt he hx w
  have hB := chartTangentMap_mdifferentiableAt he' hx' hW
  have heqB : B ∘ γ =ᶠ[𝓝 t] fun s => J s w := by
    filter_upwards [hn] with s hs
    dsimp only [B, W, Function.comp_apply]
    rw [chartTangentMap_transition he he' hs.1 hs.2, chartTangentMap_field he hs.1]
  have hdB := heqB.deriv_eq
  rw [deriv_comp_curve hB hγ, deriv_clm_apply hJ (differentiableAt_const w)] at hdB
  simp only [deriv_const, map_zero, add_zero] at hdB
  have hBval : B (γ t) = alongComponents e' V t := by
    dsimp only [B, W, w, C, alongComponents]
    rw [chartField_tangentMap he hx]
  have hconn := g.leviCivita_chart_decomposition he' hx' hW (curveVelocity γ t)
  change g.leviCivita W (γ t) (curveVelocity γ t) =
    chartField e' (mvfderiv I B (γ t) (curveVelocity γ t)) (γ t) +
      g.leviCivita (chartField e' (B (γ t))) (γ t) (curveVelocity γ t) at hconn
  rw [hdB, hBval] at hconn
  change chartField e (deriv C t) (γ t) + g.leviCivita W (γ t) (curveVelocity γ t) = _
  rw [← chartField_transition he he' hx hx' (deriv C t), hconn]
  simp only [chartCovariantAlong, hd, chartField_add]
  change chartField e' (J t (deriv C t)) (γ t) +
    (chartField e' (deriv J t w) (γ t) + _) = _
  abel

/-- The covariant derivative along a curve, taking values in its actual
tangent fibre. The arbitrary-chart theorem below removes the defining
choice of chart at every differentiability point. -/
def covariantAlong (g : LorentzMetric σ d M) {γ : ℝ → M}
    (V : AlongField (d := d) γ) (t : ℝ) : TM (γ t) :=
  g.chartCovariantAlong (chartAt E (γ t)) V t

/-- The intrinsic along-curve derivative can be computed in any smooth chart. -/
theorem covariantAlong_eq_chart (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {V : AlongField (d := d) γ} {t : ℝ} (hx : γ t ∈ e.source)
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t) :
    g.covariantAlong V t = g.chartCovariantAlong e V t :=
  g.chartCovariantAlong_eq (IsManifold.chart_mem_maximalAtlas (γ t)) he
    (mem_chart_source E (γ t)) hx hγ
    (alongComponents_mdifferentiableAt (IsManifold.chart_mem_maximalAtlas (γ t))
      (mem_chart_source E (γ t)) hV)

/-- Restricting a differentiable ambient vector field to a curve recovers the
original Levi-Civita derivative in the curve's velocity direction. -/
theorem covariantAlong_ambient (g : LorentzMetric σ d M)
    {γ : ℝ → M} {V : ∀ x, TM x} {t : ℝ}
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : MDifferentiableAt I ((I).prod I) (T% V) (γ t)) :
    g.covariantAlong (fun s => V (γ s)) t = g.leviCivita V (γ t) (curveVelocity γ t) := by
  let e := chartAt E (γ t)
  have he : e ∈ IsManifold.maximalAtlas I ∞ M := IsManifold.chart_mem_maximalAtlas (γ t)
  have hx : γ t ∈ e.source := mem_chart_source E (γ t)
  have hC := chartTangentMap_mdifferentiableAt he hx hV
  have hd := deriv_comp_curve hC hγ
  change deriv (alongComponents e (fun s => V (γ s))) t = _ at hd
  change g.chartCovariantAlong e (fun s => V (γ s)) t = _
  rw [chartCovariantAlong, hd]
  exact (g.leviCivita_chart_decomposition he hx hV (curveVelocity γ t)).symm

/-- Ambient extensions, whenever they exist, give the same along-curve
derivative if their restrictions agree near the parameter value. -/
theorem covariantAlong_congr (g : LorentzMetric σ d M) {γ : ℝ → M}
    {V W : AlongField (d := d) γ} {t : ℝ} (h : ∀ᶠ s in 𝓝 t, V s = W s) :
    g.covariantAlong V t = g.covariantAlong W t := by
  have hc : alongComponents (chartAt E (γ t)) V =ᶠ[𝓝 t]
      alongComponents (chartAt E (γ t)) W := h.mono fun s hs => congrArg _ hs
  simp only [covariantAlong, chartCovariantAlong, hc.deriv_eq, hc.self_of_nhds]

/-- Additivity of the local construction at differentiable components. -/
theorem chartCovariantAlong_add (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {V W : AlongField (d := d) γ} {t : ℝ} (hx : γ t ∈ e.source)
    (hV : DifferentiableAt ℝ (alongComponents e V) t)
    (hW : DifferentiableAt ℝ (alongComponents e W) t) :
    g.chartCovariantAlong e (V + W) t =
      g.chartCovariantAlong e V t + g.chartCovariantAlong e W t := by
  have hc : alongComponents e (V + W) = alongComponents e V + alongComponents e W := by
    funext s
    exact map_add _ _ _
  have hf : chartField e (alongComponents e V t + alongComponents e W t) =
      chartField e (alongComponents e V t) + chartField e (alongComponents e W t) := by
    funext y
    exact chartField_add e _ _ y
  simp only [chartCovariantAlong, hc, Pi.add_apply]
  rw [deriv_add hV hW, chartField_add, hf,
    g.leviCivita.isCovariantDerivativeOnUniv.add
      (chartField_mdifferentiableAt he hx _) (chartField_mdifferentiableAt he hx _)]
  simp only [add_apply]
  abel

/-- The local along-curve construction obeys the parameter Leibniz rule. -/
theorem chartCovariantAlong_smul (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {V : AlongField (d := d) γ} {f : ℝ → ℝ} {t : ℝ}
    (hx : γ t ∈ e.source) (hf : DifferentiableAt ℝ f t)
    (hV : DifferentiableAt ℝ (alongComponents e V) t) :
    g.chartCovariantAlong e (fun s => f s • V s) t =
      deriv f t • V t + f t • g.chartCovariantAlong e V t := by
  have hc : alongComponents e (fun s => f s • V s) = fun s => f s • alongComponents e V s := by
    funext s
    exact map_smul _ _ _
  have hfield : chartField e (f t • alongComponents e V t) =
      f t • chartField e (alongComponents e V t) := by
    funext y
    exact chartField_smul e _ _ y
  simp only [chartCovariantAlong, hc]
  rw [deriv_fun_smul hf hV, chartField_add, chartField_smul, chartField_smul, hfield,
    g.leviCivita.isCovariantDerivativeOnUniv.smul_const (f t)
      (chartField_mdifferentiableAt he hx _)]
  simp only [smul_apply, alongComponents, chartField_tangentMap he hx, smul_add]
  abel

/-- Intrinsic additivity for differentiable fields along the same curve. -/
theorem covariantAlong_add (g : LorentzMetric σ d M)
    {γ : ℝ → M} {V W : AlongField (d := d) γ} {t : ℝ}
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t)
    (hW : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (W s)) t) :
    g.covariantAlong (V + W) t = g.covariantAlong V t + g.covariantAlong W t :=
  g.chartCovariantAlong_add (IsManifold.chart_mem_maximalAtlas (γ t))
    (mem_chart_source E (γ t))
    (alongComponents_mdifferentiableAt (IsManifold.chart_mem_maximalAtlas (γ t))
      (mem_chart_source E (γ t)) hV)
    (alongComponents_mdifferentiableAt (IsManifold.chart_mem_maximalAtlas (γ t))
      (mem_chart_source E (γ t)) hW)

/-- Intrinsic Leibniz rule with a scalar function of the parameter. -/
theorem covariantAlong_smul (g : LorentzMetric σ d M)
    {γ : ℝ → M} {V : AlongField (d := d) γ} {f : ℝ → ℝ} {t : ℝ}
    (hf : DifferentiableAt ℝ f t)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t) :
    g.covariantAlong (fun s => f s • V s) t =
      deriv f t • V t + f t • g.covariantAlong V t :=
  g.chartCovariantAlong_smul (IsManifold.chart_mem_maximalAtlas (γ t))
    (mem_chart_source E (γ t)) hf
    (alongComponents_mdifferentiableAt (IsManifold.chart_mem_maximalAtlas (γ t))
      (mem_chart_source E (γ t)) hV)

/-- The intrinsic derivative has the usual coordinate expression in every
smooth chart that contains the curve point. -/
theorem covariantAlong_coordinates (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {V : AlongField (d := d) γ} {t : ℝ} (hx : γ t ∈ e.source)
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t) (k : Fin (d + 1)) :
    chartTangentMap e (γ t) (g.covariantAlong V t) k =
      deriv (alongComponents e V) t k + ∑ i, ∑ j,
        g.chartChristoffel e (γ t) k i j * deriv (e ∘ γ) t i * alongComponents e V t j := by
  rw [g.covariantAlong_eq_chart he hx hγ hV, chartCovariantAlong]
  simp only [map_add, Pi.add_apply, chartTangentMap_field he hx]
  have hdir : chartField e (deriv (e ∘ γ) t) (γ t) = curveVelocity γ t := by
    rw [← chartTangentMap_curveVelocity he hx hγ, chartField_tangentMap he hx]
  have h := g.leviCivita_chart_coordinates he hx
    (V := fun _ => alongComponents e V t) mdifferentiableAt_const (deriv (e ∘ γ) t) k
  rw [hdir] at h
  simpa [mvfderiv] using congrArg (fun a => deriv (alongComponents e V) t k + a) h

end ProjectAInos.SmoothGeometry.LorentzMetric
