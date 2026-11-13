/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import ProjectAInos.SmoothGeometry.Lorentzian.Dual
import ProjectAInos.SmoothGeometry.Lorentzian.PullbackExamples
import ProjectAInos.SmoothGeometry.Lorentzian.ChartExamples
import ProjectAInos.SmoothGeometry.Lorentzian.ChartConnection
import ProjectAInos.SmoothGeometry.Lorentzian.ConnectionExamples
import ProjectAInos.SmoothGeometry.Lorentzian.CurvatureExamples
import ProjectAInos.SmoothGeometry.Lorentzian.CurvatureNaturality
import ProjectAInos.SmoothGeometry.Lorentzian.ConformalExample
import ProjectAInos.SmoothGeometry.Lorentzian.LocalInertialExamples
import ProjectAInos.SmoothGeometry.Lorentzian.LocalFlatnessExamples
import ProjectAInos.SmoothGeometry.Lorentzian.FlatFrameExamples
import ProjectAInos.SmoothGeometry.Lorentzian.RadialFrame
import ProjectAInos.SmoothGeometry.Lorentzian.MotionExamples
import ProjectAInos.SmoothGeometry.Lorentzian.MotionODE
import ProjectAInos.SmoothGeometry.Lorentzian.PathExamples
import ProjectAInos.SmoothGeometry.Lorentzian.Regularity
import ProjectAInos.SmoothGeometry.Lorentzian.Restriction
import ProjectAInos.SmoothGeometry.Tensor.Bundle
import ProjectAInos.SmoothGeometry.ODE.VolterraExamples
import ProjectAInos.SmoothGeometry.ODE.RadialExamples

/-! Typed contracts for GR 5.1's shared metric, connection, curvature and motion APIs. These examples use
default elaborator options and do not assume a global frame or flatness. -/

open ProjectAInos.SmoothGeometry
open scoped Manifold ContDiff Topology

noncomputable section

section LinearODE

open LinearODE

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A : Curve (E →L[ℝ] E)} (hA : ‖A‖ < 1) (y : E)

example : (equationOperator A).IsInvertible := equationOperator_isInvertible hA

example (t : unitInterval) : solutionOperator A y t = y +
    ∫ s in 0..(t : ℝ), extend A s (extend (solutionOperator A y) s) :=
  solution_integral_eq hA y t

example : solutionOperator A y 0 = y := solution_initial hA y

example (t : unitInterval) :
    HasDerivWithinAt (extend (solutionOperator A y)) (A t (solutionOperator A y t))
      (Set.Icc (0 : ℝ) 1) t := solution_hasDerivWithinAt hA y t

example (f : Curve E) (h0 : f 0 = y)
    (hf : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt (extend f) (extend A t (extend f t)) t) :
    f = solutionOperator A y := eq_solution_of_hasDerivAt hA y f h0 hf

example : ‖solutionOperator A y‖ ≤ ‖y‖ / (1 - ‖A‖) := solution_norm_le hA y

example : ContDiffAt ℝ ∞
    (fun p : Curve (E →L[ℝ] E) × E => solutionOperator p.1 p.2) (A, y) :=
  solution_contDiffAt hA y

example {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {B : P → Curve (E →L[ℝ] E)} {z : P → E} {p : P}
    (hB : ContDiffAt ℝ ∞ B p) (hz : ContDiffAt ℝ ∞ z p) (hsmall : ‖B p‖ < 1) :
    ContDiffAt ℝ ∞ (fun q => solutionOperator (B q) (z q)) p :=
  solution_family_contDiffAt hB hz hsmall

example (t : unitInterval) :
    solutionOperator (rampCoefficient (E := E)) y t = Real.exp ((t : ℝ) ^ 2 / 4) • y :=
  solution_ramp y t

example {K T F : Type} [TopologicalSpace K] [CompactSpace K]
    [NormedAddCommGroup T] [NormedSpace ℝ T] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E × T → F} (hf : ContDiff ℝ ∞ f) (g : C(K, T)) :
    ContDiff ℝ ∞ (ContinuousFamily.slices f hf.continuous g) :=
  ContinuousFamily.slices_contDiff hf g

example (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : ContDiff ℝ ∞ Γ) (p : E) :
    ContDiff ℝ ∞ (radialCoefficient Γ hΓ p) := radialCoefficient_contDiff Γ hΓ p

example (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : ContDiff ℝ ∞ Γ) (p : E) :
    ∃ r : ℝ, 0 < r ∧
      (∀ x ∈ Metric.ball (0 : E) r, ‖radialCoefficient Γ hΓ p x‖ < 1) ∧
      (∀ x ∈ Metric.ball (0 : E) r, (radialEndpoint Γ hΓ p x).IsInvertible) ∧
      ContDiffOn ℝ ∞ (radialEndpoint Γ hΓ p) (Metric.ball 0 r) ∧
      ContDiffOn ℝ ∞ (radialCoframe Γ hΓ p) (Metric.ball 0 r) ∧
      radialCoframe Γ hΓ p 0 = ContinuousLinearMap.id ℝ E := exists_radial_ball Γ hΓ p

example (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : ContDiff ℝ ∞ Γ)
    (p x v : E) (s : unitInterval) (hx : ‖radialCoefficient Γ hΓ p x‖ < 1)
    (hsx : ‖radialCoefficient Γ hΓ p ((s : ℝ) • x)‖ < 1) :
    radialEndpoint Γ hΓ p ((s : ℝ) • x) v =
      solutionOperator (radialCoefficient Γ hΓ p x) v s :=
  radialEndpoint_on_ray Γ hΓ p x v s hx hsx

example (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : ContDiff ℝ ∞ Γ) (p : E)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ x ∈ Metric.ball (0 : E) r, ‖radialCoefficient Γ hΓ p x‖ < 1)
    {x : E} (hx : x ∈ Metric.ball (0 : E) r) (v : E) :
    fderiv ℝ (radialEndpoint Γ hΓ p) x x v =
      -(Γ (p + x) x (radialEndpoint Γ hΓ p x v)) :=
  radialEndpoint_fderiv_radial Γ hΓ p hr hsmall hx v

example (x : unitInterval) (v : ℝ) :
    radialEndpoint quadraticConnection quadraticConnection_contDiff 0 (x : ℝ) v =
      Real.exp ((x : ℝ) ^ 2 / 4) * v := quadratic_radialEndpoint x v

example (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : ContDiff ℝ ∞ Γ)
    {r : ℝ} (hr : 0 < r)
    (hsmall : ∀ x ∈ Metric.ball (0 : E) r, ‖radialCoefficient Γ hΓ 0 x‖ < 1)
    (hflat : IsFlatConnectionOn Γ (Metric.ball (0 : E) r))
    {x : E} (hx : x ∈ Metric.ball (0 : E) r) (u v : E) :
    fderiv ℝ (radialEndpoint Γ hΓ 0) x u v =
      -(Γ x u (radialEndpoint Γ hΓ 0 x v)) :=
  radialEndpoint_fderiv_of_flat Γ hΓ hr hsmall hflat hx u v

example (Γ : E → E →L[ℝ] E →L[ℝ] E) (hΓ : ContDiff ℝ ∞ Γ)
    {U : Set E} (hU : U ∈ 𝓝 (0 : E)) (hflat : IsFlatConnectionOn Γ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : E) r ⊆ U ∧
      ContDiffOn ℝ ∞ (radialCoframe Γ hΓ 0) (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball (0 : E) r, (radialCoframe Γ hΓ 0 x).IsInvertible) ∧
      radialCoframe Γ hΓ 0 0 = ContinuousLinearMap.id ℝ E ∧
      ∀ x ∈ Metric.ball (0 : E) r, ∀ u v,
        fderiv ℝ (radialCoframe Γ hΓ 0) x u v = radialCoframe Γ hΓ 0 x (Γ x u v) :=
  exists_parallel_radialCoframe Γ hΓ hU hflat

example {Γ : E → E →L[ℝ] E →L[ℝ] E} {U : Set E}
    (hflat : IsFlatConnectionOn Γ U) {x : E} (hx : x ∈ U) (u v w : E) :
    fderiv ℝ Γ x u v w - fderiv ℝ Γ x v u w +
      Γ x u (Γ x v w) - Γ x v (Γ x u w) = 0 := hflat x hx u v w

example (x v : LorentzianCharts.Plane)
    (hx : ‖radialCoefficient LorentzianCharts.shearRadialConnection
      LorentzianCharts.shearRadialConnection_contDiff 0 x‖ < 1) :
    radialEndpoint LorentzianCharts.shearRadialConnection
      LorentzianCharts.shearRadialConnection_contDiff 0 x v =
        ![v 0, v 1 - 2 * x 0 * v 0] := LorentzianCharts.shear_radialEndpoint x v hx

end LinearODE

section LocalInertial

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M) (p : M)

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

example : ∃ e : OpenPartialHomeomorph M E, g.IsInertialChartAt e p :=
  g.exists_inertialChart p

example (S : TangentSpace I p ≃L[ℝ] E)
    (hS : ∀ v w, g.form p v w = minkowskiForm σ d (S v) (S w)) :
    ∃ e : OpenPartialHomeomorph M E, g.IsInertialChartAt e p ∧
      ∀ v, chartTangentMap e p v = S v := g.exists_inertialChart_for_equiv p S hS

example {e : OpenPartialHomeomorph M E} (h : g.IsInertialChartAt e p) :
    e ∈ IsManifold.maximalAtlas I ∞ M ∧ p ∈ e.source ∧ e p = 0 ∧
      (∀ v w, g.form p (chartField e v p) (chartField e w p) = minkowskiForm σ d v w) ∧
      (∀ k i j, g.chartChristoffel e p k i j = 0) ∧
      ∀ i j, fderiv ℝ (fun y => g.chartComponent e (e.symm y) i j) (e p) = 0 :=
  ⟨h.smooth, h.mem_source, h.centered, h.metric, h.christoffel_zero, h.metric_derivative_zero⟩

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hp : p ∈ e.source) (L : E ≃L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E)
    (hB : ∀ u v, B u v = B v u) :
    ∃ e' : OpenPartialHomeomorph M E, e' ∈ IsManifold.maximalAtlas I ∞ M ∧
      p ∈ e'.source ∧ e' p = 0 ∧ fderiv ℝ (e' ∘ e.symm) (e p) = (L : E →L[ℝ] E) ∧
      ∀ u v, fderiv ℝ (fun y => fderiv ℝ (e' ∘ e.symm) y v) (e p) u = B u v :=
  QuadraticChart.exists_manifoldChart he hp L B hB

example (q : LorentzianCharts.Plane) :
    QuadraticChart.correction (ContinuousLinearEquiv.refl ℝ LorentzianCharts.Plane)
      (LorentzianCharts.metric.chartChristoffelBilinear LorentzianCharts.standardChart 0) 0 q =
      LorentzianCharts.shear q := LorentzianCharts.quadratic_correction_eq_shear q

example : LorentzianConformalExample.metric.IsInertialChartAt
    (Homeomorph.refl LorentzianConformalExample.Plane).toOpenPartialHomeomorph 0 ∧
      LorentzianConformalExample.metric.curvature 0 ≠ 0 ∧
      LorentzianConformalExample.metric.scalarCurvature 0 = -4 :=
  LorentzianConformalExample.inertial_origin_curved

end LocalInertial

section LocalFlatness

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {p : M} (hp : p ∈ e.source) :
    ∃ Γ : E → E →L[ℝ] E →L[ℝ] E, ContDiff ℝ ∞ Γ ∧
      ∃ V : Set E, IsOpen V ∧ e p ∈ V ∧ V ⊆ e.target ∧
        Set.EqOn Γ (fun q => g.chartChristoffelBilinear e (e.symm q)) V :=
  g.exists_smooth_chartChristoffel_extension he hp

example (h : g.IsLocallyMinkowski) (p : M) : g.curvature p = 0 := h.curvature_eq_zero p

example : g.IsLocallyMinkowski ↔ ∀ p, g.curvature p = 0 :=
  g.isLocallyMinkowski_iff_curvature_eq_zero

example (p : M) (hR : ∀ᶠ x in 𝓝 p, g.curvature x = 0) :
    ∃ c : OpenPartialHomeomorph M E, c ∈ IsManifold.maximalAtlas I ∞ M ∧
      p ∈ c.source ∧ ∀ x ∈ c.source, ∀ v w : TangentSpace I x,
        g.form x v w = minkowskiForm σ d (chartTangentMap c x v) (chartTangentMap c x w) :=
  g.exists_minkowskiChart_of_curvature_eq_zero_near p hR

example (p : M) (hR : ∀ᶠ x in 𝓝 p, g.curvature x = 0) :
    ∃ U : TopologicalSpace.Opens M, p ∈ U ∧ ∀ {x y : M} (a b : PiecewisePath d M x y),
      Set.range a.toPath ⊆ U → Set.range b.toPath ⊆ U → a.transport g = b.transport g :=
  g.exists_pathIndependent_neighborhood p hR

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {q : E} (hq : q ∈ e.target) (l i j k : Fin (d + 1)) :
    LinearODE.coefficientCurvature (fun z => g.chartChristoffelBilinear e (e.symm z)) q
      (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) l =
        g.chartCurvature e (e.symm q) l i j k := g.coefficientCurvature_basis he hq l i j k

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hR : ∀ x ∈ e.source, g.curvature x = 0) :
    LinearODE.IsFlatConnectionOn (fun q => g.chartChristoffelBilinear e (e.symm q)) e.target :=
  g.isFlatConnectionOn_of_curvature_eq_zero he hR

example : (minkowskiMetric σ d).IsLocallyMinkowski :=
  (minkowskiMetric σ d).isLocallyMinkowski_of_curvature_eq_zero (minkowski_curvature σ d)

example (U : TopologicalSpace.Opens M) (x : U) (u v w : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x ((g.restrict U).curvature x u v w) =
      g.curvature x.val (mfderiv I I (Subtype.val : U → M) x u)
        (mfderiv I I (Subtype.val : U → M) x v) (mfderiv I I (Subtype.val : U → M) x w) :=
  g.curvature_restrict U x u v w

example {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U)
    {θ : E → E →L[ℝ] E} (hθ : ContDiffOn ℝ ∞ θ U)
    (hclosed : ∀ x ∈ U, ∀ u v, fderiv ℝ θ x u v = fderiv ℝ θ x v u)
    (hinv : ∀ x ∈ U, (θ x).IsInvertible) {p : E} (hp : p ∈ U) :
    ∃ e : OpenPartialHomeomorph E E, p ∈ e.source ∧ e.source ⊆ U ∧ e p = 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      ∀ x ∈ e.source, HasFDerivAt e (θ x) x :=
  ClosedCoframe.exists_chart hU hconv hθ hclosed hinv hp

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {U : Set E} (hU : IsOpen U) (hconv : Convex ℝ U) (hUsub : U ⊆ e.target)
    {θ : E → E →L[ℝ] E} (hθ : ContDiffOn ℝ ∞ θ U)
    (hparallel : g.IsParallelChartCoframeOn e U θ)
    (hinv : ∀ q ∈ U, (θ q).IsInvertible) {p : M} (hp : p ∈ e.source) (hpU : e p ∈ U)
    (hnorm : ∀ v w, g.form p (chartField e v p) (chartField e w p) =
      minkowskiForm σ d (θ (e p) v) (θ (e p) w)) :
    ∃ c : OpenPartialHomeomorph M E, c ∈ IsManifold.maximalAtlas I ∞ M ∧
      p ∈ c.source ∧ ∀ x ∈ c.source, ∀ v w : TangentSpace I x,
        g.form x v w = minkowskiForm σ d (chartTangentMap c x v) (chartTangentMap c x w) :=
  g.exists_minkowskiChart_of_parallelCoframe he hU hconv hUsub hθ hparallel hinv hp hpU hnorm

example {e : OpenPartialHomeomorph M E} {U : Set E} {θ : E → E →L[ℝ] E}
    (h : g.IsParallelChartCoframeOn e U θ) {q : E} (hq : q ∈ U) (u v : E) :
    fderiv ℝ θ q u v = θ q (g.chartChristoffelBilinear e (e.symm q) u v) := h q hq u v

example : (∀ p : LorentzianConformalExample.Plane,
    ∃ e : OpenPartialHomeomorph LorentzianConformalExample.Plane LorentzianConformalExample.Plane,
      LorentzianConformalExample.metric.IsInertialChartAt e p) ∧
        ¬ LorentzianConformalExample.metric.IsLocallyMinkowski :=
  LorentzianConformalExample.pointwise_inertial_not_locallyMinkowski

example : LorentzianCharts.metric.IsParallelChartCoframeOn LorentzianCharts.standardChart Set.univ
    (fderiv ℝ LorentzianCharts.shear) := LorentzianCharts.shearCoframe_parallel

example : LorentzianCharts.metric.IsLocallyMinkowski :=
  LorentzianCharts.isLocallyMinkowski_via_parallelCoframe

example : LorentzianCharts.metric.IsLocallyMinkowski :=
  LorentzianCharts.isLocallyMinkowski_via_curvature

example {x y : LorentzianCharts.Plane} (p q : PiecewisePath 1 LorentzianCharts.Plane x y) :
    p.transport LorentzianCharts.metric = q.transport LorentzianCharts.metric :=
  LorentzianCharts.piecewise_transport_path_independent p q

end LocalFlatness

section AlongCurve

open LorentzMetric Bundle

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M) {γ : ℝ → M}

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

variable {V W : AlongField (d := d) γ} {t : ℝ}

example : AlongField (d := d) γ = (∀ t, TangentSpace I (γ t)) := rfl

example : TangentSpace I (γ t) := g.covariantAlong V t

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : γ t ∈ e.source) (hγ : MDifferentiableAt 𝓘(ℝ) I γ t) :
    MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t ↔
        DifferentiableAt ℝ (alongComponents e V) t :=
  alongField_mdifferentiableAt_iff he hx hγ

example (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) (v : TangentSpace I (γ t)) :
    ∃ ε > (0 : ℝ), ∃ V : AlongField (d := d) γ,
      V t = v ∧ g.IsParallelOn (Set.Ioo (t - ε) (t + ε)) V :=
  g.exists_parallel_local hγ v

example {s u : Set ℝ} (hs : s ∈ 𝓝 t) (hu : u ∈ 𝓝 t)
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) (hV : g.IsParallelOn s V) (hW : g.IsParallelOn u W)
    (hinit : V t = W t) : V =ᶠ[𝓝 t] W := g.parallel_unique_local hγ hs hu hV hW hinit

example (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    ∃ ε > (0 : ℝ), ∃ P : ∀ r, TangentSpace I (γ t) →L[ℝ] TangentSpace I (γ r),
      P t = ContinuousLinearMap.id ℝ _ ∧
      (∀ v, g.IsParallelOn (Set.Ioo (t - ε) (t + ε)) (fun r => P r v)) ∧
      ∀ r ∈ Set.Ioo (t - ε) (t + ε), (P r).IsInvertible ∧
        ∀ v w, g.form (γ t) v w = g.form (γ r) (P r v) (P r w) :=
  g.exists_localParallelFrame hγ

example {s : Set ℝ} (hs : Convex ℝ s)
    (hγ : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hV : g.IsParallelOn s V) (hW : g.IsParallelOn s W)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) : V a = W a ↔ V b = W b :=
  g.parallel_eq_iff hs hγ hV hW ha hb

example {a b : ℝ} (hγ : ∀ t ∈ Set.uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (v : TangentSpace I (γ a)) :
    ∃ V : AlongField (d := d) γ, V a = v ∧ g.IsParallelOn (Set.uIcc a b) V :=
  g.exists_parallel_on_segment hγ v

example {a b : ℝ} (hγ : ∀ t ∈ Set.uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    TangentSpace I (γ a) ≃L[ℝ] TangentSpace I (γ b) := g.parallelTransport hγ

example {a b : ℝ} (hγ : ∀ t ∈ Set.uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hV : g.IsParallelOn (Set.uIcc a b) V) :
    g.parallelTransport hγ (V a) = V b := g.parallelTransport_apply_eq hγ hV

example {a b : ℝ} (hγ : ∀ t ∈ Set.uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (v w : TangentSpace I (γ a)) :
    g.form (γ b) (g.parallelTransport hγ v) (g.parallelTransport hγ w) =
      g.form (γ a) v w := g.parallelTransport_metric hγ v w

example {a b : ℝ} (hγ : ∀ t ∈ Set.uIcc a b, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hrev : ∀ t ∈ Set.uIcc b a, ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    g.parallelTransport hrev = (g.parallelTransport hγ).symm := g.parallelTransport_reverse hγ hrev

example {a b c : ℝ} (hγ : ∀ t ∈ Set.uIcc a c, ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hb : b ∈ Set.uIcc a c) :
    (g.parallelTransport (a := a) (b := b)
      (fun t ht => hγ t (Set.uIcc_subset_uIcc_left hb ht))).trans
      (g.parallelTransport (a := b) (b := c)
        (fun t ht => hγ t (Set.uIcc_subset_uIcc_right hb ht))) = g.parallelTransport hγ :=
  g.parallelTransport_trans hγ hb

example {r : ℝ → ℝ} {a b : ℝ}
    (hγ : ∀ t ∈ Set.uIcc (r a) (r b), ContMDiffAt 𝓘(ℝ) I 2 γ t)
    (hr : ∀ t ∈ Set.uIcc a b, ContDiffAt ℝ 2 r t)
    (hm : Set.MapsTo r (Set.uIcc a b) (Set.uIcc (r a) (r b))) :
    g.parallelTransport (γ := γ ∘ r)
      (fun t ht => (hγ (r t) (hm ht)).comp t (hr t ht).contMDiffAt) = g.parallelTransport hγ :=
  g.parallelTransport_reparam hγ hr hm

example {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : γ t ∈ e.source) (hx' : γ t ∈ e'.source)
    (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : DifferentiableAt ℝ (alongComponents e V) t) :
    g.chartCovariantAlong e V t = g.chartCovariantAlong e' V t :=
  g.chartCovariantAlong_eq he he' hx hx' hγ hV

example (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    {Y : ∀ x, TangentSpace I x}
    (hY : MDifferentiableAt I ((I).prod I) (T% Y) (γ t)) :
    g.covariantAlong (fun s => Y (γ s)) t = g.leviCivita Y (γ t) (curveVelocity γ t) :=
  g.covariantAlong_ambient hγ hY

example {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f t)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t) :
    g.covariantAlong (fun s => f s • V s) t =
      deriv f t • V t + f t • g.covariantAlong V t := g.covariantAlong_smul hf hV

example (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t)
    (hW : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (W s)) t) :
    HasDerivAt (fun s => g.form (γ s) (V s) (W s))
      (g.form (γ t) (g.covariantAlong V t) (W t) +
        g.form (γ t) (V t) (g.covariantAlong W t)) t :=
  g.hasDerivAt_pairing_along hγ hV hW

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : γ t ∈ e.source) (hγ : MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) t) (k : Fin (d + 1)) :
    chartTangentMap e (γ t) (g.covariantAlong V t) k =
      deriv (alongComponents e V) t k + ∑ i, ∑ j,
        g.chartChristoffel e (γ t) k i j * deriv (e ∘ γ) t i * alongComponents e V t j :=
  g.covariantAlong_coordinates he hx hγ hV k

example {r : ℝ → ℝ} (hγ : MDifferentiableAt 𝓘(ℝ) I γ (r t))
    (hr : DifferentiableAt ℝ r t)
    (hV : MDifferentiableAt 𝓘(ℝ) ((I).prod I)
      (fun s => TotalSpace.mk' E (γ s) (V s)) (r t)) :
    g.covariantAlong (γ := γ ∘ r) (fun s => V (r s)) t =
      deriv r t • g.covariantAlong V (r t) := g.covariantAlong_reparam hγ hr hV

example {r : ℝ → ℝ} (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ (r t))
    (hr : ContDiffAt ℝ 2 r t) :
    g.covariantAlong (curveVelocity (γ ∘ r)) t =
      deriv (deriv r) t • curveVelocity γ (r t) +
        (deriv r t)^2 • g.covariantAlong (curveVelocity γ) (r t) :=
  g.covariantAcceleration_reparam hγ hr

example {s : Set ℝ} (hs : Convex ℝ s)
    (hγ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : g.IsParallelOn s V) (hW : g.IsParallelOn s W) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) :
    g.form (γ a) (V a) (W a) = g.form (γ b) (V b) (W b) :=
  g.parallel_pairing_eq hs hγ hV hW ha hb

example {s : Set ℝ} : g.IsGeodesicOn s γ ↔
    ∀ t ∈ s, ContMDiffAt 𝓘(ℝ) I 2 γ t ∧ g.covariantAlong (curveVelocity γ) t = 0 := Iff.rfl

example {s : Set ℝ} (h : g.IsGeodesicOn s γ) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    g.form (γ a) (curveVelocity γ a) (curveVelocity γ a) =
      g.form (γ b) (curveVelocity γ b) (curveVelocity γ b) := h.metric_velocity_eq hs ha hb

example {s : Set ℝ} (h : g.IsGeodesicOn s γ) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    (0 < σ.timeSign * g.form (γ a) (curveVelocity γ a) (curveVelocity γ a)) ↔
      (0 < σ.timeSign * g.form (γ b) (curveVelocity γ b) (curveVelocity γ b)) :=
  h.timelike_iff hs ha hb

example {s : Set ℝ} (h : g.IsGeodesicOn s γ) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    (g.form (γ a) (curveVelocity γ a) (curveVelocity γ a) = 0) ↔
      (g.form (γ b) (curveVelocity γ b) (curveVelocity γ b) = 0) := h.null_norm_iff hs ha hb

example {s u : Set ℝ} (h : g.IsGeodesicOn u γ) (a b : ℝ)
    (hm : Set.MapsTo (fun t => a * t + b) s u) :
    g.IsGeodesicOn s (fun t => γ (a * t + b)) := h.affine_reparam a b hm

example {s : Set ℝ} (h : g.IsGeodesicOn s γ) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    (curveVelocity (d := d) γ a ≠ 0 ∧ g.form (γ a) (curveVelocity γ a) (curveVelocity γ a) = 0) ↔
      (curveVelocity (d := d) γ b ≠ 0 ∧ g.form (γ b) (curveVelocity γ b) (curveVelocity γ b) = 0) :=
  h.null_iff hs ha hb

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    (hx : γ t ∈ e.source) (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    g.covariantAlong (curveVelocity γ) t = 0 ↔ ∀ k : Fin (d + 1),
      deriv (deriv (e ∘ γ)) t k + ∑ i, ∑ j,
        g.chartChristoffel e (γ t) k i j * deriv (e ∘ γ) t i * deriv (e ∘ γ) t j = 0 :=
  g.geodesic_equation_iff_coordinates he hx hγ

example (p v : E) :
    (minkowskiMetric σ d).IsGeodesicOn Set.univ (fun t : ℝ => p + t • v) :=
  minkowski_affine_geodesic σ p v

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {z : E × E} (hz : z.1 ∈ e.target) :
    ContDiffAt ℝ ∞ (g.chartGeodesicField e) z := g.chartGeodesicField_contDiffAt he hz

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {q : E} (hq : q ∈ e.target) (v : E) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ α : ℝ → E × E, α t₀ = (q, v) ∧
      ContDiffOn ℝ 2 α (Set.Ioo (t₀ - ε) (t₀ + ε)) ∧
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        (α t).1 ∈ e.target ∧ HasDerivAt α (g.chartGeodesicField e (α t)) t :=
  g.exists_chartGeodesic he hq v t₀

example (p : M) (v : TangentSpace I p) (t₀ : ℝ) :
    ∃ ε > (0 : ℝ), ∃ γ : ℝ → M, ∃ hp : γ t₀ = p,
      (hp ▸ curveVelocity (d := d) γ t₀) = v ∧
        g.IsGeodesicOn (Set.Ioo (t₀ - ε) (t₀ + ε)) γ := g.exists_geodesic p v t₀

example {β : ℝ → M} {t₀ : ℝ} {s u : Set ℝ} (hs : s ∈ 𝓝 t₀) (hu : u ∈ 𝓝 t₀)
    (hγ : g.IsGeodesicOn s γ) (hβ : g.IsGeodesicOn u β)
    (hp : γ t₀ = β t₀) (hv : (hp ▸ curveVelocity (d := d) γ t₀) = curveVelocity β t₀) :
    γ =ᶠ[𝓝 t₀] β := g.geodesic_unique hs hu hγ hβ hp hv

example (a b : ℝ) : LorentzianCharts.metric.IsParallelOn Set.univ
    (LorentzianCharts.parallelField a b) := LorentzianCharts.parallelField_parallel a b

example : LorentzianCharts.metric.IsGeodesicOn Set.univ LorentzianCharts.inertialTimePath :=
  LorentzianCharts.inertialTimePath_geodesic

example (a b s : ℝ) : alongComponents LorentzianCharts.inertialChart
    (LorentzianCharts.parallelField a b) s = ![a, b] :=
  LorentzianCharts.parallelField_inertial_components a b s

example (s₀ s₁ : ℝ) (v : LorentzianCharts.Plane) :
    LorentzianCharts.metric.parallelTransport (a := s₀) (b := s₁)
      (fun t _ => (LorentzianCharts.inertialTimePath_contDiff.of_le (by simp)).contMDiff.contMDiffAt
        (x := t)) (modelField v (LorentzianCharts.inertialTimePath s₀)) =
      modelField ![v 0, v 1 - 2 * (s₁ - s₀) * v 0] (LorentzianCharts.inertialTimePath s₁) :=
  LorentzianCharts.parallelTransport_model s₀ s₁ v

end AlongCurve

section PiecewisePaths

open Bundle

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M) {x y z w : M}

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace I (M := M)

example (p : RegularPath d M x y) : Path x y := p.toPath

example (p : RegularPath d M x y) (v : TM x) :
    ∃ V : LorentzMetric.AlongField (d := d) p.curve,
      g.IsParallelOn (Set.Icc (0 : ℝ) 1) V ∧ tangentCongr p.source (V 0) = v ∧
        tangentCongr p.target (V 1) = p.transport g v := p.exists_parallel g v

example (p : RegularPath d M x y) {V W : LorentzMetric.AlongField (d := d) p.curve}
    (hV : g.IsParallelOn (Set.Icc (0 : ℝ) 1) V) (hW : g.IsParallelOn (Set.Icc (0 : ℝ) 1) W)
    (hinit : tangentCongr p.source (V 0) = tangentCongr p.source (W 0))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : V t = W t := p.parallel_unique g hV hW hinit ht

example (p : PiecewisePath d M x y) : p.reverse.toPath = p.toPath.symm := p.toPath_reverse

example (p : PiecewisePath d M x y) (v : TM x) (w : TM y) :
    p.HasParallelLift g v w ↔ p.transport g v = w := p.hasParallelLift_iff g v w

example (p : PiecewisePath d M x y) (v : TM x) :
    ∃! w, p.HasParallelLift g v w := p.existsUnique_parallelLift g v

example (p : PiecewisePath d M x y) (T : TM x → TM y)
    (hT : ∀ v w, p.HasParallelLift g v w → T v = w) : T = p.transport g := p.transport_unique g T hT

example (p : PiecewisePath d M x y) {v : TM x} {w : TM y} (h : p.HasParallelLift g v w) :
    ∃ P : Path (TotalSpace.mk' E x v) (TotalSpace.mk' E y w),
      P.map (FiberBundle.continuous_proj E TM) = p.toPath := p.exists_continuous_parallelLift g h

example (p : PiecewisePath d M x y) (q : PiecewisePath d M y z) :
    (p.trans q).transport g = (p.transport g).trans (q.transport g) := p.transport_trans g q

example (p : PiecewisePath d M x y) (q : PiecewisePath d M y z) (r : PiecewisePath d M z w) :
    ((p.trans q).trans r).transport g = (p.trans (q.trans r)).transport g := p.transport_assoc g q r

example (p : PiecewisePath d M x y) : p.reverse.transport g = (p.transport g).symm :=
  p.transport_reverse g

example (p : PiecewisePath d M x y) (v w : TM x) :
    g.form y (p.transport g v) (p.transport g w) = g.form x v w := p.transport_metric g v w

example (v : MinkowskiModel 1) :
    ((PiecewisePath.segment (RegularPath.modelLine (0 : MinkowskiModel 1) ![1, 0])).trans
      (.segment (RegularPath.modelLine ![1, 0] ![1, 1]))).transport
        (minkowskiMetric .timeNegative 1) (LorentzMetric.modelField v 0) =
          LorentzMetric.modelField v ![1, 1] := minkowski_corner_transport v

end PiecewisePaths

section Connection

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)
  {X Y Z : ∀ x : M, TangentSpace 𝓘(ℝ, MinkowskiModel d) x} {x : M}

example : CovariantDerivative 𝓘(ℝ, MinkowskiModel d) (MinkowskiModel d)
    (TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)) := g.leviCivita

example : g.IsLeviCivita g.leviCivita := g.isLeviCivita_leviCivita

example : g.leviCivita.torsion = 0 := g.leviCivita_torsion

example
    (hY : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Y) x)
    (hZ : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Z) x)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.form y (Y y) (Z y)) x v =
      g.form x (g.leviCivita Y x v) (Z x) + g.form x (Y x) (g.leviCivita Z x v) :=
  g.leviCivita_metricCompatible v hY hZ

example
    (hX : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% X) x)
    (hY : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Y) x)
    (hZ : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Z) x) :
    g.form x (g.leviCivita Y x (X x)) (Z x) =
      (mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.form y (Y y) (Z y)) x (X x) +
       mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.form y (Z y) (X y)) x (Y x) -
       mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.form y (X y) (Y y)) x (Z x) -
       g.form x (Y x) (VectorField.mlieBracket 𝓘(ℝ, MinkowskiModel d) X Z x) -
       g.form x (Z x) (VectorField.mlieBracket 𝓘(ℝ, MinkowskiModel d) Y X x) +
       g.form x (X x) (VectorField.mlieBracket 𝓘(ℝ, MinkowskiModel d) Z Y x)) / 2 :=
  g.leviCivita_pairing hX hY hZ

example
    (cov cov' : CovariantDerivative 𝓘(ℝ, MinkowskiModel d) (MinkowskiModel d)
      (TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)))
    (h : g.IsLeviCivita cov) (h' : g.IsLeviCivita cov')
    (hY : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Y) x)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) : cov Y x v = cov' Y x v :=
  h.uniqueness g h' hY v

example : g.opposite.leviCivita = g.leviCivita := g.leviCivita_opposite

example : CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita ∞ := inferInstance

example (n : ℕ∞) : CovariantDerivative.ContMDiffCovariantDerivative g.leviCivita n :=
  inferInstance

example (n : ℕ∞) (hY : ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (n + 1) (T% Y) x) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d)) n
      (fun y => Bundle.TotalSpace.mk' (MinkowskiModel d →L[ℝ] MinkowskiModel d)
        y (g.leviCivita Y y)) x := g.contMDiffAt_leviCivita hY

example (hY : ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) 2 (T% Y) x) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d)) 1
      (fun y => Bundle.TotalSpace.mk' (MinkowskiModel d →L[ℝ] MinkowskiModel d)
        y (g.leviCivita Y y)) x := g.contMDiffAt_leviCivita hY

example (hY : ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) ∞ (T% Y) x) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d)) ∞
      (fun y => Bundle.TotalSpace.mk' (MinkowskiModel d →L[ℝ] MinkowskiModel d)
        y (g.leviCivita Y y)) x := g.contMDiffAt_leviCivita hY

end Connection

section Curvature

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "I" => 𝓘(ℝ, MinkowskiModel d)
local notation "TM" => TangentSpace 𝓘(ℝ, MinkowskiModel d) (M := M)

example (x : M) : TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x := g.curvature x

example : (LorentzMetric.curvatureBundle (d := d) (M := M)).Section I := g.curvatureTensor

example {X Y Z : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) 2 (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) 2 (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) 2 (T% Z) x) :
    g.curvature x (X x) (Y x) (Z x) =
      g.leviCivita (fun y => g.leviCivita Z y (Y y)) x (X x) -
      g.leviCivita (fun y => g.leviCivita Z y (X y)) x (Y x) -
      g.leviCivita Z x (VectorField.mlieBracket I X Y x) := g.curvature_apply hX hY hZ

example {X Y Z : ∀ x, TM x} {x : M}
    (hX : ContMDiffAt I ((I).prod I) ∞ (T% X) x)
    (hY : ContMDiffAt I ((I).prod I) ∞ (T% Y) x)
    (hZ : ContMDiffAt I ((I).prod I) ∞ (T% Z) x) :
    ContMDiffAt I ((I).prod I) ∞ (T% (g.curvatureField X Y Z)) x :=
  g.contMDiffAt_curvatureField hX hY hZ

example (x : M) (u v w : TM x) : g.curvature x u v w = -g.curvature x v u w :=
  g.curvature_swap x u v w

example (x : M) (u v w : TM x) :
    g.curvature x u v w + g.curvature x v w u + g.curvature x w u v = 0 :=
  g.curvature_first_bianchi x u v w

example (x : M) : g.opposite.curvature x = g.curvature x := g.curvature_opposite x

example (x : M) (u v w z : TM x) :
    g.form x (g.curvature x u v w) z + g.form x w (g.curvature x u v z) = 0 :=
  g.curvature_skewAdjoint x u v w z

example (x : M) (u v w z : TM x) :
    g.form x (g.curvature x u v w) z = -g.form x (g.curvature x u v z) w :=
  g.curvature_pair_swap x u v w z

example (x : M) (u v w z : TM x) :
    g.form x (g.curvature x u v w) z = g.form x (g.curvature x w z u) v :=
  g.curvature_pair_interchange x u v w z

example (x : M) (u v : TM x) : g.ricci x u v = g.ricci x v u := g.ricci_symmetric x u v

example (φ : C^∞⟮I, M; ℝ⟯) : LorentzMetric σ d M := g.conformal φ

example (φ : C^∞⟮I, M; ℝ⟯) (x : M) :
    (g.conformal φ).form x = Real.exp (2 * φ x) • g.form x := g.conformal_form φ x

example (x : M) (u v w : TM x) :
    g.curvatureEndomorphism x u v w = g.curvature x w u v :=
  g.curvatureEndomorphism_apply x u v w

example (x : M) (u v : TM x) :
    g.ricci x u v = LinearMap.trace ℝ (TM x) (g.curvatureEndomorphism x u v).toLinearMap :=
  g.ricci_apply x u v

example : CovariantTwoTensor d M := g.ricciTensor

example (x : M) (e : TM x ≃L[ℝ] MinkowskiModel d) (u v : TM x) :
    g.ricci x u v = ∑ i, e (g.curvature x (e.symm (Pi.single i 1)) u v) i :=
  g.ricci_eq_sum x e u v

example : C^∞⟮I, M; ℝ⟯ := g.scalarCurvature

example (x : M) (e : TM x ≃L[ℝ] MinkowskiModel d) :
    g.scalarCurvature x = ∑ i, ∑ j,
      g.ricci x (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1)) *
        g.inverseComponent x e i j := g.scalarCurvature_eq_sum x e

example (x : M) : g.opposite.ricci x = g.ricci x := g.ricci_opposite x

example (x : M) : g.opposite.scalarCurvature x = -g.scalarCurvature x :=
  g.scalarCurvature_opposite x

example (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d) :
    (minkowskiMetric σ d).curvature x = 0 := LorentzMetric.minkowski_curvature σ d x

example (σ : LorentzConvention) (d : ℕ) (x : MinkowskiModel d) :
    (minkowskiMetric σ d).scalarCurvature x = 0 :=
  LorentzMetric.minkowski_scalarCurvature σ d x

example (p : LorentzianCharts.Plane) : LorentzianCharts.metric.curvature p = 0 :=
  LorentzianCharts.curvature_shear p

example (p : LorentzianCharts.Plane) : LorentzianCharts.metric.scalarCurvature p = 0 :=
  LorentzianCharts.scalarCurvature_shear p

end Curvature

section ChartCurvature

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M)

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (l i j k : Fin (d + 1)) :
    g.chartCurvature e x l i j k =
      fderiv ℝ (fun z => g.chartChristoffel e (e.symm z) l j k) (e x) (Pi.single i 1) -
      fderiv ℝ (fun z => g.chartChristoffel e (e.symm z) l i k) (e x) (Pi.single j 1) +
      ∑ a, (g.chartChristoffel e x l i a * g.chartChristoffel e x a j k -
        g.chartChristoffel e x l j a * g.chartChristoffel e x a i k) :=
  g.chartCurvature_eq_fderiv he hx l i j k

example {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (l i j k : Fin (d + 1)) :
    ContMDiffAt I 𝓘(ℝ) ∞ (fun y => g.chartCurvature e y l i j k) x :=
  g.chartCurvature_contMDiffAt he hx l i j k

example {e e' : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas I ∞ M) (he' : e' ∈ IsManifold.maximalAtlas I ∞ M)
    {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source) (l i j k : Fin (d + 1)) :
    (∑ a, fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single a 1) l *
      g.chartCurvature e x a i j k) =
      ∑ a, ∑ b, ∑ c, g.chartCurvature e' x l a b c *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single i 1) a *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single j 1) b *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single k 1) c :=
  g.chartCurvature_transformation he he' hx hx' l i j k

example (p : LorentzianConformalExample.Plane) :
    LorentzianConformalExample.metric.scalarCurvature p = -4 * Real.exp (-(2 * (p 1)^2)) :=
  LorentzianConformalExample.scalarCurvature_eq p

example : (∀ k i j, LorentzianConformalExample.metric.christoffel 0 k i j = 0) ∧
    LorentzianConformalExample.metric.curvature 0 ≠ 0 ∧
    LorentzianConformalExample.metric.scalarCurvature 0 = -4 :=
  ⟨LorentzianConformalExample.christoffel_origin,
    LorentzianConformalExample.curvature_origin_ne_zero,
    LorentzianConformalExample.scalarCurvature_origin⟩

end ChartCurvature

section ConnectionNaturality

variable {σ : LorentzConvention} {d : ℕ} {M N : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]
  (g : LorentzMetric σ d M) (h : LorentzMetric σ d N)

example (x : M) (y : N)
    (L : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    (hL : ∀ v w, g.form x v w = h.form y (L v) (L w)) : L.IsInvertible :=
  g.isInvertible_of_metric h x y L hL

example {f : M → N}
    (hf : ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ f)
    (hmetric : ∀ y v w, g.form y v w = h.form (f y)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y v)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y w))
    {Y : ∀ y : N, TangentSpace 𝓘(ℝ, MinkowskiModel d) y} {x : M}
    (hY : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Y) (f x))
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x
      (g.leviCivita (VectorField.mpullback 𝓘(ℝ, MinkowskiModel d)
        𝓘(ℝ, MinkowskiModel d) f Y) x v) =
      h.leviCivita Y (f x)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x v) :=
  g.leviCivita_naturality_of_metric h hf hmetric hY v

example {f : M → N}
    (hf : ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ f)
    (hmetric : ∀ y v w, g.form y v w = h.form (f y)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y v)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f y w))
    (x : M) (u v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x (g.curvature x u v w) =
      h.curvature (f x)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x u)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x v)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x w) :=
  g.curvature_naturality_of_metric h hf hmetric x u v w

example (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ f)
    (hinv : ∀ x, (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x).IsInvertible)
    (x : M) (u v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x
      ((h.pullback f hf hinv).curvature x u v w) =
      h.curvature (f x)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x u)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x v)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x w) :=
  h.curvature_pullback hf hinv x u v w

example (f : M → N)
    (hf : ContMDiff 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞ f)
    (hinv : ∀ x, (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x).IsInvertible)
    (x : M) (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    (h.pullback f hf hinv).form x v w = h.form (f x)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x v)
      (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x w) :=
  h.pullback_form f hf hinv x v w

example (U : TopologicalSpace.Opens M) : LorentzMetric σ d U := g.restrict U

example (U : TopologicalSpace.Opens M) :
    IsLocalDiffeomorph 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) ∞
      (Subtype.val : U → M) := Manifold.isLocalDiffeomorph_subtype_val _ U

example (U : TopologicalSpace.Opens M) {x : U}
    {Y : ∀ y : M, TangentSpace 𝓘(ℝ, MinkowskiModel d) y}
    (hY : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d)
      (𝓘(ℝ, MinkowskiModel d).prod 𝓘(ℝ, MinkowskiModel d)) (T% Y) x.val)
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (Subtype.val : U → M) x
      ((g.restrict U).leviCivita
        (VectorField.mpullback 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d)
          (Subtype.val : U → M) Y) x v) =
      g.leviCivita Y x.val
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) (Subtype.val : U → M) x v) :=
  g.leviCivita_restrict U hY v

end ConnectionNaturality

section CoordinateConnection

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} (g : LorentzMetric σ d (MinkowskiModel d))

example (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.christoffel x k i j = ∑ l,
      g.inverseComponent x (NormedSpace.fromTangentSpace x) k l *
        (fderiv ℝ (fun y => g.modelComponent y j l) x (Pi.single i 1) +
         fderiv ℝ (fun y => g.modelComponent y l i) x (Pi.single j 1) -
         fderiv ℝ (fun y => g.modelComponent y i j) x (Pi.single l 1)) / 2 :=
  g.christoffel_eq x k i j

example (k i j : Fin (d + 1)) : ContDiff ℝ ∞ (fun x => g.christoffel x k i j) :=
  g.christoffel_contDiff k i j

example (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.christoffel x k i j = g.christoffel x k j i := g.christoffel_symmetric x k i j

example {Y : MinkowskiModel d → MinkowskiModel d} {x : MinkowskiModel d}
    (hY : DifferentiableAt ℝ Y x) (v : MinkowskiModel d) (k : Fin (d + 1)) :
    NormedSpace.fromTangentSpace x
      (g.leviCivita (fun y => modelField (Y y) y) x (modelField v x)) k =
        fderiv ℝ Y x v k + ∑ i, ∑ j, g.christoffel x k i j * v i * Y x j :=
  g.leviCivita_model_coordinates hY v k

example (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    g.opposite.christoffel x k i j = g.christoffel x k i j :=
  g.christoffel_opposite x k i j

example (x : MinkowskiModel d) (k i j : Fin (d + 1)) :
    (minkowskiMetric σ d).christoffel x k i j = 0 := minkowski_christoffel σ d x k i j

end CoordinateConnection

section Duality

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M) (x : M)

example (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.flat x v w = g.form x v w := g.flat_apply x v w

example (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.sharp x (g.flat x v) = v := g.sharp_flat x v

example (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.flat x (g.sharp x α) = α := g.flat_sharp x α

example : ContMDiff 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod
      𝓘(ℝ, MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)) ∞
    (fun y => Bundle.TotalSpace.mk'
      (MinkowskiModel d →L[ℝ] MinkowskiModel d →L[ℝ] ℝ)
      y (g.flat y).toContinuousLinearMap) := g.flat_smooth

example : ContMDiff 𝓘(ℝ, MinkowskiModel d)
    (𝓘(ℝ, MinkowskiModel d).prod
      𝓘(ℝ, (MinkowskiModel d →L[ℝ] ℝ) →L[ℝ] MinkowskiModel d)) ∞
    (fun y => Bundle.TotalSpace.mk'
      ((MinkowskiModel d →L[ℝ] ℝ) →L[ℝ] MinkowskiModel d)
      y (g.sharp y).toContinuousLinearMap) := g.sharp_smooth

example (v : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d,
    (fun y : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) y)⟯) :
    g.raise (g.lower v) = v := g.raise_lower v

example (α : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] ℝ,
    (fun y : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) y →L[ℝ] ℝ)⟯) :
    g.lower (g.raise α) = α := g.lower_raise α

example (α β : Cₛ^∞⟮𝓘(ℝ, MinkowskiModel d); MinkowskiModel d →L[ℝ] ℝ,
    (fun y : M => TangentSpace 𝓘(ℝ, MinkowskiModel d) y →L[ℝ] ℝ)⟯) :
    g.inversePairing α β x = α x (g.sharp x (β x)) := g.inversePairing_apply α β x

example (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.opposite.sharp x α = -g.sharp x α := g.opposite_sharp_apply x α

example (p : MinkowskiModel d) :
    (minkowskiMetric σ d).sharp p = Minkowski.sharp σ :=
  LorentzMetric.minkowskiMetric_sharp σ d p

variable {N : Type} [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]
  (h : LorentzMetric σ d N) (y : N)
  (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ]
    TangentSpace 𝓘(ℝ, MinkowskiModel d) y)

example (he : ∀ v w, g.form x v w = h.form y (e v) (e w))
    (v : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    g.flat x v = (h.flat y (e v)).comp e.toContinuousLinearMap :=
  g.flat_naturality h x y e he v

example (he : ∀ v w, g.form x v w = h.form y (e v) (e w))
    (α : TangentSpace 𝓘(ℝ, MinkowskiModel d) y →L[ℝ] ℝ) :
    g.sharp x (α.comp e.toContinuousLinearMap) = e.symm (h.sharp y α) :=
  g.sharp_naturality h x y e he α

end Duality

section Bilinear

variable {E F G X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

example (B : G →L[ℝ] G →L[ℝ] ℝ) (A : F →L[ℝ] G) (C : E →L[ℝ] F) :
    BilinearTensor.pullback B (A.comp C) =
      BilinearTensor.pullback (BilinearTensor.pullback B A) C :=
  BilinearTensor.pullback_comp B A C

example {B : X → F →L[ℝ] F →L[ℝ] ℝ} {A : X → E →L[ℝ] F}
    (hB : ContDiff ℝ ∞ B) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun x => BilinearTensor.pullback (B x) (A x)) :=
  BilinearTensor.contDiff_pullback hB hA

example {B : X → E →L[ℝ] E →L[ℝ] ℝ} {v w : X → E}
    (hB : ContDiff ℝ ∞ B) (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (fun x => B x (v x) (w x)) :=
  BilinearTensor.contDiff_contract hB hv hw

end Bilinear

section TensorBundles

variable {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

open Tensor

example (r s : ℕ) :
    ContMDiffVectorBundle ∞
      ((Shape.mixed r s).bundle 𝓘(ℝ, MinkowskiModel d) (M := M)).Model
      ((Shape.mixed r s).bundle 𝓘(ℝ, MinkowskiModel d) (M := M)).Fiber
      𝓘(ℝ, MinkowskiModel d) := inferInstance

example {σ : LorentzConvention} (g : LorentzMetric σ d M) :
    ((Shape.mixed 0 2).bundle 𝓘(ℝ, MinkowskiModel d) (M := M)).Section 𝓘(ℝ, MinkowskiModel d) :=
  g.toTensor

example (A : SmoothBundle 𝓘(ℝ, MinkowskiModel d) (M := M))
    (L : (SmoothBundle.hom 𝓘(ℝ, MinkowskiModel d) A A).Section 𝓘(ℝ, MinkowskiModel d)) :
    C^∞⟮𝓘(ℝ, MinkowskiModel d), M; ℝ⟯ := A.contract 𝓘(ℝ, MinkowskiModel d) L

example (A B : SmoothBundle 𝓘(ℝ, MinkowskiModel d) (M := M))
    (L : (SmoothBundle.hom 𝓘(ℝ, MinkowskiModel d) A
      (SmoothBundle.hom 𝓘(ℝ, MinkowskiModel d) B B)).Section 𝓘(ℝ, MinkowskiModel d))
    (x : M) (v : A.Fiber x) :
    SmoothBundle.partialContract 𝓘(ℝ, MinkowskiModel d) A B L x v =
      LinearMap.trace ℝ (B.Fiber x) (L x v).toLinearMap :=
  SmoothBundle.partialContract_apply 𝓘(ℝ, MinkowskiModel d) A B L x v

example (A : SmoothBundle 𝓘(ℝ, MinkowskiModel d) (M := M))
    (e : Bundle.Trivialization A.Model
      (Bundle.TotalSpace.proj : Bundle.TotalSpace A.Model A.Fiber → M))
    [MemTrivializationAtlas e] (T : A.Section 𝓘(ℝ, MinkowskiModel d)) :
    ContMDiffOn 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, A.Model) ∞
      (A.coefficients 𝓘(ℝ, MinkowskiModel d) e T) e.baseSet :=
  A.coefficients_contMDiffOn 𝓘(ℝ, MinkowskiModel d) e T

example (s : Shape) {x y z : M}
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    (f : TangentSpace 𝓘(ℝ, MinkowskiModel d) y ≃L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) z) :
    s.pullback 𝓘(ℝ, MinkowskiModel d) (e.trans f) =
      (s.pullback 𝓘(ℝ, MinkowskiModel d) f).trans (s.pullback 𝓘(ℝ, MinkowskiModel d) e) :=
  s.pullback_trans 𝓘(ℝ, MinkowskiModel d) e f

example (a b : Shape) {x y : M}
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] TangentSpace 𝓘(ℝ, MinkowskiModel d) y)
    (L : (a.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber x →L[ℝ]
      (b.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber x →L[ℝ]
        (b.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber x)
    (v : (a.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber y) :
    LinearMap.trace ℝ ((b.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber y)
        ((Shape.map 𝓘(ℝ, MinkowskiModel d) (.hom a (.hom b b)) e L) v).toLinearMap =
      LinearMap.trace ℝ ((b.bundle 𝓘(ℝ, MinkowskiModel d)).Fiber x)
        (L ((a.map 𝓘(ℝ, MinkowskiModel d) e).symm v)).toLinearMap :=
  Shape.partialTrace_map 𝓘(ℝ, MinkowskiModel d) a b e L v

variable {σ : LorentzConvention} (g : LorentzMetric σ d M)

example (B : CovariantTwoTensor d M) : g.lowerIndex (g.raiseIndex B) = B :=
  g.lowerIndex_raiseIndex B

example (A : TangentEndomorphism d M) : g.raiseIndex (g.lowerIndex A) = A :=
  g.raiseIndex_lowerIndex A

example (B : CovariantTwoTensor d M) : C^∞⟮𝓘(ℝ, MinkowskiModel d), M; ℝ⟯ :=
  g.contractField B

example (x : M) : g.contract x (g.form x) = d + 1 := g.contract_metric x

example (x : M)
    (B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.opposite.contract x B = -g.contract x B := g.contract_opposite x B

example (x : M)
    (e : TangentSpace 𝓘(ℝ, MinkowskiModel d) x ≃L[ℝ] MinkowskiModel d)
    (B : TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ]
      TangentSpace 𝓘(ℝ, MinkowskiModel d) x →L[ℝ] ℝ) :
    g.contract x B = ∑ i, ∑ j,
      B (e.symm (Pi.single i 1)) (e.symm (Pi.single j 1)) * g.inverseComponent x e i j :=
  g.contract_eq_sum_components x e B

end TensorBundles

section FieldPullback

open Tensor

variable {d : ℕ} {M N P : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  [TopologicalSpace N] [ChartedSpace (MinkowskiModel d) N]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ N]
  [TopologicalSpace P] [ChartedSpace (MinkowskiModel d) P]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ P]

example (s : Shape) (f : M ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ N)
    (T : (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := N)).Section 𝓘(ℝ, MinkowskiModel d)) :
    (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := M)).Section 𝓘(ℝ, MinkowskiModel d) :=
  s.pullbackField 𝓘(ℝ, MinkowskiModel d) f T

example (s : Shape) (f : M ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ N)
    (g : N ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ P)
    (T : (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := P)).Section 𝓘(ℝ, MinkowskiModel d)) :
    s.pullbackField 𝓘(ℝ, MinkowskiModel d) (f.trans g) T =
      s.pullbackField 𝓘(ℝ, MinkowskiModel d) f (s.pullbackField 𝓘(ℝ, MinkowskiModel d) g T) :=
  s.pullbackField_trans 𝓘(ℝ, MinkowskiModel d) f g T

example (s : Shape) (f : M ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ N)
    (T : (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := M)).Section 𝓘(ℝ, MinkowskiModel d)) :
    s.pullbackField 𝓘(ℝ, MinkowskiModel d) f
      (s.pullbackField 𝓘(ℝ, MinkowskiModel d) f.symm T) = T :=
  s.pullbackField_symm 𝓘(ℝ, MinkowskiModel d) f T

example (f : M ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ N)
    (T : CovariantTwoTensor d N) (x : M)
    (v w : TangentSpace 𝓘(ℝ, MinkowskiModel d) x) :
    Shape.pullbackField 𝓘(ℝ, MinkowskiModel d) (Shape.mixed 0 2) f T x v w =
      T (f x) (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x v)
        (mfderiv 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) f x w) :=
  Shape.pullbackField_covariantTwo_apply 𝓘(ℝ, MinkowskiModel d) f T x v w

example (s t : Shape)
    (f : M ≃ₘ⟮𝓘(ℝ, MinkowskiModel d), 𝓘(ℝ, MinkowskiModel d)⟯ N)
    (T : ((Shape.hom s (Shape.hom t t)).bundle 𝓘(ℝ, MinkowskiModel d) (M := N)).Section
      𝓘(ℝ, MinkowskiModel d)) :
    SmoothBundle.partialContract 𝓘(ℝ, MinkowskiModel d)
      (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := M))
      (t.bundle 𝓘(ℝ, MinkowskiModel d) (M := M))
      (Shape.pullbackField 𝓘(ℝ, MinkowskiModel d) (Shape.hom s (Shape.hom t t)) f T) =
    Shape.pullbackField 𝓘(ℝ, MinkowskiModel d) (Shape.hom s Shape.scalar) f
      (SmoothBundle.partialContract 𝓘(ℝ, MinkowskiModel d)
        (s.bundle 𝓘(ℝ, MinkowskiModel d) (M := N))
        (t.bundle 𝓘(ℝ, MinkowskiModel d) (M := N)) T) :=
  Shape.partialContract_pullbackField 𝓘(ℝ, MinkowskiModel d) s t f T

end FieldPullback

section CovariantPullback

open Tensor.Shape

variable {E H M F H' N G H'' P : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H'] (J : ModelWithCorners ℝ F H')
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H''] (K : ModelWithCorners ℝ G H'')
  [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K ∞ P]

-- Three independent model spaces: no equal dimension or invertibility premise.
example (n : ℕ) (f : C^∞⟮I, M; J, N⟯)
    (T : ((covariant n).bundle J (M := N)).Section J) :
    ((covariant n).bundle I (M := M)).Section I :=
  covariantPullbackField I J n f T

example (f : C^∞⟮I, M; J, N⟯)
    (T : (cotangent.bundle J (M := N)).Section J) (x : M) (v : TangentSpace I x) :
    covariantPullbackField I J 1 f T x v = T (f x) (mfderiv I J f x v) :=
  covariantPullbackField_one_apply I J f T x v

example (f : C^∞⟮I, M; J, N⟯)
    (T : ((covariant 2).bundle J (M := N)).Section J) (x : M)
    (v w : TangentSpace I x) :
    covariantPullbackField I J 2 f T x v w =
      T (f x) (mfderiv I J f x v) (mfderiv I J f x w) :=
  covariantPullbackField_two_apply I J f T x v w

example (f : C^∞⟮I, M; J, N⟯)
    (T : ((covariant 3).bundle J (M := N)).Section J) (x : M)
    (u v w : TangentSpace I x) :
    covariantPullbackField I J 3 f T x u v w =
      T (f x) (mfderiv I J f x u) (mfderiv I J f x v) (mfderiv I J f x w) := rfl

example (n : ℕ) (T : ((covariant n).bundle I (M := M)).Section I) :
    covariantPullbackField I I n (ContMDiffMap.id : C^∞⟮I, M; I, M⟯) T = T :=
  covariantPullbackField_id I n T

example (n : ℕ) (f : C^∞⟮I, M; J, N⟯) (g : C^∞⟮J, N; K, P⟯)
    (T : ((covariant n).bundle K (M := P)).Section K) :
    covariantPullbackField I K n (g.comp f) T =
      covariantPullbackField I J n f (covariantPullbackField J K n g T) :=
  covariantPullbackField_comp I J K n f g T

example (n : ℕ) (y : N)
    (T : ((covariant (n + 1)).bundle J (M := N)).Section J) :
    covariantPullbackField I J (n + 1) (ContMDiffMap.const y : C^∞⟮I, M; J, N⟯) T = 0 :=
  covariantPullbackField_const I J n y T

example (n : ℕ) {N' : Type} [TopologicalSpace N'] [ChartedSpace H N']
    [IsManifold I ∞ N'] (f : M ≃ₘ⟮I, I⟯ N')
    (T : ((covariant n).bundle I (M := N')).Section I) :
    covariantPullbackField I I n f.toContMDiffMap T = pullbackField I (covariant n) f T :=
  covariantPullbackField_diffeomorph I n f T

example (n : ℕ) {a : P → M} {b : P → N} {p : P}
    (ha : ContMDiffAt K I ∞ a p) (hb : ContMDiffAt K J ∞ b p)
    (L : ∀ q, TangentSpace I (a q) →L[ℝ] TangentSpace J (b q))
    (hL : ContMDiffAt K 𝓘(ℝ, E →L[ℝ] F) ∞
      (fun q => ContinuousLinearMap.inCoordinates E (TangentSpace I) F (TangentSpace J)
        (a p) (a q) (b p) (b q) (L q)) p) :
    ContMDiffAt K 𝓘(ℝ, ((covariant n).bundle J (M := N)).Model →L[ℝ]
      ((covariant n).bundle I (M := M)).Model) ∞
      (fun q => ContinuousLinearMap.inCoordinates ((covariant n).bundle J (M := N)).Model
        ((covariant n).bundle J (M := N)).Fiber
        ((covariant n).bundle I (M := M)).Model ((covariant n).bundle I (M := M)).Fiber
        (b p) (b q) (a p) (a q) (covariantPullback I J n (L q))) p :=
  contMDiffAt_covariantPullback I J K n ha hb L hL

end CovariantPullback

section CovariantPullbackExamples

open Tensor.Shape LorentzianCharts

example (t v w : ℝ) :
    covariantPullbackField 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) 2
      (timeAxis : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, Plane), Plane⟯) metric.toTensor t v w =
      (-1 + 4 * t ^ 2) * v * w := metric_timeAxis_pullback t v w

example (t v w : ℝ) :
    covariantPullbackField 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) 2
      (timeAxis : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, Plane), Plane⟯)
      (minkowskiMetric .timeNegative 1).toTensor t v w = -(v * w) :=
  minkowski_timeAxis_pullback t v w

example (v w : ℝ) :
    covariantPullbackField 𝓘(ℝ, ℝ) 𝓘(ℝ, Plane) 2
      (timeAxis : C^∞⟮𝓘(ℝ, ℝ), ℝ; 𝓘(ℝ, Plane), Plane⟯)
      metric.toTensor (1 / 2 : ℝ) v w = 0 := metric_timeAxis_pullback_degenerate v w

example (p q v w : Plane) :
    covariantPullbackField 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) 2
      (ContMDiffMap.const p) metric.toTensor q v w = 0 := metric_constant_pullback p q v w

example (p v w : Plane) :
    covariantPullbackField 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) 2
      (timeProjection : C^∞⟮𝓘(ℝ, Plane), Plane; 𝓘(ℝ, Plane), Plane⟯)
      metric.toTensor p v w = (-1 + 4 * (p 0) ^ 2) * v 0 * w 0 :=
  metric_timeProjection_pullback p v w

end CovariantPullbackExamples

section ManifoldChartConnection

open LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (MinkowskiModel d) M] [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]
  (g : LorentzMetric σ d M) {e e' : OpenPartialHomeomorph M (MinkowskiModel d)}
  (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M)
  (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, MinkowskiModel d) ∞ M)
  {x : M} (hx : x ∈ e.source) (hx' : x ∈ e'.source)

example (v : MinkowskiModel d) : chartTangentMap e x (chartField e v x) = v :=
  chartTangentMap_field he hx v

example (k i j : Fin (d + 1)) :
    ContMDiffAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ) ∞
      (fun y => g.chartChristoffel e y k i j) x :=
  g.chartChristoffel_contMDiffAt he hx k i j

example (k i j : Fin (d + 1)) :
    g.chartChristoffel e x k i j = ∑ l,
      g.inverseComponent x (chartTangentEquiv he hx) k l *
        (mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.chartComponent e y j l) x
          (chartField e (Pi.single i 1) x) +
         mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.chartComponent e y l i) x
          (chartField e (Pi.single j 1) x) -
         mvfderiv 𝓘(ℝ, MinkowskiModel d) (fun y => g.chartComponent e y i j) x
          (chartField e (Pi.single l 1) x)) / 2 :=
  g.chartChristoffel_eq he hx k i j

example {V : M → MinkowskiModel d}
    (hV : MDifferentiableAt 𝓘(ℝ, MinkowskiModel d) 𝓘(ℝ, MinkowskiModel d) V x)
    (v : MinkowskiModel d) (k : Fin (d + 1)) :
    chartTangentMap e x
      (g.leviCivita (fun y => chartField e (V y) y) x (chartField e v x)) k =
      mvfderiv 𝓘(ℝ, MinkowskiModel d) V x (chartField e v x) k +
        ∑ i, ∑ j, g.chartChristoffel e x k i j * v i * V x j :=
  g.leviCivita_chart_coordinates he hx hV v k

example (k i j : Fin (d + 1)) :
    (∑ l, fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single l 1) k *
      g.chartChristoffel e x l i j) =
      fderiv ℝ (fun z => fderiv ℝ (e' ∘ e.symm) z (Pi.single j 1))
        (e x) (Pi.single i 1) k +
      ∑ a, ∑ b, g.chartChristoffel e' x k a b *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single i 1) a *
        fderiv ℝ (e' ∘ e.symm) (e x) (Pi.single j 1) b :=
  g.chartChristoffel_transformation he he' hx hx' k i j

example (k i j : Fin (d + 1)) :
    g.chartChristoffel e x k i j = g.chartChristoffel e x k j i :=
  g.chartChristoffel_symmetric he hx k i j

example (k i j : Fin (d + 1)) :
    g.opposite.chartChristoffel e x k i j = g.chartChristoffel e x k i j :=
  g.chartChristoffel_opposite e x k i j

end ManifoldChartConnection

section Charts

open LorentzianCharts

example : spacetime.toScheme = (minkowski .timeNegative 1).toScheme := spacetime_toScheme

example : standardChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ Plane :=
  standardChart_mem_maximalAtlas

example : inertialChart ∈ IsManifold.maximalAtlas 𝓘(ℝ, Plane) ∞ Plane :=
  inertialChart_mem_maximalAtlas

example : standardChart.source ∩ inertialChart.source = Set.univ := chart_overlap

example (p : Plane) : (standardChart.symm.trans inertialChart) p = shear p :=
  transition_apply p

example (p v w : Plane) :
    metric.form p v w = (minkowskiMetric .timeNegative 1).form (shear p)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p v)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p w) := metric_covariance p v w

example (p v : Plane) :
    metric.flat p v = (Minkowski.flat .timeNegative (shearLinear (2 * p 0) v)).comp
      (shearLinear (2 * p 0)).toContinuousLinearMap := flat_covariance p v

example (p : Plane) (α : Plane →L[ℝ] ℝ) :
    metric.sharp p (α.comp (shearLinear (2 * p 0)).toContinuousLinearMap) =
      (shearLinear (2 * p 0)).symm (Minkowski.sharp .timeNegative α) :=
  sharp_covariance p α

example (p : Plane) :
    metric.form p (Pi.single 0 1) (Pi.single 0 1) = -1 + 4 * (p 0)^2 :=
  metric_time_time p

example (p : Plane) : metric.form p (Pi.single 0 1) (Pi.single 1 1) = 2 * p 0 :=
  metric_time_space p

example : metric.form ![0, 0] ≠ metric.form ![1, 0] := metric_nonconstant

example : mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear ![0, 0] ≠
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear ![1, 0] := jacobian_nonconstant

example (p v w : Plane) :
    metric.opposite.form p v w = (minkowskiMetric .timePositive 1).form (shear p)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p v)
      (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p w) := opposite_metric_covariance p v w

example (p : Plane) : metric.contractField spatialTensor p = 1 := spatialTensor_contract p

example : metric.toTensor = CovariantTwoTensor.pullback (d := 1)
    shearDiffeomorph (minkowskiMetric .timeNegative 1).toTensor := metric_tensor_pullback

example (p : Plane) (k i j : Fin 2) :
    metric.christoffel p k i j = if k = 1 ∧ i = 0 ∧ j = 0 then 2 else 0 :=
  christoffel_shear p k i j

example (p : Plane) : metric.christoffel p 1 0 0 = 2 := by
  simp [christoffel_shear]

example (p : Plane) (k i j : Fin 2) :
    metric.chartChristoffel standardChart p k i j =
      if k = 1 ∧ i = 0 ∧ j = 0 then 2 else 0 := chartChristoffel_standard p k i j

example (p : Plane) (k i j : Fin 2) :
    metric.chartChristoffel inertialChart p k i j = 0 := chartChristoffel_inertial p k i j

example (p : Plane) (k i j : Fin 2) :
    (∑ l, fderiv ℝ shear p (Pi.single l 1) k * metric.christoffel p l i j) =
      fderiv ℝ (fun z => fderiv ℝ shear z (Pi.single j 1)) p (Pi.single i 1) k :=
  chart_transformation_shear p k i j

example (p v w : Plane) :
    fderiv ℝ shear p
      (NormedSpace.fromTangentSpace p
        (metric.leviCivita (LorentzMetric.modelField w) p (LorentzMetric.modelField v p))) =
      fderiv ℝ (fun q => fderiv ℝ shear q w) p v := connection_shear_transformation p v w

example : metric = (minkowskiMetric .timeNegative 1).pullback shearDiffeomorph
    shearDiffeomorph.contMDiff (fun x =>
      shearDiffeomorph.isInvertible_mfderiv (x := x) (by simp)) :=
  metric_eq_pullback

example {Y : ∀ y : Plane, TangentSpace 𝓘(ℝ, Plane) y} {p : Plane}
    (hY : MDifferentiableAt 𝓘(ℝ, Plane) (𝓘(ℝ, Plane).prod 𝓘(ℝ, Plane))
      (T% Y) (shear p)) (v : TangentSpace 𝓘(ℝ, Plane) p) :
    mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p
      (metric.leviCivita (VectorField.mpullback 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear Y) p v) =
      (minkowskiMetric .timeNegative 1).leviCivita Y (shear p)
        (mfderiv 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) shear p v) := leviCivita_shear_naturality hY v

end Charts
