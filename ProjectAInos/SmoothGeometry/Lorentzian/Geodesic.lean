/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurveMetric
public import ProjectAInos.SmoothGeometry.Lorentzian.AlongCurveReparam
public import Mathlib.Analysis.Calculus.MeanValue

/-! # Parallel fields and affine geodesics

These definitions include local regularity at each parameter in the set.
Existence of the fields and curves is a separate ODE theorem, not a premise
hidden in the definitions. Metric preservation is proved on convex parameter
sets, including finite closed intervals with regular extensions at endpoints.
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

/-- A differentiable field along a curve is parallel where its covariant
derivative vanishes. -/
def IsParallelOn (g : LorentzMetric σ d M) {γ : ℝ → M}
    (s : Set ℝ) (V : AlongField (d := d) γ) : Prop :=
  ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ) ((I).prod I)
    (fun r => TotalSpace.mk' E (γ r) (V r)) t ∧ g.covariantAlong V t = 0

/-- A locally `C²` curve is an affinely parametrized geodesic precisely when
its velocity is parallel. No completeness is part of this predicate. -/
def IsGeodesicOn (g : LorentzMetric σ d M) (s : Set ℝ) (γ : ℝ → M) : Prop :=
  ∀ t ∈ s, ContMDiffAt 𝓘(ℝ) I 2 γ t ∧ g.covariantAlong (curveVelocity γ) t = 0

/-- Parallel fields remain parallel after any differentiable parameter
change into their original parameter set. -/
theorem IsParallelOn.reparam {g : LorentzMetric σ d M}
    {γ : ℝ → M} {V : AlongField (d := d) γ} {r : ℝ → ℝ} {s u : Set ℝ}
    (h : g.IsParallelOn u V) (hr : ∀ t ∈ s, DifferentiableAt ℝ r t)
    (hγ : ∀ t ∈ u, MDifferentiableAt 𝓘(ℝ) I γ t) (hm : Set.MapsTo r s u) :
    g.IsParallelOn s (γ := γ ∘ r) (fun t => V (r t)) := by
  intro t ht
  refine ⟨((h (r t) (hm ht)).1).comp t (hr t ht).mdifferentiableAt, ?_⟩
  rw [g.covariantAlong_reparam (hγ (r t) (hm ht)) (hr t ht) (h (r t) (hm ht)).1,
    (h (r t) (hm ht)).2, smul_zero]

/-- Affine changes of parameter preserve the affine geodesic equation.
Negative slopes include path reversal; slope zero gives a constant curve. -/
theorem IsGeodesicOn.affine_reparam {g : LorentzMetric σ d M}
    {γ : ℝ → M} {s u : Set ℝ} (h : g.IsGeodesicOn u γ) (a b : ℝ)
    (hm : Set.MapsTo (fun t => a * t + b) s u) :
    g.IsGeodesicOn s (fun t => γ (a * t + b)) := by
  let r : ℝ → ℝ := fun t => a * t + b
  have hr : ContDiff ℝ ∞ r := by dsimp [r]; fun_prop
  have hd : deriv r = fun _ => a := by
    funext t
    exact ((hasDerivAt_id t).const_mul a |>.add_const b).deriv.trans (by simp)
  intro t ht
  have hγ := (h (r t) (hm ht)).1
  refine ⟨hγ.comp t (hr.of_le (by simp)).contMDiff.contMDiffAt, ?_⟩
  change g.covariantAlong (curveVelocity (γ ∘ r)) t = 0
  rw [g.covariantAcceleration_reparam hγ (hr.of_le (by simp)).contDiffAt,
    hd, deriv_const, zero_smul, (h (r t) (hm ht)).2, smul_zero, zero_add]

/-- A geodesic's velocity is a differentiable parallel field. -/
theorem IsGeodesicOn.velocity_parallel {g : LorentzMetric σ d M} {γ : ℝ → M} {s : Set ℝ}
    (h : g.IsGeodesicOn s γ) : g.IsParallelOn s (curveVelocity γ) := by
  intro t ht
  exact ⟨(curveVelocity_contMDiffAt (n := 1) (h t ht).1).mdifferentiableAt (by norm_num), (h t ht).2⟩

/-- Parallel fields preserve their metric pairing throughout a convex
parameter set. The curve and fields need only be differentiable there. -/
theorem parallel_pairing_eq (g : LorentzMetric σ d M)
    {γ : ℝ → M} {V W : AlongField (d := d) γ} {s : Set ℝ} (hs : Convex ℝ s)
    (hγ : ∀ t ∈ s, MDifferentiableAt 𝓘(ℝ) I γ t)
    (hV : g.IsParallelOn s V) (hW : g.IsParallelOn s W) {a b : ℝ}
    (ha : a ∈ s) (hb : b ∈ s) :
    g.form (γ a) (V a) (W a) = g.form (γ b) (V b) (W b) := by
  let f : ℝ → ℝ := fun t => g.form (γ t) (V t) (W t)
  have hd (t : ℝ) (ht : t ∈ s) : HasDerivAt f 0 t := by
    simpa only [(hV t ht).2, (hW t ht).2, map_zero, zero_apply, add_zero] using
      g.hasDerivAt_pairing_along (hγ t ht) (hV t ht).1 (hW t ht).1
  apply hs.is_const_of_fderivWithin_eq_zero (𝕜 := ℝ) (f := f)
    (fun t ht => (hd t ht).differentiableAt.differentiableWithinAt) _ ha hb
  intro t ht
  by_cases hu : UniqueDiffWithinAt ℝ s t
  · have hf : HasFDerivAt f (0 : ℝ →L[ℝ] ℝ) t := by
      rw [hasFDerivAt_iff_hasDerivAt]
      exact hd t ht
    exact hf.hasFDerivWithinAt.fderivWithin hu
  · exact fderivWithin_zero_of_not_uniqueDiffWithinAt hu

/-- The signed metric norm of geodesic velocity is constant. -/
theorem IsGeodesicOn.metric_velocity_eq {g : LorentzMetric σ d M}
    {γ : ℝ → M} {s : Set ℝ} (h : g.IsGeodesicOn s γ) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    g.form (γ a) (curveVelocity γ a) (curveVelocity γ a) =
      g.form (γ b) (curveVelocity γ b) (curveVelocity γ b) :=
  g.parallel_pairing_eq hs (fun t ht => (h t ht).1.mdifferentiableAt (by norm_num))
    h.velocity_parallel h.velocity_parallel ha hb

/-- Timelike character is preserved for either Lorentz metric convention. -/
theorem IsGeodesicOn.timelike_iff {g : LorentzMetric σ d M}
    {γ : ℝ → M} {s : Set ℝ} (h : g.IsGeodesicOn s γ) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    (0 < σ.timeSign * g.form (γ a) (curveVelocity γ a) (curveVelocity γ a)) ↔
      (0 < σ.timeSign * g.form (γ b) (curveVelocity γ b) (curveVelocity γ b)) := by
  rw [h.metric_velocity_eq hs ha hb]

/-- Zero metric norm is preserved. Nonvanishing of a null velocity is a
separate consequence of uniqueness of the geodesic initial-value problem. -/
theorem IsGeodesicOn.null_norm_iff {g : LorentzMetric σ d M}
    {γ : ℝ → M} {s : Set ℝ} (h : g.IsGeodesicOn s γ) (hs : Convex ℝ s)
    {a b : ℝ} (ha : a ∈ s) (hb : b ∈ s) :
    (g.form (γ a) (curveVelocity γ a) (curveVelocity γ a) = 0) ↔
      (g.form (γ b) (curveVelocity γ b) (curveVelocity γ b) = 0) := by
  rw [h.metric_velocity_eq hs ha hb]

/-- Covariant acceleration in an arbitrary smooth chart is the ordinary
second coordinate derivative plus the quadratic Christoffel term. -/
theorem covariantAcceleration_coordinates (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {t : ℝ} (hx : γ t ∈ e.source)
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) (k : Fin (d + 1)) :
    chartTangentMap e (γ t) (g.covariantAlong (curveVelocity γ) t) k =
      deriv (deriv (e ∘ γ)) t k + ∑ i, ∑ j,
        g.chartChristoffel e (γ t) k i j * deriv (e ∘ γ) t i * deriv (e ∘ γ) t j := by
  have hγd := hγ.mdifferentiableAt (by norm_num)
  have hn := (contMDiffAt_iff_contMDiffAt_nhds (n := 1) (by norm_num)).mp (hγ.of_le (by norm_num))
  have heq : alongComponents e (curveVelocity γ) =ᶠ[𝓝 t] deriv (e ∘ γ) := by
    filter_upwards [hγ.continuousAt (e.open_source.mem_nhds hx), hn] with r hr hγr
    exact chartTangentMap_curveVelocity he hr (hγr.mdifferentiableAt (by norm_num))
  have hv := (curveVelocity_contMDiffAt (n := 1) hγ).mdifferentiableAt (by norm_num)
  rw [g.covariantAlong_coordinates he hx hγd hv, heq.deriv_eq, heq.self_of_nhds]

/-- The intrinsic affine geodesic equation is equivalent to its chart ODE
at every `C²` point, with all chart-domain hypotheses explicit. -/
theorem geodesic_equation_iff_coordinates (g : LorentzMetric σ d M)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas I ∞ M)
    {γ : ℝ → M} {t : ℝ} (hx : γ t ∈ e.source)
    (hγ : ContMDiffAt 𝓘(ℝ) I 2 γ t) :
    g.covariantAlong (curveVelocity γ) t = 0 ↔ ∀ k : Fin (d + 1),
      deriv (deriv (e ∘ γ)) t k + ∑ i, ∑ j,
        g.chartChristoffel e (γ t) k i j * deriv (e ∘ γ) t i * deriv (e ∘ γ) t j = 0 := by
  constructor
  · intro hz k
    rw [← g.covariantAcceleration_coordinates he hx hγ k, hz, map_zero]
    rfl
  · intro h
    apply (chartTangentEquiv he hx).injective
    ext k
    simpa only [chartTangentEquiv_apply, map_zero, Pi.zero_apply,
      g.covariantAcceleration_coordinates he hx hγ k] using h k

end ProjectAInos.SmoothGeometry.LorentzMetric
