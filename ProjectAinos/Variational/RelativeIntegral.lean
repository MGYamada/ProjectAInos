/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# The derivative of a relative integral

Let `L(ε, x)` be smooth near `[−r, r] × U` for an open set `U`, and independent of `ε` off a
compact set `K ⊆ U`. Then `ε ↦ ∫ (L(ε, x) − L(0, x)) dx` is differentiable at `0`, with the
derivative `∫ ∂_ε L(0, x) dx` (`hasDerivAt_integral_sub`). The integrand vanishes off `K`, and
the derivative in `ε` is bounded on the compact set `[−r, r] × K`, which dominates it.

This is the form in which actions of fields are varied: the action of a region that is not
compact need not converge, but the difference of the densities of two nearby fields that agree
off a compact set does.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace ProjectAinos.Variational

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [IsFiniteMeasureOnCompacts μ]

/-- **The derivative of a relative integral.** If `L` is smooth at every point of
`[−r, r] × U` and does not depend on `ε` off a compact set `K ⊆ U`, then
`d/dε ∫ (L(ε, x) − L(0, x)) dx = ∫ ∂_ε L(0, x) dx` at `ε = 0`. -/
theorem hasDerivAt_integral_sub {L : ℝ × E → ℝ} {U K : Set E} (hU : IsOpen U)
    (hKc : IsCompact K) (hKU : K ⊆ U) {r : ℝ} (hr : 0 < r)
    (hL : ∀ ε ∈ Metric.closedBall (0 : ℝ) r, ∀ z ∈ U, ContDiffAt ℝ ∞ L (ε, z))
    (hconst : ∀ x ∉ K, ∀ t, L (t, x) = L (0, x)) :
    HasDerivAt (fun ε => ∫ x, (L (ε, x) - L (0, x)) ∂μ)
      (∫ x, deriv (fun t => L (t, x)) 0 ∂μ) 0 := by
  set s := Metric.closedBall (0 : ℝ) r
  have hs0 : s ∈ 𝓝 (0 : ℝ) := Metric.closedBall_mem_nhds _ hr
  have h0s : (0 : ℝ) ∈ s := Metric.mem_closedBall_self hr.le
  -- the bound on the derivative in `ε`
  set D : ℝ × E → ℝ := fun q => fderiv ℝ L q (1, 0)
  have hDat : ∀ ε ∈ s, ∀ z ∈ U, ContinuousAt D (ε, z) := fun ε hε z hz =>
    ((hL ε hε z hz).fderiv_right (m := 0) (by simp)).continuousAt.clm_apply continuousAt_const
  have hDcont : ContinuousOn D (s ×ˢ K) := fun q hq =>
    (hDat q.1 hq.1 q.2 (hKU hq.2)).continuousWithinAt
  obtain ⟨C, hC⟩ := ((isCompact_closedBall (0 : ℝ) r).prod hKc).exists_bound_of_continuousOn hDcont
  have hslice : ∀ ε ∈ s, ∀ z ∈ U, HasDerivAt (fun t => L (t, z)) (D (ε, z)) ε :=
    fun ε hε z hz => by
      have hd := ((hL ε hε z hz).differentiableAt (by simp)).hasFDerivAt
      have hin : HasDerivAt (fun t : ℝ => (t, z)) ((1 : ℝ), (0 : E)) ε :=
        (hasDerivAt_id ε).prodMk (hasDerivAt_const ε z)
      exact hd.comp_hasDerivAt ε hin
  have hderiv : ∀ x, ∀ ε ∈ s, HasDerivAt (fun t => L (t, x) - L (0, x))
      (deriv (fun t => L (t, x)) ε) ε := by
    intro x ε hε
    by_cases hxK : x ∈ K
    · have hd := hslice ε hε x (hKU hxK)
      rw [hd.deriv]
      exact hd.sub_const _
    · have h1 : (fun t => L (t, x) - L (0, x)) = fun _ => 0 := funext fun t => by
        rw [hconst x hxK t, sub_self]
      have h2 : (fun t => L (t, x)) = fun _ => L (0, x) := funext fun t => hconst x hxK t
      rw [h1, h2, deriv_const]
      exact hasDerivAt_const _ _
  have hbound : ∀ x, ∀ ε ∈ s, ‖deriv (fun t => L (t, x)) ε‖ ≤ K.indicator (fun _ => C) x := by
    intro x ε hε
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK, (hslice ε hε x (hKU hxK)).deriv]
      exact hC (ε, x) ⟨hε, hxK⟩
    · have h2 : (fun t => L (t, x)) = fun _ => L (0, x) := funext fun t => hconst x hxK t
      rw [Set.indicator_of_notMem hxK, h2, deriv_const, norm_zero]
  have hbint : Integrable (K.indicator fun _ => C) μ :=
    (continuousOn_const.integrableOn_compact hKc).integrable_indicator
      hKc.isClosed.measurableSet
  -- continuity in the point
  have hin (t : ℝ) (x : E) : ContinuousAt (fun z : E => (t, z)) x :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hnear : ∀ x ∉ U, ∀ᶠ z in 𝓝 x, z ∉ K := fun x hx =>
    hKc.isClosed.isOpen_compl.mem_nhds fun h' => hx (hKU h')
  have hFcont : ∀ ε ∈ s, Continuous (fun x => L (ε, x) - L (0, x)) := by
    intro ε hε
    refine continuous_iff_continuousAt.mpr fun x => ?_
    by_cases hx : x ∈ U
    · exact ((hL ε hε x hx).continuousAt.comp_of_eq (hin ε x) rfl).sub
        ((hL 0 h0s x hx).continuousAt.comp_of_eq (hin 0 x) rfl)
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hnear x hx] with z hz
      rw [hconst z hz ε, sub_self]
  have hF'cont : Continuous (fun x => deriv (fun t => L (t, x)) 0) := by
    refine continuous_iff_continuousAt.mpr fun x => ?_
    by_cases hx : x ∈ U
    · have hDc : ContinuousAt (fun z => D (0, z)) x :=
        (hDat 0 h0s x hx).comp_of_eq (hin 0 x) rfl
      refine hDc.congr ?_
      filter_upwards [hU.mem_nhds hx] with z hz
      exact (hslice 0 h0s z hz).deriv.symm
    · refine (continuousAt_const (y := (0 : ℝ))).congr ?_
      filter_upwards [hnear x hx] with z hz
      have h2 : (fun t => L (t, z)) = fun _ => L (0, z) := funext fun t => hconst z hz t
      rw [h2, deriv_const]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun ε x => L (ε, x) - L (0, x)) (F' := fun ε x => deriv (fun t => L (t, x)) ε)
    (bound := K.indicator fun _ => C) hs0
    (Filter.eventually_of_mem hs0 fun ε hε => (hFcont ε hε).aestronglyMeasurable)
    (by simp) hF'cont.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ε hε => hbound x ε hε) hbint
    (Filter.Eventually.of_forall fun x ε hε => hderiv x ε hε)).2

/-- The integrand of the derivative is integrable. -/
theorem integrable_deriv_sub {L : ℝ × E → ℝ} {U K : Set E}
    (hKc : IsCompact K) (hKU : K ⊆ U) {r : ℝ} (hr : 0 < r)
    (hL : ∀ ε ∈ Metric.closedBall (0 : ℝ) r, ∀ z ∈ U, ContDiffAt ℝ ∞ L (ε, z))
    (hconst : ∀ x ∉ K, ∀ t, L (t, x) = L (0, x)) :
    Integrable (fun x => deriv (fun t => L (t, x)) 0) μ := by
  have h0 : (0 : ℝ) ∈ Metric.closedBall (0 : ℝ) r := Metric.mem_closedBall_self hr.le
  have hslice : ∀ z ∈ U, deriv (fun t => L (t, z)) 0 = fderiv ℝ L (0, z) (1, 0) := fun z hz => by
    have hd := ((hL 0 h0 z hz).differentiableAt (by simp)).hasFDerivAt
    have hin : HasDerivAt (fun t : ℝ => (t, z)) ((1 : ℝ), (0 : E)) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 z)
    exact (hd.comp_hasDerivAt 0 hin).deriv
  have hcont : ContinuousOn (fun z => fderiv ℝ L (0, z) (1, 0)) K := fun z hz =>
    (((hL 0 h0 z (hKU hz)).fderiv_right (m := 0) (by simp)).continuousAt.comp_of_eq
      (continuous_const.prodMk continuous_id).continuousAt rfl).clm_apply
      continuousAt_const |>.continuousWithinAt
  have hK : IntegrableOn (fun x => deriv (fun t => L (t, x)) 0) K μ :=
    (hcont.integrableOn_compact hKc).congr_fun (fun z hz => (hslice z (hKU hz)).symm)
      hKc.isClosed.measurableSet
  refine (integrableOn_iff_integrable_of_support_subset ?_).mp hK
  intro x hx
  by_contra hxK
  have h2 : (fun t => L (t, x)) = fun _ => L (0, x) := funext fun t => hconst x hxK t
  apply hx
  change deriv (fun t => L (t, x)) 0 = 0
  rw [h2, deriv_const]

end ProjectAinos.Variational
