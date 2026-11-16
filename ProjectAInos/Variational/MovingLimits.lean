/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Variational.IntervalParameter
public import ProjectAInos.SmoothAlgebra.ParametricIntegral

/-!
# Differentiating an integral whose limits move

For a smooth integrand `F(s, t)` and differentiable limits `a(s)`, `b(s)`,

`d/ds ∫_{a(s)}^{b(s)} F(s, t) dt = ∫ ∂F/∂s dt + F(s, b) b' − F(s, a) a'`.

The integral is a smooth function of the parameter and of the two limits
together, and its three partial derivatives are the derivative under the
integral sign and the two values of the integrand at the limits.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace ProjectAInos.Variational

/-- Leibniz's rule with moving limits. -/
theorem hasDerivAt_intervalIntegral_moving {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    {D : ℝ → ℝ} {a b : ℝ → ℝ} {s₀ a' b' : ℝ} (ha : HasDerivAt a a' s₀)
    (hb : HasDerivAt b b' s₀)
    (hD : ∀ t ∈ uIcc (a s₀) (b s₀), HasDerivAt (fun s => F (s, t)) (D t) s₀) :
    HasDerivAt (fun s => ∫ t in a s..b s, F (s, t))
      ((∫ t in a s₀..b s₀, D t) + F (s₀, b s₀) * b' - F (s₀, a s₀) * a') s₀ := by
  let Ψ : ℝ × ℝ × ℝ → ℝ := fun p => ∫ t in p.2.1..p.2.2, F (p.1, t)
  have hΨ : ContDiff ℝ ∞ Ψ := SmoothAlgebra.contDiff_infty_parametric_intervalIntegral_limits hF
  have hΨd := (hΨ.differentiable (by simp) (s₀, a s₀, b s₀)).hasFDerivAt
  have hcurve : HasDerivAt (fun s => (s, a s, b s)) ((1 : ℝ), a', b') s₀ :=
    (hasDerivAt_id s₀).prodMk (ha.prodMk hb)
  have hcomp := hΨd.comp_hasDerivAt s₀ hcurve
  have hFs : Continuous fun t => F (s₀, t) :=
    hF.continuous.comp (continuous_const.prodMk continuous_id)
  -- the derivative in the parameter
  have h1 : fderiv ℝ Ψ (s₀, a s₀, b s₀) ((1 : ℝ), (0 : ℝ), (0 : ℝ)) =
      ∫ t in a s₀..b s₀, D t := by
    have hline : HasDerivAt (fun s : ℝ => (s, a s₀, b s₀)) ((1 : ℝ), (0 : ℝ), (0 : ℝ)) s₀ :=
      (hasDerivAt_id s₀).prodMk (hasDerivAt_const s₀ (a s₀, b s₀))
    have hA := hΨd.comp_hasDerivAt s₀ hline
    exact hA.unique (hasDerivAt_intervalIntegral_of_contDiff (hF.of_le (by simp)) hD)
  -- the derivative in the lower limit
  have h2 : fderiv ℝ Ψ (s₀, a s₀, b s₀) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) = -F (s₀, a s₀) := by
    have hline : HasDerivAt (fun α : ℝ => (s₀, α, b s₀)) ((0 : ℝ), (1 : ℝ), (0 : ℝ)) (a s₀) :=
      (hasDerivAt_const (a s₀) s₀).prodMk ((hasDerivAt_id (a s₀)).prodMk
        (hasDerivAt_const (a s₀) (b s₀)))
    have hA := hΨd.comp_hasDerivAt (a s₀) hline
    exact hA.unique (intervalIntegral.integral_hasDerivAt_left (hFs.intervalIntegrable _ _)
      (hFs.stronglyMeasurableAtFilter _ _) hFs.continuousAt)
  -- the derivative in the upper limit
  have h3 : fderiv ℝ Ψ (s₀, a s₀, b s₀) ((0 : ℝ), (0 : ℝ), (1 : ℝ)) = F (s₀, b s₀) := by
    have hline : HasDerivAt (fun β : ℝ => (s₀, a s₀, β)) ((0 : ℝ), (0 : ℝ), (1 : ℝ)) (b s₀) :=
      (hasDerivAt_const (b s₀) s₀).prodMk ((hasDerivAt_const (b s₀) (a s₀)).prodMk
        (hasDerivAt_id (b s₀)))
    have hA := hΨd.comp_hasDerivAt (b s₀) hline
    exact hA.unique (intervalIntegral.integral_hasDerivAt_right (hFs.intervalIntegrable _ _)
      (hFs.stronglyMeasurableAtFilter _ _) hFs.continuousAt)
  have hsplit : ((1 : ℝ), a', b') =
      ((1 : ℝ), (0 : ℝ), (0 : ℝ)) + a' • ((0 : ℝ), (1 : ℝ), (0 : ℝ)) +
        b' • ((0 : ℝ), (0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  have hval : fderiv ℝ Ψ (s₀, a s₀, b s₀) ((1 : ℝ), a', b') =
      (∫ t in a s₀..b s₀, D t) + F (s₀, b s₀) * b' - F (s₀, a s₀) * a' := by
    rw [hsplit, map_add, map_add, map_smul, map_smul, h1, h2, h3]
    simp only [smul_eq_mul]
    ring
  rw [← hval]
  exact hcomp

/-- Limits that move continuously keep the segment between them inside an open
set that contains the reference segment. -/
theorem eventually_uIcc_mem_open {a b : ℝ → ℝ} {s₀ : ℝ} (ha : ContinuousAt a s₀)
    (hb : ContinuousAt b s₀) {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ∀ t ∈ uIcc (a s₀) (b s₀), (s₀, t) ∈ V) :
    ∀ᶠ s in 𝓝 s₀, ∀ t ∈ uIcc (a s) (b s), (s, t) ∈ V := by
  obtain ⟨S, W, hS, hW, hsS, hKW, hSW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := s₀)) (isCompact_uIcc (a := a s₀) (b := b s₀)) hV
    (by rintro ⟨s, t⟩ ⟨rfl, ht⟩; exact h t ht)
  obtain ⟨δ, hδ, hδW⟩ := isCompact_uIcc.exists_thickening_subset_open hW hKW
  have hconv : Convex ℝ (Metric.thickening δ (uIcc (a s₀) (b s₀))) :=
    (convex_uIcc _ _).thickening δ
  have hA : ∀ᶠ s in 𝓝 s₀, a s ∈ Metric.thickening δ (uIcc (a s₀) (b s₀)) :=
    ha.eventually_mem (Metric.isOpen_thickening.mem_nhds
      (Metric.self_subset_thickening hδ _ left_mem_uIcc))
  have hB : ∀ᶠ s in 𝓝 s₀, b s ∈ Metric.thickening δ (uIcc (a s₀) (b s₀)) :=
    hb.eventually_mem (Metric.isOpen_thickening.mem_nhds
      (Metric.self_subset_thickening hδ _ right_mem_uIcc))
  filter_upwards [hA, hB, hS.mem_nhds (hsS (mem_singleton s₀))] with s hsa hsb hsS' t ht
  refine hSW ⟨hsS', hδW ?_⟩
  rw [← segment_eq_uIcc] at ht
  exact hconv.segment_subset hsa hsb ht

/-- Leibniz's rule with moving limits for an integrand that is smooth on an open
set containing the reference segment. -/
theorem hasDerivAt_intervalIntegral_moving_on {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {D : ℝ → ℝ} {a b : ℝ → ℝ} {s₀ a' b' : ℝ}
    (ha : HasDerivAt a a' s₀) (hb : HasDerivAt b b' s₀)
    (hK : ∀ t ∈ uIcc (a s₀) (b s₀), (s₀, t) ∈ U)
    (hD : ∀ t ∈ uIcc (a s₀) (b s₀), HasDerivAt (fun s => F (s, t)) (D t) s₀) :
    HasDerivAt (fun s => ∫ t in a s..b s, F (s, t))
      ((∫ t in a s₀..b s₀, D t) + F (s₀, b s₀) * b' - F (s₀, a s₀) * a') s₀ := by
  have hKc : IsCompact ({s₀} ×ˢ uIcc (a s₀) (b s₀)) :=
    isCompact_singleton.prod isCompact_uIcc
  obtain ⟨g, hg, V, hV, hKV, heq⟩ := exists_contDiff_extension_near_compact (n := ⊤)
    hKc hU (by rintro ⟨s, t⟩ ⟨rfl, ht⟩; exact hK t ht) hF
  have hmem : ∀ t ∈ uIcc (a s₀) (b s₀), (s₀, t) ∈ V := fun t ht => hKV ⟨by simp, ht⟩
  have hp : ∀ t ∈ uIcc (a s₀) (b s₀),
      (fun s => g (s, t)) =ᶠ[𝓝 s₀] fun s => F (s, t) := by
    intro t ht
    have hev : g =ᶠ[𝓝 (s₀, t)] F :=
      eventually_of_mem (hV.mem_nhds (hmem t ht)) fun _ hp => heq hp
    exact hev.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hi := hasDerivAt_intervalIntegral_moving hg ha hb
    (fun t ht => (hD t ht).congr_of_eventuallyEq (hp t ht))
  rw [heq (hmem _ right_mem_uIcc), heq (hmem _ left_mem_uIcc)] at hi
  refine hi.congr_of_eventuallyEq ?_
  filter_upwards [eventually_uIcc_mem_open ha.continuousAt hb.continuousAt hV hmem] with s hs
  exact intervalIntegral.integral_congr fun t ht => (heq (hs t ht)).symm

end ProjectAInos.Variational
