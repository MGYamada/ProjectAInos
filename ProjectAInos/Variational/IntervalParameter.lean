/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Variational.LocalExtension
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Differentiating a finite integral from local joint C¹ regularity

Compactness supplies a common parameter neighborhood and an integrable
derivative bound. Neither a global regularity nor a domination premise is
imposed on the caller.
-/

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace ProjectAInos.Variational

/-- A local derivative identity splits a finite integral into its boundary
term and residual. Integrability of the residual follows from the hypotheses. -/
theorem integral_eq_boundary_add_residual {P D R : ℝ → ℝ} {a b : ℝ}
    (hP : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 P t)
    (hD : ContinuousOn D (uIcc a b))
    (hd : ∀ t ∈ uIcc a b, HasDerivAt P (D t - R t) t) :
    (∫ t in a..b, D t) = P b - P a + ∫ t in a..b, R t := by
  have hc : ContinuousOn (deriv P) (uIcc a b) := fun t ht =>
    (((hP t ht).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).continuousWithinAt
  have hi : IntervalIntegrable (deriv P) volume a b := hc.intervalIntegrable
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => ((hP t ht).differentiableAt (by norm_num)).hasDerivAt) hi
  have heq : (∫ t in a..b, R t) = ∫ t in a..b, D t - deriv P t := by
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [(hd t ht).deriv]
    ring
  rw [heq, intervalIntegral.integral_sub hD.intervalIntegrable hi, hfund]
  ring

/-- The specified partial derivative is continuous on the reference segment. -/
theorem continuousOn_parameter_derivative {F : ℝ × ℝ → ℝ} {D : ℝ → ℝ} {ε₀ a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 F (ε₀, t))
    (hD : ∀ t ∈ uIcc a b, HasDerivAt (fun ε => F (ε, t)) (D t) ε₀) :
    ContinuousOn D (uIcc a b) := by
  have hG : ContinuousOn (fun t => fderiv ℝ F (ε₀, t) (1, 0)) (uIcc a b) := by
    intro t ht
    exact (((hF t ht).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const).comp
      (continuous_const.prodMk continuous_id).continuousAt |>.continuousWithinAt
  apply hG.congr
  intro t ht
  have hp : HasDerivAt (fun ε : ℝ => (ε, t)) (1, 0) ε₀ :=
    (hasDerivAt_id ε₀).prodMk (hasDerivAt_const ε₀ t)
  exact (hD t ht).unique
    (((hF t ht).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt ε₀ hp)

/-- Joint C¹ regularity supplies domination for a finite parameter integral. -/
theorem hasDerivAt_intervalIntegral_of_contDiff {F : ℝ × ℝ → ℝ}
    (hF : ContDiff ℝ 1 F) {D : ℝ → ℝ} {ε₀ a b : ℝ}
    (hD : ∀ t ∈ uIcc a b, HasDerivAt (fun ε => F (ε, t)) (D t) ε₀) :
    HasDerivAt (fun ε => ∫ t in a..b, F (ε, t)) (∫ t in a..b, D t) ε₀ := by
  let G : ℝ × ℝ → ℝ := fun p => fderiv ℝ F p (1, 0)
  have hG : Continuous G :=
    (hF.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hd : ∀ ε t, HasDerivAt (fun s => F (s, t)) (G (ε, t)) ε := by
    intro ε t
    have hp : HasDerivAt (fun s : ℝ => (s, t)) (1, 0) ε :=
      (hasDerivAt_id ε).prodMk (hasDerivAt_const ε t)
    exact ((hF.differentiable (by norm_num) (ε, t)).hasFDerivAt.comp_hasDerivAt ε hp)
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_uIcc :
    IsCompact (Icc (ε₀ - 1) (ε₀ + 1) ×ˢ uIcc a b)).exists_bound_of_continuousOn hG.continuousOn
  have hi := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := a) (b := b)
    (F := fun ε t => F (ε, t)) (F' := fun ε t => G (ε, t))
    (bound := fun _ => C) (Icc_mem_nhds (by linarith) (by linarith))
    (Eventually.of_forall fun ε =>
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    ((hF.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a b)
    ((hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun t ht ε hε => hC (ε, t) ⟨hε, uIoc_subset_uIcc ht⟩)
    (intervalIntegrable_const) (Eventually.of_forall fun t _ ε _ => hd ε t)
  convert hi.2 using 1
  apply intervalIntegral.integral_congr
  intro t ht
  exact (hD t ht).unique (hd ε₀ t)

/-- Local joint C¹ regularity along the compact reference segment suffices.
The extension is of the scalar integrand, so no chart covering the whole
underlying geometric curve is required. -/
theorem hasDerivAt_intervalIntegral_of_contDiffAt {F : ℝ × ℝ → ℝ}
    {D : ℝ → ℝ} {ε₀ a b : ℝ}
    (hF : ∀ t ∈ uIcc a b, ContDiffAt ℝ 1 F (ε₀, t))
    (hD : ∀ t ∈ uIcc a b, HasDerivAt (fun ε => F (ε, t)) (D t) ε₀) :
    HasDerivAt (fun ε => ∫ t in a..b, F (ε, t)) (∫ t in a..b, D t) ε₀ := by
  let U := {p | ContDiffAt ℝ 1 F p}
  have hU : IsOpen U := by
    apply isOpen_iff_mem_nhds.mpr
    intro p hp
    exact (show ContDiffAt ℝ 1 F p from hp).eventually (by norm_num)
  have hK : IsCompact ({ε₀} ×ˢ uIcc a b) := isCompact_singleton.prod isCompact_uIcc
  have hKU : {ε₀} ×ˢ uIcc a b ⊆ U := by
    rintro ⟨ε, t⟩ ⟨rfl, ht⟩
    exact hF t ht
  obtain ⟨f, hf, V, hV, hKV, heq⟩ := exists_contDiff_extension_near_compact
    hK hU hKU (fun p hp => (show ContDiffAt ℝ 1 F p from hp).contDiffWithinAt)
  have hp : ∀ t ∈ uIcc a b,
      (fun ε => f (ε, t)) =ᶠ[𝓝 ε₀] (fun ε => F (ε, t)) := by
    intro t ht
    have hmem : (ε₀, t) ∈ V := hKV ⟨by simp, ht⟩
    have hev : f =ᶠ[𝓝 (ε₀, t)] F :=
      eventually_of_mem (hV.mem_nhds hmem) (fun _ hp => heq hp)
    exact hev.comp_tendsto (continuous_id.prodMk continuous_const).continuousAt
  have hi := hasDerivAt_intervalIntegral_of_contDiff hf
    (fun t ht => (hD t ht).congr_of_eventuallyEq (hp t ht))
  apply hi.congr_of_eventuallyEq
  have hstay := eventually_mapsTo_open_at (ε₀ := ε₀) (K := uIcc a b)
    (p := id) isCompact_uIcc continuous_id hV
    (fun t ht => hKV ⟨by simp, ht⟩)
  filter_upwards [hstay] with ε hε
  exact intervalIntegral.integral_congr fun t ht => (heq (hε t ht)).symm

end ProjectAInos.Variational
