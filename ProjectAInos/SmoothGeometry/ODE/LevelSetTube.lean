/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.ODE.LevelSetFlow

/-!
# A neighbourhood of a compact level set on which the flows are complete

Let the fields `Xᵢ` be tangent to the level sets of `F` and let the level set
`F = c` be compact. `exists_isInvariantSet_tube`: there are an open set `U`
with compact closure that contains the level set, and an open set `B` of
values that contains `c`, such that the part of `U` over `B` is preserved by
the flows of all `Σᵢ tᵢ Xᵢ`, which are defined for all times on it. A level set
over `B` does not meet the frontier of `U`, so a solution that starts in `U`
cannot leave it.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace ProjectAInos.SmoothGeometry.NonlinearODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {ι κ : Type*} [Fintype ι] [Fintype κ] {X : ι → E → E} {F : E → κ → ℝ} {c : κ → ℝ}

/-- A neighbourhood of a compact level set, over a neighbourhood of its value,
on which the flows are complete. -/
theorem exists_isInvariantSet_tube (hX : ∀ i, ContDiff ℝ ∞ (X i)) (hF : ContDiff ℝ ∞ F)
    (htan : ∀ i y, fderiv ℝ F y (X i y) = 0) (hcomp : IsCompact (F ⁻¹' {c})) :
    ∃ (U : Set E) (B : Set (κ → ℝ)), IsOpen U ∧ IsOpen B ∧ F ⁻¹' {c} ⊆ U ∧ c ∈ B ∧
      IsCompact (closure U) ∧ IsInvariantSet X (F ⁻¹' B ∩ U) := by
  obtain ⟨U, hUdef⟩ : ∃ U : Set E, U = Metric.thickening 1 (F ⁻¹' {c}) := ⟨_, rfl⟩
  have hUopen : IsOpen U := by
    rw [hUdef]
    exact Metric.isOpen_thickening
  have hMU : F ⁻¹' {c} ⊆ U := by
    rw [hUdef]
    exact Metric.self_subset_thickening one_pos _
  have hclU : IsCompact (closure U) := by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_closure ?_
    rw [hUdef]
    exact (hcomp.isBounded.thickening).closure
  have hfr : IsCompact (frontier U) :=
    hclU.of_isClosed_subset isClosed_frontier frontier_subset_closure
  have hFfr : IsClosed (F '' frontier U) := (hfr.image hF.continuous).isClosed
  have hcB : c ∈ (F '' frontier U)ᶜ := by
    rintro ⟨y, hy, hyc⟩
    have hyU : y ∈ U := hMU hyc
    have hdisj : Disjoint (frontier U) U := by
      rw [hUopen.frontier_eq]
      exact disjoint_sdiff_left
    exact hdisj.le_bot ⟨hy, hyU⟩
  -- a solution that starts in the tube stays in `U`
  have hstay : ∀ (t : ι → ℝ) (r : ℝ) (x : E), x ∈ F ⁻¹' (F '' frontier U)ᶜ ∩ U →
      (r, x) ∈ flowDomain (jointField X t) → flow (jointField X t) (r, x) ∈ U := by
    intro t r x hx hr
    have hA := contDiff_jointField hX t
    have hdom : ∀ s ∈ uIcc 0 r, (s, x) ∈ flowDomain (jointField X t) := fun s hs =>
      mem_flowDomain_of_mem_uIcc hr hs
    have hcont : ContinuousOn (fun s => flow (jointField X t) (s, x)) (uIcc 0 r) :=
      (continuousOn_flow hA).comp (continuous_id.prodMk continuous_const).continuousOn hdom
    have hpre : IsPreconnected ((fun s => flow (jointField X t) (s, x)) '' uIcc 0 r) :=
      isPreconnected_uIcc.image _ hcont
    have hsub : (fun s => flow (jointField X t) (s, x)) '' uIcc 0 r ⊆ U ∪ (closure U)ᶜ := by
      rintro y ⟨s, hs, rfl⟩
      by_cases hyU : flow (jointField X t) (s, x) ∈ U
      · exact Or.inl hyU
      · refine Or.inr fun hycl => ?_
        have hyfr : flow (jointField X t) (s, x) ∈ frontier U := by
          rw [hUopen.frontier_eq]
          exact ⟨hycl, hyU⟩
        have hFy := flow_jointField_levelSet hX hF htan t (hdom s hs)
        exact hx.1 ⟨_, hyfr, hFy⟩
    have hne : ((fun s => flow (jointField X t) (s, x)) '' uIcc 0 r ∩ U).Nonempty :=
      ⟨x, ⟨0, left_mem_uIcc, flow_zero _ x⟩, hx.2⟩
    have hdisj : Disjoint U (closure U)ᶜ :=
      disjoint_compl_right.mono_left subset_closure
    exact hpre.subset_left_of_subset_union hUopen isClosed_closure.isOpen_compl hdisj hsub hne
      ⟨r, right_mem_uIcc, rfl⟩
  have hdomain : ∀ (t : ι → ℝ) (r : ℝ) (x : E), x ∈ F ⁻¹' (F '' frontier U)ᶜ ∩ U →
      (r, x) ∈ flowDomain (jointField X t) := fun t r x hx =>
    mem_flowDomain_of_isCompact (contDiff_jointField hX t) hclU fun s _ hs =>
      subset_closure (hstay t s x hx hs)
  refine ⟨U, (F '' frontier U)ᶜ, hUopen, hFfr.isOpen_compl, hMU, hcB, hclU, hdomain,
    fun t r x hx => ⟨?_, hstay t r x hx (hdomain t r x hx)⟩⟩
  change F (flow (jointField X t) (r, x)) ∈ (F '' frontier U)ᶜ
  rw [flow_jointField_levelSet hX hF htan t (hdomain t r x hx)]
  exact hx.1

end ProjectAInos.SmoothGeometry.NonlinearODE
