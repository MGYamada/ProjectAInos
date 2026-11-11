/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.Bundle
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

/-! # Testing smoothness of finite-rank bundle maps

Smoothness of a hom-bundle section can be tested on local smooth sections of
its domain. Local trivializations provide the test fields; no global frame
or norm on the actual fibres is needed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle FiberBundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.Tensor

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Finite-dimensional linear-map-valued functions are smooth precisely when
their evaluations on each fixed vector are smooth. -/
theorem contMDiffAt_clm_iff
    {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ∞ω} {f : M → F →L[ℝ] G} {x : M} :
    ContMDiffAt I 𝓘(ℝ, F →L[ℝ] G) n f x ↔
      ∀ v, ContMDiffAt I 𝓘(ℝ, G) n (fun y => f y v) x := by
  simp only [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt,
    contDiffWithinAt_clm_apply, Function.comp_def]

namespace SmoothBundle

/-- A hom-bundle section is smooth at a point if it carries every locally
smooth section of its domain to a locally smooth section of its codomain. -/
theorem contMDiffAt_of_apply (A B : SmoothBundle I (M := M))
    {L : ∀ x, A.Fiber x →L[ℝ] B.Fiber x} {x : M}
    (h : ∀ (v : ∀ x, A.Fiber x),
      ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) ∞ (fun y => TotalSpace.mk' A.Model y (v y)) x →
      ContMDiffAt I (I.prod 𝓘(ℝ, B.Model)) ∞ (fun y => TotalSpace.mk' B.Model y (L y (v y))) x) :
    ContMDiffAt I (I.prod 𝓘(ℝ, A.Model →L[ℝ] B.Model)) ∞ (fun y => TotalSpace.mk' (A.Model →L[ℝ] B.Model) y (L y)) x := by
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  apply contMDiffAt_clm_iff.mpr
  intro v
  let e := trivializationAt A.Model A.Fiber x
  have he : x ∈ e.baseSet := mem_baseSet_trivializationAt A.Model A.Fiber x
  have hv : ContMDiffAt I (I.prod 𝓘(ℝ, A.Model)) ∞
      (fun y => TotalSpace.mk' A.Model y (e.symmL ℝ y v)) x :=
    (e.contMDiffAt_symmL he).clm_bundle_apply
      (contMDiffAt_totalSpace.mpr ⟨contMDiffAt_id, contMDiffAt_const⟩)
  have hL := h (fun y => e.symmL ℝ y v) hv
  rw [contMDiffAt_section] at hL
  apply hL.congr_of_eventuallyEq
  filter_upwards [(trivializationAt B.Model B.Fiber x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt B.Model B.Fiber x)] with y hy
  simp [inCoordinates, e, Trivialization.coe_linearMapAt_of_mem _ hy]

end SmoothBundle
end ProjectAInos.SmoothGeometry.Tensor
