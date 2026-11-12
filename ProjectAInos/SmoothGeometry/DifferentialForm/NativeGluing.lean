/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Bundle

/-! # Gluing native differential forms over open covers

Local representatives only need to be smooth on their own open sets. Their
values outside those sets are irrelevant to the resulting global section.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {E H M ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M]
  {k : ℕ}

/-- The pointwise glued native field. Agreement on overlaps makes the choice immaterial. -/
def nativeGlue (U : ι → Set M) (hU : ∀ x, ∃ i, x ∈ U i)
    (α : ι → NativeForm I M k) : NativeForm I M k :=
  fun x => α (hU x).choose x

/-- Gluing restricts to each local representative on its own set. -/
theorem nativeGlue_eq (U : ι → Set M) (hU : ∀ x, ∃ i, x ∈ U i)
    (α : ι → NativeForm I M k)
    (hα : ∀ i j x, x ∈ U i ∩ U j → α i x = α j x)
    {i : ι} {x : M} (hx : x ∈ U i) : nativeGlue I U hU α x = α i x :=
  hα _ _ x ⟨(hU x).choose_spec, hx⟩

variable [IsManifold I ∞ M]

/-- Smooth compatible native forms on an arbitrary open cover glue to a smooth form. -/
def smoothGlue (U : ι → Set M) (hopen : ∀ i, IsOpen (U i)) (hU : ∀ x, ∃ i, x ∈ U i)
    (α : ι → NativeForm I M k)
    (hsmooth : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) x (α i x)) (U i))
    (hα : ∀ i j x, x ∈ U i ∩ U j → α i x = α j x) : SmoothForm I M k :=
  ⟨nativeGlue I U hU α, by
    intro x
    obtain ⟨i, hi⟩ := hU x
    apply ((hsmooth i x hi).contMDiffAt ((hopen i).mem_nhds hi)).congr_of_eventuallyEq
    filter_upwards [(hopen i).mem_nhds hi] with y hy
    exact congrArg (TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y)
      (nativeGlue_eq I U hU α hα hy)⟩

/-- The bundled gluing has the specified local values. -/
theorem smoothGlue_apply (U : ι → Set M) (hopen : ∀ i, IsOpen (U i))
    (hU : ∀ x, ∃ i, x ∈ U i) (α : ι → NativeForm I M k)
    (hsmooth : ∀ i, ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) x (α i x)) (U i))
    (hα : ∀ i j x, x ∈ U i ∩ U j → α i x = α j x) {i : ι} {x : M} (hx : x ∈ U i) :
    smoothGlue I U hopen hU α hsmooth hα x = α i x := nativeGlue_eq I U hU α hα hx

/-- Local equality on a cover determines a smooth native form uniquely. -/
theorem smoothForm_ext_of_cover (U : ι → Set M) (hU : ∀ x, ∃ i, x ∈ U i)
    {α β : SmoothForm I M k} (h : ∀ i x, x ∈ U i → α x = β x) : α = β := by
  ext x : 1
  obtain ⟨i, hi⟩ := hU x
  exact h i x hi

end ProjectAInos.SmoothGeometry.DifferentialForm
