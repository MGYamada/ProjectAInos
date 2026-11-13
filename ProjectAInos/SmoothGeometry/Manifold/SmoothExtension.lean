/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Localizing vector-valued coordinate functions

A smooth cutoff gives a globally regular representative of a locally regular
coordinate function near a compact subset. The target may be an operator
space; no positivity or metric structure is needed.
-/

@[expose] public section
noncomputable section

open Set Filter
open scoped Topology ContDiff Manifold

namespace ProjectAInos.SmoothGeometry.Manifold

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Extend a vector-valued `C^n` coordinate function while preserving its germ
near any compact subset of an open domain. This includes smooth functions. -/
theorem exists_contDiff_extension_near_compact {n : ℕ∞} {f : E → F} {K U : Set E}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) (hf : ContDiffOn ℝ n f U) :
    ∃ g : E → F, ContDiff ℝ n g ∧
      ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ EqOn g f V := by
  obtain ⟨φ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) (n := n) hU.isClosed_compl hK.isClosed
    (Set.disjoint_left.mpr fun _ hx hk => hx (hKU hk))
  have hφ : ContDiff ℝ n (φ : E → ℝ) := contMDiff_iff_contDiff.mp φ.contMDiff
  let g : E → F := fun x => φ x • f x
  have hg : ContDiff ℝ n g := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ U
    · exact hφ.contDiffAt.smul ((hf x hx).contDiffAt (hU.mem_nhds hx))
    · have h0 : ∀ᶠ y in 𝓝 x, φ y = 0 := hzero.filter_mono (nhds_le_nhdsSet hx)
      have he : g =ᶠ[𝓝 x] fun _ => 0 := h0.mono fun y hy => by simp [g, hy]
      exact contDiffAt_const.congr_of_eventuallyEq he
  obtain ⟨V, hV, hKV, hφV⟩ := mem_nhdsSet_iff_exists.mp hone
  refine ⟨g, hg, V ∩ U, hV.inter hU, fun x hx => ⟨hKV hx, hKU hx⟩,
    inter_subset_right, ?_⟩
  intro x hx
  change φ x • f x = f x
  rw [hφV hx.1, one_smul]

end ProjectAInos.SmoothGeometry.Manifold
