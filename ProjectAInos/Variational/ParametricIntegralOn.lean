/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.Variational.LocalExtension
public import ProjectAInos.SmoothAlgebra.ParametricIntegral

/-!
# Parametric integrals of functions that are smooth on an open set

`contDiffAt_parametric_intervalIntegral`: if `f` is smooth on an open set that
contains the segment `{x₀} × [a, b]`, then `x ↦ ∫ t in a..b, f (x, t)` is
smooth at `x₀`. The function is replaced near the segment by a function that is
smooth everywhere.
-/

@[expose] public section
noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace ProjectAInos.Variational

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A parametric integral of a function that is smooth on an open set containing
the segment of integration over a point is smooth at that point. -/
theorem contDiffAt_parametric_intervalIntegral {f : E × ℝ → ℝ} {U : Set (E × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {a b : ℝ} {x₀ : E}
    (h : ∀ t ∈ uIcc a b, (x₀, t) ∈ U) :
    ContDiffAt ℝ ∞ (fun x => ∫ t in a..b, f (x, t)) x₀ := by
  have hK : IsCompact (({x₀} : Set E) ×ˢ uIcc a b) := isCompact_singleton.prod isCompact_uIcc
  have hKU : ({x₀} : Set E) ×ˢ uIcc a b ⊆ U := by
    rintro ⟨x, t⟩ ⟨hx, ht⟩
    rw [mem_singleton_iff] at hx
    subst hx
    exact h t ht
  obtain ⟨g, hg, V, hV, hKV, heq⟩ := exists_contDiff_extension_near_compact hK hU hKU hf
  have hsmooth : ContDiff ℝ ∞ fun x => ∫ t in a..b, g (x, t) :=
    SmoothAlgebra.contDiff_infty_parametric_intervalIntegral hg a b
  obtain ⟨N, W, hN, _, hxN, hKW, hNW⟩ := generalized_tube_lemma
    (isCompact_singleton (x := x₀)) (isCompact_uIcc (a := a) (b := b)) hV hKV
  refine hsmooth.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [hN.mem_nhds (hxN rfl)] with x hx
  exact intervalIntegral.integral_congr fun t ht => (heq (hNW ⟨hx, hKW ht⟩)).symm

/-- The same on a set of parameters. -/
theorem contDiffOn_parametric_intervalIntegral {f : E × ℝ → ℝ} {U : Set (E × ℝ)}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) {a b : ℝ} {S : Set E}
    (h : ∀ x ∈ S, ∀ t ∈ uIcc a b, (x, t) ∈ U) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in a..b, f (x, t)) S :=
  fun x hx => (contDiffAt_parametric_intervalIntegral hU hf (h x hx)).contDiffWithinAt

end ProjectAInos.Variational
