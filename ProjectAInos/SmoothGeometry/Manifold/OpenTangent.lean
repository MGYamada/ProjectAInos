/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Manifold.OpenSubset
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Analysis.Convex.Basic

/-! # The tangent map of an open inclusion in model coordinates -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open TopologicalSpace Set Filter ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.Manifold

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The inherited charts of an open submanifold make its inclusion derivative
the identity on the underlying model coordinates. The native tangent fibres
are still kept in the statement. -/
theorem mfderiv_subtype_val_apply (U : Opens M) (x : U)
    (v : TangentSpace 𝓘(ℝ, E) x) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x v = v := by
  let e := chartAt E x.val
  have hcomp : (fun y => e (Subtype.val ((chartAt E x).symm y))) =ᶠ[𝓝 (e x.val)] id := by
    filter_upwards [U.chartAt_subtype_val_symm_eventuallyEq,
      e.open_target.mem_nhds (e.map_source (mem_chart_source E x.val))] with y hy hye
    change e (Subtype.val ((chartAt E x).symm y)) = y
    change e.symm y = Subtype.val ((chartAt E x).symm y) at hy
    rw [← hy, e.right_inv hye]
  rw [((contMDiff_subtype_val (n := ∞)).mdifferentiableAt (by simp)).mfderiv]
  change fderivWithin ℝ (fun y => e (Subtype.val ((chartAt E x).symm y)))
    (Set.range (id : E → E)) (e x.val) v = v
  rw [Set.range_id, fderivWithin_univ, hcomp.fderiv_eq]
  simp only [fderiv_id]
  rfl

/-- Any smooth maximal-atlas chart restricts to a diffeomorphism of its open
source and target. This also applies to newly constructed local charts. -/
def diffeomorphOfMaximalAtlas {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) :
    (⟨e.source, e.open_source⟩ : Opens M) ≃ₘ⟮𝓘(ℝ, E), 𝓘(ℝ, E)⟯
      (⟨e.target, e.open_target⟩ : Opens E) where
  toEquiv := e.toHomeomorphSourceTarget.toEquiv
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff (⟨e.target, e.open_target⟩ : Opens E) _).mp
    intro y
    exact (contMDiffAt_of_mem_maximalAtlas he y.property).comp y
      contMDiff_subtype_val.contMDiffAt
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff (⟨e.source, e.open_source⟩ : Opens M) _).mp
    intro y
    exact (contMDiffAt_symm_of_mem_maximalAtlas he y.property).comp y
      contMDiff_subtype_val.contMDiffAt

/-- The restricted chart diffeomorphism has the same underlying tangent
coordinate derivative as the original local chart. -/
theorem mfderiv_diffeomorphOfMaximalAtlas_apply {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M)
    (x : (⟨e.source, e.open_source⟩ : Opens M)) (v : TangentSpace 𝓘(ℝ, E) x) :
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (diffeomorphOfMaximalAtlas he) x v =
      mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x.val v := by
  let U : Opens M := ⟨e.source, e.open_source⟩
  let V : Opens E := ⟨e.target, e.open_target⟩
  let f := diffeomorphOfMaximalAtlas he
  have h₁ := congrArg (fun L => L v) (mfderiv_comp x
    ((contMDiff_subtype_val (U := V) (n := ∞)).mdifferentiableAt (by simp))
    (f.mdifferentiable (by simp) x))
  have h₂ := congrArg (fun L => L v) (mfderiv_comp x
    ((contMDiffAt_of_mem_maximalAtlas he x.property).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (U := U) (n := ∞)).mdifferentiableAt (by simp)))
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) ((Subtype.val : V → E) ∘ f) x v =
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : V → E) (f x)
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v) at h₁
  rw [mfderiv_subtype_val_apply] at h₁
  change mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (e ∘ (Subtype.val : U → M)) x v =
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x.val
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (Subtype.val : U → M) x v) at h₂
  rw [mfderiv_subtype_val_apply] at h₂
  exact h₁.symm.trans h₂

/-- A smooth chart can be shrunk about a point to have a convex target,
without changing either coordinate function on its new domain. -/
theorem exists_chart_convexTarget [IsManifold 𝓘(ℝ, E) ∞ M] {e : OpenPartialHomeomorph M E}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M) {p : M} (hp : p ∈ e.source) :
    ∃ c : OpenPartialHomeomorph M E, c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M ∧
      p ∈ c.source ∧ c.source ⊆ e.source ∧ (⇑c = ⇑e) ∧ (⇑c.symm = ⇑e.symm) ∧
      Convex ℝ c.target := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hp))
  let c := (e.symm.restrOpen (Metric.ball (e p) ε) Metric.isOpen_ball).symm
  have ht : c.target = Metric.ball (e p) ε := inter_eq_right.mpr hball
  have hs : c.source ⊆ e.source := fun _ hx => hx.1
  have hc : c ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ M := by
    apply c.mem_maximalAtlas_of_contMDiffOn
    · exact (contMDiffOn_of_mem_maximalAtlas he).mono hs
    · exact (contMDiffOn_symm_of_mem_maximalAtlas he).mono (fun _ hx => hx.1)
  refine ⟨c, hc, ?_, hs, rfl, rfl, ?_⟩
  · exact ⟨hp, Metric.mem_ball_self hε⟩
  · rw [ht]
    exact convex_ball (e p) ε

end ProjectAInos.SmoothGeometry.Manifold
