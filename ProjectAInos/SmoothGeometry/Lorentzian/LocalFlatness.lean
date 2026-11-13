/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Lorentzian.CurvatureNaturality
public import ProjectAInos.SmoothGeometry.Lorentzian.CurvatureExamples
public import ProjectAInos.SmoothGeometry.Lorentzian.Restriction
public import ProjectAInos.SmoothGeometry.Manifold.OpenTangent

/-! # Local Minkowski geometry and vanishing curvature

The local coordinate definition of `IsLocallyMinkowski` implies zero native
curvature. Its converse requires a flat parallel frame and local integration;
it is not inferred from pointwise inertial normalization.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open TopologicalSpace ContinuousLinearMap
open scoped Manifold ContDiff

namespace ProjectAInos.SmoothGeometry.LorentzMetric

variable {σ : LorentzConvention} {d : ℕ} {M : Type}
  [TopologicalSpace M] [ChartedSpace (MinkowskiModel d) M]
  [IsManifold 𝓘(ℝ, MinkowskiModel d) ∞ M]

local notation "E" => MinkowskiModel d
local notation "I" => 𝓘(ℝ, MinkowskiModel d)

/-- Restriction of the native curvature intertwines the actual tangent map
of the open inclusion. -/
theorem curvature_restrict (g : LorentzMetric σ d M) (U : Opens M) (x : U)
    (u v w : TangentSpace I x) :
    mfderiv I I (Subtype.val : U → M) x ((g.restrict U).curvature x u v w) =
      g.curvature x.val (mfderiv I I (Subtype.val : U → M) x u)
        (mfderiv I I (Subtype.val : U → M) x v)
        (mfderiv I I (Subtype.val : U → M) x w) :=
  g.curvature_pullback contMDiff_subtype_val
    (Manifold.isInvertible_mfderiv_subtype_val I U) x u v w

/-- In the inherited charts, the same restriction law is the equality of
underlying tangent-coordinate values. -/
theorem curvature_restrict_apply (g : LorentzMetric σ d M) (U : Opens M) (x : U)
    (u v w : TangentSpace I x) :
    (g.restrict U).curvature x u v w = g.curvature x.val u v w := by
  simpa only [Manifold.mfderiv_subtype_val_apply] using g.curvature_restrict U x u v w

/-- Every open submanifold of Minkowski space has zero native curvature. -/
theorem minkowski_restrict_curvature (σ : LorentzConvention) (d : ℕ)
    (V : Opens (MinkowskiModel d)) (x : V) :
    ((minkowskiMetric σ d).restrict V).curvature x = 0 := by
  ext u v w
  rw [curvature_restrict_apply, minkowski_curvature]
  rfl

/-- Local Minkowski coordinate diffeomorphisms force the intrinsic curvature
tensor to vanish at every point. -/
theorem IsLocallyMinkowski.curvature_eq_zero {g : LorentzMetric σ d M}
    (h : g.IsLocallyMinkowski) (p : M) : g.curvature p = 0 := by
  obtain ⟨U, hp, V, e, he⟩ := h p
  let x : U := ⟨p, hp⟩
  let η := (minkowskiMetric σ d).restrict V
  have hm (y : U) (u v : TangentSpace I y) :
      (g.restrict U).form y u v = η.form (e y) (mfderiv I I e y u) (mfderiv I I e y v) := by
    simp only [η, restrict_form, Manifold.mfderiv_subtype_val_apply]
    exact he y u v
  have h0 : (g.restrict U).curvature x = 0 := by
    ext u v w
    change (g.restrict U).curvature x u v w = 0
    apply (e.isInvertible_mfderiv (x := x) (by simp)).injective
    rw [(g.restrict U).curvature_naturality_of_metric η e.contMDiff hm]
    simp only [η, minkowski_restrict_curvature, zero_apply, map_zero]
  ext u v w
  have hx := g.curvature_restrict_apply U x u v w
  rw [h0] at hx
  exact hx.symm

/-- Smooth maximal-atlas charts that normalize the metric on their entire
sources supply the existing open-submanifold definition of local Minkowski
geometry. Normalization only at the center would not suffice. -/
theorem isLocallyMinkowski_of_charts (g : LorentzMetric σ d M)
    (h : ∀ p : M, ∃ e : OpenPartialHomeomorph M E,
      e ∈ IsManifold.maximalAtlas I ∞ M ∧ p ∈ e.source ∧
      ∀ x ∈ e.source, ∀ v w : TangentSpace I x,
        g.form x v w = minkowskiForm σ d (chartTangentMap e x v) (chartTangentMap e x w)) :
    g.IsLocallyMinkowski := by
  intro p
  obtain ⟨e, he, hp, hm⟩ := h p
  refine ⟨⟨e.source, e.open_source⟩, hp, ⟨e.target, e.open_target⟩,
    Manifold.diffeomorphOfMaximalAtlas he, ?_⟩
  intro x v w
  rw [Manifold.mfderiv_diffeomorphOfMaximalAtlas_apply,
    Manifold.mfderiv_diffeomorphOfMaximalAtlas_apply]
  exact hm x.val x.property v w

end ProjectAInos.SmoothGeometry.LorentzMetric
