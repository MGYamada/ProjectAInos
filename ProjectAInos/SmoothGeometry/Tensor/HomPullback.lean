/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.HomMap

/-! # Smooth composition maps between native hom bundles

The source and target manifolds may have different dimensions. Neither
of the fibre maps needs to be invertible; continuity on actual fibres
uses fixed-map precomposition and postcomposition. Smoothness is proved
in the normed local models, without norms on tangent fibres.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace ProjectAInos.SmoothGeometry.Tensor.SmoothBundle

variable {E H M F H' N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H'] (J : ModelWithCorners ℝ F H')
  [TopologicalSpace N] [ChartedSpace H' N]

theorem inCoordinates_homPullback (A₁ A₂ : SmoothBundle I (M := M))
    (B₁ B₂ : SmoothBundle J (M := N)) (x₀ x : M) (y₀ y : N)
    (hA₁ : x ∈ (trivializationAt A₁.Model A₁.Fiber x₀).baseSet)
    (hA₂ : x ∈ (trivializationAt A₂.Model A₂.Fiber x₀).baseSet)
    (hB₁ : y ∈ (trivializationAt B₁.Model B₁.Fiber y₀).baseSet)
    (hB₂ : y ∈ (trivializationAt B₂.Model B₂.Fiber y₀).baseSet)
    (e₁ : B₁.Fiber y →L[ℝ] A₁.Fiber x) (e₂ : A₂.Fiber x →L[ℝ] B₂.Fiber y) :
    inCoordinates (A₁.Model →L[ℝ] A₂.Model) (fun z => A₁.Fiber z →L[ℝ] A₂.Fiber z)
      (B₁.Model →L[ℝ] B₂.Model) (fun z => B₁.Fiber z →L[ℝ] B₂.Fiber z)
      x₀ x y₀ y ((postcomp (B₁.Fiber y) e₂).comp (precomp (A₂.Fiber x) e₁)) =
    (compL ℝ B₁.Model A₂.Model B₂.Model
      (inCoordinates A₂.Model A₂.Fiber B₂.Model B₂.Fiber x₀ x y₀ y
        e₂)).comp
      ((compL ℝ B₁.Model A₁.Model A₂.Model).flip
        (inCoordinates B₁.Model B₁.Fiber A₁.Model A₁.Fiber y₀ y x₀ x
          e₁)) := by
  rw [inCoordinates_eq (by simpa using And.intro hA₁ hA₂)
    (by simpa using And.intro hB₁ hB₂), inCoordinates_eq hA₂ hB₂,
    inCoordinates_eq hB₁ hA₁]
  ext L v
  have hsymm :
      ((trivializationAt A₁.Model A₁.Fiber x₀).continuousLinearMap (RingHom.id ℝ)
        (trivializationAt A₂.Model A₂.Fiber x₀)).symm x L =
      ((trivializationAt A₂.Model A₂.Fiber x₀).symmL ℝ x).comp
        (L.comp ((trivializationAt A₁.Model A₁.Fiber x₀).continuousLinearMapAt ℝ x)) :=
    Pretrivialization.continuousLinearMap_symm_apply' (RingHom.id ℝ)
      (trivializationAt A₁.Model A₁.Fiber x₀) (trivializationAt A₂.Model A₂.Fiber x₀)
      ⟨hA₁, hA₂⟩ L
  simp [hom_trivializationAt, Trivialization.continuousLinearMap_apply, hsymm,
    hA₁, hA₂, hB₁, hB₂, precomp_apply, postcomp_apply]

variable {G H'' P : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H''] (K : ModelWithCorners ℝ G H'')
  [TopologicalSpace P] [ChartedSpace H'' P]

/-- Smooth linear input and output maps induce smooth maps of hom tensors.
The two bundle base points may vary independently over a third manifold. -/
theorem contMDiffAt_homPullback (A₁ A₂ : SmoothBundle I (M := M))
    (B₁ B₂ : SmoothBundle J (M := N)) {a : P → M} {b : P → N} {p : P}
    (ha : ContMDiffAt K I ∞ a p) (hb : ContMDiffAt K J ∞ b p)
    (e₁ : ∀ q, B₁.Fiber (b q) →L[ℝ] A₁.Fiber (a q))
    (e₂ : ∀ q, A₂.Fiber (a q) →L[ℝ] B₂.Fiber (b q))
    (h₁ : ContMDiffAt K 𝓘(ℝ, B₁.Model →L[ℝ] A₁.Model) ∞
      (fun q => inCoordinates B₁.Model B₁.Fiber A₁.Model A₁.Fiber
        (b p) (b q) (a p) (a q) (e₁ q)) p)
    (h₂ : ContMDiffAt K 𝓘(ℝ, A₂.Model →L[ℝ] B₂.Model) ∞
      (fun q => inCoordinates A₂.Model A₂.Fiber B₂.Model B₂.Fiber
        (a p) (a q) (b p) (b q) (e₂ q)) p) :
    ContMDiffAt K 𝓘(ℝ, (A₁.Model →L[ℝ] A₂.Model) →L[ℝ]
      (B₁.Model →L[ℝ] B₂.Model)) ∞
      (fun q => inCoordinates (A₁.Model →L[ℝ] A₂.Model)
        (fun x => A₁.Fiber x →L[ℝ] A₂.Fiber x)
        (B₁.Model →L[ℝ] B₂.Model) (fun y => B₁.Fiber y →L[ℝ] B₂.Fiber y)
        (a p) (a q) (b p) (b q)
        ((postcomp (B₁.Fiber (b q)) (e₂ q)).comp
          (precomp (A₂.Fiber (a q)) (e₁ q)))) p := by
  have hout := h₂.clm_postcomp (F₁ := B₁.Model)
  have hin := h₁.clm_precomp (F₃ := A₂.Model)
  apply (hout.clm_comp hin).congr_of_eventuallyEq
  have hA₁ : ∀ᶠ q in 𝓝 p, a q ∈ (trivializationAt A₁.Model A₁.Fiber (a p)).baseSet :=
    ha.continuousAt ((trivializationAt _ _ _).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' _))
  have hA₂ : ∀ᶠ q in 𝓝 p, a q ∈ (trivializationAt A₂.Model A₂.Fiber (a p)).baseSet :=
    ha.continuousAt ((trivializationAt _ _ _).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' _))
  have hB₁ : ∀ᶠ q in 𝓝 p, b q ∈ (trivializationAt B₁.Model B₁.Fiber (b p)).baseSet :=
    hb.continuousAt ((trivializationAt _ _ _).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' _))
  have hB₂ : ∀ᶠ q in 𝓝 p, b q ∈ (trivializationAt B₂.Model B₂.Fiber (b p)).baseSet :=
    hb.continuousAt ((trivializationAt _ _ _).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' _))
  filter_upwards [hA₁, hA₂, hB₁, hB₂] with q hA₁ hA₂ hB₁ hB₂
  exact inCoordinates_homPullback I J A₁ A₂ B₁ B₂ (a p) (a q) (b p) (b q)
    hA₁ hA₂ hB₁ hB₂ (e₁ q) (e₂ q)

end ProjectAInos.SmoothGeometry.Tensor.SmoothBundle
