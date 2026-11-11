/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.Tensor.Bundle
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! # Coordinate maps on tensor hom bundles

Transporting a hom tensor conjugates its input and output maps. The
coordinate identity below is the local ingredient for smooth field pullback.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace ProjectAInos.SmoothGeometry.Tensor.SmoothBundle

variable {E H M N : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace N] [ChartedSpace H N]

theorem inCoordinates_homMap (A₁ A₂ : SmoothBundle I (M := M))
    (B₁ B₂ : SmoothBundle I (M := N)) (x₀ x : M) (y₀ y : N)
    (hA₁ : x ∈ (trivializationAt A₁.Model A₁.Fiber x₀).baseSet)
    (hA₂ : x ∈ (trivializationAt A₂.Model A₂.Fiber x₀).baseSet)
    (hB₁ : y ∈ (trivializationAt B₁.Model B₁.Fiber y₀).baseSet)
    (hB₂ : y ∈ (trivializationAt B₂.Model B₂.Fiber y₀).baseSet)
    (e₁ : A₁.Fiber x ≃L[ℝ] B₁.Fiber y) (e₂ : A₂.Fiber x ≃L[ℝ] B₂.Fiber y) :
    inCoordinates (A₁.Model →L[ℝ] A₂.Model) (fun z => A₁.Fiber z →L[ℝ] A₂.Fiber z)
      (B₁.Model →L[ℝ] B₂.Model) (fun z => B₁.Fiber z →L[ℝ] B₂.Fiber z)
      x₀ x y₀ y (e₁.arrowCongr e₂).toContinuousLinearMap =
    (compL ℝ B₁.Model A₂.Model B₂.Model
      (inCoordinates A₂.Model A₂.Fiber B₂.Model B₂.Fiber x₀ x y₀ y
        e₂.toContinuousLinearMap)).comp
      ((compL ℝ B₁.Model A₁.Model A₂.Model).flip
        (inCoordinates B₁.Model B₁.Fiber A₁.Model A₁.Fiber y₀ y x₀ x
          e₁.symm.toContinuousLinearMap)) := by
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
    hA₁, hA₂, hB₁, hB₂]

variable {P : Type} [TopologicalSpace P] [ChartedSpace H P]

/-- Inverting a smooth family of fibre isomorphisms is smooth in local coordinates. -/
theorem contMDiffAt_inverse (A : SmoothBundle I (M := M)) (B : SmoothBundle I (M := N))
    {a : P → M} {b : P → N} {p : P}
    (ha : ContMDiffAt I I ∞ a p) (hb : ContMDiffAt I I ∞ b p)
    (e : ∀ q, A.Fiber (a q) ≃L[ℝ] B.Fiber (b q))
    (he : ContMDiffAt I 𝓘(ℝ, A.Model →L[ℝ] B.Model) ∞
      (fun q => inCoordinates A.Model A.Fiber B.Model B.Fiber
        (a p) (a q) (b p) (b q) (e q).toContinuousLinearMap) p) :
    ContMDiffAt I 𝓘(ℝ, B.Model →L[ℝ] A.Model) ∞
      (fun q => inCoordinates B.Model B.Fiber A.Model A.Fiber
        (b p) (b q) (a p) (a q) (e q).symm.toContinuousLinearMap) p := by
  have hi : ContMDiffAt I 𝓘(ℝ, B.Model →L[ℝ] A.Model) ∞
      (fun q => (inCoordinates A.Model A.Fiber B.Model B.Fiber
        (a p) (a q) (b p) (b q) (e q).toContinuousLinearMap).inverse) p := by
    apply ContMDiffAt.comp (g := ContinuousLinearMap.inverse) p _ he
    apply ContDiffAt.contMDiffAt
    apply IsInvertible.contDiffAt_map_inverse
    rw [inCoordinates_eq (FiberBundle.mem_baseSet_trivializationAt' (a p))
      (FiberBundle.mem_baseSet_trivializationAt' (b p))]
    exact isInvertible_equiv.comp (isInvertible_equiv.comp isInvertible_equiv)
  apply hi.congr_of_eventuallyEq
  have hA : ∀ᶠ q in 𝓝 p, a q ∈ (trivializationAt A.Model A.Fiber (a p)).baseSet :=
    ha.continuousAt ((trivializationAt _ _ _).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' _))
  have hB : ∀ᶠ q in 𝓝 p, b q ∈ (trivializationAt B.Model B.Fiber (b p)).baseSet :=
    hb.continuousAt ((trivializationAt _ _ _).open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' _))
  filter_upwards [hA, hB] with q hA hB
  rw [inCoordinates_eq hB hA, inCoordinates_eq hA hB]
  simp only [inverse_equiv_comp, inverse_comp_equiv, ContinuousLinearEquiv.symm_symm,
    inverse_equiv, ContinuousLinearMap.comp_assoc]

/-- Smooth input and output transport induce smooth transport of hom tensors.
The two bundle base points may vary independently over a third manifold. -/
theorem contMDiffAt_homMap (A₁ A₂ : SmoothBundle I (M := M))
    (B₁ B₂ : SmoothBundle I (M := N)) {a : P → M} {b : P → N} {p : P}
    (ha : ContMDiffAt I I ∞ a p) (hb : ContMDiffAt I I ∞ b p)
    (e₁ : ∀ q, A₁.Fiber (a q) ≃L[ℝ] B₁.Fiber (b q))
    (e₂ : ∀ q, A₂.Fiber (a q) ≃L[ℝ] B₂.Fiber (b q))
    (h₁ : ContMDiffAt I 𝓘(ℝ, B₁.Model →L[ℝ] A₁.Model) ∞
      (fun q => inCoordinates B₁.Model B₁.Fiber A₁.Model A₁.Fiber
        (b p) (b q) (a p) (a q) (e₁ q).symm.toContinuousLinearMap) p)
    (h₂ : ContMDiffAt I 𝓘(ℝ, A₂.Model →L[ℝ] B₂.Model) ∞
      (fun q => inCoordinates A₂.Model A₂.Fiber B₂.Model B₂.Fiber
        (a p) (a q) (b p) (b q) (e₂ q).toContinuousLinearMap) p) :
    ContMDiffAt I 𝓘(ℝ, (A₁.Model →L[ℝ] A₂.Model) →L[ℝ]
      (B₁.Model →L[ℝ] B₂.Model)) ∞
      (fun q => inCoordinates (A₁.Model →L[ℝ] A₂.Model)
        (fun x => A₁.Fiber x →L[ℝ] A₂.Fiber x)
        (B₁.Model →L[ℝ] B₂.Model) (fun y => B₁.Fiber y →L[ℝ] B₂.Fiber y)
        (a p) (a q) (b p) (b q) ((e₁ q).arrowCongr (e₂ q)).toContinuousLinearMap) p := by
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
  exact inCoordinates_homMap I A₁ A₂ B₁ B₂ (a p) (a q) (b p) (b q)
    hA₁ hA₂ hB₁ hB₂ (e₁ q) (e₂ q)

end ProjectAInos.SmoothGeometry.Tensor.SmoothBundle
