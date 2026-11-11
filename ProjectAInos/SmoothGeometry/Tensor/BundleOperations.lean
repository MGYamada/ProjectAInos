/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-! # Composition of smooth bundle homomorphisms

The intermediate fibre coordinates cancel under composition. This local
identity proves smoothness without choosing any global trivialization.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle ContinuousLinearMap
open scoped Manifold Topology ContDiff

namespace ProjectAInos.SmoothGeometry.Tensor

variable {M E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]
  {V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)]
  [∀ x, TopologicalSpace (V₁ x)] [TopologicalSpace (TotalSpace F₁ V₁)]
  [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)]
  [∀ x, TopologicalSpace (V₂ x)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)]
  [∀ x, TopologicalSpace (V₃ x)] [TopologicalSpace (TotalSpace F₃ V₃)]
  [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]

theorem inCoordinates_comp (x₀ x : M)
    (h₁ : x ∈ (trivializationAt F₁ V₁ x₀).baseSet)
    (h₂ : x ∈ (trivializationAt F₂ V₂ x₀).baseSet)
    (h₃ : x ∈ (trivializationAt F₃ V₃ x₀).baseSet)
    (A : V₂ x →L[ℝ] V₃ x) (B : V₁ x →L[ℝ] V₂ x) :
    inCoordinates F₁ V₁ F₃ V₃ x₀ x x₀ x (A.comp B) =
      (inCoordinates F₂ V₂ F₃ V₃ x₀ x x₀ x A).comp
        (inCoordinates F₁ V₁ F₂ V₂ x₀ x x₀ x B) := by
  rw [inCoordinates_eq h₁ h₃, inCoordinates_eq h₂ h₃, inCoordinates_eq h₁ h₂]
  ext v
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

variable [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul ℝ (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]

/-- Fibrewise composition preserves smoothness of sections of hom bundles. -/
theorem contMDiff_comp {n : WithTop ℕ∞}
    {A : ∀ x, V₂ x →L[ℝ] V₃ x} {B : ∀ x, V₁ x →L[ℝ] V₂ x}
    (hA : ContMDiff I (I.prod 𝓘(ℝ, F₂ →L[ℝ] F₃)) n
      (fun x => TotalSpace.mk' (F₂ →L[ℝ] F₃) x (A x)))
    (hB : ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₂)) n
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₂) x (B x))) :
    ContMDiff I (I.prod 𝓘(ℝ, F₁ →L[ℝ] F₃)) n
      (fun x => TotalSpace.mk' (F₁ →L[ℝ] F₃) x ((A x).comp (B x))) := by
  intro x₀
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  have hAc := ((contMDiffAt_hom_bundle _).mp (hA x₀)).2
  have hBc := ((contMDiffAt_hom_bundle _).mp (hB x₀)).2
  apply (hAc.clm_comp hBc).congr_of_eventuallyEq
  have h₁ : (trivializationAt F₁ V₁ x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
  have h₂ : (trivializationAt F₂ V₂ x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
  have h₃ : (trivializationAt F₃ V₃ x₀).baseSet ∈ 𝓝 x₀ :=
    (trivializationAt _ _ _).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)
  filter_upwards [h₁, h₂, h₃] with x hx₁ hx₂ hx₃
  exact inCoordinates_comp x₀ x hx₁ hx₂ hx₃ (A x) (B x)

/-- Composition as an operation on smooth sections, independent of a metric. -/
def comp (A : Cₛ^∞⟮I; F₂ →L[ℝ] F₃, (fun x => V₂ x →L[ℝ] V₃ x)⟯)
    (B : Cₛ^∞⟮I; F₁ →L[ℝ] F₂, (fun x => V₁ x →L[ℝ] V₂ x)⟯) :
    Cₛ^∞⟮I; F₁ →L[ℝ] F₃, (fun x => V₁ x →L[ℝ] V₃ x)⟯ :=
  ⟨fun x => (A x).comp (B x), contMDiff_comp A.contMDiff B.contMDiff⟩

@[simp] theorem comp_apply
    (A : Cₛ^∞⟮I; F₂ →L[ℝ] F₃, (fun x => V₂ x →L[ℝ] V₃ x)⟯)
    (B : Cₛ^∞⟮I; F₁ →L[ℝ] F₂, (fun x => V₁ x →L[ℝ] V₂ x)⟯)
    (x : M) (v : V₁ x) : comp A B x v = A x (B x v) := rfl

end ProjectAInos.SmoothGeometry.Tensor
