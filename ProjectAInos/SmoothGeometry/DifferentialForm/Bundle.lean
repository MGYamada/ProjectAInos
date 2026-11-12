/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-! # Smooth alternating bundles and native differential forms

The topology is mathlib's continuous-alternating-map bundle topology.
Smoothness of its transition maps is proved from the two original bundles.
No norm or global frame is installed on any actual tangent fibre.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

open Bundle Set Pretrivialization
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

section AlternatingBundle

variable {ι B F₁ F₂ : Type*} [Fintype ι] {n : ℕ∞ω}
  {E₁ : B → Type*} {E₂ : B → Type*}
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module ℝ (E₁ x)]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [TopologicalSpace (TotalSpace F₁ E₁)] [∀ x, TopologicalSpace (E₁ x)]
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module ℝ (E₂ x)]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [TopologicalSpace (TotalSpace F₂ E₂)] [∀ x, TopologicalSpace (E₂ x)]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [FiberBundle F₁ E₁] [VectorBundle ℝ F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle ℝ F₂ E₂]
  [ContMDiffVectorBundle n F₁ E₁ IB] [ContMDiffVectorBundle n F₂ E₂ IB]

/-- Smooth transition maps for the existing bundle of alternating maps. -/
theorem contMDiffOn_alternatingCoordChange
    (e₁ e₁' : Trivialization F₁ (π F₁ E₁))
    (e₂ e₂' : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁']
    [MemTrivializationAtlas e₂] [MemTrivializationAtlas e₂'] :
    ContMDiffOn IB 𝓘(ℝ, (F₁ [⋀^ι]→L[ℝ] F₂) →L[ℝ] (F₁ [⋀^ι]→L[ℝ] F₂)) n
      (continuousAlternatingMapCoordChange ℝ ι e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) := by
  have h₁ := contMDiffOn_coordChangeL (IB := IB) e₁' e₁ (n := n)
  have h₂ := contMDiffOn_coordChangeL (IB := IB) e₂ e₂' (n := n)
  refine (h₁.mono ?_).continuousAlternatingMapCongr (h₂.mono ?_) <;> mfld_set_tac

variable [∀ x, IsTopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul ℝ (E₂ x)]

instance alternatingPrebundle_isContMDiff :
    (Bundle.ContinuousAlternatingMap.vectorPrebundle ℝ ι F₁ E₁ F₂ E₂).IsContMDiff IB n where
  exists_contMDiffCoordChange := by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    exact ⟨continuousAlternatingMapCoordChange ℝ ι e₁ e₁' e₂ e₂',
      contMDiffOn_alternatingCoordChange e₁ e₁' e₂ e₂',
      continuousAlternatingMapCoordChange_apply⟩

instance alternatingBundle_contMDiff :
    ContMDiffVectorBundle n (F₁ [⋀^ι]→L[ℝ] F₂) (fun x => E₁ x [⋀^ι]→L[ℝ] E₂ x) IB :=
  (Bundle.ContinuousAlternatingMap.vectorPrebundle ℝ ι F₁ E₁ F₂ E₂).contMDiffVectorBundle IB

end AlternatingBundle

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- An unbundled form assigns a continuous alternating map to each actual tangent fibre. -/
abbrev NativeForm (k : ℕ) := ∀ x : M, TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ

/-- Smooth native forms use the smooth structure of the alternating tangent bundle. -/
abbrev SmoothForm [IsManifold I ∞ M] (k : ℕ) :=
  Cₛ^∞⟮I; E [⋀^Fin k]→L[ℝ] ℝ, (fun x : M => TangentSpace I x [⋀^Fin k]→L[ℝ] ℝ)⟯

variable {M} [IsManifold I ∞ M]

/-- Form coefficients in a tangent trivialization, extracted from the native field. -/
def trivializationCoefficients {k : ℕ} (α : NativeForm I M k) (x₀ x : M) :
    E [⋀^Fin k]→L[ℝ] ℝ :=
  (α x).compContinuousLinearMap ((trivializationAt E (TangentSpace I) x₀).symmL ℝ x)

/-- Native section regularity is regularity of its actual tangent-trivialization coefficients. -/
theorem contMDiffAt_form_iff {k : ℕ} {r : ℕ∞ω} {α : NativeForm I M k} {x : M} :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ)) r
      (fun y => TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] ℝ) y (α y)) x ↔
        ContMDiffAt I 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ) r (trivializationCoefficients I α x) x := by
  rw [contMDiffAt_section]
  apply Iff.of_eq
  apply congrArg (fun f : M → E [⋀^Fin k]→L[ℝ] ℝ =>
    ContMDiffAt I 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ) r f x)
  funext y
  ext v
  simp [FiberBundle.trivializationAt_continuousAlternatingMap_apply,
    ContinuousAlternatingMap.inCoordinates, trivializationCoefficients]

theorem SmoothForm.coefficients_contMDiffAt {k : ℕ}
    (α : SmoothForm I M k) (x : M) :
    ContMDiffAt I 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] ℝ) ∞
      (trivializationCoefficients I (fun y => α y) x) x :=
  (contMDiffAt_form_iff I).mp (α.contMDiff x)

end ProjectAInos.SmoothGeometry.DifferentialForm
