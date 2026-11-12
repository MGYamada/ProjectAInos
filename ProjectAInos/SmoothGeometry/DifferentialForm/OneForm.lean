/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.NativeChart
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! # Native one-forms and smooth cotangent sections

The identification respects the existing hom and alternating bundle
topologies. No norm is assigned to a native tangent fibre.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]

/-- A continuous covector is exactly an alternating one-form on a native fibre. -/
def oneFormEquiv : (V →L[ℝ] ℝ) ≃ₗ[ℝ] (V [⋀^Fin 1]→L[ℝ] ℝ) where
  __ := ContinuousAlternatingMap.ofSubsingleton ℝ V ℝ (0 : Fin 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem oneFormEquiv_apply (α : V →L[ℝ] ℝ) (v : Fin 1 → V) :
    oneFormEquiv α v = α (v 0) := rfl

@[simp] theorem oneFormEquiv_symm_apply (α : V [⋀^Fin 1]→L[ℝ] ℝ) (v : V) :
    oneFormEquiv.symm α v = α (fun _ => v) := rfl

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]

theorem oneFormEquiv_comp (L : V →L[ℝ] W) (α : W →L[ℝ] ℝ) :
    oneFormEquiv (α.comp L) = (oneFormEquiv α).compContinuousLinearMap L := by ext v; rfl

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev SmoothCovector :=
  Cₛ^∞⟮I; E →L[ℝ] ℝ, (fun x : M => TangentSpace I x →L[ℝ] ℝ)⟯

/-- Covector regularity is regularity of its actual tangent-trivialization coefficients. -/
theorem contMDiffAt_covector_iff {r : ℕ∞ω}
    {α : ∀ x : M, TangentSpace I x →L[ℝ] ℝ} {x : M} :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) r
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y (α y)) x ↔
    ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) r
      (fun y => (α y).comp ((trivializationAt E (TangentSpace I) x).symmL ℝ y)) x := by
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  apply Iff.of_eq
  apply congrArg (fun f : M → E →L[ℝ] ℝ => ContMDiffAt I 𝓘(ℝ, E →L[ℝ] ℝ) r f x)
  funext y
  ext v
  simp [inCoordinates]

/-- The one-form/covector identification preserves local regularity in both directions. -/
theorem contMDiffAt_oneForm_iff {r : ℕ∞ω}
    {α : ∀ x : M, TangentSpace I x →L[ℝ] ℝ} {x : M} :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) r
      (fun y => TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (oneFormEquiv (α y))) x ↔
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) r
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) y (α y)) x := by
  rw [contMDiffAt_form_iff, contMDiffAt_covector_iff]
  let e := (ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℝ)
    (0 : Fin 1)).toContinuousLinearEquiv
  have hc : trivializationCoefficients I (fun y => oneFormEquiv (α y)) x =
      fun y => e ((α y).comp ((trivializationAt E (TangentSpace I) x).symmL ℝ y)) := by
    funext y
    ext v
    rfl
  rw [hc]
  constructor
  · intro h
    simpa only [Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply] using!
      e.symm.toContinuousLinearMap.contMDiffAt.comp x h
  · intro h
    exact e.toContinuousLinearMap.contMDiffAt.comp x h

/-- Smooth cotangent sections and smooth native one-forms are linearly equivalent. -/
def smoothOneFormEquiv : SmoothCovector I (M := M) ≃ₗ[ℝ] SmoothForm I M 1 where
  toFun α := ⟨fun x => oneFormEquiv (α x), fun x => (contMDiffAt_oneForm_iff I).mpr (α.contMDiff x)⟩
  invFun α := ⟨fun x => oneFormEquiv.symm (α x), fun x =>
    (contMDiffAt_oneForm_iff I).mp (by simpa only [LinearEquiv.apply_symm_apply] using α.contMDiff x)⟩
  left_inv α := by ext x : 1; exact oneFormEquiv.symm_apply_apply (α x)
  right_inv α := by ext x : 1; exact oneFormEquiv.apply_symm_apply (α x)
  map_add' α β := by ext x v; rfl
  map_smul' r α := by ext x v; rfl

@[simp] theorem smoothOneFormEquiv_apply (α : SmoothCovector I (M := M)) (x : M)
    (v : Fin 1 → TangentSpace I x) : smoothOneFormEquiv I α x v = α x (v 0) := rfl

end ProjectAInos.SmoothGeometry.DifferentialForm
