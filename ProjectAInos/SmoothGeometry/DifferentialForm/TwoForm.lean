/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Interior
public import ProjectAInos.SmoothGeometry.Tensor.Regularity
public import Mathlib.Topology.VectorBundle.FiniteDimensional

/-! # Native two-forms as smooth bilinear tensors -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Bundle ContinuousLinearMap
open scoped Manifold ContDiff Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul ℝ V] [T2Space V] [FiniteDimensional ℝ V]

/-- Currying a native two-form into the existing continuous hom representation. -/
def twoFormBilinear (α : V [⋀^Fin 2]→L[ℝ] ℝ) : V →L[ℝ] V →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap {
    toFun v := oneFormEquiv.symm (interior v α)
    map_add' v w := by
      ext u
      exact α.vecCons_add (fun _ => u) v w
    map_smul' a v := by
      ext u
      exact α.vecCons_smul (fun _ => u) a v }

@[simp] theorem twoFormBilinear_apply (α : V [⋀^Fin 2]→L[ℝ] ℝ) (v w : V) :
    twoFormBilinear α v w = α ![v, w] := by
  change α (Matrix.vecCons v (fun _ => w)) = α ![v, w]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- Currying is linear in the two-form. -/
def twoFormBilinearLinear : (V [⋀^Fin 2]→L[ℝ] ℝ) →ₗ[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) where
  toFun := twoFormBilinear
  map_add' _ _ := by ext v w; rfl
  map_smul' _ _ := by ext v w; rfl

theorem twoFormBilinear_skew (α : V [⋀^Fin 2]→L[ℝ] ℝ) (v w : V) :
    twoFormBilinear α v w = -twoFormBilinear α w v := by
  have h := α.toAlternatingMap.map_swap ![w, v] (show (0 : Fin 2) ≠ 1 by decide)
  have hv : ![w, v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v, w] := by
    ext i
    fin_cases i <;> rfl
  rw [hv] at h
  rw [twoFormBilinear_apply, twoFormBilinear_apply]
  exact h

variable {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local instance (x : M) : T2Space (TangentSpace I x) := FiberBundle.t2Space E (TangentSpace I) x
local instance (x : M) : FiniteDimensional ℝ (TangentSpace I x) :=
  VectorBundle.finiteDimensional ℝ E (TangentSpace I) x

/-- Currying respects actual bundle smoothness. -/
theorem SmoothForm.contMDiffAt_twoFormBilinear (α : SmoothForm I M 2) (x : M) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y (twoFormBilinear (α y))) x := by
  rw [contMDiffAt_section]
  simp only [hom_trivializationAt_apply]
  apply Tensor.contMDiffAt_clm_iff.mpr
  intro v
  apply Tensor.contMDiffAt_clm_iff.mpr
  intro w
  have h := (α.coefficients_contMDiffAt I x).continuousAlternatingMap_apply
    (f := fun i _ => (![v, w] : Fin 2 → E) i) (fun _ => contMDiffAt_const)
  apply h.congr_of_eventuallyEq
  let e' := trivializationAt (E →L[ℝ] ℝ) (fun y : M => TangentSpace I y →L[ℝ] ℝ) x
  filter_upwards [e'.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt _ _ x)] with y hy
  simp only [inCoordinates, ContinuousLinearMap.comp_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hy]
  simp [e', hom_trivializationAt_apply, inCoordinates, twoFormBilinear_apply,
    trivializationCoefficients]
  congr 1
  ext i
  fin_cases i <;> rfl

/-- The smooth tensor has exactly the same evaluation as the original native two-form. -/
def smoothTwoFormBilinear (α : SmoothForm I M 2) :
    Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] ℝ,
      (fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)⟯ :=
  ⟨fun x => twoFormBilinear (α x), α.contMDiffAt_twoFormBilinear⟩

@[simp] theorem smoothTwoFormBilinear_apply (α : SmoothForm I M 2) (x : M)
    (v w : TangentSpace I x) : smoothTwoFormBilinear α x v w = α x ![v, w] :=
  twoFormBilinear_apply _ _ _

omit [FiniteDimensional ℝ E] in
/-- The coordinate exterior derivative of a two-form has the three alternating terms. -/
theorem extDeriv_two {F : E → E [⋀^Fin 2]→L[ℝ] ℝ} {x : E}
    (hF : DifferentiableAt ℝ F x) (u v w : E) :
    extDeriv F x ![u, v, w] =
      fderiv ℝ (fun y => F y ![v, w]) x u -
      fderiv ℝ (fun y => F y ![u, w]) x v +
      fderiv ℝ (fun y => F y ![u, v]) x w := by
  rw [extDeriv_apply hF]
  have h₁ : Fin.removeNth (1 : Fin 3) ![u, v, w] = ![u, w] := by
    ext i
    fin_cases i <;> rfl
  have h₂ : Fin.removeNth (2 : Fin 3) ![u, v, w] = ![u, v] := by
    ext i
    fin_cases i <;> rfl
  simp [Fin.sum_univ_succ, h₁, h₂, sub_eq_add_neg, add_assoc]

end ProjectAInos.SmoothGeometry.DifferentialForm
