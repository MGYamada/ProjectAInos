/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.InteriorDerivative
public import ProjectAInos.SmoothGeometry.DifferentialForm.TwoForm

/-! # Coordinate volume duality for bivectors in four dimensions

The signs use first-slot contraction and determinant-normalized volume.
This metric-free calculation will be applied to density-weighted raised
two-form components in each oriented chart.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open ContinuousLinearMap
open scoped Topology

namespace ProjectAInos.SmoothGeometry.DifferentialForm

local notation "E" => (Fin 4 → ℝ)
local notation "A" => (Fin 4 → Fin 4 → ℝ)

/-- The volume-dual two-form, with the sign used by `H = -⋆F`. -/
def bivectorVolume : A →L[ℝ] (E [⋀^Fin 2]→L[ℝ] ℝ) :=
  -((proj 1 : E →L[ℝ] ℝ).comp (proj 0 : A →L[ℝ] E)).smulRight (coordinateForm ![2, 3]) +
    ((proj 2 : E →L[ℝ] ℝ).comp (proj 0 : A →L[ℝ] E)).smulRight (coordinateForm ![1, 3]) -
    ((proj 3 : E →L[ℝ] ℝ).comp (proj 0 : A →L[ℝ] E)).smulRight (coordinateForm ![1, 2]) -
    ((proj 2 : E →L[ℝ] ℝ).comp (proj 1 : A →L[ℝ] E)).smulRight (coordinateForm ![0, 3]) +
    ((proj 3 : E →L[ℝ] ℝ).comp (proj 1 : A →L[ℝ] E)).smulRight (coordinateForm ![0, 2]) -
    ((proj 3 : E →L[ℝ] ℝ).comp (proj 2 : A →L[ℝ] E)).smulRight (coordinateForm ![0, 1])

theorem bivectorVolume_apply (B : A) :
    bivectorVolume B = -B 0 1 • coordinateForm ![2, 3] + B 0 2 • coordinateForm ![1, 3] -
      B 0 3 • coordinateForm ![1, 2] - B 1 2 • coordinateForm ![0, 3] +
      B 1 3 • coordinateForm ![0, 2] - B 2 3 • coordinateForm ![0, 1] := by
  ext v
  simp [bivectorVolume]

set_option maxHeartbeats 1600000 in
/-- The alternating derivative of volume duality is the contraction divergence. -/
theorem alternatize_bivectorVolume (D : E →L[ℝ] A)
    (hD : ∀ u i j, D u i j = -D u j i) :
    ContinuousAlternatingMap.alternatizeUncurryFin (bivectorVolume.comp D) =
      interior (fun j => ∑ i : Fin 4, D (Pi.single i 1) i j) (coordinateForm id) := by
  have hdiag (u : E) (i : Fin 4) : D u i i = 0 := by linarith [hD u i i]
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply Module.Basis.ext_alternating (Pi.basisFun ℝ (Fin 4))
  intro f _
  have ht : (fun i : Fin 3 => (Pi.basisFun ℝ (Fin 4)) (f i)) =
      ![Pi.single (f 0) 1, Pi.single (f 1) 1, Pi.single (f 2) 1] := by
    ext i j
    fin_cases i <;> simp [Pi.basisFun_apply]
  change ContinuousAlternatingMap.alternatizeUncurryFin (bivectorVolume.comp D)
    (fun i => (Pi.basisFun ℝ (Fin 4)) (f i)) = _
  rw [ht]
  generalize f 0 = i
  generalize f 1 = j
  generalize f 2 = k
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    norm_num [ContinuousAlternatingMap.alternatizeUncurryFin_apply, bivectorVolume_apply,
      interior, coordinateForm_apply, Matrix.det_fin_two, Matrix.det_succ_row_zero,
      Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove, Pi.single_apply,
      hdiag, hD _ 1 0, hD _ 2 0, hD _ 2 1, hD _ 3 0, hD _ 3 1, hD _ 3 2] <;> ring

theorem fderiv_matrix_apply {B : E → A} {x : E} (hB : DifferentiableAt ℝ B x)
    (i j : Fin 4) (u : E) :
    fderiv ℝ (fun y => B y i j) x u = fderiv ℝ B x u i j := by
  let L : A →L[ℝ] ℝ := (proj j : E →L[ℝ] ℝ).comp (proj i : A →L[ℝ] E)
  exact congrArg (fun K : E →L[ℝ] ℝ => K u) (L.hasFDerivAt.comp x hB.hasFDerivAt).fderiv

/-- Local antisymmetry and local differentiability suffice for the derivative formula. -/
theorem extDeriv_bivectorVolume {B : E → A} {x : E} (hB : DifferentiableAt ℝ B x)
    (hskew : ∀ᶠ y in 𝓝 x, ∀ i j, B y i j = -B y j i) :
    extDeriv (fun y => bivectorVolume (B y)) x =
      interior (fun j => ∑ i : Fin 4, fderiv ℝ B x (Pi.single i 1) i j) (coordinateForm id) := by
  have hd : ∀ u i j, fderiv ℝ B x u i j = -fderiv ℝ B x u j i := by
    intro u i j
    rw [← fderiv_matrix_apply hB i j u, ← fderiv_matrix_apply hB j i u]
    have heq : (fun y => B y i j) =ᶠ[𝓝 x] fun y => -B y j i := by
      filter_upwards [hskew] with y hy
      exact hy i j
    rw [heq.fderiv_eq, fderiv_fun_neg]
    rfl
  have hf := bivectorVolume.hasFDerivAt.comp x hB.hasFDerivAt
  simp only [Function.comp_def] at hf
  unfold extDeriv
  rw [hf.fderiv]
  exact alternatize_bivectorVolume (fderiv ℝ B x) hd

end ProjectAInos.SmoothGeometry.DifferentialForm
