/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothGeometry.DifferentialForm.InteriorDerivative
public import ProjectAinos.SmoothGeometry.DifferentialForm.TwoForm

/-! # Coordinate volume duality for bivectors in four dimensions

The signs use first-slot contraction and determinant-normalized volume.
This metric-free calculation will be applied to density-weighted raised
two-form components in each oriented chart.
-/

@[expose] public section
noncomputable section
open ContinuousLinearMap
open scoped Topology

namespace ProjectAinos.SmoothGeometry.DifferentialForm

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

/-- Evaluate both sides of `alternatize_bivectorVolume` on one triple of basis vectors. The
three indices are distinct, and the cases in which two of them coincide are excluded by the
hypotheses before any computation. -/
local macro "bivector_basis_cases" hD:ident hdiag:ident hj:ident hk:ident hjk:ident : tactic =>
  `(tactic| first
    | exact absurd rfl $hj
    | exact absurd rfl $hk
    | exact absurd rfl $hjk
    | (norm_num [ContinuousAlternatingMap.alternatizeUncurryFin_apply, bivectorVolume_apply,
        interior, coordinateForm_apply, Matrix.det_fin_two, Matrix.det_succ_row_zero,
        Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.removeNth, Fin.succAbove, Pi.single_apply,
        $hdiag:ident, $hD:ident _ 1 0, $hD:ident _ 2 0, $hD:ident _ 2 1, $hD:ident _ 3 0,
        $hD:ident _ 3 1, $hD:ident _ 3 2] <;> ring))

private theorem alternatize_bivectorVolume_basis_zero (D : E →L[ℝ] A)
    (hD : ∀ u i j, D u i j = -D u j i) (j k : Fin 4) (hj : (0 : Fin 4) ≠ j)
    (hk : (0 : Fin 4) ≠ k) (hjk : j ≠ k) :
    ContinuousAlternatingMap.alternatizeUncurryFin (bivectorVolume.comp D)
        ![Pi.single 0 1, Pi.single j 1, Pi.single k 1] =
      (interior (fun j => ∑ i : Fin 4, D (Pi.single i 1) i j) (coordinateForm id)).toAlternatingMap
        ![Pi.single 0 1, Pi.single j 1, Pi.single k 1] := by
  have hdiag (u : E) (i : Fin 4) : D u i i = 0 := by linarith [hD u i i]
  fin_cases j <;> fin_cases k <;> bivector_basis_cases hD hdiag hj hk hjk

private theorem alternatize_bivectorVolume_basis_one (D : E →L[ℝ] A)
    (hD : ∀ u i j, D u i j = -D u j i) (j k : Fin 4) (hj : (1 : Fin 4) ≠ j)
    (hk : (1 : Fin 4) ≠ k) (hjk : j ≠ k) :
    ContinuousAlternatingMap.alternatizeUncurryFin (bivectorVolume.comp D)
        ![Pi.single 1 1, Pi.single j 1, Pi.single k 1] =
      (interior (fun j => ∑ i : Fin 4, D (Pi.single i 1) i j) (coordinateForm id)).toAlternatingMap
        ![Pi.single 1 1, Pi.single j 1, Pi.single k 1] := by
  have hdiag (u : E) (i : Fin 4) : D u i i = 0 := by linarith [hD u i i]
  fin_cases j <;> fin_cases k <;> bivector_basis_cases hD hdiag hj hk hjk

private theorem alternatize_bivectorVolume_basis_two (D : E →L[ℝ] A)
    (hD : ∀ u i j, D u i j = -D u j i) (j k : Fin 4) (hj : (2 : Fin 4) ≠ j)
    (hk : (2 : Fin 4) ≠ k) (hjk : j ≠ k) :
    ContinuousAlternatingMap.alternatizeUncurryFin (bivectorVolume.comp D)
        ![Pi.single 2 1, Pi.single j 1, Pi.single k 1] =
      (interior (fun j => ∑ i : Fin 4, D (Pi.single i 1) i j) (coordinateForm id)).toAlternatingMap
        ![Pi.single 2 1, Pi.single j 1, Pi.single k 1] := by
  have hdiag (u : E) (i : Fin 4) : D u i i = 0 := by linarith [hD u i i]
  fin_cases j <;> fin_cases k <;> bivector_basis_cases hD hdiag hj hk hjk

private theorem alternatize_bivectorVolume_basis_three (D : E →L[ℝ] A)
    (hD : ∀ u i j, D u i j = -D u j i) (j k : Fin 4) (hj : (3 : Fin 4) ≠ j)
    (hk : (3 : Fin 4) ≠ k) (hjk : j ≠ k) :
    ContinuousAlternatingMap.alternatizeUncurryFin (bivectorVolume.comp D)
        ![Pi.single 3 1, Pi.single j 1, Pi.single k 1] =
      (interior (fun j => ∑ i : Fin 4, D (Pi.single i 1) i j) (coordinateForm id)).toAlternatingMap
        ![Pi.single 3 1, Pi.single j 1, Pi.single k 1] := by
  have hdiag (u : E) (i : Fin 4) : D u i i = 0 := by linarith [hD u i i]
  fin_cases j <;> fin_cases k <;> bivector_basis_cases hD hdiag hj hk hjk

/-- The alternating derivative of volume duality is the contraction divergence. -/
theorem alternatize_bivectorVolume (D : E →L[ℝ] A)
    (hD : ∀ u i j, D u i j = -D u j i) :
    ContinuousAlternatingMap.alternatizeUncurryFin (bivectorVolume.comp D) =
      interior (fun j => ∑ i : Fin 4, D (Pi.single i 1) i j) (coordinateForm id) := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  apply Module.Basis.ext_alternating (Pi.basisFun ℝ (Fin 4))
  intro f hf
  have ht : (fun i : Fin 3 => (Pi.basisFun ℝ (Fin 4)) (f i)) =
      ![Pi.single (f 0) 1, Pi.single (f 1) 1, Pi.single (f 2) 1] := by
    ext i j
    fin_cases i <;> simp [Pi.basisFun_apply]
  change ContinuousAlternatingMap.alternatizeUncurryFin (bivectorVolume.comp D)
    (fun i => (Pi.basisFun ℝ (Fin 4)) (f i)) = _
  rw [ht]
  have h01 : f 0 ≠ f 1 := fun h => absurd (hf h) (by decide)
  have h02 : f 0 ≠ f 2 := fun h => absurd (hf h) (by decide)
  have h12 : f 1 ≠ f 2 := fun h => absurd (hf h) (by decide)
  generalize f 0 = i at h01 h02 ⊢
  generalize f 1 = j at h01 h12 ⊢
  generalize f 2 = k at h02 h12 ⊢
  fin_cases i
  · exact alternatize_bivectorVolume_basis_zero D hD j k h01 h02 h12
  · exact alternatize_bivectorVolume_basis_one D hD j k h01 h02 h12
  · exact alternatize_bivectorVolume_basis_two D hD j k h01 h02 h12
  · exact alternatize_bivectorVolume_basis_three D hD j k h01 h02 h12

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

end ProjectAinos.SmoothGeometry.DifferentialForm
