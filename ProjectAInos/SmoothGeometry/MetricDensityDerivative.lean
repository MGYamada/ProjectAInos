/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.MetricDensity
public import ProjectAInos.SmoothGeometry.DifferentialForm.FiniteDual
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-! # Differentiating a metric determinant and its positive density

The derivative in a metric-compatible direction `A * G + G * Aᵀ`
is controlled by the trace of `A`. The proof uses multilinearity of the
determinant and works for indefinite metrics as well.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace ProjectAInos.SmoothGeometry.MetricDensity

variable {n : ℕ}

/-- Row multilinearity gives the derivative of the determinant in any direction. -/
theorem fderiv_det_apply (G D : Fin n → Fin n → ℝ) :
    fderiv ℝ (fun A : Fin n → Fin n → ℝ => Matrix.det (Matrix.of A)) G D =
      ∑ i, (Matrix.updateRow (Matrix.of G) i (D i)).det := by
  let f := (DifferentialForm.finiteContinuousAlternating
    (Matrix.detRowAlternating : (Fin n → ℝ) [⋀^Fin n]→ₗ[ℝ] ℝ)).toContinuousMultilinearMap
  have h : (fun A : Fin n → Fin n → ℝ => Matrix.det (Matrix.of A)) = f := rfl
  rw [h, (f.hasFDerivAt G).fderiv, ContinuousMultilinearMap.linearDeriv_apply]
  rfl

/-- Left multiplication changes the determinant by `trace A * det G` to first order. -/
theorem fderiv_det_mul_left (G A : Fin n → Fin n → ℝ) :
    fderiv ℝ (fun B : Fin n → Fin n → ℝ => Matrix.det (Matrix.of B)) G
      (Matrix.of A * Matrix.of G) = Matrix.trace (Matrix.of A) * Matrix.det (Matrix.of G) := by
  rw [fderiv_det_apply]
  have h (i : Fin n) : (Matrix.of A * Matrix.of G) i = ∑ j, A i j • G j := by
    ext k
    simp [Matrix.mul_apply, Finset.sum_apply]
  simp_rw [h]
  have hr (i : Fin n) : ((Matrix.of G).updateRow i (∑ j, A i j • G j)).det =
      A i i * (Matrix.of G).det := Matrix.det_updateRow_sum _ _ _
  simp_rw [hr]
  simp [Matrix.trace, Finset.sum_mul]

/-- Right multiplication has the same trace formula, by transposition. -/
theorem fderiv_det_mul_right (G A : Fin n → Fin n → ℝ) :
    fderiv ℝ (fun B : Fin n → Fin n → ℝ => Matrix.det (Matrix.of B)) G
      (Matrix.of G * Matrix.of A) = Matrix.trace (Matrix.of A) * Matrix.det (Matrix.of G) := by
  let T : (Fin n → Fin n → ℝ) →L[ℝ] (Fin n → Fin n → ℝ) :=
    LinearMap.toContinuousLinearMap {
      toFun B := Matrix.transpose (Matrix.of B)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hc := ((contDiff_matrix_det (n := n) (r := 1)).differentiable (by simp)
    (T G)).hasFDerivAt.comp G T.hasFDerivAt
  have hf : (fun B : Fin n → Fin n → ℝ => Matrix.det (Matrix.of (T B))) =
      fun B : Fin n → Fin n → ℝ => Matrix.det (Matrix.of B) := by
    funext B
    exact Matrix.det_transpose _
  change HasFDerivAt (fun B => Matrix.det (Matrix.of (T B))) _ G at hc
  rw [hf] at hc
  rw [hc.fderiv]
  change fderiv ℝ (fun B : Fin n → Fin n → ℝ => Matrix.det (Matrix.of B))
    (Matrix.transpose (Matrix.of G)) (Matrix.transpose (Matrix.of G * Matrix.of A)) = _
  rw [Matrix.transpose_mul]
  have hm := fderiv_det_mul_left (Matrix.transpose (Matrix.of G)) (Matrix.transpose (Matrix.of A))
  change fderiv ℝ (fun B : Fin n → Fin n → ℝ => Matrix.det (Matrix.of B))
    (Matrix.transpose (Matrix.of G)) ((Matrix.of A).transpose * (Matrix.of G).transpose) =
    (Matrix.of A).transpose.trace * (Matrix.of G).transpose.det at hm
  simpa only [Matrix.trace_transpose, Matrix.det_transpose] using hm

/-- The determinant derivative in a metric-compatible direction. -/
theorem fderiv_det_compatible (G A : Fin n → Fin n → ℝ) :
    fderiv ℝ (fun B : Fin n → Fin n → ℝ => Matrix.det (Matrix.of B)) G
      (Matrix.of A * Matrix.of G + Matrix.of G * (Matrix.of A).transpose) =
      2 * Matrix.trace (Matrix.of A) * Matrix.det (Matrix.of G) := by
  rw [map_add, fderiv_det_mul_left]
  have hr := fderiv_det_mul_right G (Matrix.transpose (Matrix.of A))
  change fderiv ℝ (fun B : Fin n → Fin n → ℝ => Matrix.det (Matrix.of B)) G
    (Matrix.of G * (Matrix.of A).transpose) =
    (Matrix.of A).transpose.trace * (Matrix.of G).det at hr
  rw [hr]
  rw [Matrix.trace_transpose]
  ring

/-- The positive density differentiates to `trace A * density`, with no definiteness assumption. -/
theorem fderiv_density_compatible (G A : Fin n → Fin n → ℝ)
    (hG : Matrix.det (Matrix.of G) ≠ 0) :
    fderiv ℝ (fun B : Fin n → Fin n → ℝ => Real.sqrt |Matrix.det (Matrix.of B)|) G
      (Matrix.of A * Matrix.of G + Matrix.of G * (Matrix.of A).transpose) =
      Matrix.trace (Matrix.of A) * Real.sqrt |Matrix.det (Matrix.of G)| := by
  have hd := ((contDiff_matrix_det (n := n) (r := 1)).differentiable (by simp) G).hasFDerivAt
  have hs := (hd.abs hG).sqrt (abs_ne_zero.mpr hG)
  rw [hs.fderiv]
  simp only [smul_apply, smul_eq_mul, fderiv_det_compatible]
  have hp : 0 < Real.sqrt |Matrix.det (Matrix.of G)| := Real.sqrt_pos.mpr (abs_pos.mpr hG)
  have hsq := Real.sq_sqrt (abs_nonneg (Matrix.det (Matrix.of G)))
  have hsign : (SignType.sign (Matrix.det (Matrix.of G)) : ℝ) * Matrix.det (Matrix.of G) =
      |Matrix.det (Matrix.of G)| := by
    rcases lt_or_gt_of_ne hG with h | h
    · simp [SignType.sign, h, not_lt.mpr h.le, abs_of_neg h]
    · simp [SignType.sign, h, abs_of_pos h]
  calc
    _ = Matrix.trace (Matrix.of A) *
        ((SignType.sign (Matrix.det (Matrix.of G)) : ℝ) * Matrix.det (Matrix.of G)) /
        Real.sqrt |Matrix.det (Matrix.of G)| := by ring
    _ = Matrix.trace (Matrix.of A) * Real.sqrt |Matrix.det (Matrix.of G)| := by
      rw [hsign]
      apply (div_eq_iff (ne_of_gt hp)).mpr
      rw [mul_assoc, ← pow_two, hsq]

theorem differentiableAt_density (G : Fin n → Fin n → ℝ)
    (hG : Matrix.det (Matrix.of G) ≠ 0) :
    DifferentiableAt ℝ (fun B : Fin n → Fin n → ℝ => Real.sqrt |Matrix.det (Matrix.of B)|) G :=
  ((((contDiff_matrix_det (n := n) (r := 1)).differentiable (by simp) G).hasFDerivAt.abs hG).sqrt
    (abs_ne_zero.mpr hG)).differentiableAt

end ProjectAInos.SmoothGeometry.MetricDensity
