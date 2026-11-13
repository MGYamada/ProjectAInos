/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAInos.SmoothGeometry.DifferentialForm.Calculus
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! # Compact-support Stokes identity in Euclidean coordinates -/

@[expose] public section
noncomputable section

open MeasureTheory
open scoped ContDiff

namespace ProjectAInos.SmoothGeometry.DifferentialForm

variable {n k : ℕ}

theorem exteriorDerivative_contDiff {F : Form (Fin n → ℝ) k} {r : ℕ∞ω}
    (hF : ContDiff ℝ (r + 1) F) : ContDiff ℝ r (exteriorDerivative F) := by
  have hD : ContDiff ℝ r (fderiv ℝ F) := hF.fderiv_right le_rfl
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ (Fin n → ℝ) ℝ
    (n := k)).contDiff.comp hD

/-- Integrating the top-degree exterior derivative of a compactly supported
form over all coordinates gives zero. Each summand is a directional derivative
of a compactly supported scalar coefficient. -/
theorem integral_exteriorDerivative_basis_zero {F : Form (Fin (k + 1) → ℝ) k}
    (hF : ContDiff ℝ 1 F) (hK : HasCompactSupport F) :
    (∫ x, exteriorDerivative F x (Pi.basisFun ℝ (Fin (k + 1)))) = 0 := by
  let b : Fin (k + 1) → Fin (k + 1) → ℝ := Pi.basisFun ℝ (Fin (k + 1))
  let A (i : Fin (k + 1)) := ContinuousAlternatingMap.apply ℝ (Fin (k + 1) → ℝ) ℝ
    (i.removeNth b)
  let f (i : Fin (k + 1)) (x : Fin (k + 1) → ℝ) := A i (F x)
  have hf (i) : ContDiff ℝ 1 (f i) := (A i).contDiff.comp hF
  have hk (i) : HasCompactSupport (f i) := hK.mono fun x hx hzero =>
    hx (by simp [f, hzero])
  have hi (i) : Integrable (fun x => fderiv ℝ (f i) x (b i)) volume :=
    Continuous.integrable_of_hasCompactSupport
      (((hf i).fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const)
      ((hk i).fderiv_apply ℝ (b i))
  have hz (i) : (∫ x, fderiv ℝ (f i) x (b i)) = 0 := by
    have hzero : Integrable (fun x : Fin (k + 1) → ℝ =>
        fderiv ℝ (fun _ : Fin (k + 1) → ℝ => (1 : ℝ)) x (b i) * f i x) volume := by
      simp
    have hleft : Integrable (fun x => (1 : ℝ) * fderiv ℝ (f i) x (b i)) volume := by
      simpa only [one_mul] using hi i
    have hprod : Integrable (fun x => (1 : ℝ) * f i x) volume := by
      simpa only [one_mul] using
        (hf i).continuous.integrable_of_hasCompactSupport (hk i)
    simpa using integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      hzero hleft hprod (fun _ _ => differentiableAt_const _) (fun x _ =>
        (hf i).differentiable one_ne_zero x)
  have he (x : Fin (k + 1) → ℝ) :
      exteriorDerivative F x b =
        ∑ i : Fin (k + 1), (-1 : ℝ) ^ i.val * fderiv ℝ (f i) x (b i) := by
    rw [exteriorDerivative, extDeriv_apply (hF.differentiable one_ne_zero x)]
    apply Finset.sum_congr rfl
    intro i _
    change (-1 : ℤ) ^ i.val • fderiv ℝ (f i) x (b i) = _
    simp only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_eq_mul]
  change (∫ x, exteriorDerivative F x b) = 0
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => (hi i).const_mul _)]
  simp only [integral_const_mul, hz, mul_zero, Finset.sum_const_zero]

end ProjectAInos.SmoothGeometry.DifferentialForm
