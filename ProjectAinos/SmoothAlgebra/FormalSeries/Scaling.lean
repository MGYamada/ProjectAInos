/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SmoothAlgebra.FormalSeries.Bracket
public import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# The canonical scaling of formal power series

The substitution `q ↦ λ q`, `p ↦ λ⁻¹ p` with `λ ≠ 0` is an automorphism
`scale λ` of `ℝ[[q, p]]` that preserves the Poisson bracket (`scale_bracket`).
-/

@[expose] public section
noncomputable section

open MvPowerSeries

namespace ProjectAinos.SmoothAlgebra.FormalSeries

theorem prod_add_single {σ : Type*} (a : σ → ℝ) (n : σ →₀ ℕ) (i : σ) :
    (n + Finsupp.single i 1).prod (fun s m => a s ^ m) =
      n.prod (fun s m => a s ^ m) * a i := by
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
    Finsupp.prod_single_index (h := fun s m => a s ^ m) (pow_zero _), pow_one]

/-- A partial derivative of a rescaled series. -/
theorem pderiv_rescale {σ : Type*} (a : σ → ℝ) (i : σ) (f : MvPowerSeries σ ℝ) :
    pderiv i (rescale a f) = a i • rescale a (pderiv i f) := by
  ext n
  rw [coeff_pderiv, coeff_rescale, map_smul, coeff_rescale, coeff_pderiv, prod_add_single,
    smul_eq_mul]
  ring

theorem rescale_X {σ : Type*} (a : σ → ℝ) (i : σ) :
    rescale a (X i : MvPowerSeries σ ℝ) = a i • X i := by
  classical
  ext n
  rw [coeff_rescale, map_smul, coeff_X, smul_eq_mul]
  split_ifs with h
  · subst h
    rw [Finsupp.prod_single_index (h := fun s m => a s ^ m) (pow_zero _), pow_one]
  · rw [mul_zero, mul_zero]

/-- The bracket of two rescaled series. -/
theorem bracket_rescale (a : Fin 2 → ℝ) (f g : PhaseSeries) :
    bracket (rescale a f) (rescale a g) = (a 0 * a 1) • rescale a (bracket f g) := by
  rw [bracket, bracket, pderiv_rescale, pderiv_rescale, pderiv_rescale, pderiv_rescale,
    map_sub, map_mul, map_mul, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (a 1) (a 0),
    smul_sub]

/-- The factors of the canonical scaling `q ↦ λ q`, `p ↦ λ⁻¹ p`. -/
def scaling (lam : ℝ) : Fin 2 → ℝ := ![lam, lam⁻¹]

theorem scaling_mul_inv {lam : ℝ} (hlam : lam ≠ 0) : scaling lam * scaling lam⁻¹ = 1 := by
  funext i
  fin_cases i <;> simp [scaling, hlam]

theorem scaling_inv_mul {lam : ℝ} (hlam : lam ≠ 0) : scaling lam⁻¹ * scaling lam = 1 := by
  funext i
  fin_cases i <;> simp [scaling, hlam]

/-- The canonical scaling `q ↦ λ q`, `p ↦ λ⁻¹ p` as an automorphism of the
algebra. -/
def scale (lam : ℝ) (hlam : lam ≠ 0) : PhaseSeries ≃ₐ[ℝ] PhaseSeries :=
  AlgEquiv.ofAlgHom (rescaleAlgHom (scaling lam)) (rescaleAlgHom (scaling lam⁻¹))
    (by rw [← rescaleAlgHom_mul, scaling_inv_mul hlam, rescaleAlgHom_one])
    (by rw [← rescaleAlgHom_mul, scaling_mul_inv hlam, rescaleAlgHom_one])

theorem scale_apply (lam : ℝ) (hlam : lam ≠ 0) (f : PhaseSeries) :
    scale lam hlam f = rescale (scaling lam) f :=
  rescaleAlgHom_apply _ f

/-- The canonical scaling preserves the Poisson bracket. -/
theorem scale_bracket (lam : ℝ) (hlam : lam ≠ 0) (f g : PhaseSeries) :
    scale lam hlam (bracket f g) = bracket (scale lam hlam f) (scale lam hlam g) := by
  rw [scale_apply, scale_apply, scale_apply, bracket_rescale]
  have h : scaling lam 0 * scaling lam 1 = 1 := by simp [scaling, hlam]
  rw [h, one_smul]

theorem scale_X_zero (lam : ℝ) (hlam : lam ≠ 0) :
    scale lam hlam (X 0 : PhaseSeries) = lam • X 0 := by
  rw [scale_apply, rescale_X]
  simp [scaling]

theorem scale_X_one (lam : ℝ) (hlam : lam ≠ 0) :
    scale lam hlam (X 1 : PhaseSeries) = lam⁻¹ • X 1 := by
  rw [scale_apply, rescale_X]
  simp [scaling]

end ProjectAinos.SmoothAlgebra.FormalSeries
