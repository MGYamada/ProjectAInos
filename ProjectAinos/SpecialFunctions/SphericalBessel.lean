/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ProjectAinos.SpecialFunctions.LegendreMonomials
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Spherical Bessel functions and Rayleigh's plane-wave expansion

The Legendre integral normalizes the regular spherical Bessel function also at the origin.
Expand the plane wave in its entire exponential series, expand each monomial in the Legendre
basis, and interchange the two sums using the positive monomial weights of total mass one.
-/

@[expose] public section
noncomputable section

open Complex MeasureTheory
namespace ProjectAinos.SpecialFunctions.Bessel
open Legendre

/-- Regular spherical Bessel function of degree `n`, by its entire Legendre integral. -/
def sphericalJ (n : ℕ) (z : ℂ) : ℂ :=
  (∫ t in (-1 : ℝ)..1, exp (I * z * t) * ((polynomial n).eval t : ℝ)) / (2 * I ^ n)

/-- The regular mode has value one in degree zero and vanishes in positive degree at the origin. -/
@[simp] theorem sphericalJ_zero (n : ℕ) : sphericalJ n 0 = if n = 0 then 1 else 0 := by
  have h := integral_mul n 0
  simp only [polynomial_zero, Polynomial.eval_one, mul_one] at h
  simp only [sphericalJ, mul_zero, zero_mul, exp_zero, one_mul, intervalIntegral.integral_ofReal, h]
  split_ifs with hn
  · subst n
    norm_num
  · simp

/-- The zeroth regular spherical Bessel function is the cardinal sine away from zero. -/
theorem sphericalJ_zero_order {z : ℂ} (hz : z ≠ 0) : sphericalJ 0 z = sin z / z := by
  rw [sphericalJ]
  simp only [polynomial_zero, Polynomial.eval_one, Complex.ofReal_one, mul_one, pow_zero]
  rw [integral_exp_mul_complex (mul_ne_zero I_ne_zero hz)]
  simp only [Complex.ofReal_one, Complex.ofReal_neg, mul_one, mul_neg]
  rw [mul_comm I z, Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I, cos_neg, sin_neg]
  field_simp
  ring

private def term (z : ℂ) (k : ℕ) : ℂ := (I * z) ^ k / k.factorial

private theorem wave (z : ℂ) (t : ℝ) :
    HasSum (fun k : ℕ => term z k * (t : ℂ) ^ k) (exp (I * z * t)) := by
  rw [Complex.exp_eq_exp_ℂ]
  apply (NormedSpace.expSeries_div_hasSum_exp (I * z * t)).congr_fun
  intro k
  simp [term, mul_pow, div_mul_eq_mul_div]

private theorem summable_term (z : ℂ) : Summable (fun k => ‖term z k‖) := by
  simpa using (wave z 1).summable.norm

private theorem sum_coeff (n : ℕ) (z : ℂ) :
    HasSum (fun k => term z k * (monomialWeights k n : ℂ))
      ((2 * (n : ℂ) + 1) * I ^ n * sphericalJ n z) := by
  let P (t : ℝ) : ℂ := ((polynomial n).eval t : ℝ)
  let F (k : ℕ) (t : ℝ) := term z k * (t : ℂ) ^ k * P t
  have bound (t : ℝ) (ht : t ∈ Set.uIoc (-1 : ℝ) 1) : |t| ≤ 1 := by
    rw [Set.uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at ht
    exact abs_le.mpr ⟨ht.1.le, ht.2⟩
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (a := -1) (b := 1)
    (μ := volume) (F := F) (fun k _ => ‖term z k‖)
    (fun _ => Continuous.aestronglyMeasurable (by unfold F P; fun_prop))
    (fun k => ae_of_all _ fun t ht => by
      have ht' := bound t ht
      simp only [F, P, norm_mul, norm_pow, norm_real, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (by positivity) (abs_eval_le_one n ht')).trans
        (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (abs_nonneg _) ht')))
    (ae_of_all _ fun _ _ => summable_term z) intervalIntegrable_const
    (ae_of_all _ fun t _ => (wave z t).mul_right (P t))
  have hg k : (∫ t in (-1 : ℝ)..1, F k t) =
      term z k * (monomialWeights k n : ℂ) * (2 / (2 * (n : ℂ) + 1)) := by
    simp only [F, P, mul_assoc, intervalIntegral.integral_const_mul, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, intervalIntegral.integral_ofReal, integral_pow_mul]
    push_cast
    ring
  have hn : (2 * (n : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (by positivity : 2 * (n : ℝ) + 1 ≠ 0)
  convert (h.mul_right ((2 * (n : ℂ) + 1) / 2)) using 1
  · funext k
    rw [hg]
    field_simp
  · unfold sphericalJ P
    field_simp

/-- Rayleigh's absolutely convergent plane-wave expansion, for arbitrary complex wave argument. -/
theorem hasSum_planeWave (z : ℂ) {t : ℝ} (ht : |t| ≤ 1) :
    HasSum (fun n : ℕ => (2 * (n : ℂ) + 1) * I ^ n * sphericalJ n z *
      ((polynomial n).eval t : ℝ)) (exp (I * z * t)) := by
  let f (p : ℕ × ℕ) := term z p.1 * (monomialWeights p.1 p.2 : ℂ) *
    ((polynomial p.2).eval t : ℝ)
  let g (p : ℕ × ℕ) := ‖term z p.1‖ * monomialWeights p.1 p.2
  have row k : HasSum (fun n => g (k,n)) ‖term z k‖ := by
    simpa [g] using (hasSum_monomialWeights k).mul_left ‖term z k‖
  have hg : Summable g := (summable_prod_of_nonneg (f := g) (fun p =>
    mul_nonneg (norm_nonneg _) (monomialWeights_nonneg p.1 p.2))).mpr
    ⟨fun k => (row k).summable, by simpa only [fun k => (row k).tsum_eq] using summable_term z⟩
  have hf : Summable f := hg.of_norm_bounded fun ⟨k,n⟩ => by
    simp only [f, g, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (monomialWeights_nonneg k n)]
    exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (monomialWeights_nonneg k n))
      (abs_eval_le_one n ht)
  have byDegree k : HasSum (fun n => f (k,n)) (term z k * (t : ℂ) ^ k) := by
    simpa [f, mul_assoc] using
      (Complex.hasSum_ofReal.mpr (hasSum_monomial k t)).mul_left (term z k)
  have total := (hf.hasSum.prod_fiberwise byDegree).unique (wave z t)
  have H : HasSum f (exp (I * z * t)) := total ▸ hf.hasSum
  apply ((Equiv.prodComm ℕ ℕ).hasSum_iff.mpr H).prod_fiberwise
  intro n
  exact (sum_coeff n z).mul_right (Complex.ofReal ((polynomial n).eval t))

end ProjectAinos.SpecialFunctions.Bessel
