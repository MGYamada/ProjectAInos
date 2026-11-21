/-
Copyright (c) 2026 Masahiko G. Yamada. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Bessel
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic

/-! # The Bessel equation and recurrences for complex order

Differentiate the entire regularized ₀F₁ series and use the reciprocal gamma recurrence even
at gamma poles. The principal power in Mathlib's first-kind Bessel function is differentiable on
the slit plane, where both order recurrences and the differential equation follow.
-/

@[expose] public section
noncomputable section

open Complex FormalMultilinearSeries
namespace ProjectAinos.SpecialFunctions.Bessel

private abbrev F (b : ℂ) := regularizedHGFun 0 {b}
private abbrev a (b : ℂ) := regularizedHGFunCoeff 0 {b}
private abbrev P (b : ℂ) := regularizedHGFunSeries 0 {b}

private theorem next_coeff (b : ℂ) (n : ℕ) : (n + 1 : ℂ) * a b (n + 1) = a (b + 1) n := by
  simp [a, regularizedHGFunCoeff, Nat.factorial_succ, add_comm, add_left_comm]
  field_simp

private theorem lower_coeff (b : ℂ) (n : ℕ) : a b n = (b + n) * a (b + 1) n := by
  have h := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (b + n)
  simp only [a, regularizedHGFunCoeff, Multiset.map_zero, Multiset.prod_zero,
    Multiset.map_singleton, Multiset.prod_singleton, one_div, mul_inv]
  rw [show b + 1 + n = b + n + 1 by ring, h]
  ring

private theorem series (b z : ℂ) : HasSum (fun n : ℕ => z ^ n * a b n) (F b z) := by
  simpa [F, P, a, regularizedHGFun, apply_eq_pow_smul_coeff, smul_eq_mul] using
    ((P b).hasFPowerSeriesOnBall (by simp [P])).hasSum (y := z) (by simp [P])

private theorem deriv_F (b z : ℂ) : HasDerivAt (F b) (F (b + 1) z) z := by
  have hs := ((P b).hasFPowerSeriesOnBall (by simp [P])).fderiv.hasSum (y := z) (by simp [P])
  have h := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).hasSum hs
  have he : deriv (F b) z = F (b + 1) z := by
    apply HasSum.unique _ (series _ _)
    change HasSum _ ((fderiv ℂ (P b).sum z) 1)
    simpa only [zero_add, ContinuousLinearMap.apply_apply,
      apply_eq_pow_smul_coeff, _root_.smul_apply, derivSeries_coeff_one, P,
      regularizedHGFunSeries_coeff,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_succ, next_coeff] using h
  rw [← he]
  exact (analyticAt_regularizedHGFun_zero ..).differentiableAt.hasDerivAt

private theorem contiguous (b z : ℂ) : F b z = b * F (b + 1) z + z * F (b + 1 + 1) z := by
  have h : HasSum (fun n : ℕ => z ^ n * (n * a (b + 1) n)) (z * F (b + 1 + 1) z) := by
    apply (hasSum_nat_add_iff' 1).mp
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, mul_zero, sub_zero, Nat.cast_succ,
      next_coeff, pow_succ]
    exact ((series (b + 1 + 1) z).mul_left z).congr_fun fun n => by ring
  apply (series b z).unique
  exact (((series (b + 1) z).mul_left b).add h).congr_fun fun n => by rw [lower_coeff b]; ring

private theorem half_slit {z : ℂ} (hz : z ∈ slitPlane) : z / 2 ∈ slitPlane := by
  simpa [mem_slitPlane_iff, div_ofNat_re, div_ofNat_im] using hz

/-- Differentiation of Mathlib's `J` in terms of the next order. -/
theorem hasDerivAt_besselJ (a z : ℂ) (hz : z ∈ slitPlane) :
    HasDerivAt (besselJ a) (a / z * besselJ a z - besselJ (a + 1) z) z := by
  have ht := (hasDerivAt_id z).div_const (2 : ℂ)
  have h₁ := ht.cpow_const (c := a) (half_slit hz)
  have h₂ := (deriv_F (a + 1) (-(z / 2) ^ 2)).comp z ((ht.pow 2).neg)
  convert h₁.mul h₂ using 1
  · rfl
  unfold besselJ
  simp only [id_eq, cpow_add _ _ (slitPlane_ne_zero (half_slit hz)),
    cpow_sub _ _ (slitPlane_ne_zero (half_slit hz)), cpow_one, Nat.cast_ofNat, F,
    Function.comp_apply, Pi.neg_apply, Pi.pow_apply]
  field_simp [slitPlane_ne_zero hz]
  ring

/-- Three-term recurrence for all complex orders on the principal slit plane. -/
theorem recurrence (a z : ℂ) (hz : z ∈ slitPlane) :
    besselJ (a - 1) z + besselJ (a + 1) z = 2 * a / z * besselJ a z := by
  have h := contiguous a (-(z / 2) ^ 2)
  unfold besselJ
  simp only [sub_add_cancel, cpow_sub _ _ (slitPlane_ne_zero (half_slit hz)),
    cpow_add _ _ (slitPlane_ne_zero (half_slit hz)), cpow_one]
  change _ / _ * F a _ + _ * _ * F (a + 1 + 1) _ = _ * (_ * F (a + 1) _)
  rw [h]
  field_simp [slitPlane_ne_zero hz]
  ring

/-- The derivative relation `2J′ₐ = Jₐ₋₁ − Jₐ₊₁`. -/
theorem twice_deriv (a z : ℂ) (hz : z ∈ slitPlane) :
    2 * deriv (besselJ a) z = besselJ (a - 1) z - besselJ (a + 1) z := by
  rw [(hasDerivAt_besselJ a z hz).deriv]
  linear_combination -(recurrence a z hz)

/-- Bessel's differential equation for the pinned complex first-kind Bessel function. -/
theorem equation (a z : ℂ) (hz : z ∈ slitPlane) :
    z ^ 2 * deriv (deriv (besselJ a)) z + z * deriv (besselJ a) z +
      (z ^ 2 - a ^ 2) * besselJ a z = 0 := by
  have hz0 := slitPlane_ne_zero hz
  have hd := hasDerivAt_besselJ a z hz
  have he := (((hasDerivAt_const z a).div (hasDerivAt_id z) hz0).mul hd).sub
    (hasDerivAt_besselJ (a + 1) z hz)
  have hfun : deriv (besselJ a) =ᶠ[nhds z] (fun x => a / x * besselJ a x - besselJ (a + 1) x) :=
    Filter.eventually_of_mem (isOpen_slitPlane.mem_nhds hz) fun x hx =>
      (hasDerivAt_besselJ a x hx).deriv
  rw [(he.congr_of_eventuallyEq hfun).deriv, hd.deriv]
  have hr := recurrence (a + 1) z hz
  rw [add_sub_cancel_right] at hr
  dsimp only [id_eq, Pi.div_apply]
  field_simp [hz0] at hr ⊢
  linear_combination z * hr

end ProjectAinos.SpecialFunctions.Bessel
